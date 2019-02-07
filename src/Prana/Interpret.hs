{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecursiveDo #-}

-- |

module Prana.Interpret where

import           Control.Concurrent.MVar
import           Control.Monad
import           Data.Foldable
import           Data.Hashable
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.Int
import           Data.Vector (Vector)
import qualified Data.Vector as V
import           Prana.Types
import           System.IO.Unsafe (unsafePerformIO)

deriving instance Hashable MethId
deriving instance Hashable GlobalVarId
deriving instance Hashable LocalVarId

type LocalEnv = HashMap LocalVarId ValueRef

data Env = Env
  { envGlobals :: !(HashMap GlobalVarId ValueRef)
  , envMethods :: !(HashMap MethId Int64)
  }

emptyEnv :: Env
emptyEnv = Env mempty mempty

newtype ValueRef = ValueRef (MVar Value)
  deriving Eq

-- Gnarly, I know :)
instance Show ValueRef where
  show (ValueRef var) = unsafePerformIO $ do
    val <- tryReadMVar var
    return $ case val of
      Nothing -> "<in-progress>"
      Just (Value whnf) -> show whnf
      -- TODO: also do something with locals?
      Just (Thunk _ expr) -> show expr

data Value
  = Value !WHNF
  | Thunk !LocalEnv !Exp
  deriving (Show, Eq)

data WHNF
  = LamW !LocalEnv !LocalVarId !Exp
  | LitW !Lit
  | ConW !ConId !(Vector ValueRef)
  deriving (Show, Eq)

evalExp :: Env -> LocalEnv -> Exp -> IO WHNF
evalExp env@Env{..} local expr = case expr of
  LitE lit -> pure (LitW lit)
  LamE param body -> pure (LamW local param body)
  LetE bindings body -> mdo
    let addBinding mp (k, e) = do
          ref <- ValueRef <$> newMVar (Thunk local' e)
          return $ HM.insert k ref mp
    local' <- foldM addBinding local bindings
    evalExp env local' body
  VarE var ->
    case var of
      ExportedIndex i ->
        case HM.lookup i envGlobals of
          Nothing -> error "eval.VarE.ExportedIndex = Nothing"
          Just ref -> evalValueRef env ref
      LocalIndex i ->
        case HM.lookup i local of
          Nothing -> error "eval.VarE.LocalIndex = Nothing"
          Just ref -> evalValueRef env ref
  AppE (MethodE i) dict ->
    case HM.lookup i envMethods of
      Nothing -> error "AppE.MethodE.MethId = Nothing"
      Just idx ->
        case idx of
          0 -> evalExp env local dict
          _ -> do
            whnf <- evalExp env local dict
            case whnf of
              ConW _cid args ->
                case args V.!? (fromIntegral idx - 1) of
                  Nothing ->
                    error "AppE.Method: Couldn't find method in dictionary!"
                  Just ref -> evalValueRef env ref
              _ -> error "AppE.Method: Expected class dictionary!"
  AppE func arg -> do
    result <- evalExp env local func
    argRef <- ValueRef <$> newMVar (Thunk local arg)
    case result of
      LamW local' param body -> evalExp env (HM.insert param argRef local') body
      LitW lit -> error ("eval.AppE.LitW: expected function: " ++ show lit)
      ConW cid args -> pure (ConW cid (args <> V.singleton argRef))
  -- No alternatives implies that scrutinee will diverge.
  CaseE scrutinee _ _ [] -> evalExp env local scrutinee
  -- TODO: ByteCodeGen has special cases for unit unboxed tuples and
  -- unboxed tuples with state tokens.
  CaseE scrutinee scrutineeBinder _ alts -> do
    scrutineeValue <- evalExp env local scrutinee
    scrutineeRef <- ValueRef <$> newMVar (Value scrutineeValue)
    let local' = HM.insert scrutineeBinder scrutineeRef local
    evalAlts env local' scrutineeValue alts
  ConE cid -> pure (ConW cid mempty)
  -- To support $ and other hacks by GHC.
  WiredInE {} -> error "eval.WiredInE: undefined"
  -- To support type classes (needed for numbers).
  MethodE {} ->
    error "eval.MethodE: should not be evaluated directly, but has been!"
  -- To support numeric operations (ints, chars, etc. ..).
  PrimOpE {} -> error "eval.PrimOpE: undefined"
  -- To support FFI calls (probably do this last):
  FFIE {} -> error "eval.FFIE: undefined"

evalValueRef :: Env -> ValueRef -> IO WHNF
evalValueRef env (ValueRef var) =
  modifyMVar var $ \case
    v@(Value whnf) -> return (v, whnf)
    Thunk local expr -> do
      whnf <- evalExp env local expr
      return (Value whnf, whnf)

-- TODO: Is 'body' a good name?  Perhaps 'rhs' instead?

evalAlts :: Env -> LocalEnv -> WHNF -> [Alt] -> IO WHNF
evalAlts env local scrutineeValue alts =
  case scrutineeValue of
    LamW {} -> error "eval.CaseE.LamW: Didn't expect LamW result from scrutinee."
    LitW litScrutinee -> do
      let matches =
            [ body
            | Alt { altCon = LitAlt lit, altExp = body } <- alts
            , lit == litScrutinee
            ]
      handleMatches matches (evalExp env local)
    ConW conScrutinee conFields -> do
      let matches =
            [ (strictnesses, vars, body)
            | Alt { altCon = DataAlt (DataCon conId strictnesses)
                  , altVars = vars
                  , altExp = body
                  } <- alts
            , conId == conScrutinee
            ]
      handleMatches matches $ \(strictnesses, vars, body) -> do
        evaluatedFields <- zipWithM evalField strictnesses (V.toList conFields)
        let local' =
              foldl'
                (\localEnv (i, ex) -> HM.insert i ex localEnv)
                local
                (zip vars evaluatedFields)
        evalExp env local' body
  where
    handleMatches :: [match] -> (match -> IO WHNF) -> IO WHNF
    handleMatches [] _ =
      case alts of
        Alt { altCon = DEFAULT, altExp = body } : _ ->
          evalExp env local body
        _ -> error "eval.CaseE: Invariant violated: no matching alt"
    handleMatches [match] f = f match
    handleMatches _ _ = error "eval.CaseE: Invariant violated: redundant alts"

    evalField :: Strictness -> ValueRef -> IO ValueRef
    evalField Strict valueRef = do
      void $ evalValueRef env valueRef
      return valueRef
    evalField NonStrict valueRef =
      return valueRef
