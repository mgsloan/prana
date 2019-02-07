{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |

module TestLib where

import           Control.Concurrent.MVar
import           Data.Bifunctor
import           Data.Binary.Get
import qualified Data.ByteString.Lazy as L
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.Int
import           Data.List
import           Data.Maybe
import           GHC.Stack
import           Prana.Decode
import           Prana.Interpret
import           Prana.Types
import           System.Exit
import           System.IO.Temp
import           System.IO.Unsafe (unsafePerformIO)
import           System.Process

deriving instance Num LocalVarId
deriving instance Num GlobalVarId

evalCode :: Exp -> [(String, String)] -> IO WHNF
evalCode expr code = do
  (idmod, methods) <- compileModulesWith Normal code
  let (env, local) = link idmod methods
  evalExp env local expr

ignoreEnv :: WHNF -> WHNF
ignoreEnv (ConW ci _) = ConW ci []
ignoreEnv w = w

data CompileType = Normal

-- | Compile a single module.
compileModule :: CompileType -> String -> String -> IO ([Bind], [(MethodId, Int64)])
compileModule ty name contents =
  fmap (first (snd . head)) (compileModulesWith ty [(name, contents)])

-- | Compile the given sources as a set of modules.
compileModulesWith :: CompileType -> [(String,String)] -> IO ([(String, [Bind])], [(MethodId, Int64)])
compileModulesWith ty modules =
  withSystemTempDirectory
    "prana-compile"
    (\dir -> do
       let fps = map (\(moduleName, src) -> (moduleName ++ ".hs", src)) modules
       mapM_ (\(fp, src) -> writeFile (dir ++ "/" ++ fp) src) fps
       (code, out, err) <- compileFile ty dir (map fst fps)
       case code of
         ExitSuccess -> do
           mods <-
             mapM
               (\(moduleName, _) -> do
                  bytes <-
                    L.readFile (dir ++ "/prana-test_" ++ moduleName ++ ".prana")
                  case runGetOrFail (decodeArray decodeBind) bytes of
                    Left (_, pos, e) ->
                      error
                        ("Decoding error! " ++
                         e ++
                         " at index " ++
                         show pos ++
                         "\n\nFile:\n\n" ++
                         show (L.unpack bytes) ++
                         "\n\nAt index:\n\n" ++
                         show (drop (fromIntegral pos - 1) (L.unpack bytes)))
                    Right (_, _, binds) -> pure (moduleName, binds))
               modules
           bytes <- L.readFile (dir <> "/names-cache.db")
           case runGetOrFail
                  (decodeArray decodeExportedId *> decodeArray decodeLocalId *>
                   decodeArray decodeConstrId *>
                   decodeArray decodeMethodId)
                  bytes of
             Left (_, pos, e) ->
               error
                 ("Decoding error! " ++
                  e ++
                  " at index " ++
                  show pos ++
                  "\n\nFile:\n\n" ++
                  show (L.unpack bytes) ++
                  "\n\nAt index:\n\n" ++
                  show (drop (fromIntegral pos - 1) (L.unpack bytes)))
             Right (_, _, methIds) -> pure (mods, methIds)
         ExitFailure {} -> error (unlines ["Compile failed:", out, err]))

-- | Run a compile with docker in the given dir on the given file.
compileFile :: CompileType -> FilePath -> [FilePath] -> IO (ExitCode, String, String)
compileFile ty pwd fps = do
  case ty of
    Normal ->
      (if False
         then readIt
         else readProcessWithExitCode)
        "docker"
        ([ "run"
         , "-v" ++ pwd ++ ":" ++ pwd
         , "-w" ++ pwd
         , "--rm"
         , "ghc-compile"
         , "sh"
         , "-c"
         , intercalate
             "&&"
             [unwords
                (["ghc", "-O0", "-fbyte-code", "-this-unit-id", "prana-test"] ++
                 fps)
             ,"cp /root/prana/names-cache.db " ++ pwd]
         ])
        ""
  where
    readIt n args _ = do
      code <- System.Process.rawSystem n args
      pure (code, "", "")

-- | Drop the module header that's not of use to us in the test-suite.
dropModuleHeaders :: [(String, [Bind])] -> [(String, [Bind])]
dropModuleHeaders = map (second (filter (not . header)))
  where
    header (Bind { bindVar = ExportedIndex _
                 , bindExp = AppE (AppE (ConE (ConId _)) (AppE (ConE (ConId _)) (LitE (Str "prana-test")))) (AppE (ConE (ConId _)) (LitE (Str _)))
                 }) = True
    header _ = False

link
  :: [(String, [Bind])]
  -> [(MethodId, Int64)]
  -> (Env, LocalEnv)
link mods methods = (Env globals methodsMap, locals)
  where
    bs = concatMap snd mods
    globals =
      HM.fromList
        (mapMaybe
           (\b ->
              case bindVar b of
                ExportedIndex i -> Just (i, mkThunkRef b)
                _ -> Nothing)
           bs)
    locals =
      HM.fromList
        (mapMaybe
           (\b ->
              case bindVar b of
                LocalIndex i -> Just (i, mkThunkRef b)
                _ -> Nothing)
           bs)
    methodsMap = HM.fromList $ zipWith (\i (_, x) -> (MethId i, x)) [0..] methods
    -- ¯\_(ツ)_/¯ Safety third! ¯\_(ツ)_/¯
    mkThunkRef =
      unsafePerformIO . fmap ValueRef . newMVar . Thunk locals . bindExp

deref :: HasCallStack => ValueRef -> Value
deref (ValueRef var) = unsafePerformIO $ do
  mval <- tryReadMVar var
  case mval of
    Just val -> return val
    Nothing ->
      error $ unwords
        [ "Expected to dereference a Value, but the MVar is empty"
        , "(typically indicating in progress evaluation)"
        ]
