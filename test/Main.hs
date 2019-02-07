{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

-- | Test all things on the prana side from compiling, reading .prana
-- files, sanity checks, interpreting, etc.

module Main where

import           Prana.Interpret
import           Prana.Types
import           Test.Hspec
import           TestLib

-- | Main entry point.
main :: IO ()
main = hspec spec

-- | Test suite spec.
spec :: Spec
spec = do
  describe "Compile and Decode" compileAndDecode
  describe "Dependencies" dependencies
  describe "Evaluation" evaluation

-- | Test evaluation of expressions.
evaluation :: Spec
evaluation = do
  describe
    "Literals"
    (it
       "Ints"
       (do result <- evalExp emptyEnv mempty (LitE (Int 123))
           shouldBe result (LitW (Int 123))))
  describe "Lambdas with local envs" localLambdas
  it
    "Church"
    (do result <-
          evalCode
            (VarE (ExportedIndex 6610))
            [ ( "Church"
              , "module Church where\n\
                \data Nat = Succ Nat | Zero deriving Show\n\
                \it =  (Succ (Succ (Succ Zero)))\n\
                \")
            ]
        ignoreEnv result `shouldBe` ConW (ConId 816) [])
  it
    "Type classes [1 method]"
    (do result <-
          evalCode
            (VarE (ExportedIndex 6610))
            [ ( "Classes"
              , "module Classes where\n\
                \data Nat = Succ Nat | Zero\n\
                \data C = S | Z | L | R\n\
                \class ToC a where toC :: a -> C\n\
                \instance ToC Nat where \
                \  toC _ = S\n\
                \it = toC Zero")
            ]
        ignoreEnv result `shouldBe` ConW (ConId 817) [])
  it
    "Type classes [2 method, one parent class]"
    (do result <-
          evalCode
            (VarE (ExportedIndex 6611))
            [ ( "Classes"
              , "module Classes where\n\
                \data Nat = Succ Nat | Zero\n\
                \data C = S | Z | L | R\n\
                \class Parent a => ToC a where\n\
                \  toC :: a -> C\n\
                \  fromC :: C -> a\n\
                \class Parent a where parent :: a -> a\n\
                \instance Parent Nat where parent x = x\n\
                \instance ToC Nat where\n\
                \  toC _ = S\n\
                \  fromC _ = parent Zero\n\
                \it = fromC S :: Nat")
            ]
        ignoreEnv result `shouldBe` ConW (ConId 823) [])

-- | Lambda evaluation with local evaluation.
localLambdas :: Spec
localLambdas = do
  it
    "Id"
    (do result <-
          evalCode
            (VarE (ExportedIndex 6612))
            [ ("Id", "module Id where id x = x")
            , ( "On"
              , "module On where\n\
                \import Id\n\
                \const x _ = Id.id x\n\
                \it = On.const (123 :: Int) (57 :: Int)")
            ]
        case result of
          (ConW
             (ConId 233)
             [ deref -> Thunk
                 []
                 {- FIXME: Should these be expected?

                 [ (57218, deref -> Thunk _ (VarE (LocalIndex 57221)))
                 , (57221, deref -> Thunk _ (AppE (ConE (ConId 233)) (LitE (Int 123))))
                 , (57222, deref -> Thunk _ (AppE (ConE (ConId 233)) (LitE (Int 57))))
                 ]
                 -}
                 (LitE (Int 123))
             ]) -> return ()
          _ -> error $ "Unexpected evaluation result: " ++ show result)
  it
    "Lets"
    (do result <-
          evalCode
            (VarE (ExportedIndex 6610))
            [ ( "Let"
              , "module Let where\n\
                \idem f x = let v = f x; g _ = (666::Int) in g (f v)\n\
                \it = idem (\\x -> x) (123 :: Int)")
            ]
        case result of
          (ConW
             (ConId 233)
             [ deref -> Thunk
                 []
                 {- FIXME: Should these be expected?

                 [ (57218, deref -> Thunk _ (LamE (LocalVarId 57222) (VarE (LocalIndex 57222))))
                 , (57219, deref -> Thunk _ (AppE (ConE (ConId 233)) (LitE (Int 123))))
                 , ( 57221
                   , deref -> Thunk _
                       (AppE
                         (VarE (LocalIndex 57218))
                         (AppE
                            (VarE (LocalIndex 57218))
                            (VarE (LocalIndex 57219)))))
                 ]
                 -}
                 (LitE (Int 666))
             ]) -> return ()
          _ -> error $ "Unexpected evaluation result: " ++ show result)

-- | Test compiling and decoding.
dependencies :: Spec
dependencies =
  it
    "Compile two modules with interdependencies"
    (do (idmod, _) <-
          compileModulesWith
            Normal
            [ ("Id", "module Id where id x = x")
            , ( "On"
              , "module On where\n\
                \import Id\n\
                \const x _ = Id.id x")
            ]
        shouldBe
          (dropModuleHeaders idmod)
          [("Id",[Bind {bindVar = ExportedIndex 6609, bindExp = LamE (LocalVarId 57218) (VarE (LocalIndex 57218))}]),("On",[Bind {bindVar = ExportedIndex 6611, bindExp = LamE (LocalVarId 57221) (LamE (LocalVarId 57222) (AppE (VarE (ExportedIndex 6609)) (VarE (LocalIndex 57221))))}])])

-- | Test compiling and decoding.
compileAndDecode :: Spec
compileAndDecode =
  it
    "Compile id"
    (do (idmod, _) <-
          compileModulesWith
            Normal
            [ ("Id", "module Id where id x = x")
            , ( "On"
              , "module On where\n\
                \on :: (b -> b -> c) -> (a -> b) -> a -> a -> c\n\
                \(.*.) `on` f = \\x y -> f x .*. f y")
            ]
        shouldBe
          (dropModuleHeaders idmod)
          [("Id",[Bind {bindVar = ExportedIndex 6609, bindExp = LamE (LocalVarId 57218) (VarE (LocalIndex 57218))}]),("On",[Bind {bindVar = ExportedIndex 6611, bindExp = LamE (LocalVarId 57222) (LamE (LocalVarId 57223) (LamE (LocalVarId 57224) (LamE (LocalVarId 57225) (AppE (AppE (VarE (LocalIndex 57222)) (AppE (VarE (LocalIndex 57223)) (VarE (LocalIndex 57224)))) (AppE (VarE (LocalIndex 57223)) (VarE (LocalIndex 57225)))))))}])])
