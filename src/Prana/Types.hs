{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |

module Prana.Types where

import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as S8
import qualified Data.ByteString.Lazy.Builder as L
import           Data.Data
import           Data.List
import           GHC.Generics

class Pretty a where
  pretty :: a -> L.Builder

data Bind
  = NonRec Id
           Exp
  | Rec [(Id, Exp)]
  deriving (Generic, Data, Typeable, Show, Ord, Eq)

data Exp
  = VarE Id
  | LitE Lit
  | AppE Exp Exp
  | LamE Id Exp
  | CaseE Exp Id Typ [Alt]
  | TypE Typ
  | CoercionE
  | LetE Bind Exp
  | CastE Exp
  | TickE Exp
  deriving (Generic, Data, Typeable, Eq, Show, Ord)

instance Pretty Exp where
  pretty =
    \case
      VarE i -> pretty i
      LitE l -> pretty l
      AppE f x -> "(" <> pretty f <> " " <> pretty x <> ")"
      LamE i e -> "(\\" <> pretty i <> " -> " <> pretty e <> ")"
      LetE _ e -> "(let in " <> pretty e <> ")"
      CastE e -> pretty e
      TypE {} -> "Type"
      CoercionE {} -> "Coercion"
      TickE e -> pretty e
      CaseE e _ty _i alts ->
        "(case " <> pretty e <> " of {" <>
        mconcat (intersperse ";" (map pretty alts)) <>
        " })"

instance Pretty Id where
  pretty (Id i _ _) = L.byteString i

data Id = Id
  { idStableName :: {-# UNPACK #-}!ByteString
  , idUnique :: {-# UNPACK #-}!Unique
  , idCategory :: !Cat
  } deriving (Generic, Data, Typeable, Eq, Show, Ord)

data Cat
  = ValCat
  | DataCat
  | ClassCat
  deriving (Generic, Data, Typeable, Eq, Show, Ord)

data Typ = Typ ByteString
  deriving (Generic, Data, Typeable, Eq, Show, Ord)

data Alt = Alt
  { altCon :: AltCon
  , altVars :: [Id]
  , altExp :: Exp
  } deriving (Generic, Data, Typeable, Eq, Show, Ord)

instance Pretty Alt where
  pretty (Alt con ids e) =
    pretty con <> "(" <> mconcat (intersperse " " (map pretty ids)) <> ") -> " <>
    pretty e

data AltCon
  = DataAlt DataCon
  | LitAlt Lit
  | DEFAULT
  deriving (Generic, Data, Typeable, Eq, Show, Ord)

instance Pretty AltCon where
  pretty =
    \case
      DataAlt dc -> L.byteString . S8.pack . show $ dc
      LitAlt l -> pretty l
      DEFAULT -> "_"

newtype Unique = Unique Int
 deriving (Generic, Data, Typeable, Eq, Show, Ord)

newtype DataCon = DataCon Unique
  deriving (Generic, Data, Typeable, Eq, Show, Ord)

data Lit
  = Char Char
  | Str ByteString
  | NullAddr
  | Int Integer
  | Int64 Integer
  | Word Integer
  | Word64 Integer
  | Float Rational
  | Double Rational
  | Label
  | Integer Integer
  deriving (Generic, Data, Typeable, Eq, Show, Ord)

instance Pretty Lit where
  pretty = L.byteString . S8.pack . (++ ")") . ("("++) .show
