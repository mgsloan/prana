{-# LANGUAGE LambdaCase #-}

-- |

module Prana.Decode where

import           Data.Binary.Get
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as S8
import           GHC.Real
import           Prana.Types

decodeExportedId :: Get ExportedId
decodeExportedId =
  ExportedId <$> decodeShortByteString <*> decodeShortByteString <*>
  decodeShortByteString

decodeLocalId :: Get LocalId
decodeLocalId =
  LocalId <$> decodeShortByteString <*> decodeShortByteString <*>
  decodeShortByteString <*> decodeInt

decodeMethodIndex :: Get (Id, Int)
decodeMethodIndex = label "decodeMethodIndex" ((,) <$> decodeId <*> decodeInt)

decodeEnums :: Get (Id, [Id])
decodeEnums = do
  tyId <- label "decodeEnums type" decodeId
  cons <- label "decodeEnums cons" (decodeArray decodeId)
  pure (tyId, cons)

decodeBind :: Get Bind
decodeBind =
  label "decodeBind" $ do
    tag <- getWord8
    case tag of
      0 -> NonRec <$> decodeId <*> decodeExpr
      1 -> Rec <$> decodeArray ((,) <$> decodeId <*> decodeExpr)
      _ -> fail ("decodeBind: unknown tag " ++ show tag)

decodeExpr :: Get Exp
decodeExpr =
  label "decodeExpr" $ do
    tag <- getWord8
    case tag of
      0 -> VarE <$> decodeId
      1 -> LitE <$> decodeLit
      2 -> AppE <$> decodeExpr <*> decodeExpr
      3 -> LamE <$> decodeBool <*> decodeId <*> decodeExpr
      4 -> LetE <$> decodeBind <*> decodeExpr
      5 ->
        CaseE <$> decodeExpr <*> decodeId <*> decodeType <*>
        decodeArray decodeAlt
      6 -> CastE <$> decodeExpr
      7 -> TickE <$> decodeExpr
      8 -> TypE <$> decodeType
      9 -> pure CoercionE
      _ -> fail ("decodeExpr: unknown tag " ++ show tag)

decodeLit :: Get Lit
decodeLit =
  label "decodeLit" $ do
    tag <- getWord8
    case tag of
      0 -> Char <$> decodeChar
      1 -> Str <$> decodeByteString
      2 -> pure NullAddr
      3 -> Int <$> decodeInteger
      4 -> Int64 <$> decodeInteger
      5 -> Word <$> decodeInteger
      6 -> Word64 <$> decodeInteger
      7 -> Float <$> ((:%) <$> decodeInteger <*> decodeInteger)
      8 -> Double <$> ((:%) <$> decodeInteger <*> decodeInteger)
      9 -> pure Label
      10 -> Integer <$> decodeInteger
      _ -> fail ("decodeLit: unknown tag " ++ show tag)

decodeAltCon :: Get AltCon
decodeAltCon =
  label "decodeAltCon" $ do
    tag <- getWord8
    case tag of
      0 -> DataAlt <$> decodeDataCon
      1 -> LitAlt <$> decodeLit
      2 -> pure DEFAULT
      _ -> fail ("decodeAltCon: unknown tag " ++ show tag)

decodeInteger :: Get Integer
decodeInteger = label "decodeInteger" $ fmap (read . S8.unpack) decodeByteString

decodeInt :: Get Int
decodeInt = label "decodeInteger" $ fmap fromIntegral getInt64le

decodeBool :: Get Bool
decodeBool =
  label "decodeBool" $
  fmap
    (\case
       1 -> True
       _ -> False)
    getWord8

decodeCat :: Get Cat
decodeCat =
  label "decodeCat" $
  fmap
    (\case
       1 -> DataCat
       2 -> ClassCat
       _ -> ValCat)
    getWord8

decodeAlt :: Get Alt
decodeAlt =
  label "decodeAlt" $
  Alt <$> decodeAltCon <*> decodeArray decodeId <*> decodeExpr

decodeType :: Get Typ
decodeType =
  label "decodeType" $ do
    tag <- getWord8
    case tag of
      0 -> OpaqueType <$> decodeByteString
      _ -> TyConApp <$> decodeId <*> decodeArray decodeType

decodeId :: Get Id
decodeId = label "decodeId" $ Id <$> decodeByteString <*> decodeUnique <*> decodeCat

decodeUnique :: Get Unique
decodeUnique = label "decodeUnique" $ fmap (Unique . fromIntegral) getInt64le

decodeDataCon :: Get DataCon
decodeDataCon = label "decodeDataCon" $ DataCon <$> decodeId <*> decodeArray decodeStrictness

decodeStrictness :: Get Strictness
decodeStrictness =
  label
    "decodeStrictness"
    (fmap
       (\case
          0 -> Strict
          _ -> NonStrict)
       getWord8)

decodeByteString :: Get ByteString
decodeByteString =
  label "decodeByteString" $ do
    len <- getInt64le
    getByteString (fromIntegral len)

decodeShortByteString :: Get ByteString
decodeShortByteString =
  label "decodeShortByteString" $ do
    len <- getInt16le
    getByteString (fromIntegral len)

decodeChar :: Get Char
decodeChar =
  label "decodeChar" $ do
    i <- getInt64le
    pure (toEnum (fromIntegral i))

decodeArray :: Get a -> Get [a]
decodeArray v =
  label "decodeArray" $ do
    i <- getInt64le
    sequence (replicate (fromIntegral i) v)
