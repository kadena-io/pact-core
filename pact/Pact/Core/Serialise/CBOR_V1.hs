-- |
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}


module Pact.Core.Serialise.CBOR_V1
  ( encodeModuleData, decodeModuleData
  , encodeModuleData_repl_spaninfo, decodeModuleData_repl_spaninfo
  , encodeModuleData_raw_spaninfo, decodeModuleData_raw_spaninfo
  , encodeModuleData_lineinfo, decodeModuleData_lineinfo
  , encodeKeySet, decodeKeySet
  , encodeDefPactExec, decodeDefPactExec
  , encodeNamespace, decodeNamespace
  , decodeRowData
  , encodeRowDataNoGas
  -- only used for legacy translation
  , encodeModuleName
  , encodeModuleHash
  , SerialiseV1(..)
  ) where

import Codec.CBOR.Read (deserialiseFromBytes)
import Codec.CBOR.Write (toStrictByteString)
import Codec.Serialise
import Codec.CBOR.Encoding
import Codec.CBOR.Decoding
import Data.ByteString (ByteString, fromStrict)
import Data.Decimal
import Data.Coerce

import Pact.Core.Builtin
import Pact.Core.Capabilities
import Pact.Core.ChainData
import Pact.Core.DefPacts.Types
import Pact.Core.Guards
import Pact.Core.Hash
import Pact.Core.Imports
import Pact.Core.Info
import Pact.Core.IR.Term
import Pact.Core.Literal
import Pact.Core.ModRefs
import Pact.Core.Names
import Pact.Core.Namespace
import Pact.Core.PactValue
import Pact.Core.Persistence
import Pact.Core.Type
import Pact.Time.Internal (UTCTime(..), NominalDiffTime(..))
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Unsafe.Coerce (unsafeCoerce)
import Data.Word (Word16)

newtype SerialiseV1 a
  = SerialiseV1 { _getSV1 :: a }
  deriving newtype (Eq, Show, Ord)


encodeModuleData :: ModuleData CoreBuiltin () -> ByteString
encodeModuleData = toStrictByteString . encodeS

encodeModuleData_repl_spaninfo :: ModuleData ReplCoreBuiltin SpanInfo -> ByteString
encodeModuleData_repl_spaninfo = toStrictByteString . encodeS

encodeModuleData_raw_spaninfo :: ModuleData CoreBuiltin SpanInfo -> ByteString
encodeModuleData_raw_spaninfo = toStrictByteString . encodeS

encodeModuleData_lineinfo :: ModuleData CoreBuiltin LineInfo -> ByteString
encodeModuleData_lineinfo = toStrictByteString . encodeS

decodeModuleData :: ByteString -> Maybe (ModuleData CoreBuiltin ())
decodeModuleData bs = either (const Nothing) (Just . _getSV1) (deserialiseOrFail (fromStrict bs))

decodeModuleData_repl_spaninfo :: ByteString -> Maybe (ModuleData ReplCoreBuiltin SpanInfo)
decodeModuleData_repl_spaninfo bs =
  case deserialiseOrFail (fromStrict bs) of
    Right (SerialiseV1 v) -> Just v
    Left _ -> Nothing

decodeModuleData_raw_spaninfo :: ByteString -> Maybe (ModuleData CoreBuiltin SpanInfo)
decodeModuleData_raw_spaninfo bs = either (const Nothing) (Just . _getSV1) (deserialiseOrFail (fromStrict bs))

decodeModuleData_lineinfo :: ByteString -> Maybe (ModuleData CoreBuiltin LineInfo)
decodeModuleData_lineinfo bs = either (const Nothing) (Just . _getSV1) (deserialiseOrFail (fromStrict bs))

encodeModuleName :: ModuleName -> ByteString
encodeModuleName = toStrictByteString . encodeS

encodeModuleHash :: ModuleHash -> ByteString
encodeModuleHash = toStrictByteString . encodeS

encodeKeySet :: KeySet -> ByteString
encodeKeySet = toStrictByteString . encodeS

decodeKeySet :: ByteString -> Maybe KeySet
decodeKeySet bs = either (const Nothing) (Just . snd) (deserialiseFromBytes decodeS (fromStrict bs))


encodeDefPactExec :: Maybe DefPactExec -> ByteString
encodeDefPactExec =  toStrictByteString . encodeS

decodeDefPactExec :: ByteString -> Maybe (Maybe DefPactExec)
decodeDefPactExec bs = either (const Nothing) (Just . snd) (deserialiseFromBytes decodeS (fromStrict bs))

encodeNamespace :: Namespace -> ByteString
encodeNamespace = toStrictByteString . encodeS

decodeNamespace :: ByteString -> Maybe Namespace
decodeNamespace bs =either (const Nothing) (Just . snd) (deserialiseFromBytes decodeS (fromStrict bs))

encodeRowDataNoGas :: RowData -> ByteString
encodeRowDataNoGas rd =
  toStrictByteString $ encodeS rd


decodeRowData :: ByteString -> Maybe RowData
decodeRowData bs = either (const Nothing) (Just . snd) (deserialiseFromBytes decodeS (fromStrict bs))

encodeS :: Serialise (SerialiseV1 a) => a -> Encoding
encodeS a = encode (SerialiseV1 a)
{-# INLINE encodeS #-}

decodeS :: Serialise (SerialiseV1 a) => Decoder s a
decodeS = c decode
  where
  c :: Decoder s (SerialiseV1 a) -> Decoder s a
  c = coerce
{-# INLINE decodeS #-}

safeDecodeListLen :: Int -> String -> Decoder s ()
safeDecodeListLen expected ctor = do
  actualLen <- decodeListLen
  enforceCBORListLen expected actualLen ctor

enforceCBORListLen :: Int -> Int -> String -> Decoder s ()
enforceCBORListLen expected actualLen ctor = do
  if expected /= actualLen then
    fail ("Expected list length of " <> show expected <> " for data type " <> ctor <> " but got " <> show actualLen)
  else pure ()

instance Serialise (SerialiseV1 ()) where
  encode _ = encode ()
  {-# INLINE encode #-}
  decode = SerialiseV1 <$> decode
  {-# INLINE decode #-}

instance {-# OVERLAPPABLE #-}
  (Serialise (SerialiseV1 a), Functor f, (forall b. (Serialise b) => Serialise (f b))) => Serialise (SerialiseV1 (f a)) where
  encode (SerialiseV1 m) = encode (SerialiseV1 <$> m)
  {-# INLINE encode #-}
  decode = SerialiseV1 . fmap _getSV1 <$> decode
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 Namespace) where
  encode (SerialiseV1 (Namespace n user admin)) =
    encodeListLen 3 <> encodeS n <> encodeS user <> encodeS admin
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 3 "Namespace"
    SerialiseV1 <$> (Namespace <$> decodeS <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 RowData) where
  encode (SerialiseV1 (RowData m)) = encode (SerialiseV1 <$> m)
  {-# INLINE encode #-}
  decode = SerialiseV1 . RowData . fmap _getSV1 <$> decode
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 NamespaceName) where
  encode (SerialiseV1 (NamespaceName ns)) = encode ns
  {-# INLINE encode #-}
  decode = SerialiseV1 . NamespaceName <$> decode
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 ModuleName) where
  encode (SerialiseV1 (ModuleName mn mns)) =
    encodeListLen 2 <> encode mn <> encode (SerialiseV1 <$> mns)
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "ModuleName"
    SerialiseV1 <$> (ModuleName <$> decode <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 KeySetName) where
  encode (SerialiseV1 (KeySetName ksn ns)) =
    encodeListLen 2 <> encode ksn <> encodeS ns
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "KeySetName"
    SerialiseV1 <$> (KeySetName <$> decode <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 PublicKeyText) where
  encode (SerialiseV1 (PublicKeyText t)) = encode t
  {-# INLINE encode #-}
  decode = SerialiseV1 . PublicKeyText <$> decode
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 KeySet) where
  encode (SerialiseV1 (KeySet ks p)) =
    encodeListLen 2 <> encode ks <> encodeS p
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "KeySet"
    SerialiseV1 <$> (KeySet <$> decode <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 KSPredicate) where
  encode (SerialiseV1 k) = case k of
    KeysAll -> encodeListLen 1 <> encodeWord 0
    Keys2 -> encodeListLen 1 <> encodeWord 1
    KeysAny -> encodeListLen 1 <> encodeWord 2
    CustomPredicate pn -> encodeListLen 2 <> encodeWord 3 <> encodeS pn
  {-# INLINE encode #-}

  decode = do
    _ <- decodeListLen
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> pure KeysAll
      1 -> pure Keys2
      2 -> pure KeysAny
      3 -> CustomPredicate <$> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 QualifiedName) where
  encode (SerialiseV1 (QualifiedName qn mn)) = do
    encodeListLen 2 <> encode qn <> encodeS mn
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "QualifiedName"
    SerialiseV1 <$> (QualifiedName <$> decode <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 BareName) where
  encode (SerialiseV1 (BareName bn)) = encode bn
  {-# INLINE encode #-}
  decode = SerialiseV1 . BareName <$> decode
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 DynamicName) where
  encode (SerialiseV1 (DynamicName dn dcall)) =
    encodeListLen 2 <> encode dn <> encode dcall
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "DynamicName"
    SerialiseV1 <$> (DynamicName <$> decode <*> decode)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 ParsedTyName) where
  encode (SerialiseV1 n) =
    encodeListLen 2 <>
      case n of
        TQN qn -> encodeWord 0 <> encodeS qn
        TBN bn -> encodeWord 1 <> encodeS bn
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 2 "ParsedTyName"
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> TQN <$> decodeS
      1 -> TBN <$> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}


instance Serialise (SerialiseV1 Hash) where
  encode (SerialiseV1 (Hash h)) = encode h
  {-# INLINE encode #-}
  decode = SerialiseV1 . Hash <$> decode
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 ModuleHash) where
  encode (SerialiseV1 (ModuleHash mh)) = encodeS mh
  {-# INLINE encode #-}
  decode = SerialiseV1 . ModuleHash <$> decodeS
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 FullyQualifiedName) where
  encode (SerialiseV1 (FullyQualifiedName mn fqn h)) =
    encodeListLen 3 <> encodeS mn <> encode fqn <> encodeS h
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 3 "FullyQualifiedName"
    SerialiseV1 <$> (FullyQualifiedName <$> decodeS <*> decode <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 (Governance Name)) where
  encode (SerialiseV1 g) =
    encodeListLen 2 <>
      case g of
        KeyGov ksn -> encodeWord 0 <> encodeS ksn
        CapGov cgn -> encodeWord 1 <> encodeS cgn
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 2 "Governance"
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> KeyGov <$> decodeS
      1 -> CapGov <$> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance (Serialise (SerialiseV1 ty), Serialise (SerialiseV1 i)) => Serialise (SerialiseV1 (Arg ty i)) where
  encode (SerialiseV1 (Arg n ty i)) =
    encodeListLen 3 <>
      encode n <> encodeS ty <> encodeS i
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 3 "Arg"
    SerialiseV1 <$> (Arg <$> decode <*> decodeS <*> decodeS)
  {-# INLINE decode #-}


instance Serialise (SerialiseV1 Decimal) where
  encode (SerialiseV1 (Decimal places mantissa)) =
    encodeListLen 2 <> encode places <> encode mantissa
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "Decimal"
    SerialiseV1 <$> (Decimal <$> decode <*> decode)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 Literal) where
  encode (SerialiseV1 l) = case l of
    LString s -> encodeListLen 2 <> encodeWord 0 <> encode s
    LInteger i -> encodeListLen 2 <> encodeWord 1 <> encode i
    LDecimal d -> encodeListLen 2 <> encodeWord 2 <> encodeS d
    LUnit -> encodeListLen 1 <> encodeWord 3
    LBool b -> encodeListLen 2 <> encodeWord 4 <> encode b
  {-# INLINE encode #-}

  decode = do
    _ <- decodeListLen
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> LString <$> decode
      1 -> LInteger <$> decode
      2 -> LDecimal <$> decodeS
      3 -> pure LUnit
      4 -> LBool <$> decode
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 Field) where
  encode (SerialiseV1 (Field f)) = encode f
  {-# INLINE encode #-}
  decode = SerialiseV1 <$> (Field <$> decode)
  {-# INLINE decode #-}

instance (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i))
  => Serialise (SerialiseV1 (BuiltinForm (Term Name Type b i))) where
  encode (SerialiseV1 bf) = case bf of
      CAnd t1 t2 ->
        encodeListLen 3 <> encodeWord 0 <> encodeS t1 <> encodeS t2
      COr t1 t2 ->
        encodeListLen 3 <> encodeWord 1 <> encodeS t1 <> encodeS t2
      CIf t1 t2 t3 ->
        encodeListLen 4 <> encodeWord 2 <> encodeS t1 <> encodeS t2 <> encodeS t3
      CEnforceOne t1 t2 ->
        encodeListLen 3 <> encodeWord 3 <> encodeS t1 <> encodeS t2
      CEnforce t1 t2 ->
        encodeListLen 3 <> encodeWord 4 <> encodeS t1 <> encodeS t2
      CWithCapability t1 t2 ->
        encodeListLen 3 <> encodeWord 5 <> encodeS t1 <> encodeS t2
      CTry t1 t2 ->
        encodeListLen 3 <> encodeWord 6 <> encodeS t1 <> encodeS t2
      CCreateUserGuard t1 ->
        encodeListLen 2 <> encodeWord 7 <> encodeS t1
      CRunReadOnly t1 ->
        encodeListLen 2 <> encodeWord 8 <> encodeS t1
  {-# INLINE encode #-}

  decode = do
    _ <- decodeListLen
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> CAnd <$> decodeS <*> decodeS
      1 -> COr <$> decodeS <*> decodeS
      2 -> CIf <$> decodeS <*> decodeS <*> decodeS
      3 -> CEnforceOne <$> decodeS <*> decodeS
      4 -> CEnforce <$> decodeS <*> decodeS
      5 -> CWithCapability <$> decodeS <*> decodeS
      6 -> CTry <$> decodeS <*> decodeS
      7 -> CCreateUserGuard <$> decodeS
      8 -> CRunReadOnly <$> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance
  (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i))
  => Serialise (SerialiseV1 (Term Name Type b i)) where
  encode (SerialiseV1 term) = case term of
    Var n i ->
      encodeListLen 3 <> encodeWord 0 <> encodeS n <> encodeS i
    Lam args body i ->
      encodeListLen 4 <> encodeWord 1 <> encodeS args <> encodeS body <> encodeS i
    Let arg t1 t2 i ->
      encodeListLen 5 <> encodeWord 2 <> encodeS arg <> encodeS t1 <> encodeS t2 <> encodeS i
    App t1 t2 i ->
      encodeListLen 4 <> encodeWord 3 <> encodeS t1 <> encodeS t2 <> encodeS i
    Sequence t1 t2 i ->
      encodeListLen 4 <> encodeWord 4 <> encodeS t1 <> encodeS t2 <> encodeS i
    Nullary t i ->
      encodeListLen 3 <> encodeWord 5 <> encodeS t <> encodeS i
    BuiltinForm bi i ->
      encodeListLen 3 <> encodeWord 6 <> encodeS bi <> encodeS i
    Builtin bi i ->
      encodeListLen 3 <> encodeWord 7 <> encodeS bi <> encodeS i
    Constant lit i ->
      encodeListLen 3 <> encodeWord 8 <> encodeS lit <> encodeS i
    ListLit t i ->
      encodeListLen 3 <> encodeWord 9 <> encodeS t <> encodeS i
    ObjectLit o i ->
      encodeListLen 3 <> encodeWord 10 <> encodeS o <> encodeS i
    InlineValue pv i ->
      encodeListLen 3 <> encodeWord 11 <> encodeS pv <> encodeS i
  {-# INLINE encode #-}

  decode = do
    _ <- decodeListLen
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> Var <$> decodeS <*> decodeS
      1 -> Lam <$> decodeS <*> decodeS <*> decodeS
      2 -> Let <$> decodeS <*> decodeS <*> decodeS <*> decodeS
      3 -> App <$> decodeS <*> decodeS <*> decodeS
      4 -> Sequence <$> decodeS <*> decodeS <*> decodeS
      5 -> Nullary <$> decodeS <*> decodeS
      6 -> BuiltinForm <$> decodeS <*> decodeS
      7 -> Builtin <$> decodeS <*> decodeS
      8 -> Constant <$> decodeS <*> decodeS
      9 -> ListLit <$> decodeS <*> decodeS
      10 -> ObjectLit <$> decodeS <*> decodeS
      -- Internal term used for back. compat pact < 5
      11 -> InlineValue <$> decodeS <*> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance
  (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i))
  => Serialise (SerialiseV1 (Defun Name Type b i)) where
  encode (SerialiseV1 (Defun spec args term i)) =
    encodeListLen 4 <> encodeS spec <> encodeS args <> encodeS term <> encodeS i
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 4 "Defun"
    SerialiseV1 <$> (Defun <$> decodeS <*> decodeS <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance
  (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i))
  => Serialise (SerialiseV1 (DefConst Name Type b i)) where
  encode (SerialiseV1 (DefConst spec term i)) =
    encodeListLen 3 <> encodeS spec <> encodeS term <> encodeS i
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 3 "DefConst"
    SerialiseV1 <$> (DefConst <$> decodeS <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance (Serialise (SerialiseV1 term)) => Serialise (SerialiseV1 (ConstVal term)) where
  encode (SerialiseV1 c) =
    encodeListLen 2 <> case c of
      TermConst t -> encodeWord 0 <> encodeS t
      EvaledConst pv -> encodeWord 1 <> encodeS pv
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 2 "ConstVal"
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> TermConst <$> decodeS
      1 -> EvaledConst <$> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 (FQNameRef Name)) where
  encode (SerialiseV1 (FQName fqn)) = encodeS fqn
  {-# INLINE encode #-}
  decode = SerialiseV1 . FQName <$> decodeS
  {-# INLINE decode #-}

instance (Serialise (SerialiseV1 name)) => Serialise (SerialiseV1 (DefManagedMeta name)) where
  encode (SerialiseV1 dmm) = case dmm of
    DefManagedMeta i ref -> encodeListLen 3 <> encodeWord 0 <> encode i <> encodeS ref
    AutoManagedMeta -> encodeListLen 1 <> encodeWord 1
  {-# INLINE encode #-}

  decode = do
    len <- decodeListLen
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> enforceCBORListLen 3 len "DefManagedMeta" *> (DefManagedMeta <$> decode <*> decodeS)
      1 -> AutoManagedMeta <$ enforceCBORListLen 1 len "AutoManagedMeta"
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 name) => Serialise (SerialiseV1 (DefCapMeta name)) where
  encode (SerialiseV1 dcm) = case dcm of
    DefEvent -> encodeListLen 1 <> encodeWord 0
    DefManaged meta -> encodeListLen 2 <> encodeWord 1 <> encodeS meta
    Unmanaged -> encodeListLen 1 <> encodeWord 2
  {-# INLINE encode #-}

  decode = do
    _ <- decodeListLen
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> pure DefEvent
      1 -> DefManaged <$> decodeS
      2 -> pure Unmanaged
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i)) => Serialise (SerialiseV1 (DefCap Name Type b i)) where
  encode (SerialiseV1 (DefCap spec args term meta i)) =
    encodeListLen 5
    <> encodeS spec
    <> encodeS args
    <> encodeS term
    <> encodeS meta
    <> encodeS i
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 5 "DefCap"
    SerialiseV1 <$> (DefCap <$> decodeS <*> decodeS <*> decodeS <*> decodeS <*> decodeS)
  {-# INLINE decode #-}


instance (Serialise (SerialiseV1 ty), Serialise (SerialiseV1 i)) => Serialise (SerialiseV1 (DefSchema ty i)) where
  encode (SerialiseV1 (DefSchema n schema i)) =
    encodeListLen 3 <> encode n <> encodeS schema <> encodeS i
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 3 "DefSchema"
    SerialiseV1 <$> (DefSchema <$> decode <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 (TableSchema Name)) where
  encode (SerialiseV1 (ResolvedTable n)) = encodeS n
  {-# INLINE encode #-}
  decode = SerialiseV1 . ResolvedTable <$> decodeS
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 i) => Serialise (SerialiseV1 (DefTable Name i)) where
  encode (SerialiseV1 (DefTable n schema i)) =
    encodeListLen 3 <> encode n <> encodeS schema <> encodeS i
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 3 "DefTable"
    SerialiseV1 <$> (DefTable <$> decode <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance
  (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i))
  => Serialise (SerialiseV1 (Step Name Type b i)) where
  encode (SerialiseV1 step) = case step of
    Step t ->
      encodeListLen 2 <> encodeWord 0 <> encodeS t
    StepWithRollback t rb ->
      encodeListLen 3 <> encodeWord 1 <> encodeS t <> encodeS rb
  {-# INLINE encode #-}

  decode = do
    _ <- decodeListLen
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> Step <$> decodeS
      1 -> StepWithRollback <$> decodeS <*> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance
  (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i))
  => Serialise (SerialiseV1 (DefPact Name Type b i)) where
  encode (SerialiseV1 (DefPact spec args steps i)) =
    encodeListLen 4 <> encodeS spec <> encodeS args <> encodeS steps <> encodeS i
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 4 "DefPact"
    SerialiseV1 <$> (DefPact <$> decodeS <*> decodeS <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance
  (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i))
  => Serialise (SerialiseV1 (Def Name Type b i)) where
  encode (SerialiseV1 defn) =
    encodeListLen 2 <>
    case defn of
      Dfun df -> encodeWord 0 <> encodeS df
      DConst dc -> encodeWord 1 <> encodeS dc
      DCap cap -> encodeWord 2 <> encodeS cap
      DSchema schema -> encodeWord 3 <> encodeS schema
      DTable table -> encodeWord 4 <> encodeS table
      DPact dp -> encodeWord 5 <> encodeS dp
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 2 "Def"
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> Dfun <$> decodeS
      1 -> DConst <$> decodeS
      2 -> DCap <$> decodeS
      3 -> DSchema <$> decodeS
      4 -> DTable <$> decodeS
      5 -> DPact <$> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 DynamicRef) where
  encode (SerialiseV1 (DynamicRef n b)) =
    encodeListLen 2 <> encode n <> encode b
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "DynamicRef"
    SerialiseV1 <$> (DynamicRef <$> decode <*> decode)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 NameKind) where
  encode (SerialiseV1 nk) = case nk of
    NBound d ->
      encodeListLen 2 <> encodeWord 0 <> encode d
    NTopLevel mn mh ->
      encodeListLen 3 <> encodeWord 1 <> encodeS mn <> encodeS mh
    NModRef mn ms ->
      encodeListLen 3 <> encodeWord 2 <> encodeS mn <> encodeS ms
    NDynRef dref ->
      encodeListLen 2 <> encodeWord 3 <> encodeS dref
  {-# INLINE encode #-}

  decode = do
    _ <- decodeListLen
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> NBound <$> decode
      1 -> NTopLevel <$> decodeS <*> decodeS
      2 -> NModRef <$> decodeS <*> decodeS
      3 -> NDynRef <$> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 Name) where
  encode (SerialiseV1 (Name n k)) =
    encodeListLen 2 <> encode n <> encodeS k
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "Name"
    SerialiseV1 <$> (Name <$> decode <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 PrimType) where
  encode (SerialiseV1 pt) = case pt of
    PrimInt -> encodeWord 0
    PrimDecimal -> encodeWord 1
    PrimBool -> encodeWord 2
    PrimString -> encodeWord 3
    PrimGuard -> encodeWord 4
    PrimTime -> encodeWord 5
    PrimUnit -> encodeWord 6
  {-# INLINE encode #-}

  decode = decodeWord >>= fmap SerialiseV1 . \case
    0 -> pure PrimInt
    1 -> pure PrimDecimal
    2 -> pure PrimBool
    3 -> pure PrimString
    4 -> pure PrimGuard
    5 -> pure PrimTime
    6 -> pure PrimUnit
    _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 Schema) where
  encode (SerialiseV1 (Schema sc m)) =
    encodeListLen 2 <> encodeS sc <> encodeS m
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "Schema"
    SerialiseV1 <$> (Schema <$> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 Type) where
  encode (SerialiseV1 ty) = case ty of
    TyPrim pt -> encodeListLen 2 <> encodeWord 0 <> encodeS pt
    TyList t -> encodeListLen 2 <> encodeWord 1 <> encodeS t
    TyAnyList -> encodeListLen 1 <> encodeWord 2
    TyModRef mr -> encodeListLen 2 <> encodeWord 3 <> encode (coerceSetToSerialize mr)
    TyObject s -> encodeListLen 2 <> encodeWord 4 <> encodeS s
    TyAnyObject -> encodeListLen 1 <> encodeWord 5
    TyTable s -> encodeListLen 2 <> encodeWord 6 <> encodeS s
    TyCapToken -> encodeListLen 1 <> encodeWord 7
    TyAny -> encodeListLen 1 <> encodeWord 8
  {-# INLINE encode #-}

  decode = do
    _ <- decodeListLen
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> TyPrim <$> decodeS
      1 -> TyList <$> decodeS
      2 -> pure TyAnyList
      3 -> TyModRef . coerceSetFromSerialize <$> decode
      4 -> TyObject <$> decodeS
      5 -> pure TyAnyObject
      6 -> TyTable <$> decodeS
      7 -> pure TyCapToken
      8 -> pure TyAny
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 Import) where
  encode (SerialiseV1 (Import mn mh mimp)) =
    encodeListLen 3 <> encodeS mn <> encodeS mh <> encode mimp
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 3 "Import"
    SerialiseV1 <$> (Import <$> decodeS <*> decodeS <*> decode)
  {-# INLINE decode #-}

instance
  (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i))
  => Serialise (SerialiseV1 (EvalModule b i)) where
  -- Note: we _do not_ store module code in our CBOR representation. This is _purely_
  -- a backcompat thing
  encode (SerialiseV1 (Module mn mg mdef mbless mimports mimpl mhash txhash _ minfo)) =
    encodeListLen 9 <>
    encodeS mn <> encodeS mg <> encodeS mdef
    <> encode (coerceSetToSerialize mbless) <> encodeS mimports <> encodeS mimpl
    <> encodeS mhash <> encodeS txhash <> encodeS minfo
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 9 "Module"
    fmap SerialiseV1 $
      Module <$> decodeS <*> decodeS <*> decodeS <*> (coerceSetFromSerialize <$> decode) <*> decodeS
            <*> decodeS <*> decodeS <*> decodeS <*> pure (ModuleCode mempty) <*> decodeS
  {-# INLINE decode #-}


instance
  Serialise (SerialiseV1 i)
  => Serialise (SerialiseV1 (IfDefun Type i)) where
  encode (SerialiseV1 (IfDefun spec args i)) =
    encodeListLen 3 <> encodeS spec <> encodeS args <> encodeS i
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 3 "IfDefun"
    SerialiseV1 <$> (IfDefun <$> decodeS <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance
  Serialise (SerialiseV1 i)
  => Serialise (SerialiseV1 (IfDefCap name Type i)) where
  encode (SerialiseV1 (IfDefCap spec args meta i)) =
    encodeListLen 4 <> encodeS spec <> encodeS args <> encodeS meta <> encodeS i
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 4 "IfDefCap"
    SerialiseV1 <$> (IfDefCap <$> decodeS <*> decodeS <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance
  Serialise (SerialiseV1 i)
  => Serialise (SerialiseV1 (IfDefPact Type i)) where
  encode (SerialiseV1 (IfDefPact spec args i)) =
    encodeListLen 3 <> encodeS spec <> encodeS args <> encodeS i
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 3 "IfDefPact"
    SerialiseV1 <$> (IfDefPact <$> decodeS <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance
  (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i))
  => Serialise (SerialiseV1 (IfDef Name Type b i)) where
  encode (SerialiseV1 ifdef) =
    encodeListLen 2 <>
    case ifdef of
      IfDfun df -> encodeWord 0 <> encodeS df
      IfDConst dc -> encodeWord 1 <> encodeS dc
      IfDCap cap -> encodeWord 2 <> encodeS cap
      IfDSchema schema -> encodeWord 3 <> encodeS schema
      IfDPact dp ->  encodeWord 4 <> encodeS dp
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 2 "IfDef"
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> IfDfun <$> decodeS
      1 -> IfDConst <$> decodeS
      2 -> IfDCap <$> decodeS
      3 -> IfDSchema <$> decodeS
      4 -> IfDPact <$> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance
  (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i))
  => Serialise (SerialiseV1 (EvalInterface b i)) where
  encode (SerialiseV1 (Interface n defs imp h txh _ i)) =
    encodeListLen 6 <> encodeS n <> encodeS defs <> encodeS imp <> encodeS h <> encodeS txh <> encodeS i
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 6 "Interface"
    SerialiseV1 <$> (Interface <$> decodeS <*> decodeS <*> decodeS <*> decodeS <*> decodeS <*> pure (ModuleCode mempty) <*> decodeS)
  {-# INLINE decode #-}

coerceMapFromSerialise :: M.Map (SerialiseV1 k) (SerialiseV1 v) -> M.Map k v
coerceMapFromSerialise = unsafeCoerce

coerceMapToSerialise :: M.Map k v -> M.Map (SerialiseV1 k) (SerialiseV1 v)
coerceMapToSerialise = unsafeCoerce

coerceSetToSerialize :: S.Set k -> S.Set (SerialiseV1 k)
coerceSetToSerialize = unsafeCoerce

coerceSetFromSerialize :: S.Set (SerialiseV1 k) -> S.Set k
coerceSetFromSerialize = unsafeCoerce

instance
  (Serialise (SerialiseV1 b), Serialise (SerialiseV1 i))
  => Serialise (SerialiseV1 (ModuleData b i)) where
  encode (SerialiseV1 md) = do
    encodeListLen 2 <>
      case md of
        ModuleData em m -> encodeWord 0 <> encodeS em <> encode (coerceMapToSerialise m)
        InterfaceData ei m -> encodeWord 1 <> encodeS ei <> encode (coerceMapToSerialise m)
  {-# INLINE encode #-}

  decode = do
    safeDecodeListLen 2 "ModuleData"
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> ModuleData <$> decodeS <*> (coerceMapFromSerialise <$> decode)
      1 -> InterfaceData <$> decodeS <*> (coerceMapFromSerialise <$> decode)
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}


instance Serialise (SerialiseV1 SpanInfo) where
  encode (SerialiseV1 (SpanInfo sl sc el ec)) =
    encodeListLen 4 <> encode sl <> encode sc <> encode el <> encode ec
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 4 "SpanInfo"
    SerialiseV1 <$> (SpanInfo <$> decode <*> decode <*> decode <*> decode)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 LineInfo) where
  encode (SerialiseV1 (LineInfo li)) = encode li
  {-# INLINE encode #-}
  decode = SerialiseV1 <$> (LineInfo <$> decode)
  {-# INLINE decode #-}

-- Note: this encoder/decoder relies on the derived `Enum` instance
-- for `CoreBuiltin`. That said: we _do_ have a golden test in
-- ConTagGolden.hs for ensuring that any constructor ordering changes
-- are caught.
instance Serialise (SerialiseV1 CoreBuiltin) where
  encode (SerialiseV1 cb) =
    encodeWord16 $ fromIntegral (fromEnum cb)
  {-# INLINE encode #-}

  decode = do
    d <- decodeWord16
    if d <= cbMax then pure (SerialiseV1 (toEnum (fromIntegral d)))
    else fail "unexpected decoding: CoreBuiltin"
    where
    cbMax :: Word16
    cbMax = fromIntegral $ fromEnum $ (maxBound :: CoreBuiltin)
  {-# INLINE decode #-}


instance Serialise (SerialiseV1 ReplOnlyBuiltin) where
  encode = encodeWord . fromIntegral . fromEnum . _getSV1
  {-# INLINE encode #-}
  decode = do
    vInd <- toEnum . fromIntegral <$> decodeWord
    pure $ SerialiseV1 (toEnum vInd)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 ReplCoreBuiltin) where
  encode (SerialiseV1 rb) = case rb of
    RBuiltinWrap b -> encodeWord 0 <> encodeS b
    RBuiltinRepl r -> encodeWord 1 <> encodeS r
  {-# INLINE encode #-}

  decode = decodeWord >>= fmap SerialiseV1 . \case
    0 -> RBuiltinWrap <$> decodeS
    1 -> RBuiltinRepl <$> decodeS
    _ -> fail "unexpected decoding"
  {-# INLINE decode #-}



-- DefPacts

instance Serialise (SerialiseV1 (UserGuard QualifiedName PactValue)) where
  encode (SerialiseV1 (UserGuard f a)) =
    encodeListLen 2 <> encodeS f <> encodeS a
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "UserGuard"
    SerialiseV1 <$> (UserGuard <$> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 DefPactId) where
  encode (SerialiseV1 (DefPactId pid)) = encode pid
  {-# INLINE encode #-}
  decode = SerialiseV1 . DefPactId <$> decode
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 (CapabilityGuard QualifiedName PactValue)) where
  encode (SerialiseV1 (CapabilityGuard n a pid)) =
    encodeListLen 3 <> encodeS n <> encodeS a <> encodeS pid
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 3 "CapabilityGuard"
    SerialiseV1 <$> (CapabilityGuard <$> decodeS <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 ModuleGuard) where
  encode (SerialiseV1 (ModuleGuard mn n)) =
    encodeListLen 2 <> encodeS mn <> encode n
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "ModuleGuard"
    SerialiseV1 <$> (ModuleGuard <$> decodeS <*> decode)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 (Guard QualifiedName PactValue)) where
  encode (SerialiseV1 g) =
    encodeListLen 2 <>
    case g of
      GKeyset ks -> encodeWord 0 <> encodeS ks
      GKeySetRef ksn -> encodeWord 1 <> encodeS ksn
      GUserGuard ug -> encodeWord 2 <> encodeS ug
      GCapabilityGuard cg -> encodeWord 3 <> encodeS cg
      GModuleGuard mg -> encodeWord 4 <> encodeS mg
      GDefPactGuard dpg -> encodeWord 5 <> encodeS dpg
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "Guard"
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> GKeyset <$> decodeS
      1 -> GKeySetRef <$> decodeS
      2 -> GUserGuard <$> decodeS
      3 -> GCapabilityGuard <$> decodeS
      4 -> GModuleGuard <$> decodeS
      5 -> GDefPactGuard <$> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 DefPactGuard) where
  encode (SerialiseV1 (DefPactGuard i name)) =
    encodeListLen 2 <> encodeS i <> encode name
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "DefPactGuard"
    SerialiseV1 <$> (DefPactGuard <$> decodeS <*> decode)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 ModRef) where
  encode (SerialiseV1 (ModRef mn imp)) =
    encodeListLen 2 <> encodeS mn <> encode (coerceSetToSerialize imp)
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "ModRef"
    SerialiseV1 <$> (ModRef <$> decodeS <*> (coerceSetFromSerialize <$> decode))
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 name) => Serialise (SerialiseV1 (CapToken name PactValue)) where
  encode (SerialiseV1 (CapToken n a)) =
    encodeListLen 2 <> encodeS n <> encodeS a
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "CapToken"
    SerialiseV1 <$> (CapToken <$> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 TableName) where
  encode (SerialiseV1 (TableName tn mn)) =
    encodeListLen 2 <> encode tn <> encodeS mn
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "TableName"
    SerialiseV1 <$> (TableName <$> decode <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 TableValue) where
  encode (SerialiseV1 (TableValue tn k v)) =
    encodeListLen 3 <> encodeS tn <> encodeS k <> encodeS v
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 3 "TableValue"
    SerialiseV1 <$> (TableValue <$> decodeS <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 PactValue) where
  encode (SerialiseV1 pv) =
    encodeListLen 2 <>
    case pv of
      PLiteral l -> encodeWord 0 <> encodeS l
      PList l -> encodeWord 1 <> encodeS l
      PGuard g -> encodeWord 2 <> encodeS g
      PObject o -> encodeWord 3 <> encodeS o
      PModRef mr -> encodeWord 4 <> encodeS mr
      PCapToken ct -> encodeWord 5 <> encodeS ct
      PTime (UTCTime (NominalDiffTime pt)) -> encodeWord 6 <> encode pt
      PTable t -> encodeWord 7 <> encodeS t
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "PactValue"
    decodeWord >>= fmap SerialiseV1 . \case
      0 -> PLiteral <$> decodeS
      1 -> PList <$> decodeS
      2 -> PGuard <$> decodeS
      3 -> PObject <$> decodeS
      4 -> PModRef <$> decodeS
      5 -> PCapToken <$> decodeS
      6 -> PTime . UTCTime . NominalDiffTime <$> decode
      7 -> PTable <$> decodeS
      _ -> fail "unexpected decoding"
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 ChainId) where
  encode (SerialiseV1 (ChainId cid)) = encode cid
  {-# INLINE encode #-}
  decode = SerialiseV1 . ChainId <$> decode
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 Provenance) where
  encode (SerialiseV1 (Provenance tcid mh)) =
    encodeListLen 2 <> encodeS tcid <> encodeS mh
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "Provenance"
    SerialiseV1 <$> (Provenance <$> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 Yield) where
  encode (SerialiseV1 (Yield d p s)) =
    encodeListLen 3 <> encodeS d <> encodeS p <> encodeS s
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 3 "Yield"
    SerialiseV1 <$> (Yield <$> decodeS <*> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 (DefPactContinuation QualifiedName PactValue)) where
  encode (SerialiseV1 (DefPactContinuation n a)) =
    encodeListLen 2 <> encodeS n <> encodeS a
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 2 "DefPactContinuation"
    SerialiseV1 <$> (DefPactContinuation <$> decodeS <*> decodeS)
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 DefPactExec) where
  encode (SerialiseV1 (DefPactExec sc y s dpid cont rb ndp)) =
    encodeListLen 7 <>
    encode sc <> encodeS y <> encode s <>
    encodeS dpid <> encodeS cont <> encode rb <>
    encode (coerceMapToSerialise ndp)
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 7 "DefPactExec"
    SerialiseV1 <$> (DefPactExec <$> decode <*> decodeS <*> decode <*> decodeS <*> decodeS <*> decode <*> (coerceMapFromSerialise <$> decode))
  {-# INLINE decode #-}

instance Serialise (SerialiseV1 NestedDefPactExec) where
  encode (SerialiseV1 (NestedDefPactExec sc y s dpid cont ndp)) =
    encodeListLen 6 <>
    encode sc <> encodeS y <> encode s <>
    encodeS dpid <> encodeS cont <>
    encode (coerceMapToSerialise ndp)
  {-# INLINE encode #-}
  decode = do
    safeDecodeListLen 6 "DefPactExec"
    SerialiseV1 <$> (NestedDefPactExec <$> decode <*> decodeS <*> decode <*> decodeS <*> decodeS <*> (coerceMapFromSerialise <$> decode))
  {-# INLINE decode #-}
