{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Pact.Core.Legacy.LegacyPactValue
  (Legacy(..), roundtripPactValue) where

import Control.Applicative
import Data.Aeson
import Data.String (IsString (..))

import qualified Pact.JSON.Encode as J

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Aeson as A
import qualified Data.Aeson.KeyMap as A

import Pact.Core.Names
import Pact.Core.Guards
import Pact.Core.Literal
import Pact.Core.ModRefs
import Pact.Core.PactValue
import Pact.Core.Legacy.LegacyCodec
import Pact.Core.StableEncoding
import Data.List
import Pact.Core.Persistence.Types
import Pact.Core.Serialise.LegacyPact.Types (RowDataValue, ObjectMap)
import Data.Vector (Vector)
import Data.Text (Text)
import Control.Monad


newtype Legacy a
  = Legacy { _unLegacy :: a }

data GuardProperty
  = GuardArgs
  | GuardCgArgs
  | GuardCgName
  | GuardCgPactId
  | GuardFun
  | GuardKeys
  | GuardKeysetref
  | GuardKsn
  | GuardModuleName
  | GuardName
  | GuardNs
  | GuardPactId
  | GuardPred
  | GuardUnknown !String
  deriving (Show, Eq, Ord)

_gprop :: IsString a => Semigroup a => GuardProperty -> a
_gprop GuardArgs = "args"
_gprop GuardCgArgs = "cgArgs"
_gprop GuardCgName = "cgName"
_gprop GuardCgPactId = "cgPactId"
_gprop GuardFun = "fun"
_gprop GuardKeys = "keys"
_gprop GuardKeysetref = "keysetref"
_gprop GuardKsn = "ksn"
_gprop GuardModuleName = "moduleName"
_gprop GuardName = "name"
_gprop GuardNs = "ns"
_gprop GuardPactId = "pactId"
_gprop GuardPred = "pred"
_gprop (GuardUnknown t) = "UNKNOWN_GUARD[" <> fromString t <> "]"

ungprop :: IsString a => Eq a => Show a => a -> GuardProperty
ungprop "args" = GuardArgs
ungprop "cgArgs" = GuardCgArgs
ungprop "cgName" = GuardCgName
ungprop "cgPactId" = GuardCgPactId
ungprop "fun" = GuardFun
ungprop "keys" = GuardKeys
ungprop "keysetref" = GuardKeysetref
ungprop "ksn" = GuardKsn
ungprop "moduleName" = GuardModuleName
ungprop "name" = GuardName
ungprop "ns" = GuardNs
ungprop "pactId" = GuardPactId
ungprop "pred" = GuardPred
ungprop t = GuardUnknown (show t)

keyNamef :: Key
keyNamef = "keysetref"

instance FromJSON (Legacy QualifiedName) where
  parseJSON = withText "QualifiedName" $ \t -> case parseQualifiedName t of
    Just qn -> pure (Legacy qn)
    _ -> fail "could not parse qualified name"

instance FromJSON (Legacy ModuleName) where
  parseJSON = withObject "module name" $ \o ->
    fmap Legacy $
      ModuleName
        <$> (o .: "name")
        <*> (fmap NamespaceName <$> (o .: "namespace"))

instance FromJSON (Legacy (UserGuard QualifiedName PactValue)) where
  parseJSON = withObject "UserGuard" $ \o ->
      Legacy <$> (UserGuard
        <$> (_unLegacy <$> o .: "fun")
        <*> (fmap _unLegacy <$> o .: "args"))

instance FromJSON (Legacy KeySetName) where
  parseJSON v =
    Legacy <$> (newKs v <|> oldKs v)
    where
    oldKs = withText "KeySetName" (pure . (`KeySetName` Nothing))
    newKs =
      withObject "KeySetName" $ \o -> KeySetName
        <$> o .: "ksn"
        <*> (fmap NamespaceName <$> o .:? "ns")

instance FromJSON (Legacy (Guard QualifiedName PactValue)) where
  parseJSON v = case props v of
    [GuardKeys, GuardPred] -> Legacy . GKeyset . _unLegacy <$> parseJSON v
    [GuardKeysetref] -> flip (withObject "KeySetRef") v $ \o ->
        Legacy . GKeySetRef . _unLegacy <$> o .: keyNamef
    [GuardName, GuardPactId] -> Legacy . GDefPactGuard . _unLegacy <$> parseJSON v
    [GuardModuleName, GuardName] -> Legacy . GModuleGuard . _unLegacy <$> parseJSON v
    [GuardArgs, GuardFun] -> Legacy . GUserGuard . _unLegacy <$> parseJSON v
    [GuardCgArgs, GuardCgName, GuardCgPactId] -> Legacy . GCapabilityGuard . _unLegacy <$> parseJSON v
    _ -> fail $ "unexpected properties for Guard: "
      <> show (props v)
      <> ", " <> show (J.encode v)
   where
    props (A.Object o) = sort $ ungprop <$> A.keys o
    props _ = []
  {-# INLINEABLE parseJSON #-}

instance FromJSON (Legacy Literal) where
  parseJSON n@Number{} =  Legacy . LDecimal <$> decoder decimalCodec n
  parseJSON (String s) = pure $ Legacy $ LString s
  parseJSON (Bool b) = pure $ Legacy $ LBool b
  parseJSON o@Object {} =
    (Legacy . LInteger <$> decoder integerCodec o) <|>
    -- (LTime <$> decoder timeCodec o) <|>
    (Legacy . LDecimal <$> decoder decimalCodec o)
  parseJSON _t = fail "Literal parse failed"

instance FromJSON (Legacy KSPredicate) where
  parseJSON = withText "kspredfun" $ \case
    "keys-all" -> pure $ Legacy KeysAll
    "keys-any" -> pure $ Legacy KeysAny
    "keys-2" -> pure $ Legacy Keys2
    t | Just pn <- parseParsedTyName t -> pure $ Legacy (CustomPredicate pn)
      | otherwise -> fail "invalid keyset predicate"


instance FromJSON (Legacy KeySet) where

    parseJSON v =
      Legacy <$> (withObject "KeySet" keyListPred v <|> keyListOnly)
      where

        keyListPred o = KeySet
          <$> (S.fromList . fmap PublicKeyText <$> (o .: "keys"))
          <*> (maybe KeysAll _unLegacy <$>  o .:? "pred")

        keyListOnly = KeySet
          <$> (S.fromList . fmap PublicKeyText <$> parseJSON v)
          <*> pure KeysAll

instance FromJSON (Legacy ModRef) where
  parseJSON = withObject "ModRef" $ \o ->
    fmap Legacy $
      ModRef <$> (_unLegacy <$> o .: "refName")
        <*> (fmap _unLegacy <$> o .: "refSpec")
        <*> pure Nothing

instance FromJSON (Legacy PactValue) where
  parseJSON v = fmap Legacy $
    (PLiteral . _unLegacy <$> parseJSON v) <|>
    (PList . fmap _unLegacy <$> parseJSON v) <|>
    (PGuard . _unLegacy <$> parseJSON v) <|>
    (PModRef . _unLegacy <$> parseJSON v) <|>
    (PObject . M.mapKeys Field . fmap _unLegacy <$> parseJSON v)

instance FromJSON (Legacy ModuleGuard) where
  parseJSON = withObject "ModuleGuard" $ \o ->
    fmap Legacy $
      ModuleGuard <$> (_unLegacy <$> o .: "moduleName")
        <*> (o .: "name")

instance FromJSON (Legacy DefPactGuard) where
  parseJSON = withObject "DefPactGuard" $ \o -> do
    fmap Legacy $
      DefPactGuard
        <$> (DefPactId <$> o .: "pactId")
        <*> o .: "name"

instance FromJSON (Legacy (CapabilityGuard QualifiedName PactValue)) where
  parseJSON = withObject "CapabilityGuard" $ \o ->
    fmap Legacy $
      CapabilityGuard
        <$> (_unLegacy <$> o .: "cgName")
        <*> (fmap _unLegacy <$> o .: "cgArgs")
        <*> (fmap DefPactId <$> o .: "cgPactId")

roundtripPactValue :: PactValue -> Maybe PactValue
roundtripPactValue pv =
  _unLegacy <$> A.decodeStrict' (encodeStable pv)

instance J.Encode (Legacy WriteType) where
  build (Legacy Insert) = J.text "Insert"
  build (Legacy Update) = J.text "Update"
  build (Legacy Write) = J.text "Write"
instance FromJSON (Legacy WriteType) where
  parseJSON = withText "WriteType" $ \case
    "Insert" -> return $ Legacy Insert
    "Update" -> return $ Legacy Update
    "Write" -> return $ Legacy Write
    _ -> fail "invalid, expected Insert, Update, or Write"

instance J.Encode (Legacy RowKey) where
  build (Legacy rk) = J.text (_rowKey rk)

instance J.Encode (Legacy (SomeDomain b i)) where
  build (Legacy (SomeDomain d)) = case d of
    DUserTables tn
      -- this is specifically for prod compat
      | let qn = QualifiedName (_tableName tn) (_tableModuleName tn)
      -> J.build $ J.Object
          [ J.KeyValue "tag" $ J.text "UserTables"
          , J.KeyValue "tableName" $ J.text $ renderQualName qn
          ]
    DKeySets -> J.text "KeySets"
    DModules -> J.text "Modules"
    DNamespaces -> J.text "Namespaces"
    DDefPacts -> J.text "Pacts"
instance FromJSON (Legacy (SomeDomain b i)) where
  parseJSON v =
    (withText "Domain" $ \case
      "KeySets" -> return $ Legacy $ SomeDomain DKeySets
      "Modules" -> return $ Legacy $ SomeDomain DModules
      "Namespaces" -> return $ Legacy $ SomeDomain DNamespaces
      "Pacts" -> return $ Legacy $ SomeDomain DDefPacts
      _ -> fail "invalid Domain") v <|>
    (withObject "Domain" $ \o -> do
      tag :: Text <- o .: "tag"
      unless (tag == "UserTables") $
        fail "JSON object Domain must have UserTables tag"
      -- this is specifically for prod compat
      Just qualifiedTableName <- parseQualifiedName <$> o .: "tableName"
      let asTableName = TableName
            { _tableName = _qnName qualifiedTableName
            , _tableModuleName = _qnModName qualifiedTableName
            }
      return $ Legacy $ SomeDomain (DUserTables asTableName)
    ) v
