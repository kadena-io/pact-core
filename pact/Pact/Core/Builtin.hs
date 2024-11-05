{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}

module Pact.Core.Builtin
 ( CoreBuiltin(..)
 , coreBuiltinMap
 , coreBuiltinNames
 , ReplBuiltin(..)
 , replCoreBuiltinNames
 , replBuiltinMap
 , replCoreBuiltinOnlyMap
 , coreBuiltinToUserText
 , coreBuiltinToText
 , replCoreBuiltinToUserText
 , IsBuiltin(..)
 , ReplCoreBuiltin
 , BuiltinForm(..)
 , ReplOnlyBuiltin(..)
 , _CAnd, _COr, _CIf
 , _CEnforceOne, _CEnforce
 , _CWithCapability, _CCreateUserGuard
 )where

import Control.Lens
import Data.Text(Text)
import Data.Map.Strict(Map)
import Control.DeepSeq
import GHC.Generics

import qualified Data.Map.Strict as M

import Pact.Core.Names(NativeName(..))
import Pact.Core.Pretty
import Pact.Core.DeriveConTag

-- | Our type alias for the majority of our repl builtins wrap
type ReplCoreBuiltin = ReplBuiltin CoreBuiltin

-- | Our syntactic builtin forms, which capture terms and may evaluate them lazily
--   Note: this does not include capability forms
data BuiltinForm o
  = CAnd o o
  | COr o o
  | CIf o o o
  | CEnforce o o
  | CWithCapability o o
  | CCreateUserGuard o
  | CEnforceOne o o
  | CRunReadOnly o
  | CTry o o
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic)

instance NFData o => NFData (BuiltinForm o)

instance Pretty o => Pretty (BuiltinForm o) where
  pretty = \case
    CAnd o o' ->
      parens ("and" <+> pretty o <+> pretty o')
    COr o o' ->
      parens ("or" <+> pretty o <+> pretty o')
    CIf o o' o3 ->
      parens ("if" <+> pretty o <+> pretty o' <+> pretty o3)
    CEnforceOne o o' ->
      parens ("enforce-one" <+> pretty o <+> pretty o')
    CEnforce o o' ->
      parens ("enforce" <+> pretty o <+> pretty o')
    CWithCapability o o' ->
      parens ("with-capability" <+> pretty o <+> (nest 2 (line <> pretty o')))
    CCreateUserGuard o ->
      parens ("create-user-guard" <+> pretty o)
    CTry o o' ->
      parens ("try" <+> pretty o <+> pretty o')
    CRunReadOnly o ->
      parens ("run-read-only" <+> pretty o)

-- | Our list of base-builtins to pact.
data CoreBuiltin
  -- Operators
  -- Addition/Concatenation
  = CoreAdd
  -- Num
  | CoreSub
  | CoreMultiply
  | CoreDivide
  | CoreNegate
  | CoreAbs
  | CorePow
  -- Boolean Ops
  | CoreNot
  -- Equality and Comparisons
  | CoreEq
  | CoreNeq
  -- Ord
  | CoreGT
  | CoreGEQ
  | CoreLT
  | CoreLEQ
  -- Bitwise Ops
  | CoreBitwiseAnd
  | CoreBitwiseOr
  | CoreBitwiseXor
  | CoreBitwiseFlip
  | CoreBitShift
  --  Rounding
  | CoreRound
  | CoreCeiling
  | CoreFloor
  | CoreRoundPrec
  | CoreCeilingPrec
  | CoreFloorPrec
  -- Fractional
  | CoreExp
  | CoreLn
  | CoreSqrt
  | CoreLogBase
  -- List like
  | CoreLength
  | CoreTake
  | CoreDrop
  | CoreConcat
  | CoreReverse
  | CoreContains
  | CoreSort
  | CoreSortObject
  | CoreRemove
  -- General
  | CoreMod
  | CoreMap
  | CoreFilter
  | CoreZip
  | CoreIntToStr
  | CoreStrToInt
  | CoreStrToIntBase
  | CoreFold
  | CoreDistinct
  | CoreFormat
  -- | CoreEnforce
  -- | CoreEnforceOne
  | CoreEnumerate
  | CoreEnumerateStepN
  -- Guards + read functions
  | CoreShow
  | CoreReadMsg
  | CoreReadMsgDefault
  | CoreReadInteger
  | CoreReadDecimal
  | CoreReadString
  | CoreReadKeyset
  | CoreEnforceGuard
  | CoreEnforceKeyset
  | CoreKeysetRefGuard
  | CoreAt
  | CoreMakeList
  | CoreB64Encode
  | CoreB64Decode
  | CoreStrToList
  | CoreYield
  | CoreYieldToChain
  | CoreResume
  | CoreBind
  | CoreRequireCapability
  | CoreComposeCapability
  | CoreInstallCapability
  | CoreEmitEvent
  | CoreCreateCapabilityGuard
  | CoreCreateCapabilityPactGuard
  | CoreCreateModuleGuard
  | CoreCreateDefPactGuard
  -- Database functions
  | CoreCreateTable
  | CoreDescribeKeyset
  | CoreDescribeModule
  | CoreDescribeTable
  | CoreDefineKeySet
  | CoreDefineKeysetData
  | CoreFoldDb
  | CoreInsert
  | CoreKeys
  | CoreRead
  | CoreSelect
  | CoreSelectWithFields
  | CoreUpdate
  | CoreWithDefaultRead
  | CoreWithRead
  | CoreWrite
  | CoreTxHash
  -- Db QueryFunctions
  | CoreAndQ
  | CoreOrQ
  | CoreWhere
  | CoreNotQ
  | CoreHash
  | CoreContinue
  -- Time functions
  | CoreParseTime
  | CoreFormatTime
  | CoreTime
  | CoreAddTime
  | CoreDiffTime
  | CoreHours
  | CoreMinutes
  | CoreDays
  | CoreCompose
  | CoreCreatePrincipal
  | CoreIsPrincipal
  | CoreTypeOfPrincipal
  | CoreValidatePrincipal
  -- Namespaces
  | CoreNamespace
  | CoreDefineNamespace
  | CoreDescribeNamespace
  | CoreChainData
  | CoreIsCharset
  | CorePactId
  -- ZK
  | CoreZkPairingCheck
  | CoreZKScalarMult
  | CoreZkPointAdd
  -- Poseidon Hackachain
  | CorePoseidonHashHackachain
  -- Misc
  | CoreTypeOf
  | CoreDec
  | CoreCond
  | CoreIdentity
  | CoreVerifySPV
  | CoreEnforceVerifier
  | CoreAcquireModuleAdmin
  -- Hyperlane
  | CoreHyperlaneMessageId
  | CoreHyperlaneDecodeMessage
  | CoreHyperlaneEncodeMessage
  -- | BackCompat: read with filtering columns
  | CoreReadWithFields
  | CoreListModules
  | CoreStaticRedeploy
  deriving (Eq, Show, Ord, Bounded, Enum, Generic)

instance NFData CoreBuiltin

-- | A list of our internal overloads.
coreBuiltinOverloads :: [CoreBuiltin]
coreBuiltinOverloads =
  [ CoreEnumerateStepN
  , CoreSelectWithFields
  , CoreSortObject
  , CoreRoundPrec
  , CoreCeilingPrec
  , CoreFloorPrec
  , CoreStrToIntBase
  , CoreReadMsgDefault
  , CoreDefineKeysetData
  , CoreYieldToChain
  , CoreReadWithFields]

-- | NOTE: this function spits out fully resolved overload name of a native.
--   This is used for both errors and hashes. DO NOT CHANGE unless you know what you are doing,
--   or we are forking this change.
--
--   coreBuiltinToText gives us a unique text representation of each function. For a function for UX use, see
--   coreBuiltinToUserText
coreBuiltinToText :: CoreBuiltin -> Text
coreBuiltinToText = \case
  -- Addition
  CoreAdd -> "+"
  -- Num
  CoreSub -> "-"
  CoreMultiply -> "*"
  CoreDivide -> "/"
  CoreNegate -> "negate"
  CoreAbs -> "abs"
  CorePow -> "^"
  -- Boolean ops
  CoreNot -> "not"
  -- Eq
  CoreEq -> "="
  CoreNeq -> "!="
  -- Ord
  CoreGT -> ">"
  CoreGEQ -> ">="
  CoreLT -> "<"
  CoreLEQ -> "<="
  -- Int ops
  CoreBitwiseAnd -> "&"
  CoreBitwiseOr -> "|"
  CoreBitwiseXor -> "xor"
  CoreBitwiseFlip -> "~"
  CoreBitShift -> "shift"
  CoreMod -> "mod"
  -- roundings
  CoreRound -> "round"
  CoreCeiling -> "ceiling"
  CoreFloor -> "floor"
  CoreRoundPrec -> "round-prec"
  CoreCeilingPrec -> "ceiling-prec"
  CoreFloorPrec -> "floor-prec"
  -- Fractional
  CoreExp -> "exp"
  CoreLn -> "ln"
  CoreSqrt -> "sqrt"
  CoreLogBase -> "log"
  -- ListLike
  CoreLength -> "length"
  CoreTake -> "take"
  CoreDrop -> "drop"
  CoreConcat -> "concat"
  CoreReverse -> "reverse"
  -- general
  CoreMap -> "map"
  CoreFilter -> "filter"
  CoreContains -> "contains"
  CoreSort -> "sort"
  CoreSortObject -> "sort-object"
  CoreRemove -> "remove"
  -- CoreIf -> "if"
  CoreIntToStr -> "int-to-str"
  CoreStrToInt -> "str-to-int"
  CoreStrToIntBase -> "str-to-int-base"
  CoreFold -> "fold"
  CoreZip -> "zip"
  CoreDistinct -> "distinct"
  CoreFormat -> "format"
  CoreEnumerate -> "enumerate"
  CoreEnumerateStepN -> "enumerate-step"
  CoreShow -> "show"
  CoreReadMsg -> "read-msg"
  CoreReadMsgDefault -> "read-msg-default"
  CoreReadInteger -> "read-integer"
  CoreReadDecimal -> "read-decimal"
  CoreReadString -> "read-string"
  CoreReadKeyset -> "read-keyset"
  CoreEnforceGuard -> "enforce-guard"
  CoreEnforceKeyset -> "enforce-keyset"
  CoreKeysetRefGuard -> "keyset-ref-guard"
  CoreCreateCapabilityGuard -> "create-capability-guard"
  CoreCreateCapabilityPactGuard -> "create-capability-pact-guard"
  CoreCreateModuleGuard -> "create-module-guard"
  CoreCreateDefPactGuard -> "create-pact-guard"
  CoreAt -> "at"
  CoreMakeList -> "make-list"
  CoreB64Encode -> "base64-encode"
  CoreB64Decode -> "base64-decode"
  CoreStrToList -> "str-to-list"
  CoreYield -> "yield"
  CoreYieldToChain -> "yield-to-chain"
  CoreResume -> "resume"
  CoreBind -> "bind"
  CoreRequireCapability -> "require-capability"
  CoreComposeCapability -> "compose-capability"
  CoreInstallCapability -> "install-capability"
  CoreEmitEvent -> "emit-event"
  CoreCreateTable -> "create-table"
  CoreDescribeKeyset -> "describe-keyset"
  CoreDescribeModule -> "describe-module"
  CoreDescribeTable -> "describe-table"
  CoreDefineKeySet -> "define-keyset"
  CoreDefineKeysetData -> "define-read-keyset"
  CoreFoldDb -> "fold-db"
  CoreInsert -> "insert"
  CoreKeys -> "keys"
  CoreRead -> "read"
  CoreSelect -> "select"
  CoreSelectWithFields -> "select-with-fields"
  CoreUpdate -> "update"
  CoreWithDefaultRead -> "with-default-read"
  CoreWithRead -> "with-read"
  CoreWrite -> "write"
  CoreTxHash -> "tx-hash"
  CoreAcquireModuleAdmin -> "acquire-module-admin"
  CoreAndQ -> "and?"
  CoreOrQ -> "or?"
  CoreWhere -> "where"
  CoreNotQ -> "not?"
  CoreHash -> "hash"
  CoreContinue -> "continue"
  CoreParseTime -> "parse-time"
  CoreFormatTime -> "format-time"
  CoreTime -> "time"
  CoreAddTime -> "add-time"
  CoreDiffTime -> "diff-time"
  CoreHours -> "hours"
  CoreMinutes -> "minutes"
  CoreDays -> "days"
  CoreCompose -> "compose"
  CoreCreatePrincipal -> "create-principal"
  CoreIsPrincipal -> "is-principal"
  CoreTypeOfPrincipal -> "typeof-principal"
  CoreValidatePrincipal -> "validate-principal"
  CoreNamespace -> "namespace"
  CoreDefineNamespace -> "define-namespace"
  CoreDescribeNamespace -> "describe-namespace"
  CoreZkPairingCheck -> "pairing-check"
  CoreZKScalarMult -> "scalar-mult"
  CoreZkPointAdd -> "point-add"
  CorePoseidonHashHackachain -> "poseidon-hash-hack-a-chain"
  CoreChainData -> "chain-data"
  CoreIsCharset -> "is-charset"
  CorePactId -> "pact-id"
  CoreTypeOf -> "typeof"
  CoreDec -> "dec"
  CoreCond -> "cond"
  CoreIdentity -> "identity"
  CoreVerifySPV -> "verify-spv"
  CoreEnforceVerifier -> "enforce-verifier"
  CoreHyperlaneMessageId -> "hyperlane-message-id"
  CoreHyperlaneDecodeMessage -> "hyperlane-decode-token-message"
  CoreHyperlaneEncodeMessage -> "hyperlane-encode-token-message"
  CoreReadWithFields -> "read-with-fields"
  CoreListModules -> "list-modules"
  CoreStaticRedeploy -> "static-redeploy"

-- | Our `CoreBuiltin` user-facing representation.
-- note: `coreBuiltinToUserText` is primarily for pretty printing
coreBuiltinToUserText :: CoreBuiltin -> Text
coreBuiltinToUserText = \case
  -- Addition
  CoreAdd -> "+"
  -- Num
  CoreSub -> "-"
  CoreMultiply -> "*"
  CoreDivide -> "/"
  CoreNegate -> "negate"
  CoreAbs -> "abs"
  CorePow -> "^"
  -- Boolean ops
  CoreNot -> "not"
  -- Eq
  CoreEq -> "="
  CoreNeq -> "!="
  -- Ord
  CoreGT -> ">"
  CoreGEQ -> ">="
  CoreLT -> "<"
  CoreLEQ -> "<="
  -- Int ops
  CoreBitwiseAnd -> "&"
  CoreBitwiseOr -> "|"
  CoreBitwiseXor -> "xor"
  CoreBitwiseFlip -> "~"
  CoreBitShift -> "shift"
  CoreMod -> "mod"
  -- roundings
  CoreRound -> "round"
  CoreCeiling -> "ceiling"
  CoreFloor -> "floor"
  CoreRoundPrec -> "round"
  CoreCeilingPrec -> "ceiling"
  CoreFloorPrec -> "floor"
  -- Fractional
  CoreExp -> "exp"
  CoreLn -> "ln"
  CoreSqrt -> "sqrt"
  CoreLogBase -> "log"
  -- ListLike
  CoreLength -> "length"
  CoreTake -> "take"
  CoreDrop -> "drop"
  CoreConcat -> "concat"
  CoreReverse -> "reverse"
  -- general
  CoreMap -> "map"
  CoreFilter -> "filter"
  CoreContains -> "contains"
  CoreSort -> "sort"
  CoreSortObject -> "sort"
  CoreRemove -> "remove"
  -- CoreIf -> "if"
  CoreIntToStr -> "int-to-str"
  CoreStrToInt -> "str-to-int"
  CoreStrToIntBase -> "str-to-int"
  CoreFold -> "fold"
  CoreZip -> "zip"
  CoreDistinct -> "distinct"
  CoreFormat -> "format"
  CoreEnumerate -> "enumerate"
  CoreEnumerateStepN -> "enumerate"
  CoreShow -> "show"
  CoreReadMsg -> "read-msg"
  CoreReadMsgDefault -> "read-msg"
  CoreReadInteger -> "read-integer"
  CoreReadDecimal -> "read-decimal"
  CoreReadString -> "read-string"
  CoreReadKeyset -> "read-keyset"
  CoreEnforceGuard -> "enforce-guard"
  CoreEnforceKeyset -> "enforce-keyset"
  CoreKeysetRefGuard -> "keyset-ref-guard"
  CoreCreateCapabilityGuard -> "create-capability-guard"
  CoreCreateCapabilityPactGuard -> "create-capability-pact-guard"
  CoreCreateModuleGuard -> "create-module-guard"
  CoreCreateDefPactGuard -> "create-pact-guard"
  CoreAt -> "at"
  CoreMakeList -> "make-list"
  CoreB64Encode -> "base64-encode"
  CoreB64Decode -> "base64-decode"
  CoreStrToList -> "str-to-list"
  CoreYield -> "yield"
  CoreYieldToChain -> "yield"
  CoreResume -> "resume"
  CoreBind -> "bind"
  CoreRequireCapability -> "require-capability"
  CoreComposeCapability -> "compose-capability"
  CoreInstallCapability -> "install-capability"
  CoreEmitEvent -> "emit-event"
  CoreCreateTable -> "create-table"
  CoreDescribeKeyset -> "describe-keyset"
  CoreDescribeModule -> "describe-module"
  CoreDescribeTable -> "describe-table"
  CoreDefineKeySet -> "define-keyset"
  CoreDefineKeysetData -> "define-keyset"
  CoreFoldDb -> "fold-db"
  CoreInsert -> "insert"
  CoreKeys -> "keys"
  CoreRead -> "read"
  CoreSelect -> "select"
  CoreSelectWithFields -> "select"
  CoreUpdate -> "update"
  CoreWithDefaultRead -> "with-default-read"
  CoreWithRead -> "with-read"
  CoreWrite -> "write"
  CoreTxHash -> "tx-hash"
  CoreAndQ -> "and?"
  CoreOrQ -> "or?"
  CoreWhere -> "where"
  CoreNotQ -> "not?"
  CoreHash -> "hash"
  CoreContinue -> "continue"
  CoreParseTime -> "parse-time"
  CoreFormatTime -> "format-time"
  CoreTime -> "time"
  CoreAddTime -> "add-time"
  CoreDiffTime -> "diff-time"
  CoreHours -> "hours"
  CoreMinutes -> "minutes"
  CoreDays -> "days"
  CoreCompose -> "compose"
  CoreCreatePrincipal -> "create-principal"
  CoreIsPrincipal -> "is-principal"
  CoreTypeOfPrincipal -> "typeof-principal"
  CoreValidatePrincipal -> "validate-principal"
  CoreNamespace -> "namespace"
  CoreDefineNamespace -> "define-namespace"
  CoreDescribeNamespace -> "describe-namespace"
  CoreZkPairingCheck -> "pairing-check"
  CoreZKScalarMult -> "scalar-mult"
  CoreZkPointAdd -> "point-add"
  CorePoseidonHashHackachain -> "poseidon-hash-hack-a-chain"
  CoreChainData -> "chain-data"
  CoreIsCharset -> "is-charset"
  CorePactId -> "pact-id"
  CoreTypeOf -> "typeof"
  CoreDec -> "dec"
  CoreCond -> "cond"
  CoreIdentity -> "identity"
  CoreVerifySPV -> "verify-spv"
  CoreEnforceVerifier -> "enforce-verifier"
  CoreHyperlaneMessageId -> "hyperlane-message-id"
  CoreHyperlaneDecodeMessage -> "hyperlane-decode-token-message"
  CoreHyperlaneEncodeMessage -> "hyperlane-encode-token-message"
  CoreAcquireModuleAdmin -> "acquire-module-admin"
  CoreReadWithFields -> "read"
  CoreListModules -> "list-modules"
  CoreStaticRedeploy -> "static-redeploy"

instance IsBuiltin CoreBuiltin where
  builtinName = NativeName . coreBuiltinToText
  builtinArity = \case
    CoreAdd -> 2
    -- Num ->
    CoreSub -> 2
    CoreMultiply -> 2
    CoreDivide -> 2
    CoreNegate -> 1
    CoreAbs -> 1
    CorePow -> 2
    -- Boolean Ops ->
    -- CoreAnd -> 2
    -- CoreOr -> 2
    CoreNot -> 1
    -- Equality and Comparisons ->
    CoreEq -> 2
    CoreNeq -> 2
    -- Ord ->
    CoreGT -> 2
    CoreGEQ -> 2
    CoreLT -> 2
    CoreLEQ -> 2
    -- Bitwise Ops ->
    CoreBitwiseAnd -> 2
    CoreBitwiseOr -> 2
    CoreBitwiseXor -> 2
    CoreBitwiseFlip -> 1
    CoreBitShift -> 2
    --  Rounding ->
    CoreRound -> 1
    CoreCeiling -> 1
    CoreFloor -> 1
    CoreRoundPrec -> 2
    CoreCeilingPrec -> 2
    CoreFloorPrec -> 2
    -- Fractional ->
    CoreExp -> 1
    CoreLn -> 1
    CoreSqrt -> 1
    CoreLogBase -> 2
    -- List like ->
    CoreLength -> 1
    CoreTake -> 2
    CoreDrop -> 2
    CoreConcat -> 1
    CoreReverse -> 1
    CoreContains -> 2
    CoreSort -> 1
    CoreSortObject -> 2
    CoreRemove -> 2
    -- General ->
    CoreMod -> 2
    CoreMap -> 2
    CoreFilter -> 2
    CoreZip -> 3
    -- CoreIf -> 3
    CoreIntToStr -> 2
    CoreStrToInt -> 1
    CoreStrToIntBase -> 2
    CoreFold -> 3
    CoreDistinct -> 1
    CoreFormat -> 2
    -- CoreEnforce -> 2
    -- CoreEnforceOne -> 2
    CoreEnumerate -> 2
    CoreEnumerateStepN -> 3
    -- Show ->
    CoreShow -> 1
    CoreReadMsg -> 1
    CoreReadMsgDefault -> 0
    CoreReadInteger -> 1
    CoreReadDecimal -> 1
    CoreReadString -> 1
    CoreReadKeyset -> 1
    CoreEnforceKeyset -> 1
    CoreEnforceGuard -> 1
    CoreKeysetRefGuard -> 1
    CoreCreateCapabilityGuard -> 1
    CoreCreateCapabilityPactGuard -> 1
    CoreCreateModuleGuard -> 1
    CoreCreateDefPactGuard -> 1
    CoreAt -> 2
    CoreMakeList -> 2
    CoreB64Encode -> 1
    CoreB64Decode -> 1
    CoreStrToList -> 1
    CoreYield -> 1
    CoreYieldToChain -> 2
    CoreResume -> 1
    CoreBind -> 2
    CoreRequireCapability -> 1
    CoreComposeCapability -> 1
    CoreInstallCapability -> 1
    CoreEmitEvent -> 1
    CoreCreateTable -> 1
    CoreDescribeKeyset -> 1
    CoreDescribeModule -> 1
    CoreDescribeTable -> 1
    CoreDefineKeySet -> 2
    CoreDefineKeysetData -> 1
    CoreFoldDb -> 3
    CoreInsert -> 3
    CoreKeys -> 1
    CoreRead -> 2
    CoreSelect -> 2
    CoreSelectWithFields -> 3
    CoreUpdate -> 3
    CoreWithDefaultRead -> 4
    CoreWithRead -> 3
    CoreWrite -> 3
    CoreTxHash -> 0
    CoreAndQ -> 3
    CoreOrQ -> 3
    CoreWhere -> 3
    CoreNotQ -> 2
    CoreHash -> 1
    CoreContinue -> 1
    CoreParseTime -> 2
    CoreFormatTime -> 2
    CoreTime -> 1
    CoreAddTime -> 2
    CoreDiffTime -> 2
    CoreHours -> 1
    CoreMinutes -> 1
    CoreDays -> 1
    CoreCompose -> 3
    CoreCreatePrincipal -> 1
    CoreIsPrincipal -> 1
    CoreTypeOfPrincipal -> 1
    CoreValidatePrincipal -> 2
    CoreNamespace -> 1
    CoreDefineNamespace -> 3
    CoreDescribeNamespace -> 1
    CoreZkPairingCheck -> 2
    CoreZKScalarMult -> 3
    CoreZkPointAdd -> 3
    CorePoseidonHashHackachain -> 1
    CoreChainData -> 0
    CoreIsCharset -> 2
    CorePactId -> 0
    CoreTypeOf -> 1
    CoreDec -> 1
    CoreCond -> 1
    CoreIdentity -> 1
    CoreAcquireModuleAdmin -> 1
    CoreVerifySPV -> 2
    CoreEnforceVerifier -> 1
    CoreHyperlaneMessageId -> 1
    CoreHyperlaneDecodeMessage -> 1
    CoreHyperlaneEncodeMessage -> 1
    CoreReadWithFields -> 3
    CoreListModules -> 0
    CoreStaticRedeploy -> 1

coreBuiltinNames :: [Text]
coreBuiltinNames =
  [ coreBuiltinToText b
  | b <- [minBound .. maxBound]
  , b `notElem` coreBuiltinOverloads]

coreBuiltinMap :: Map Text CoreBuiltin
coreBuiltinMap = M.fromList
  [ (coreBuiltinToText b, b)
  | b <- [minBound .. maxBound]
  , b `notElem` coreBuiltinOverloads]

-- | Our repl builtins.
data ReplOnlyBuiltin
  = RExpect
  | RExpectFailure
  | RExpectFailureMatch
  | RExpectThat
  | RPrint
  | REnvStackFrame
  | REnvChainData
  | REnvData
  | REnvEvents
  | REnvHash
  | REnvKeys
  | REnvSigs
  | RBeginTx
  | RBeginNamedTx
  | RCommitTx
  | RRollbackTx
  | RSigKeyset
  | RTestCapability
  | REnvExecConfig
  | REnvNamespacePolicy
  | REnvGas
  | REnvGasSet
  | REnvMilliGas
  | REnvSetMilliGas
  | REnvGasLimit
  | REnvGasLog
  | REnvGasModel
  | REnvAskGasModel
  | REnvGasModelFixed
  -- | REnvGasPrice
  -- | REnvGasRate
  -- Defpact
  | RContinuePact
  | RContinuePactRollback
  | RContinuePactRollbackYield
  | RContinuePactRollbackYieldObj
  | RPactState
  | RResetPactState
  | RPactVersion
  | REnforcePactVersionMin
  | REnforcePactVersionRange
  | REnvEnableReplNatives
  | REnvModuleAdmin
  | REnvVerifiers
  | REnvSetDebugFlag
  deriving (Show, Enum, Bounded, Eq, Generic)


instance IsBuiltin ReplOnlyBuiltin where
  builtinName = NativeName . replBuiltinsToText
  builtinArity = \case
    RExpect -> 3
    RExpectFailure -> 2
    RExpectFailureMatch -> 3
    RExpectThat -> 3
    RPrint -> 1
    RPactState -> 0
    RResetPactState -> 1
    REnvStackFrame -> 0
    REnvChainData -> 1
    REnvData -> 1
    REnvEvents -> 1
    REnvHash -> 1
    REnvKeys -> 1
    REnvSigs -> 1
    RBeginTx -> 0
    RBeginNamedTx -> 1
    RCommitTx -> 0
    RRollbackTx -> 0
    RSigKeyset -> 0
    RTestCapability -> 1
    RContinuePact -> 1
    RContinuePactRollback -> 2
    RContinuePactRollbackYield -> 3
    RContinuePactRollbackYieldObj -> 4
    REnvExecConfig -> 1
    REnvNamespacePolicy -> 2
    REnvGas -> 0
    REnvGasSet -> 1
    REnvMilliGas -> 0
    REnvSetMilliGas -> 1
    REnvGasLimit -> 1
    REnvGasLog -> 0
    REnvGasModel -> 1
    REnvAskGasModel -> 0
    REnvGasModelFixed -> 1
    RPactVersion -> 0
    REnforcePactVersionMin -> 1
    REnforcePactVersionRange -> 2
    REnvEnableReplNatives -> 1
    REnvModuleAdmin -> 1
    REnvVerifiers -> 1
    REnvSetDebugFlag -> 1

    -- RLoad -> 1
    -- RLoadWithEnv -> 2
-- Note: commented out natives are
-- to be implemented later
data ReplBuiltin b
  = RBuiltinWrap b
  | RBuiltinRepl ReplOnlyBuiltin
  deriving (Eq, Show, Generic)

-- NOTE: Maybe `ReplBuiltin` is not a great abstraction, given
-- expect arity changes based on whether it's corebuiltin or rawbuiltin
instance IsBuiltin b => IsBuiltin (ReplBuiltin b) where
  builtinName = NativeName . replBuiltinToText (_natName . builtinName)
  builtinArity = \case
    RBuiltinWrap b -> builtinArity b
    RBuiltinRepl b -> builtinArity b

    -- RLoad -> 1

instance Bounded b => Bounded (ReplBuiltin b) where
  minBound = RBuiltinWrap minBound
  maxBound = RBuiltinRepl maxBound

instance (Enum b, Bounded b) => Enum (ReplBuiltin b) where
  toEnum  i =
    if i <= mbound then RBuiltinWrap (toEnum i)
    else RBuiltinRepl (toEnum (i - mbound - 1))
    where
    mbound = fromEnum (maxBound :: b)
  {-# SPECIALIZE toEnum :: Int -> ReplBuiltin CoreBuiltin #-}

  fromEnum e =
    let maxContained = fromEnum (maxBound :: b) + 1
    in case e of
      RBuiltinWrap b -> fromEnum b
      RBuiltinRepl rb -> maxContained + fromEnum rb
  {-# SPECIALIZE fromEnum :: ReplBuiltin CoreBuiltin -> Int #-}

replBuiltinsToText :: ReplOnlyBuiltin -> Text
replBuiltinsToText = \case
  RExpect -> "expect"
  RExpectFailure -> "expect-failure"
  RExpectFailureMatch -> "expect-failure-match"
  RExpectThat -> "expect-that"
  RPrint -> "print"
  RPactState -> "pact-state"
  RResetPactState -> "reset-pact-state"
  REnvStackFrame -> "env-stackframe"
  REnvChainData -> "env-chain-data"
  REnvData -> "env-data"
  REnvEvents -> "env-events"
  REnvHash -> "env-hash"
  REnvKeys -> "env-keys"
  REnvSigs -> "env-sigs"
  RBeginTx -> "begin-tx"
  RBeginNamedTx -> "begin-named-tx"
  RCommitTx -> "commit-tx"
  RRollbackTx -> "rollback-tx"
  RSigKeyset -> "sig-keyset"
  RTestCapability -> "test-capability"
  RContinuePact -> "continue-pact"
  RContinuePactRollback -> "continue-pact-with-rollback"
  RContinuePactRollbackYield -> "continue-pact-rollback-yield"
  RContinuePactRollbackYieldObj -> "continue-pact-rollback-yield-object"
  REnvExecConfig -> "env-exec-config"
  REnvNamespacePolicy -> "env-namespace-policy"
  REnvGas -> "env-gas"
  REnvGasSet -> "env-set-gas"
  REnvMilliGas -> "env-milligas"
  REnvSetMilliGas -> "env-set-milligas"
  REnvGasLimit -> "env-gaslimit"
  REnvGasLog -> "env-gaslog"
  REnvGasModel -> "env-gasmodel"
  REnvAskGasModel -> "env-ask-gasmodel"
  REnvGasModelFixed -> "env-gasmodel-fixed"
  RPactVersion -> "pact-version"
  REnforcePactVersionMin -> "enforce-pact-version"
  REnforcePactVersionRange -> "enforce-pact-version-range"
  REnvEnableReplNatives -> "env-enable-repl-natives"
  REnvModuleAdmin -> "env-module-admin"
  REnvVerifiers -> "env-verifiers"
  REnvSetDebugFlag -> "env-set-debug-flag"

replBuiltinToText :: (t -> Text) -> ReplBuiltin t -> Text
replBuiltinToText f = \case
  RBuiltinWrap b -> f b
  RBuiltinRepl rb -> replBuiltinsToText rb

replCoreBuiltinToText :: ReplCoreBuiltin -> Text
replCoreBuiltinToText = replBuiltinToText coreBuiltinToText

-- | UX version of replCoreBuiltinToText, for use with LSP
-- this function takes a `ReplCoreBuiltin` and prints its name
-- while removing the overloaded internal names
replCoreBuiltinToUserText :: ReplCoreBuiltin -> Text
replCoreBuiltinToUserText = replBuiltinToText coreBuiltinToUserText

replCoreBuiltinNames :: [Text]
replCoreBuiltinNames =
  [ txtRepr
  | b <- [minBound .. maxBound]
  , b `notElem` (RBuiltinWrap <$> coreBuiltinOverloads)
  , let !txtRepr = replCoreBuiltinToText b]

-- | A map from raw text name of a builtin
--   to a `ReplBuiltin CoreBuiltin`
replBuiltinMap :: Map Text (ReplBuiltin CoreBuiltin)
replBuiltinMap =
  M.fromList $
    [ (txtRepr, b)
    | b <- [minBound .. maxBound]
    , b `notElem` (RBuiltinWrap <$> coreBuiltinOverloads)
    , let !txtRepr = replCoreBuiltinToText b]

-- | A map from raw text name of a builtin
--   to a `ReplBuiltin CoreBuiltin`, but
--   we do not resolve repl natives.
--   This is so the repl resolves `.pact` files and
--   `.repl` files differently
replCoreBuiltinOnlyMap :: Map Text (ReplBuiltin CoreBuiltin)
replCoreBuiltinOnlyMap =
  M.fromList $
    [ (txtRepr, RBuiltinWrap b)
    | b <- [minBound .. maxBound]
    , b `notElem` coreBuiltinOverloads
    , let !txtRepr = coreBuiltinToText b]

-- | A typeclass for general information about pact builtins, mostly
--   useful for runtime native information and for error messages. Note that
--   builtinArity only has 1 value per builtin, meaning overload resolution must
--   happen before using `builtinArity` to check for app saturation.
class Show b => IsBuiltin b where
  builtinArity :: b -> Int
  builtinName :: b -> NativeName


instance Pretty CoreBuiltin where
  pretty b = pretty (coreBuiltinToUserText b)

instance (Pretty b) => Pretty (ReplBuiltin b) where
  pretty = \case
    RBuiltinWrap b -> pretty b
    RBuiltinRepl t -> pretty (replBuiltinsToText t)

deriveConstrInfo ''CoreBuiltin
deriveConstrInfo ''ReplOnlyBuiltin
makePrisms ''BuiltinForm
