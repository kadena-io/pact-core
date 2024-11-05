{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE CPP #-}

module Pact.Core.IR.Desugar
 ( runDesugarTerm
 , runDesugarTopLevel
 , runDesugarReplTopLevel
 , DesugarOutput(..)
 , DesugarBuiltin(..)
 , runDesugarModule
 ) where

import Control.Applicative((<|>))
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict ( StateT(..), MonadState )
import Control.Monad.Trans.Maybe(MaybeT(..), runMaybeT, hoistMaybe)
import Control.Monad.Except
import Control.Lens hiding (List)
import Data.Text(Text)
import Data.Map.Strict(Map)
import Data.Maybe(mapMaybe, isJust)
import Data.List(findIndex)
#if !MIN_VERSION_base(4,20,0)
import Data.List(foldl')
#endif
import Data.List.NonEmpty(NonEmpty(..))
import Data.Set(Set)
import Data.Graph(stronglyConnComp, SCC(..))
import Data.Foldable(find, traverse_, foldrM, foldlM)
import qualified Data.Map.Strict as M
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S
import Data.List.Unsafe

import Pact.Core.Builtin
import Pact.Core.Names
import Pact.Core.Type
import Pact.Core.Literal
import Pact.Core.Hash
import Pact.Core.Persistence hiding (loaded)
import Pact.Core.Capabilities
import Pact.Core.Errors
import Pact.Core.IR.Term
import Pact.Core.Guards
import Pact.Core.Imports
import Pact.Core.Environment
import Pact.Core.Namespace
import Pact.Core.Gas
import Pact.Core.SizeOf

import qualified Pact.Core.Syntax.ParseTree as Lisp

{- Note on Desugaring + Renaming:

  [Desugaring]
  In core, we have partially closures as semantic values, auto-curried application
  for certain natives, and native names with arity multiple arities. That is,
  a native like `select` has a 2-argument and 3-argument list version.
  Thus, in pact-core, our solution to this is to pick a "Default" arity to resolve for natives,
  and let fully saturated application of certain natives determine the overload. To do this,
  We desugar saturated arity applications for certain natives and make them resolve to the intended
  overload.

  [Renaming]
  In core, we use a locally nameless representation for bound variable representation via basic debruijn indices.
-}

type DesugarType = Lisp.Type

data ModuleType = MTModule | MTInterface

data CurrModule
  = CurrModule
  { _cmName :: ModuleName
  , _cmImplements :: [ModuleName]
  , _cmType :: ModuleType
  }
makeLenses ''CurrModule

data RenamerEnv b i
  = RenamerEnv
  { _reBinds :: Map Text (NameKind, Maybe DefKind)
  , _reCurrModuleTmpBinds ::  Map Text (NameKind, DefKind)
  , _reVarDepth :: DeBruijn
  , _reCurrModule :: Maybe CurrModule
  , _reCurrDef :: Maybe DefKind
  }
makeLenses ''RenamerEnv

currModuleName :: MonadReader (RenamerEnv b i) m => m (Maybe ModuleName)
currModuleName = preview $ reCurrModule . folded . cmName

-- Our type to keep track of
newtype RenamerState
  = RenamerState { _rsDependencies :: Set ModuleName }

makeLenses ''RenamerState

newtype RenamerT b i m a =
  RenamerT (StateT RenamerState (ReaderT (RenamerEnv b i) m) a)
  deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadReader (RenamerEnv b i)
    , MonadState RenamerState
    , MonadIO)

instance MonadTrans (RenamerT b i) where
  lift = RenamerT . lift . lift

type RenamerM e b i =
  RenamerT b i (EvalM e b i)

-- | A simple typeclass for resolving arity overloads
class (IsBuiltin b, SizeOf b) => DesugarBuiltin b where
  liftCoreBuiltin :: CoreBuiltin -> b
  desugarAppArity :: i -> b -> [Term n dt b i] -> Term n dt b i

instance DesugarBuiltin CoreBuiltin where
  liftCoreBuiltin = id
  desugarAppArity = desugarCoreBuiltinArity id

-- | Our general function for resolving builtin overloads
--   for a specified arity.
desugarCoreBuiltinArity
  :: (CoreBuiltin -> builtin)
  -> info
  -> CoreBuiltin
  -> [Term name t builtin info]
  -> Term name t builtin info
desugarCoreBuiltinArity f i CoreSub [e1] =
    App (Builtin (f CoreNegate) i) ([e1]) i
desugarCoreBuiltinArity f i CoreEnumerate [e1, e2, e3] =
    App (Builtin (f CoreEnumerateStepN) i) ([e1, e2, e3]) i
desugarCoreBuiltinArity f i CoreSelect [e1, e2, e3] =
    App (Builtin (f CoreSelectWithFields) i) ([e1, e2, e3]) i
desugarCoreBuiltinArity f i CoreSort [e1, e2] =
  App (Builtin (f CoreSortObject) i) [e1, e2] i
-- Rounding functions
desugarCoreBuiltinArity f i CoreRound [e1, e2] =
  App (Builtin (f CoreRoundPrec) i) [e1, e2] i
desugarCoreBuiltinArity f i CoreCeiling [e1, e2] =
  App (Builtin (f CoreCeilingPrec) i) [e1, e2] i
desugarCoreBuiltinArity f i CoreFloor [e1, e2] =
  App (Builtin (f CoreFloorPrec) i) [e1, e2] i


desugarCoreBuiltinArity f i CoreStrToInt [e1, e2] =
  App (Builtin (f CoreStrToIntBase) i) [e1, e2] i
desugarCoreBuiltinArity f i CoreReadMsg [] =
  App (Builtin (f CoreReadMsgDefault) i) [] i
desugarCoreBuiltinArity f i CoreDefineKeySet [e1] =
  App (Builtin (f CoreDefineKeysetData) i) [e1] i
desugarCoreBuiltinArity f i CorePoseidonHashHackachain li =
  App (Builtin (f CorePoseidonHashHackachain) i )[(ListLit li i)] i
desugarCoreBuiltinArity f i CoreYield [e1, e2] =
  App (Builtin (f CoreYieldToChain) i) [e1, e2] i
desugarCoreBuiltinArity f i CoreRead [e1, e2, e3] =
  App (Builtin (f CoreReadWithFields) i) [e1, e2, e3] i
desugarCoreBuiltinArity f i b args =
    App (Builtin (f b) i) args i

instance DesugarBuiltin (ReplBuiltin CoreBuiltin) where
  liftCoreBuiltin = RBuiltinWrap
  desugarAppArity i (RBuiltinWrap b) ne =
    desugarCoreBuiltinArity RBuiltinWrap i b ne
  -- (expect <description> <expected> <expression-to-eval>)
  desugarAppArity i (RBuiltinRepl RExpect) ([e1, e2, e3]) | isn't _Nullary e3 =
    App (Builtin (RBuiltinRepl RExpect) i) ([e1, suspendTerm e2, suspendTerm e3]) i
  -- (expect-failure <arg1> <term>)
  desugarAppArity i (RBuiltinRepl RExpectFailure) [e1, e2] | isn't _Nullary e2 =
    App (Builtin (RBuiltinRepl RExpectFailure) i) [e1, suspendTerm e2] i
  -- (expect-failure <arg1> <expected-msg> <term>)
  desugarAppArity i (RBuiltinRepl RExpectFailure) [e1, e2, e3] | isn't _Nullary e2 =
    App (Builtin (RBuiltinRepl RExpectFailureMatch) i) [e1, e2, suspendTerm e3] i
  -- (pact-state <arg>)
  desugarAppArity i (RBuiltinRepl RPactState) [e1] =
    App (Builtin (RBuiltinRepl RResetPactState) i) [e1] i
  -- (continue-pact <arg1> <arg2>)
  desugarAppArity i (RBuiltinRepl RContinuePact) [e1, e2] =
    App (Builtin (RBuiltinRepl RContinuePactRollback) i) [e1, e2] i
  -- (continue-pact <arg1> <arg2> <arg3>)
  desugarAppArity i (RBuiltinRepl RContinuePact) [e1, e2, e3] =
      App (Builtin (RBuiltinRepl RContinuePactRollbackYield) i) [e1, e2, e3] i
  -- (continue-pact <arg1> <arg2> <arg3> <arg4>)
  desugarAppArity i (RBuiltinRepl RContinuePact) [e1, e2, e3, e4] =
      App (Builtin (RBuiltinRepl RContinuePactRollbackYieldObj) i) [e1, e2, e3, e4] i
  desugarAppArity i (RBuiltinRepl REnvGas) [e1] =
      App (Builtin (RBuiltinRepl REnvGasSet) i) [e1] i
  desugarAppArity i (RBuiltinRepl REnvGasModel) [] =
      App (Builtin (RBuiltinRepl REnvAskGasModel) i) [] i
  desugarAppArity i (RBuiltinRepl REnvGasModel) [e1, e2] =
      App (Builtin (RBuiltinRepl REnvGasModelFixed) i) [e1, e2] i
  desugarAppArity i (RBuiltinRepl RBeginTx) [e1] =
      App (Builtin (RBuiltinRepl RBeginNamedTx) i) [e1] i
  desugarAppArity i (RBuiltinRepl REnforcePactVersionMin) [e1, e2] =
      App (Builtin (RBuiltinRepl REnforcePactVersionRange) i) [e1, e2] i
  desugarAppArity i b ne =
    App (Builtin b i) ne i


data DesugarOutput a
  = DesugarOutput
  { _dsOut :: a
  , _dsDeps :: Set ModuleName
  } deriving (Show, Functor)

dsOut :: Lens (DesugarOutput a) (DesugarOutput a') a a'
dsOut f (DesugarOutput a d) =
  f a <&> \a' -> DesugarOutput a' d

throwDesugarError :: MonadError (PactError i) m => DesugarError -> i -> RenamerT b i m a
throwDesugarError de = RenamerT . lift . throwError . PEDesugarError de

viewEvalEnv' :: Lens' (EvalEnv b i) s -> RenamerM e b i s
viewEvalEnv' l = lift (viewEvalEnv l)

useEvalState :: Lens' (EvalState b i) s -> RenamerM e b i s
useEvalState l = RenamerT (lift (lift (use l)))

usesEvalState :: Lens' (EvalState b i) s -> (s -> s') -> RenamerM e b i s'
usesEvalState l f = RenamerT (lift (lift (uses l f)))

(%==) :: Traversal' (EvalState b i) s -> (s -> s) -> RenamerM e b i ()
l %== f =
  RenamerT (lift (lift (l %= f)))

infixr 4 %==

data SpecialForm
  = SFAnd
  | SFOr
  | SFIf
  | SFEnforce
  | SFWithCapability
  | SFSuspend
  | SFDo
  | SFEnforceOne
  | SFTry
  | SFMap
  | SFCond
  | SFRunReadOnly
  | SFCreateUserGuard
  deriving (Eq, Show, Enum, Bounded)

toSpecialForm :: Text -> Maybe SpecialForm
toSpecialForm = \case
  "and" -> Just SFAnd
  "or" -> Just SFOr
  "if" -> Just SFIf
  "enforce" -> Just SFEnforce
  "with-capability" -> Just SFWithCapability
  "suspend" -> Just SFSuspend
  "enforce-one" -> Just SFEnforceOne
  "try" -> Just SFTry
  "map" -> Just SFMap
  "run-read-only" -> Just SFRunReadOnly
  "do" -> Just SFDo
  "cond" -> Just SFCond
  "create-user-guard" -> Just SFCreateUserGuard
  _ -> Nothing

conditionalLam2Arg :: (Term ParsedName ty1 builtin1 info  -> Term ParsedName ty2 builtin2 info  -> BuiltinForm (Term name Lisp.Type builtin3 info)) -> info -> Term name Lisp.Type builtin3 info
conditionalLam2Arg c info = let
  arg1Name = "#condArg1"
  arg1 = Arg arg1Name (Just (Lisp.TyPrim PrimBool)) info
  arg2Name = "#condArg2"
  arg2 = Arg arg2Name (Just (Lisp.TyPrim PrimBool)) info
  in Lam (arg1 :| [arg2]) (BuiltinForm (c (Var (BN (BareName arg1Name)) info) (Var (BN (BareName arg2Name)) info)) info) info

nelToSequence :: info -> NonEmpty (Term name ty builtin info) -> Term name ty builtin info
nelToSequence info nel =
  foldr (\a b -> Sequence a b info) (NE.last nel) (NE.init nel)

-- | Desugar our special forms,
--   including one special case of eta expansion
desugarSpecial
  :: (DesugarBuiltin b)
  => (BareName, i)
  -> [Lisp.Expr i]
  -> i
  -> RenamerM e b i (Term ParsedName Lisp.Type b i)
desugarSpecial (bn@(BareName t), varInfo) dsArgs appInfo = case toSpecialForm t of
    Just sf -> goSpecial dsArgs sf
    Nothing -> desugarFn (Lisp.Var (BN bn) varInfo) dsArgs
  where
  injectedArg1 = ":ijHO1"
  injectedArg1Name = BN (BareName injectedArg1)
  desugarFn fn a = do
    fn' <- desugarLispTerm fn
    desugarArgs fn' a
  desugarArgs e a = do
    args' <- traverse desugarLispTerm a
    case e of
      Builtin b _ -> pure (desugarAppArity appInfo b args')
      _ -> pure (App e args' appInfo)
  -- Desugar 1 argument higher order functions to eta-expand for the sake of
  -- arity resolution
  desugar1ArgHOF f args = case args of
    Lisp.App operand appArgs appI:xs -> do
      let v = Lisp.Var injectedArg1Name appInfo
          newArg = Lisp.Lam [Lisp.MArg injectedArg1 Nothing appI] (Lisp.App operand (appArgs++ [v]) appI :| []) appI
      desugarFn (f varInfo) (newArg:xs)
    _ -> desugarFn (f varInfo) args
  goSpecial args = \case
    SFAnd -> case args of
      [e1, e2] ->
        BuiltinForm <$> (CAnd <$> desugarLispTerm e1 <*> desugarLispTerm e2) <*> pure appInfo
      _ -> desugarArgs (conditionalLam2Arg CAnd varInfo) args
    SFOr -> case args of
      [e1, e2] ->
        BuiltinForm <$> (COr <$> desugarLispTerm e1 <*> desugarLispTerm e2) <*> pure appInfo
      _ -> desugarArgs (conditionalLam2Arg COr varInfo) args
    SFIf -> case args of
      [e1, e2, e3] ->
        BuiltinForm <$> (CIf <$> desugarLispTerm e1 <*> desugarLispTerm e2 <*> desugarLispTerm e3) <*> pure appInfo
      _ -> throwDesugarError (InvalidSyntax "if must take three arguments") appInfo
    SFEnforce -> case args of
      [e1, e2] ->
        BuiltinForm <$> (CEnforce <$> desugarLispTerm e1 <*> desugarLispTerm e2) <*> pure appInfo
      _ -> desugarArgs (conditionalLam2Arg CEnforce varInfo) args
    SFDo -> case args of
      x:xs -> nelToSequence appInfo <$> traverse desugarLispTerm (x :| xs)
      _ -> throwDesugarError (InvalidSyntax "do form must have at least 1 expression") appInfo
    SFWithCapability -> case args of
      e1:e2:xs -> do
        e1' <- desugarLispTerm e1
        e2' <- nelToSequence appInfo <$> traverse desugarLispTerm (e2 :| xs)
        pure $ (`BuiltinForm` appInfo) $ CWithCapability e1' e2'
      _ -> throwDesugarError (InvalidSyntax "with-capability must take at least 2 expressions") appInfo
    SFSuspend -> case args of
      [e1] ->
        Nullary <$> desugarLispTerm e1 <*> pure appInfo
      _ -> throwDesugarError (InvalidSyntax "suspend must take only 1 argument") appInfo
    SFEnforceOne -> case args of
      [e1, e2] ->
        BuiltinForm <$> (CEnforceOne <$> desugarLispTerm e1 <*> desugarLispTerm e2) <*> pure appInfo
      _ -> throwDesugarError (InvalidSyntax "enforce-one must take two arguments") appInfo
    SFTry -> case args of
      [e1, e2] ->
        BuiltinForm <$> (CTry <$> desugarLispTerm e1 <*> desugarLispTerm e2) <*> pure appInfo
      _ -> throwDesugarError (InvalidSyntax "try must take two arguments") appInfo
    SFCreateUserGuard -> case args of
      [e] -> BuiltinForm <$> (CCreateUserGuard <$> desugarLispTerm e) <*> pure appInfo
      _ -> throwDesugarError (InvalidSyntax "create-user-guard must take one argument, which must be an application") appInfo
    SFMap -> desugar1ArgHOF MapV args
    SFRunReadOnly -> case args of
      [e] -> BuiltinForm <$> (CRunReadOnly <$> desugarLispTerm e) <*> pure appInfo
      _ -> throwDesugarError (InvalidSyntax "run-read-only must take one argument") appInfo
    SFCond -> case reverse args of
      defCase:xs -> do
        defCase' <- desugarLispTerm defCase
        body <- foldlM toNestedIf defCase' xs
        pure $ App (Builtin (liftCoreBuiltin CoreCond) appInfo) [Nullary body appInfo] appInfo
      _ -> throwDesugarError (InvalidSyntax "cond: expected list of conditions with a default case") appInfo
      where
      toNestedIf b (Lisp.App cond [body] i') = do
        cond' <- desugarLispTerm cond
        body' <- desugarLispTerm body
        pure $ BuiltinForm (CIf cond' body' b) i'
      toNestedIf _ _ =
        throwDesugarError (InvalidSyntax "cond: expected application of conditions") appInfo

desugarLispTerm
  :: (DesugarBuiltin b)
  => Lisp.Expr i
  -> RenamerM e b i (Term ParsedName DesugarType b i)
desugarLispTerm = \case
  Lisp.Var (BN n) i  -> do
    reservedNatives <- viewEvalEnv' eeNatives
    case M.lookup (_bnName n) reservedNatives of
      Just b -> pure (Builtin b i)
      Nothing
        | n == BareName "constantly" -> do
          let c1 = Arg cvar1 Nothing i
              c2 = Arg cvar2 Nothing i
          pure $ Lam (c1 :| [c2]) (Var (BN (BareName cvar1)) i) i
        | n == BareName "CHARSET_ASCII" -> pure (Constant (LInteger 0) i)
        | n == BareName "CHARSET_LATIN1" -> pure (Constant (LInteger 1) i)
        | otherwise ->
          pure (Var (BN n) i)
    where
    cvar1 = "#constantlyA1"
    cvar2 = "#constantlyA2"
  Lisp.Var n i -> pure (Var n i)
  Lisp.Let _ binders expr i -> do
    expr' <- nelToSequence i <$> traverse desugarLispTerm expr
    foldrM (binderToLet i) expr' binders
  Lisp.Lam args body i -> do
    body' <- nelToSequence i <$> traverse desugarLispTerm body
    case args of
      [] -> pure (Nullary body' i)
      x:xs -> do
        let nsts = x :| xs
            args' = (\(Lisp.MArg n t ai) -> Arg n t ai) <$> nsts
        pure (Lam args' body' i)
  Lisp.Binding fs hs i -> do
    hs' <- traverse desugarLispTerm hs
    body <- bindingBody hs'
    let bodyLam b = Lam (pure (Arg objFreshText Nothing i)) b i
    pure $ bodyLam $ foldr bindToLet body fs
      where
      bindingBody hs' = case reverse hs' of
        [] -> throwDesugarError EmptyBindingBody i
        x:xs -> pure $ foldl' (\acc e -> Sequence e acc i) x xs
      objFreshText = "#bindObject"
      objFreshVar = Var (BN (BareName objFreshText)) i
      bindToLet (Field field, marg) body =
        let arg = toArg marg
            fieldLit = Constant (LString field) i
            access = App (Builtin (liftCoreBuiltin CoreAt) i) [fieldLit, objFreshVar] i
        in Let arg access body i
  Lisp.App (Lisp.Var (BN n) varInfo) hs appInfo ->
    desugarSpecial (n, varInfo) hs appInfo
  Lisp.App operator operands i -> do
    e' <- desugarLispTerm operator
    hs' <- traverse desugarLispTerm operands
    case e' of
      Builtin b _ -> pure (desugarAppArity i b hs')
      _ -> pure (App e' hs' i)
  Lisp.List e1 i ->
    ListLit <$> traverse desugarLispTerm e1 <*> pure i
  Lisp.Constant l i ->
    pure (Constant l i)
  Lisp.Object fields i ->
    ObjectLit <$> (traverse._2) desugarLispTerm fields <*> pure i
  where
  binderToLet i (Lisp.Binder n mty expr) term = do
    expr' <- desugarLispTerm expr
    pure $ Let (Arg n mty i) expr' term i

pattern MapV :: i -> Lisp.Expr i
pattern MapV info = Lisp.Var (BN (BareName "map")) info

suspendTerm
  :: Term n dt builtin info
  -> Term n dt builtin info
suspendTerm e' =
  Nullary e' (view termInfo e')

toArg
  :: Lisp.MArg i
  -> Arg DesugarType i
toArg (Lisp.MArg n mty i) = Arg n mty i

desugarDefun
  :: (DesugarBuiltin b)
  => ModuleName             -- ^ proves this function is called within Pact module scope
  -> Lisp.Defun i
  -> RenamerM e b i (Defun ParsedName DesugarType b i)
desugarDefun _modWitness (Lisp.Defun spec [] body _anns i) = do
  body' <- nelToSequence i <$> traverse desugarLispTerm body
  let bodyLam = Nullary body' i
      spec' = toArg spec
  pure $ Defun spec' [] bodyLam i
desugarDefun _modWitness (Lisp.Defun spec (arg:args) body _anns i) = do
  let args' = toArg <$> (arg :| args)
  body' <- nelToSequence i <$> traverse desugarLispTerm body
  let bodyLam = Lam args' body' i
      spec' = toArg spec
  pure $ Defun spec' (NE.toList args') bodyLam i

desugarDefPact
  :: (DesugarBuiltin b)
  => ModuleName
  -> Lisp.DefPact i
  -> RenamerM e b i (DefPact ParsedName DesugarType b i)
desugarDefPact mn (Lisp.DefPact spec@(Lisp.MArg dpname _ _) margs (step :| steps) _anns i) = do
  let args' = toArg <$> margs
      spec' = toArg spec
  steps' <- forM (step :| steps) \case
    Lisp.Step s _ ->
      Step <$> desugarLispTerm s
    Lisp.StepWithRollback s rb _ ->
      StepWithRollback
      <$> desugarLispTerm s
      <*> desugarLispTerm rb

  -- In DefPacts, last step is not allowed to rollback.
  when (hasRollback $ NE.last steps') $
    throwDesugarError (LastStepWithRollback (QualifiedName dpname mn)) i

  pure $ DefPact spec' args' steps' i

desugarDefConst
  :: (DesugarBuiltin b)
  => ModuleName             -- ^ proves this function is called within Pact module scope
  -> Lisp.DefConst i
  -> RenamerM e b i (DefConst ParsedName DesugarType b i)
desugarDefConst _modWitness (Lisp.DefConst spec e _ i) = do
  e' <- desugarLispTerm e
  let spec' = toArg spec
  pure $ DefConst spec' (TermConst e') i

desugarDefMeta
  :: i
  -> [Arg t i]
  -> Lisp.DCapMeta
  -> RenamerM e b i (DefCapMeta ParsedName)
desugarDefMeta info args = \case
  Lisp.DefEvent -> pure DefEvent
  Lisp.DefManaged marg -> case marg of
    Just (arg, name) ->
        case findIndex ((==) arg . view argName) args of
          Just index' ->
            let dmanaged = DefManagedMeta (index', arg) name
            in pure (DefManaged dmanaged)
          Nothing ->
            throwDesugarError (InvalidManagedArg arg) info
    Nothing -> pure (DefManaged AutoManagedMeta)

desugarDefCap
  :: (DesugarBuiltin b)
  => ModuleName             -- ^ proves this function is called within Pact module scope
  -> Lisp.DefCap i
  -> RenamerM e b i (DefCap ParsedName DesugarType b i)
desugarDefCap _modWitness (Lisp.DefCap spec arglist term _anns meta i) = do
  let arglist' = toArg <$> arglist
      spec' = toArg spec
  term' <- nelToSequence i <$> traverse desugarLispTerm term
  meta' <- fmap FQParsed <$> maybe (pure Unmanaged) (desugarDefMeta i arglist') meta
  pure (DefCap spec' arglist' term' meta' i)

desugarDefSchema
  :: ModuleName             -- ^ proves this function is called within Pact module scope
  -> Lisp.DefSchema i
  -> RenamerM e b i (DefSchema DesugarType i)
desugarDefSchema _modWitness (Lisp.DefSchema dsn args _anns i) = do
  let args' = (\(Lisp.Arg n ty _) -> (Field n, ty)) <$> args
      scd = M.fromList args'
  pure $ DefSchema dsn scd i

desugarDefTable
  :: ModuleName             -- ^ proves this function is called within Pact module scope
  -> Lisp.DefTable i
  -> RenamerM e b i (DefTable ParsedName i)
desugarDefTable _modWitness (Lisp.DefTable dtn dts _ i) =
  pure (DefTable dtn (DesugaredTable dts) i)

desugarIfDef
  :: (DesugarBuiltin b)
  => ModuleName
  -> Lisp.IfDef i
  -> RenamerM e b i (IfDef ParsedName DesugarType b i)
desugarIfDef ifn = \case
  Lisp.IfDfun (Lisp.IfDefun spec margs _anns i) -> pure $ IfDfun $ IfDefun (toArg spec) (toArg <$> margs) i
  -- Todo: check managed impl
  Lisp.IfDCap (Lisp.IfDefCap spec margs _anns meta i) -> IfDCap <$> do
    let args = toArg <$> margs
        spec' = toArg spec
    meta' <- fmap (BareName . rawParsedName) <$> maybe (pure Unmanaged) (desugarDefMeta i args) meta
    pure $ IfDefCap spec' args meta' i
  Lisp.IfDConst dc -> IfDConst <$> desugarDefConst ifn dc
  Lisp.IfDPact (Lisp.IfDefPact spec margs _anns i) -> pure $ IfDPact $ IfDefPact (toArg spec) (toArg <$> margs) i
  Lisp.IfDSchema ds -> IfDSchema <$> desugarDefSchema ifn ds

desugarDef
  :: (DesugarBuiltin b)
  => ModuleName
  -> Lisp.Def i
  -> RenamerM e b i (Def ParsedName DesugarType b i)
desugarDef mname = \case
  Lisp.Dfun d -> Dfun <$> desugarDefun mname d
  Lisp.DConst d -> DConst <$> desugarDefConst mname d
  Lisp.DCap dc -> DCap <$> desugarDefCap mname dc
  Lisp.DSchema d -> DSchema <$> desugarDefSchema mname d
  Lisp.DTable d -> DTable <$> desugarDefTable mname d
  Lisp.DPact d -> DPact <$> desugarDefPact mname d

desugarModule
  :: (DesugarBuiltin b)
  => Lisp.Module i
  -> RenamerM e b i (Module ParsedName DesugarType b i)
desugarModule (Lisp.Module n mgov extdecls defs _anns i) = do
  let mname = ModuleName n Nothing
  (imports, blessed, implemented) <- splitExts extdecls
  defs' <- locally reCurrModule (const (Just $ CurrModule mname [] MTModule))
          $ traverse (desugarDef mname) (NE.toList defs)
  txHash <- viewEvalEnv' eeHash
  pure $ Module mname (toModuleGov mgov) defs' blessed imports implemented placeholderHash txHash (ModuleCode mempty) i
  where
  toModuleGov = \case
    Lisp.KeyGov t -> KeyGov (KeySetName t Nothing)
    Lisp.CapGov cg -> CapGov (FQParsed (BN (BareName cg)))
  splitExts = split ([], S.empty, [])
  split (accI, accB, accImp) (h:hs) = case h of
    Lisp.ExtBless b eInfo -> case parseModuleHash b of
      Nothing -> throwDesugarError (InvalidBlessedHash b) eInfo
      Just mh -> split (accI, S.insert mh accB, accImp) hs
    Lisp.ExtImport imp -> do
      imp' <- desugarImport imp
      split (imp':accI, accB, accImp) hs
    Lisp.ExtImplements mn _ -> split (accI, accB, mn:accImp) hs
  split (a, b, c) [] = pure (reverse a, b, reverse c)

desugarImport :: Lisp.Import i -> RenamerM e b i Import
desugarImport (Lisp.Import mn (Just blessed) imported info) = case parseModuleHash blessed of
  Just mbh' -> pure (Import mn (Just mbh') imported)
  Nothing -> throwDesugarError (InvalidBlessedHash blessed) info
desugarImport (Lisp.Import mn Nothing imported _) = pure (Import mn Nothing imported)

-- Todo: Interface hashing, either on source or
-- the contents
desugarInterface
  :: (DesugarBuiltin b)
  => Lisp.Interface i
  -> RenamerM e b i (Interface ParsedName DesugarType b i)
desugarInterface (Lisp.Interface iname_ ifdefns imps _anns info) = do
  let ifn = ModuleName iname_ Nothing
  imps' <- traverse desugarImport imps
  defs' <- traverse (desugarIfDef ifn) ifdefns
  let mhash = ModuleHash (Hash "placeholder")
  txh <- viewEvalEnv' eeHash
  pure $ Interface ifn defs' imps' mhash txh (ModuleCode mempty) info

desugarUse
  :: Lisp.Import i
  -> RenamerM e b i Import
desugarUse imp = do
  imp' <- desugarImport imp
  imp' <$ handleImport (view Lisp.importInfo imp) mempty imp'

-----------------------------------------------------------
-- Renaming
-----------------------------------------------------------

-- | Get the set of strongly connected free variables for a particular term.
termSCC
  :: ModuleName
  -- ^ The current module
  -> Set Text
  -- ^ The current set of definitions, we thread this through
  -- because lambdas may shadow.
  -- Note: this is a decent place to emit shadowing warnings.
  -> Term ParsedName DesugarType b1 i1
  -> Set Text
termSCC currM currDefns = \case
  -- todo: factor out this patmat on `ParsedName`,
  -- we use it multiple times
  Var n _ -> parsedNameSCC currM currDefns n
  -- Note: Lambda Args contain types, which may contain names that
  -- show up in the dependency graph
  Lam args e _ ->
    let currDefns' = foldl' (\s t -> S.delete (_argName t) s) currDefns args
        tySCC = foldMap (argSCC currM currDefns) args
    in tySCC <> termSCC currM currDefns' e
  -- Note: Let args contain types, which may contain names that
  -- show up in the dependency graph
  Let arg e1 e2 _ ->
    let currDefns' = S.delete (_argName arg) currDefns
        tySCC = argSCC currM currDefns arg
    in tySCC <> termSCC currM currDefns e1 <> termSCC currM currDefns' e2
  App fn apps _ ->
    S.union (termSCC currM currDefns fn) (foldMap (termSCC currM currDefns) apps)
  Sequence e1 e2 _ -> S.union (termSCC currM currDefns e1) (termSCC currM currDefns e2)
  BuiltinForm c _ ->
    foldMap (termSCC currM currDefns) c
  Builtin{} -> S.empty
  Constant{} -> S.empty
  ListLit v _ -> foldMap (termSCC currM currDefns) v
  Nullary e _ -> termSCC currM currDefns e
  ObjectLit m _ ->
    foldMap (termSCC currM currDefns . view _2) m
  InlineValue{} -> mempty

parsedNameSCC :: ModuleName -> Set Text -> ParsedName -> Set Text
parsedNameSCC currM currDefns n = case n of
  BN bn | S.member (_bnName bn) currDefns -> S.singleton (_bnName bn)
        | otherwise -> mempty
  QN (QualifiedName n' mn')
    | S.member n' currDefns && mn' == currM -> S.singleton n'
    | otherwise -> mempty
  DN _ -> mempty

tyNameSCC :: ModuleName -> Set Text -> ParsedTyName -> Set Text
tyNameSCC currM currDefs = \case
  TBN bn | S.member (_bnName bn) currDefs -> S.singleton (_bnName bn)
        | otherwise -> mempty
  TQN (QualifiedName n' mn')
    | S.member n' currDefs && mn' == currM -> S.singleton n'
    | otherwise -> mempty

typeSCC
  :: ModuleName
  -> Set Text
  -> DesugarType
  -> Set Text
typeSCC currM currDefs = \case
  Lisp.TyPrim _ -> mempty
  Lisp.TyList l -> typeSCC currM currDefs l
  Lisp.TyModRef _ -> mempty
  Lisp.TyObject pn -> tyNameSCC currM currDefs pn
  Lisp.TyKeyset -> mempty
  Lisp.TyPolyList -> mempty
  Lisp.TyPolyObject -> mempty
  Lisp.TyTable pn -> tyNameSCC currM currDefs pn
  Lisp.TyAny -> mempty

-- | Get the dependent components from an `Arg`
-- Args mean local bindings to something, therefore
-- the actual arg name _cannot_ refer to a dependency,
-- but the type annotation may contain a reference to a schema ann
argSCC :: ModuleName -> Set Text -> Arg DesugarType i -> Set Text
argSCC currM currDefs (Arg _ ty _) = case ty of
  Just t -> typeSCC currM currDefs t
  Nothing -> mempty

-- | Get the set of dependencies from a defun
-- Note: names will show up in:
--   - Defun terms
--   - Defun args
--   - Defun return type
defunSCC
  :: ModuleName
  -> Set Text
  -> Defun ParsedName DesugarType  b i
  -> Set Text
defunSCC mn cd df =
  let tscc = termSCC mn cd (_dfunTerm df)
      argScc = foldMap (argSCC mn cd) (_dfunArgs df)
  in tscc <> argScc <> maybe mempty (typeSCC mn cd) (_argType $ _dfunSpec df)

-- | Get the set of dependencies from a defconst
-- Note: names will show up in:
--   - Defconst terms
--   - Defconst return type
defConstSCC
  :: ModuleName
  -> Set Text
  -> DefConst ParsedName DesugarType  b i
  -> Set Text
defConstSCC mn cd dc =
  let tscc = foldMap (termSCC mn cd) (_dcTerm dc)
      tyscc = maybe mempty (typeSCC mn cd) (_argType $ _dcSpec dc)
  in tscc <> tyscc

-- | Get the set of dependencies from a deftable
-- Note: names will show up in:
--   - The schema reference of the table
defTableSCC
  :: ModuleName
  -> Set Text
  -> DefTable ParsedName info
  -> Set Text
defTableSCC mn cd dt =
  let (DesugaredTable t) = (_dtSchema dt)
  in parsedNameSCC mn cd t

-- | Get the set of dependencies from a defcap
-- Note: names will show up in:
--   - Defcap terms
--   - Defcap args
--   - Defcap return type
--   - Defcap managed meta
defCapSCC
  :: ModuleName
  -> Set Text
  -> DefCap ParsedName DesugarType b i1
  -> Set Text
defCapSCC mn cd dc =
  let argsScc = foldMap (argSCC mn cd) (_dcapArgs dc)
      rtypeScc = maybe mempty (typeSCC mn cd) (_argType $ _dcapSpec dc)
      termScc = termSCC mn cd (_dcapTerm dc)
  in argsScc <> rtypeScc <> termScc <> case _dcapMeta dc of
    DefManaged (DefManagedMeta _ (FQParsed pn)) -> parsedNameSCC mn cd pn
    _ -> mempty

-- | Get the set of dependencies from a defpact
-- Note: names will show up in:
--   - Defpact Steps
--   - Defpact args
--   - Defpact return type
defPactSCC
  :: ModuleName
  -> Set Text
  -> DefPact ParsedName DesugarType b i
  -> Set Text
defPactSCC mn cd dp =
  let argsScc = foldMap (argSCC mn cd) (_dpArgs dp)
      rtScc = maybe mempty (typeSCC mn cd) (_argType $ _dpSpec dp)
      stepsScc = foldMap (defPactStepSCC mn cd) (_dpSteps dp)
  in argsScc <> rtScc <> stepsScc

-- | Calculate the functions the particular defpact step depends on
defPactStepSCC
  :: ModuleName
  -> Set Text
  -> Step ParsedName DesugarType b i
  -> Set Text
defPactStepSCC mn cd = \case
  Step step -> termSCC mn cd step
  StepWithRollback step rollback ->
    S.unions $ [termSCC mn cd step, termSCC mn cd rollback]

-- | Get the set of dependencies from a defun signature defn
-- Note: names will show up in:
--   - Defun signature arguments
--   - Defun signature return type
ifDefunSCC
  :: ModuleName
  -> Set Text
  -> IfDefun DesugarType i
  -> Set Text
ifDefunSCC mn currDefs (IfDefun (Arg _name ty _) args _info) =
   foldMap (argSCC mn currDefs) args <> maybe mempty (typeSCC mn currDefs) ty

-- | Get the set of dependencies from a defcap signature
-- Note: names will show up in:
--   - Defcap signature args
--   - Defcap signature return type
--   - Defcap signature meta
ifDefCapSCC
  :: ModuleName
  -> Set Text
  -> IfDefCap ParsedName DesugarType i
  -> Set Text
ifDefCapSCC mn currDefs (IfDefCap (Arg _name rty _) args meta _info) =
   foldMap (argSCC mn currDefs) args <> maybe mempty (typeSCC mn currDefs) rty <> metaSCC meta
   where
  metaSCC (DefManaged (DefManagedMeta _ bn)) = parsedNameSCC mn currDefs (BN bn)
  metaSCC _ = mempty

-- | Get the set of dependencies from a defpact signature
-- Note: names will show up in:
--   - Defpact signature args
--   - Defpact signature return type
ifDefPactSCC
  :: ModuleName
  -> Set Text
  -> IfDefPact DesugarType i
  -> Set Text
ifDefPactSCC mn currDefs (IfDefPact (Arg _name rty _) args _info) =
   foldMap (argSCC mn currDefs) args <> maybe mempty (typeSCC mn currDefs) rty

-- | Calculate the dependency set for any type of def
defSCC
  :: ModuleName
  -> Set Text
  -> Def ParsedName DesugarType b i1
  -> Set Text
defSCC mn cd = \case
  Dfun d -> defunSCC mn cd d
  DConst d -> defConstSCC mn cd d
  DCap dc -> defCapSCC mn cd dc
  DSchema ds -> foldMap (typeSCC mn cd) ( _dsSchema ds)
  DPact dp -> defPactSCC mn cd dp
  DTable dt -> defTableSCC mn cd dt

-- | Calculate the dependency set for any type of interface def
ifDefSCC
  :: ModuleName
  -> Set Text
  -> IfDef ParsedName DesugarType b i1
  -> Set Text
ifDefSCC mn currDefs = \case
  IfDfun ifd -> ifDefunSCC mn currDefs ifd
  IfDCap d -> ifDefCapSCC mn currDefs d
  IfDConst d -> defConstSCC mn currDefs d
  IfDPact d -> ifDefPactSCC mn currDefs d
  IfDSchema ds -> foldMap (typeSCC mn currDefs) ( _dsSchema ds)

-- Todo: this handles imports, rename?
loadTopLevelMembers
  :: i
  -> Maybe (Set Text)
  -> ModuleData b i
  -> Map Text (NameKind, Maybe DefKind)
  -> RenamerM e b i (Map Text (NameKind, Maybe DefKind))
loadTopLevelMembers i mimports mdata binds = case mdata of
  ModuleData md _ -> do
    let modName = _mName md
        mhash = _mHash md
    let depMap = M.fromList $ toLocalDepMap modName mhash <$> _mDefs md
        loadedDeps = M.fromList $ toLoadedDepMap modName mhash <$> _mDefs md
    loadWithImports modName depMap loadedDeps
  InterfaceData iface _ -> do
    let ifname = _ifName iface
    let ifhash = _ifHash iface
        dcDeps = mapMaybe ifDefToDef (_ifDefns iface)
        depMap = M.fromList $ toLocalDepMap ifname ifhash <$> dcDeps
        loadedDeps = M.fromList $ toLoadedDepMap ifname ifhash <$> dcDeps
    loadWithImports ifname depMap loadedDeps
  where
  toLocalDepMap modName mhash defn = (defName defn, (NTopLevel modName mhash, Just (defKind modName defn)))
  toLoadedDepMap modName mhash defn = (defName defn, (FullyQualifiedName modName (defName defn) mhash, defKind modName defn))
  loadWithImports mn depMap loadedDeps = case mimports of
      Just st -> do
        let depsKeys = M.keysSet depMap
        unless (S.isSubsetOf st depsKeys) $ throwDesugarError (InvalidImports mn (S.toList (S.difference st depsKeys))) i
        (esLoaded . loToplevel) %== (`M.union` (M.restrictKeys loadedDeps st))
        pure (M.union (M.restrictKeys depMap st) binds)
      Nothing -> do
        (esLoaded . loToplevel) %== (`M.union` loadedDeps)
        pure (M.union depMap binds)

-- | Resolve a module name, return the implemented members as well if any
-- including all current
resolveModuleName
  :: i
  -> ModuleName
  -> RenamerM e b i (ModuleName, [ModuleName])
resolveModuleName i mn@(ModuleName name mNs) =
  view reCurrModule >>= \case
    -- TODO better error message if it's not MTMOdule
    -- If we are in a Module eval, we will need to check two conditions:
    -- is the current module name exactly equivalent? if so, return it.
    -- if not, why not? Is it because the module we're searching for is unmangled, or
    -- because it lives in the root namespace?
    -- We therefore check the root namespace first, and if nothing was found, then
    -- we mangle and check again.
    Just (CurrModule currMod imps MTModule)
      | currMod == mn -> pure (currMod, imps)
      | otherwise -> do
        lift (lookupModuleData i mn) >>= \case
          Just md -> getModName md
          Nothing -> case mNs of
            Just _ -> throwDesugarError (NoSuchModule mn) i
            -- Over here, it means we have not found it in the root namespace
            -- and the currModule's name may be mangled
            Nothing -> useEvalState (esLoaded . loNamespace) >>= \case
              Nothing -> throwDesugarError (NoSuchModule mn) i
              Just (Namespace ns _ _)
                | ModuleName name (Just ns) == currMod -> pure (currMod, imps)
                | otherwise ->
                  lift (getModuleData i (ModuleName name (Just ns))) >>= getModName
    _ -> resolveModuleData mn i >>= getModName
    where
    getModName = \case
      ModuleData module_ _ -> pure (_mName module_, _mImplements module_)
      InterfaceData _ _ ->
        throwDesugarError (InvalidModuleReference mn) i

-- | Resolve a module name, return the implemented members as well if any
-- including all current
resolveInterfaceName :: i -> ModuleName -> RenamerM e b i (ModuleName)
resolveInterfaceName i mn@(ModuleName name mNs) =
  view reCurrModule >>= \case
    -- TODO better error message if it's not MTInterface
    -- If we are in an interface eval, we will need to check two conditions:
    -- is the current module name exactly equivalent? if so, return it.
    -- if not, why not? Is it because the module we're searching for is unmangled, or
    -- because it lives in the root namespace?
    -- We therefore check the root namespace first, and if nothing was found, then
    -- we mangle and check again.
    Just (CurrModule currMod _ MTInterface)
      | currMod == mn -> pure mn
      | otherwise -> do
          lift (lookupModuleData i mn) >>= \case
            Just (InterfaceData _ _) -> pure mn
            Just _ -> throwDesugarError (InvalidModuleReference mn) i
            Nothing -> case mNs of
              Just _ -> throwDesugarError (NoSuchModule mn) i
              -- Over here, it means we have not found it in the root namespace
              -- and the currModule's name may be mangled
              Nothing -> useEvalState (esLoaded . loNamespace) >>= \case
                Nothing -> throwDesugarError (NoSuchModule mn) i
                Just (Namespace ns _ _)
                  | ModuleName name (Just ns) == currMod -> pure currMod
                  | otherwise ->
                    lift (getModuleData i (ModuleName name (Just ns))) >>= getModName
    _ -> resolveModuleData mn i >>= getModName
    where
    getModName = \case
      ModuleData _ _ ->
        throwDesugarError (InvalidModuleReference mn) i
      InterfaceData _ _ -> pure mn


-- | Resolve module data, fail if not found
resolveModuleData
  :: ModuleName
  -> i
  -> RenamerM e b i (ModuleData b i)
resolveModuleData mn@(ModuleName name mNs) i = do
  lift (lookupModuleData i mn) >>= \case
    Just md -> pure md
    Nothing -> case mNs of
      Just _ -> throwDesugarError (NoSuchModule mn) i
      Nothing -> useEvalState (esLoaded . loNamespace) >>= \case
        Nothing -> throwDesugarError (NoSuchModule mn) i
        Just (Namespace ns _ _) ->
          lift (getModuleData i (ModuleName name (Just ns)))

renameType
  :: (DesugarBuiltin b)
  => i
  -> DesugarType
  -> RenamerM e b i Type
renameType i = \case
  Lisp.TyPrim p -> pure (TyPrim p)
  Lisp.TyList ty ->
    TyList <$> renameType i ty
  Lisp.TyModRef tmr ->
    TyModRef (S.fromList tmr) <$ traverse (resolveInterfaceName i) tmr
  Lisp.TyKeyset -> pure TyGuard
  Lisp.TyObject pn ->
    TyObject <$> resolveSchema pn
  Lisp.TyTable pn ->
    TyTable <$> resolveSchema pn
  Lisp.TyPolyList -> pure TyAnyList
  Lisp.TyPolyObject -> pure TyAnyObject
  Lisp.TyAny -> pure TyAny
  where
  resolveSchema = \case
    TBN bn -> do
      (_, dkty) <- resolveBare bn i
      case dkty of
        Just (DKDefSchema sc) -> pure sc
        Just _ -> throwDesugarError (InvalidDefInSchemaPosition (_bnName bn)) i
        Nothing ->
          throwDesugarError (UnboundTypeVariable (_bnName bn)) i
    TQN qn -> do
      (_, dt) <- resolveQualified qn i
      case dt of
        Just (DKDefSchema sc) -> pure sc
        _ -> throwDesugarError (InvalidDefInSchemaPosition (_qnName qn)) i

argType' :: Traversal (Arg ty i) (Arg ty' i) ty ty'
argType' f (Arg n ty i) = Arg n <$> traverse f ty <*> pure i

-- Rename a term (that is part of a module)
-- emitting the list of dependent calls
renameTerm
  :: (DesugarBuiltin b)
  => Term ParsedName DesugarType b i
  -> RenamerM e b i (Term Name Type b i)
renameTerm (Var n i) = resolveName i n >>= \case
  (n', Just dk)
    | dk `elem` legalVarDefs  -> pure (Var n' i)
    | otherwise ->
      throwDesugarError (InvalidDefInTermVariable (rawParsedName n)) i
    where
    legalVarDefs = [DKDefun, DKDefConst, DKDefTable, DKDefCap, DKDefPact]
  (n', _) -> pure (Var n' i)
-- Todo: what happens when an argument is shadowed?
renameTerm (Lam nsts body i) = do
  depth <- view reVarDepth
  let len = fromIntegral (NE.length nsts)
      newDepth = depth + len
      ixs = NE.fromList [depth .. newDepth - 1]
  let m = M.fromList $ NE.toList $ NE.zip (_argName <$> nsts) ((,Nothing). NBound <$> ixs)
  term' <- local (inEnv m newDepth) (renameTerm body)
  nsts' <- (traversed . argType . _Just) (renameType i) nsts
  pure (Lam nsts' term' i)
  where
  inEnv m newDepth =
    over reBinds (M.union m) .
    set reVarDepth newDepth
renameTerm (Let arg e1 e2 i) = do
  depth <- view reVarDepth
  arg' <- argType' (renameType i) arg
  let inEnv = over reVarDepth succ .
              over reBinds (M.insert (_argName arg) (NBound depth, Nothing))
  e1' <- renameTerm e1
  e2' <- local inEnv (renameTerm e2)
  pure (Let arg' e1' e2' i)
renameTerm (App fn apps i) = do
  fn' <- renameTerm fn
  apps' <- traverse renameTerm apps
  pure (App fn' apps' i)
renameTerm (Nullary term i) =
  Nullary <$> renameTerm term <*> pure i
renameTerm (Sequence e1 e2 i) = do
  Sequence <$> renameTerm e1 <*> renameTerm e2 <*> pure i
renameTerm (BuiltinForm c i) = do
  when (has _CWithCapability c) $ enforceNotWithinDefcap i "with-capability"
  BuiltinForm <$> traverse renameTerm c <*> pure i
renameTerm (Builtin b i) =
  pure (Builtin b i)
renameTerm (Constant l i) =
  pure (Constant l i)
renameTerm (ListLit v i) = do
  ListLit <$> traverse renameTerm v <*> pure i
renameTerm (ObjectLit o i) =
  ObjectLit <$> (traverse._2) renameTerm o <*> pure i
renameTerm (InlineValue pb i) = pure (InlineValue pb i)

enforceNotWithinDefcap
  :: i
  -> Text
  -> RenamerM e b i ()
enforceNotWithinDefcap i form = do
  withinDefCap <- (== Just DKDefCap) <$> view reCurrDef
  when withinDefCap $ throwDesugarError (NotAllowedWithinDefcap form) i

renameDefun
  :: (DesugarBuiltin b)
  => Defun ParsedName DesugarType b i
  -> RenamerM e b i (Defun Name Type b i)
renameDefun (Defun (Arg n ret ni) args term i) = do
  -- Todo: put type variables in scope here, if we want to support polymorphism
  args' <- (traverse.argType') (renameType i) args
  ret' <- traverse (renameType i) ret
  term' <- local (set reCurrDef (Just DKDefun)) $ renameTerm term
  pure (Defun (Arg n ret' ni) args' term' i)

renamePactStep
  :: (DesugarBuiltin b)
  => Step ParsedName DesugarType b i
  -> RenamerM e b i (Step Name Type b i)
renamePactStep = \case
  Step step ->
    Step <$> renameTerm step
  StepWithRollback step rollback ->
    StepWithRollback <$> renameTerm step <*> renameTerm rollback

renameDefPact
  :: (DesugarBuiltin b)
  => DefPact ParsedName DesugarType b i
  -> RenamerM e b i (DefPact Name Type b i)
renameDefPact (DefPact (Arg n mret ni) argtys steps i) = do
  args' <- (traverse.argType') (renameType i) argtys
  mret' <- traverse (renameType i) mret
  steps' <- local (set reCurrDef (Just DKDefPact) . bindArgs) $
    traverse renamePactStep steps
  pure (DefPact (Arg n mret' ni) args' steps' i)
  where
  -- Todo: duplication, factor out
  bindArgs rEnv
      | null argtys = rEnv
      | otherwise = let
        depth = view reVarDepth rEnv
        len = fromIntegral (length argtys)
        newDepth = depth + len
        ixs = [depth .. newDepth - 1]
        m = M.fromList $ zip (_argName <$> argtys) ((, Nothing) . NBound <$> ixs)
        in over reBinds (M.union m) $ set reVarDepth newDepth rEnv


renameDefSchema
  :: (DesugarBuiltin b)
  => DefSchema DesugarType i
  -> RenamerM e b i (DefSchema Type i)
renameDefSchema (DefSchema dsn dsc i) = do
  dsc' <- traverse (renameType i) dsc
  pure (DefSchema dsn dsc' i)

renameDefTable
  :: DefTable ParsedName i
  -> RenamerM e b i (DefTable Name i)
renameDefTable (DefTable dtn sc i) = do
  case sc of
    DesugaredTable dn -> resolveName i dn >>= \case
      (_, Just (DKDefSchema rsc)) -> pure (DefTable dtn (ResolvedTable rsc) i)
      (n, Just _) ->
        throwDesugarError (InvalidDefInSchemaPosition (_nName n)) i
      (_n, Nothing) -> throwDesugarError (UnboundTypeVariable (rawParsedName dn)) i

renameReplDefun
  :: (DesugarBuiltin b)
  => Defun ParsedName DesugarType b i
  -> RenamerM e b i (Defun Name Type b i)
renameReplDefun (Defun (Arg n ret ni) args term i) = do
  let fqn = FullyQualifiedName replModuleName n replModuleHash
  args' <- (traverse.argType') (renameType i) args
  ret' <- traverse (renameType i) ret
  esLoaded . loToplevel %== M.insert n (fqn, DKDefun)
  term' <- local (set reCurrDef (Just DKDefun)) $ renameTerm term
  pure (Defun (Arg n ret' ni) args' term' i)

renameReplDefConst
  :: (DesugarBuiltin b)
  => DefConst ParsedName DesugarType b i
  -> RenamerM e b i (DefConst Name Type b i)
renameReplDefConst (DefConst (Arg n mty ni) term i) = do
  let fqn = FullyQualifiedName replModuleName n replModuleHash
  esLoaded . loToplevel %== M.insert n (fqn, DKDefConst)
  mty' <- traverse (renameType i) mty
  term' <- local (set reCurrDef (Just DKDefConst)) $ traverse renameTerm term
  pure (DefConst (Arg n mty' ni) term' i)

renameDefConst
  :: (DesugarBuiltin b)
  => DefConst ParsedName DesugarType b i
  -> RenamerM e b i (DefConst Name Type b i)
renameDefConst (DefConst (Arg n mty ni) term i) = do
  mty' <- traverse (renameType i) mty
  term' <- local (set reCurrDef (Just DKDefConst)) $ traverse renameTerm term
  pure (DefConst (Arg n mty' ni) term' i)

renameDefCap
  :: (DesugarBuiltin b)
  => DefCap ParsedName DesugarType b i
  -> RenamerM e b i (DefCap Name Type b i)
renameDefCap (DefCap (Arg name rtype ni) argtys term meta info) = do
  meta' <- resolveMeta info meta
  argtys' <- (traverse.argType') (renameType info) argtys
  rtype' <- traverse (renameType info) rtype
  term' <- local (set reCurrDef (Just DKDefCap) .  bindArgs) $ renameTerm term
  pure (DefCap (Arg name rtype' ni) argtys' term' meta' info)
  where
  -- Todo: debruijn code should be isolated
  bindArgs rEnv
    | null argtys = rEnv
    | otherwise = let
      depth = view reVarDepth rEnv
      len = fromIntegral (length argtys)
      newDepth = depth + len
      ixs = [depth .. newDepth - 1]
      m = M.fromList $ zip (_argName <$> argtys) ((, Nothing) . NBound <$> ixs)
      in over reBinds (M.union m) $ set reVarDepth newDepth rEnv

resolveMeta
  :: i
  -> DefCapMeta (FQNameRef ParsedName)
  -> RenamerM e b i (DefCapMeta (FQNameRef Name))
resolveMeta _ DefEvent = pure DefEvent
resolveMeta _ Unmanaged = pure Unmanaged
resolveMeta _ (DefManaged AutoManagedMeta) = pure (DefManaged AutoManagedMeta)
resolveMeta info (DefManaged (DefManagedMeta i (FQParsed pn))) = do
  (name', _) <- resolveName info pn
  fqn <- expectedFree info name'
  pure (DefManaged (DefManagedMeta i (FQName fqn)))

expectedFree
  :: i
  -> Name
  -> RenamerM e b i FullyQualifiedName
expectedFree i (Name n nk) = case nk of
  NTopLevel mname mh ->
    pure (FullyQualifiedName mname n mh)
  _ -> throwDesugarError (ExpectedFreeVariable n) i


renameDef
  :: (DesugarBuiltin b)
  => Def ParsedName DesugarType b i
  -> RenamerM e b i (Def Name Type b i)
renameDef = \case
  Dfun d -> Dfun <$> renameDefun d
  DConst d -> DConst <$> renameDefConst d
  DCap d -> DCap <$> renameDefCap d
  DSchema d -> DSchema <$> renameDefSchema d
  DTable d -> DTable <$> renameDefTable d
  DPact d -> DPact <$> renameDefPact d

renameIfDef
  :: (DesugarBuiltin b)
  => ModuleName
  -> Set Text
  -> IfDef ParsedName DesugarType b i
  -> RenamerM e b i (IfDef Name Type b i)
renameIfDef mn ifDefuns = \case
  IfDfun (IfDefun spec args i) -> do
    args' <- (traverse.argType') (renameType i) args
    rtype' <- traverse (renameType i) (_argType spec)
    let spec' = spec & argType .~ rtype'
    pure (IfDfun $ IfDefun spec' args' i)

  IfDConst d -> IfDConst <$> renameDefConst d
  IfDSchema d -> IfDSchema <$> renameDefSchema d
  IfDCap (IfDefCap spec args meta i) -> do
    args' <- (traverse.argType') (renameType i) args
    rtype' <- traverse (renameType i) (_argType spec)
    traverse_ (ensureInLocals i) meta

    let spec' = spec & argType .~ rtype'
    pure (IfDCap $ IfDefCap spec' args' meta i)
    where
    ensureInLocals info (BareName n) = do
      unless (S.member n ifDefuns) $ throwDesugarError (NoSuchModuleMember mn n) info

  IfDPact (IfDefPact spec args i) -> do
    args' <- (traverse.argType') (renameType i) args
    rtype' <- traverse (renameType i) (_argType spec)
    let spec' = spec & argType .~ rtype'
    pure (IfDPact $ IfDefPact spec' args' i)

resolveName
  :: i
  -> ParsedName
  -> RenamerM e b i (Name, Maybe DefKind)
resolveName i = \case
  BN b -> resolveBare b i
  QN q -> resolveQualified q i
  DN dn -> (, Nothing) <$> resolveDynamic i dn

resolveDynamic
  :: i
  -> DynamicName
  -> RenamerM e b i Name
resolveDynamic i dynName@(DynamicName dn dArg) = views reBinds (M.lookup dn) >>= \case
  Just tnk -> case tnk of
    (NBound d, _) -> do
      depth <- view reVarDepth
      let dbjIx = depth - d - 1
          dr = NDynRef (DynamicRef dArg dbjIx)
      pure (Name dn dr)
    _ ->
      throwDesugarError (InvalidDynamicInvoke dynName) i
  Nothing ->
    throwDesugarError (UnboundTermVariable dn) i

-- | Resolve bare name atoms
-- which either correspond to:
--  - A top-level name in scope (e.g a definition)
--  - A module reference (we query bare module names first)
--  - A module reference with
resolveBare
  :: BareName
  -> i
  -> RenamerM e b i (Name, Maybe DefKind)
resolveBare (BareName bn) i = views reBinds (M.lookup bn) >>= \case
  Just tnk -> case tnk of
    (NBound d, _) -> do
      depth <- view reVarDepth
      pure (Name bn (NBound (depth - d - 1)), Nothing)
    (nk@(NTopLevel mn _), dk) -> do
      currMod <- currModuleName
      when (isJust currMod && currMod /= Just mn) $ rsDependencies %= S.insert mn
      pure (Name bn nk, dk)
    (nk, dk) -> do
      pure (Name bn nk, dk)
  Nothing -> usesEvalState (esLoaded . loToplevel) (M.lookup bn) >>= \case
    Just (fqn, dk) -> do
      rsDependencies %= S.insert (_fqModule fqn)
      pure (Name bn (NTopLevel (_fqModule fqn) (_fqHash fqn)), Just dk)
    Nothing -> do
      let unmangled = ModuleName bn Nothing
      (mn, imps) <- resolveModuleName i unmangled
      pure (Name bn (NModRef mn imps), Nothing)

-- | Resolve a qualified name `<qual>.<name>` with the following
-- procedure:
--  - <qual> has the form `<namespace>.<module>`:
--    - if we find no identifier loaded or in the database, then it must not exist.
--      it definitely refers to a fully qualified member
--  - <qual> is of the form `<module>` (so, no namespace):
--    - The identifier can mean one of three things: a root-namespaced identifier (e.g `coin.transfer`),
--      a namespaced identifier when a namespace is in scope (so m.f when `(namespace 'free)` has been called),
--      or a module reference where `<name>` is actually the module name, and `<module>` was actually the namespace.
--
resolveQualified
  :: QualifiedName
  -> i
  -> RenamerM e b i (Name, Maybe DefKind)
resolveQualified (QualifiedName qn qmn@(ModuleName modName mns)) i = do
  runMaybeT (baseLookup qn qmn <|> modRefLookup <|> namespacedLookup) >>= \case
    Just p -> pure p
    Nothing -> throwDesugarError (NoSuchModuleMember qmn qn) i
  where
  lookupLocalQual defnName moduleName = do
    currMod <- MaybeT currModuleName
    guard (currMod == moduleName)
    (nk, dk) <- MaybeT $ view (reCurrModuleTmpBinds . at defnName)
    pure (Name defnName nk, Just dk)
  baseLookup defnName moduleName = lookupLocalQual defnName moduleName <|> do
    MaybeT (lift (lookupModuleData i moduleName)) >>= \case
      ModuleData module' _ -> do
        d <- hoistMaybe (findDefInModule defnName module' )
        lift $ rsDependencies %= S.insert moduleName
        pure (Name qn (NTopLevel moduleName (_mHash module')), Just (defKind (_mName module') d))
      InterfaceData iface _ -> do
        let ifn = _ifName iface
        d <- hoistMaybe (findDefInInterface defnName iface)
        lift $ rsDependencies %= S.insert moduleName
        pure (Name qn (NTopLevel moduleName (_ifHash iface)), Just (defKind ifn d))
  modRefLookup = case mns of
    -- Fail eagerly: the previous lookup was fully qualified
    Just _ -> MaybeT (throwDesugarError (NoSuchModuleMember qmn qn) i)
    Nothing -> do
      let mn' = ModuleName qn (Just (NamespaceName modName))
      m <- MaybeT $ lift $ lookupModule i mn'
      let nk = NModRef mn' (_mImplements m)
      pure (Name qn nk, Nothing)
  namespacedLookup = do
    Namespace ns _ _ <- MaybeT (useEvalState (esLoaded . loNamespace))
    let mn' = ModuleName modName (Just ns)
    baseLookup qn mn'

-- | Handle all name resolution for modules
renameModule
  :: (DesugarBuiltin b)
  => Module ParsedName DesugarType b i
  -> RenamerM e b i (Module Name Type b i)
renameModule (Module unmangled mgov defs blessed imports implements mhash txh mcode i) = do
  rsDependencies .= mempty
  mname <- lift $ mangleNamespace unmangled
  mgov' <- resolveGov mname mgov
  let defNames = S.fromList $ fmap defName defs
  let scc = mkScc mname defNames <$> defs
  defs' <- forM (stronglyConnComp scc) \case
    AcyclicSCC d -> pure d
    CyclicSCC d ->
      -- todo: just in case, match on `d` because it makes no sense for there to be an empty cycle
      -- but all uses of `head` are still scary
      throwDesugarError (RecursionDetected mname (defName <$> d)) (defInfo (unsafeHead d))
  binds <- view reBinds
  bindsWithImports <- foldlM (handleImport i) binds imports
  (defs'', _, _, _) <- over _1 reverse <$> foldlM (go mname) ([], S.empty, bindsWithImports, M.empty) defs'
  traverse_ (checkImplements i defs'' mname) implements
  let resolvedModule = Module mname mgov' defs'' blessed imports implements mhash txh mcode i
  modSize <- lift $ sizeOf i SizeOfV0 (() <$ resolvedModule)
  lift $ chargeGasArgs i (GModuleOp (MOpDesugarModule modSize))
  pure resolvedModule
  where
  -- Our deps are acyclic, so we resolve all names
  go mname (!defns, !s, !m, !mlocals) defn = do
    when (S.member (defName defn) s) $ throwDesugarError (DuplicateDefinition (QualifiedName (defName defn) mname)) i
    let dn = defName defn
    defn' <- local (set reCurrModule (Just $ CurrModule mname implements MTModule) . set reCurrModuleTmpBinds mlocals)
             $ local (set reBinds m) $ renameDef defn
    let dk = defKind mname defn'
    let depPair = (NTopLevel mname mhash, dk)
    let m' = M.insert dn (over _2 Just depPair) m
        mlocals' = M.insert dn depPair mlocals
    pure (defn':defns, S.insert (defName defn) s, m', mlocals')

  resolveGov mname = \case
    KeyGov rawKsn -> case parseAnyKeysetName (_keysetName rawKsn) of
      Left {} -> lift $ throwExecutionError i (InvalidKeysetNameFormat (_keysetName rawKsn))
      Right ksn ->
        pure (KeyGov ksn)
    CapGov (FQParsed govName) ->
      case find (\d -> BN (BareName (defName d)) == govName) defs of
        Just (DCap d) -> do
          let fqn = FullyQualifiedName mname (_argName $ _dcapSpec d) mhash
          let dcName = (_argName . _dcapSpec) d
          unless (null (_dcapArgs d)) $ throwDesugarError (InvalidGovernanceRef (QualifiedName dcName mname)) i
          pure (CapGov (FQName fqn))
        Just d -> throwDesugarError (InvalidGovernanceRef (QualifiedName (defName d) mname)) i
        Nothing -> throwDesugarError (InvalidGovernanceRef (QualifiedName (rawParsedName govName) mname)) i
  mkScc mname dns def = (def, defName def, S.toList (defSCC mname dns def))


handleImport
  :: i
  -> Map Text (NameKind, Maybe DefKind)
  -> Import
  -> RenamerM e b i (Map Text (NameKind, Maybe DefKind))
handleImport info binds (Import mn mh imported) = do
  mdata <- resolveModuleData mn info
  let imported' = S.fromList <$> imported
      mdhash = view mdModuleHash mdata
  case mh of
    Just modHash -> when (modHash /= mdhash) $ throwDesugarError (InvalidImportModuleHash mn mdhash) info
    Nothing -> pure ()
  loadTopLevelMembers info imported' mdata binds

checkImplements
  :: i
  -> [Def Name Type b i]
  -> ModuleName
  -> ModuleName
  -> RenamerM e b i ()
checkImplements i defs moduleName ifaceName = do
  resolveModuleData ifaceName i >>= \case
    InterfaceData iface _deps ->
      traverse_ checkImplementedMember (_ifDefns iface)
    _ -> throwDesugarError (NoSuchInterface ifaceName) i
  where
  checkImplementedMember = \case
    IfDConst{} -> pure ()
    IfDSchema{} -> pure ()
    IfDfun (IfDefun (Arg ifdName ifRty _) ifArgs _) ->
      case find (\df -> ifdName == defName df) defs of
        Just (Dfun (Defun (Arg funName funRty _) funArgs _ _)) ->
          when (weakArgsNeq funArgs ifArgs || funRty /= ifRty) $
            throwDesugarError (ImplementationError moduleName ifaceName funName) i
        Just d ->
          throwDesugarError (ImplementationError moduleName ifaceName  (defName d)) i
        Nothing ->
          throwDesugarError (NotImplemented moduleName ifaceName ifdName) i
    IfDCap (IfDefCap (Arg ifdcName ifdcRty _) ifdcArgs' ifdcMeta' _) ->
      case find (\df -> ifdcName == defName df) defs of
        Just (DCap (DefCap (Arg dcapName dcapRty _) dcapArgs' _ dcapMeta' _)) -> do
          unless (checkMetaMatches dcapMeta' ifdcMeta') $
             throwDesugarError (ImplementationError moduleName ifaceName $ ": defcap mismatch for " <> dcapName) i
          when (weakArgsNeq dcapArgs' ifdcArgs' || dcapRty /= ifdcRty) $
            throwDesugarError (ImplementationError moduleName ifaceName dcapName) i
        Just d -> throwDesugarError (ImplementationError moduleName ifaceName  (defName d)) i
        Nothing ->
          throwDesugarError (NotImplemented moduleName ifaceName ifdcName) i
    IfDPact (IfDefPact (Arg ifdpName ifdpRty _) ifdpArgs' _) ->
      case find (\df -> ifdpName == defName df) defs of
        Just (DPact (DefPact (Arg _ dpRty _) dpArgs' _ _)) ->
          when (weakArgsNeq dpArgs' ifdpArgs' || dpRty /= ifdpRty) $
          throwDesugarError (ImplementationError moduleName ifaceName ifdpName) i
        Just _ ->  throwDesugarError (ImplementationError moduleName ifaceName ifdpName) i
        Nothing -> throwDesugarError (NotImplemented moduleName ifaceName ifdpName) i

  -- Weak comparison of 'Arg' by ignoring '_argInfo' via mapping it to unit.
  weakArgsNeq a b = fmap void a /= fmap void b

  checkMetaMatches :: DefCapMeta (FQNameRef Name) -> DefCapMeta BareName -> Bool
  checkMetaMatches Unmanaged Unmanaged = True
  checkMetaMatches DefEvent DefEvent = True
  checkMetaMatches (DefManaged l) (DefManaged r) = checkManagedMatches l r
  checkMetaMatches _ _ = False

  checkManagedMatches :: DefManagedMeta (FQNameRef Name) -> DefManagedMeta BareName -> Bool
  checkManagedMatches _ AutoManagedMeta = True
  checkManagedMatches (DefManagedMeta lhs (FQName lName)) (DefManagedMeta rhs (BareName rName)) =
    lhs == rhs &&
    _fqName lName == rName &&
    _fqModule lName == moduleName
  checkManagedMatches _ _ = False


-- | Todo: support imports
--   Todo: support
renameInterface
  :: (DesugarBuiltin b)
  => Interface ParsedName DesugarType b i
  -> RenamerM e b i (Interface Name Type b i)
renameInterface (Interface unmangled defs imports ih txHash mcode info) = do
  ifn <- lift $ mangleNamespace unmangled
  let defNames = ifDefName <$> defs
  let scc = mkScc ifn (S.fromList defNames) <$> defs
  defs' <- forM (stronglyConnComp scc) \case
    AcyclicSCC d -> pure d
    CyclicSCC d ->
      -- todo: just in case, match on `d` because it makes no sense for there to be an empty cycle
      -- but all uses of `head` are still scary
      throwDesugarError (RecursionDetected ifn (ifDefName <$> d)) (ifDefInfo (unsafeHead d))
  binds <- view reBinds
  bindsWithImports <- foldlM (handleImport info) binds imports
  (defs'', _, _, _) <- over _1 reverse <$> foldlM (go ifn) ([], S.empty, bindsWithImports, S.empty) defs'
  let resolvedIface = Interface ifn defs'' imports ih txHash mcode info
  ifaceSize <- lift $ sizeOf info SizeOfV0 (() <$ resolvedIface)
  lift $ chargeGasArgs info (GModuleOp (MOpDesugarModule ifaceSize))
  pure resolvedIface
  where
  mkScc ifn dns def = (def, ifDefName def, S.toList (ifDefSCC ifn dns def))
  go ifn (ds, s, m, dfnSet) d = do
    let dn = ifDefName d
    when (S.member dn s) $
      throwDesugarError (DuplicateDefinition (QualifiedName dn ifn)) info
    d' <- local (set reBinds m) $
          local (set reCurrModule (Just $ CurrModule ifn [] MTInterface)) $ renameIfDef ifn dfnSet d
    let m' = case ifDefToDef d' of
              Just defn ->
                let dk = defKind ifn defn
                in M.insert dn (NTopLevel ifn ih, Just dk) m
              Nothing -> m
        dfnSet' = case d of
          IfDfun{} -> S.insert dn dfnSet
          _ -> dfnSet
    pure (d':ds, S.insert dn s, m', dfnSet')

runRenamerT
  :: RenamerM e b i a
  -> EvalM e b i (a, RenamerState)
runRenamerT (RenamerT act) = do
  tlBinds <- uses loToplevel (fmap (\(fqn, dk) -> (fqnToNameKind fqn, Just dk)))
  let renamerEnv = RenamerEnv tlBinds mempty 0 Nothing Nothing
      renamerState = RenamerState mempty
  runReaderT (runStateT act renamerState) renamerEnv
  where
  fqnToNameKind fqn = NTopLevel (_fqModule fqn) (_fqHash fqn)

runDesugar
  :: RenamerM e b i a
  -> EvalM e b i (DesugarOutput a)
runDesugar act = do
  (renamed, RenamerState deps) <- runRenamerT act
  pure (DesugarOutput renamed deps)

runDesugarTerm
  :: (DesugarBuiltin b)
  => Lisp.Expr i
  -> EvalM e b i (DesugarOutput (Term Name Type b i))
runDesugarTerm = runDesugar . (desugarLispTerm >=> renameTerm)

runDesugarModule
  :: (DesugarBuiltin b)
  => Lisp.Module i
  -> EvalM e b i (DesugarOutput (Module Name Type b i))
runDesugarModule  = runDesugar . (desugarModule >=> renameModule)

runDesugarInterface
  :: (DesugarBuiltin b)
  => Lisp.Interface i
  -> EvalM e b i (DesugarOutput (Interface Name Type b i))
runDesugarInterface  = runDesugar . (desugarInterface >=> renameInterface)

runDesugarReplDefun
  :: (DesugarBuiltin b)
  => Lisp.Defun i
  -> EvalM e b i (DesugarOutput (Defun Name Type b i))
runDesugarReplDefun =
  runDesugar
  . local (set reCurrModule (Just $ CurrModule replModuleName [] MTModule))
  . (desugarDefun replModuleName >=> renameReplDefun)

runDesugarReplDefConst
  :: (DesugarBuiltin b)
  =>  Lisp.DefConst i
  -> EvalM e b i (DesugarOutput (DefConst Name Type b i))
runDesugarReplDefConst  =
  runDesugar
  . local (set reCurrModule (Just $ CurrModule replModuleName [] MTModule))
  . (desugarDefConst replModuleName >=> renameReplDefConst)

runDesugarTopLevel
  :: (DesugarBuiltin b)
  => Lisp.TopLevel i
  -> EvalM e b i (DesugarOutput (TopLevel Name Type b i))
runDesugarTopLevel = \case
  Lisp.TLModule m -> over dsOut TLModule <$> runDesugarModule m
  Lisp.TLTerm e -> over dsOut TLTerm <$> runDesugarTerm e
  Lisp.TLInterface i -> over dsOut TLInterface <$> runDesugarInterface i
  Lisp.TLUse imp -> runDesugar $ (`TLUse` (view Lisp.importInfo imp)) <$> desugarUse imp



runDesugarReplTopLevel
  :: (DesugarBuiltin b)
  => Lisp.ReplTopLevel i
  -> EvalM e b i (DesugarOutput (ReplTopLevel Name Type b i))
runDesugarReplTopLevel = \case
  -- We do not run desugar here for the repl.
  -- We pattern match before we ever hit this case, therefore this should not be reachable
  -- This is fine to stay in `error`. The repl special functions and forms do not show up on chain
  -- and we want this to be a clear haskell error. The current repl implementation
  -- makes sure to not ever hit this.
  Lisp.RTLTopLevel _ ->
    error "Fatal: do not use desugarReplTopLevel on toplevel forms from the parser. Use runDesugarTopLevel directly"
  Lisp.RTLDefun de ->
    over dsOut RTLDefun <$> runDesugarReplDefun de
  Lisp.RTLDefConst dc ->
    over dsOut RTLDefConst <$> runDesugarReplDefConst dc


-- Some types don't get all their lenses used, hence GHC warns about unused bindings.
-- This is one way to controllably silence these warnings.
data Unused where Unused :: a -> Unused

_unused :: [Unused]
_unused = [Unused $ set cmImplements, Unused $ set cmType]
