{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE CPP #-}

module Pact.Core.IR.Eval.Direct.Evaluator
 ( eval
 , evalResumePact
 , interpretGuard
 , resumePact
 , applyPact
 , applyLamUnsafe
 , evalCap
 , installCap
 , enforcePactValue
 , enforcePactValue'
 , enforceBool
 , enforceBool'
 , requireCap
 , composeCap
 , acquireModuleAdminCapability
 , mkDefunClosure
 , enforceGuard
 , applyLam
 , evalWithinCap
 , enforceNotWithinDefcap
 , isKeysetInSigs
 , isKeysetNameInSigs
 ) where

import Control.Lens hiding (op, from, to, parts)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Text(Text)
import Data.Foldable
import Data.List.NonEmpty(NonEmpty(..))
import qualified Data.RAList as RAList
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Vector as V
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.List.NonEmpty as NE

#ifdef WITH_TRACING
import System.Clock
#endif


import Pact.Core.IR.Eval.Runtime.Utils
import Pact.Core.IR.Eval.Runtime.Types
import Pact.Core.IR.Term
import Pact.Core.Names
import Pact.Core.Environment
import Pact.Core.Type
import Pact.Core.Errors
import Pact.Core.PactValue
import Pact.Core.Hash
import Pact.Core.Persistence
import Pact.Core.Guards
import Pact.Core.Capabilities
import Pact.Core.DefPacts.Types
import Pact.Core.Literal
import Pact.Core.ModRefs
import Pact.Core.Builtin
import Pact.Core.IR.Eval.Direct.Types
import Pact.Core.Gas
import Pact.Core.StableEncoding
import Pact.Core.SizeOf

mkDefunClosure
  :: EvalDefun b i
  -> FullyQualifiedName
  -> DirectEnv e b i
  -> EvalM e b i (Closure e b i)
mkDefunClosure d fqn e = case _dfunTerm d of
  Lam args body i ->
    pure (Closure fqn (ArgClosure args) (NE.length args) body (_dfunRType d) e i)
  Nullary body i ->
    pure (Closure fqn NullaryClosure 0 body (_dfunRType d) e i)
  _ ->
    failInvariant (_dfunInfo d) (InvariantMalformedDefun fqn)


mkDefPactClosure
  :: i
  -> FullyQualifiedName
  -> DefPact Name Type b i
  -> DirectEnv e b i
  -> EvalValue e b i
mkDefPactClosure info fqn dpact env = case _dpArgs dpact of
  [] ->
    let dpc = DefPactClosure fqn NullaryClosure 0 env info
    in VDefPactClosure dpc
  (x:xs) ->
    let dpc = DefPactClosure fqn (ArgClosure (x :| xs)) (length (x:xs)) env info
    in VDefPactClosure dpc

envFromPurity :: Purity -> DirectEnv e b i -> DirectEnv e b i
envFromPurity PImpure = id
envFromPurity PReadOnly = readOnlyEnv
envFromPurity PSysOnly = sysOnlyEnv

eval
  :: (IsBuiltin b)
  => Purity
  -> BuiltinEnv e b i
  -> EvalTerm b i
  -> EvalM e b i PactValue
eval purity benv term = do
  ee <- viewEvalEnv id
  let directEnv = envFromPurity purity (DirectEnv mempty (_eePactDb ee) benv (_eeDefPactStep ee) False)
  evaluate directEnv term >>= \case
    VPactValue pv -> pure pv
    _ -> throwExecutionError (view termInfo term) (EvalError "Evaluation did not reduce to a value")


evalWithinCap
  :: forall e b i
  .  (IsBuiltin b)
  => i
  -> Purity
  -> BuiltinEnv e b i
  -> CapToken QualifiedName PactValue
  -> EvalTerm b i
  -> EvalM e b i PactValue
evalWithinCap info purity benv (CapToken qualName vs) term = do
  ee <- viewEvalEnv id
  (_, mh) <- getDefCapQN info qualName
  let ct = CapToken (qualNameToFqn qualName mh) vs
  let cekEnv = envFromPurity purity (DirectEnv mempty (_eePactDb ee) benv (_eeDefPactStep ee) False)
  evalCap (view termInfo term) cekEnv ct PopCapInvoke NormalCapEval term >>= \case
    VPactValue pv -> pure pv
    _ ->
      throwExecutionError (view termInfo term) (EvalError "Evaluation did not reduce to a value")

interpretGuard
  :: forall e b i
  .  (IsBuiltin b)
  => i
  -> BuiltinEnv e b i
  -> Guard QualifiedName PactValue
  -> EvalM e b i PactValue
interpretGuard info bEnv g = do
  ee <- viewEvalEnv id
  let eEnv = DirectEnv mempty (_eePactDb ee) bEnv (_eeDefPactStep ee) False
  PBool <$> enforceGuard info eEnv g

evalResumePact
  :: (IsBuiltin b)
  => i
  -> BuiltinEnv e b i
  -> Maybe DefPactExec
  -> EvalM e b i PactValue
evalResumePact info bEnv mdpe = do
  ee <- viewEvalEnv id
  let pdb = _eePactDb ee
  let env = DirectEnv mempty pdb bEnv (_eeDefPactStep ee) False
  resumePact info env mdpe >>= \case
    VPactValue pv -> pure pv
    _ ->
      throwExecutionError info (EvalError "Evaluation did not reduce to a value")

evaluate
  :: IsBuiltin b
  => DirectEnv e b i
  -> EvalTerm b i
  -> EvalM e b i (EvalValue e b i)
evaluate env = \case
  Var n info -> do
    case _nKind n of
      NBound i -> do
        case RAList.lookup (_ceLocal env) i of
          Just v -> return v
          Nothing -> failInvariant info (InvariantInvalidBoundVariable (_nName n))
      -- Top level names are not closures, so we wipe the env
      NTopLevel mname mh -> do
        let fqn = FullyQualifiedName mname (_nName n) mh
        lookupFqName fqn >>= \case
          Just (Dfun d) -> do
            dfunClo <- VDefClosure <$> mkDefunClosure d fqn env
            return dfunClo
          -- Todo: this should be GADT'd out
          -- and defconsts should already be evaluated
          Just (DConst d) -> case _dcTerm d of
            -- Note: `TermConst` cannot and should not be `evalCEK`'d. This is an error
            -- this can cause semantic divergences, due to things like provided data.
            -- moreover defcosts are always evaluated in `SysOnly` mode.
            TermConst _term ->
              failInvariant info (InvariantDefConstNotEvaluated fqn)
            EvaledConst v ->
              return (VPactValue v)
          Just (DPact d) -> do
            let dpactClo = mkDefPactClosure info fqn d env
            return dpactClo
          Just (DTable d) ->
            let (ResolvedTable sc) = _dtSchema d
                tn = TableName (_dtName d) mname
                tbl = VTable (TableValue tn mh sc)
            in return tbl
          Just (DCap d) -> do
            let args = _argType <$> _dcapArgs d
                clo = CapTokenClosure fqn args (length args) info
            return (VClosure (CT clo))
          Just d ->
            failInvariant info (InvariantInvalidDefKind (defKind mname d) "in var position")
          Nothing ->
            failInvariant info (InvariantUnboundFreeVariable fqn)
      NModRef m ifs ->
        return (VModRef (ModRef m (S.fromList ifs)))
      NDynRef (DynamicRef dArg i) -> case RAList.lookup (view ceLocal env) i of
        Just (VModRef mr) -> do
          modRefHash <- _mHash <$> getModule info (_mrModule mr)
          let nk = NTopLevel (_mrModule mr) modRefHash
          evaluate env (Var (Name dArg nk) info)
        Just _ -> throwExecutionError info (DynNameIsNotModRef dArg)
        Nothing -> failInvariant info (InvariantInvalidBoundVariable (_nName n))
  Constant l _info -> do
    return (VLiteral l)
  App ufn uargs info -> do
    fn <- enforceUserAppClosure info =<< evaluate env ufn
    args <- traverse (evaluate env) uargs
    applyLam fn args
  Sequence e1 e2 _ -> do
    _ <- evaluate env e1
    evaluate env e2
  Builtin b info -> do
    let builtins = _ceBuiltins env
    return (VNative (builtins info b env))
  Nullary body info -> do
    let clo = VLamClosure (LamClosure NullaryClosure 0 body Nothing env info)
    pure clo
  Let _ e1 e2 _ -> do
    e1val <- evaluate env e1
    let newEnv = RAList.cons e1val (_ceLocal env)
    let env' = env {_ceLocal = newEnv }
    evaluate env' e2
  Lam args body info -> do
      let clo = VLamClosure (LamClosure (ArgClosure args) (NE.length args) body Nothing env info)
      return clo
  BuiltinForm c info -> case c of
    CAnd te te' -> do
      b <- evaluate env te >>= enforceBool info
      -- chargeGasArgs info (GAConstant constantWorkNodeGas)
      if b then evaluate env te' >>= enforceBoolValue info
      else pure (VBool False)
    COr te te' -> do
      b <- evaluate env te >>= enforceBool info
      -- chargeGasArgs info (GAConstant constantWorkNodeGas)
      if b then pure (VBool True)
      else evaluate env te' >>= enforceBoolValue info
    CIf bExpr ifExpr elseExpr -> do
      b <- enforceBool info =<< evaluate env bExpr
      -- chargeGasArgs info (GAConstant constantWorkNodeGas)
      if b then evaluate env ifExpr
      else evaluate env elseExpr
    CEnforce cond str -> do
      let env' = sysOnlyEnv env
      b <- enforceBool info =<< evaluate env' cond
      -- chargeGasArgs info (GAConstant constantWorkNodeGas)
      if b then return (VBool True)
      else do
        msg <- enforceString info =<< evaluate env str
        throwUserRecoverableError info (UserEnforceError msg)
    CRunReadOnly e -> do
      let env' = readOnlyEnv env
      evaluate env' e
    CWithCapability cap body -> do
      enforceNotWithinDefcap info env "with-capability"
      rawCap <- enforceCapToken info =<< evaluate env cap
      let capModule = view (ctName . fqModule) rawCap
      guardForModuleCall info capModule $ pure ()
      evalCap info env rawCap PopCapInvoke NormalCapEval body
    CCreateUserGuard term -> case term of
      App (Var (Name n (NTopLevel mn mh)) _) uargs _ -> do
        let fqn = FullyQualifiedName mn n mh
        args <- traverse (evaluate env >=> enforcePactValue info) uargs
        createUserGuard info fqn args
      _ -> throwExecutionError info $ NativeExecutionError (NativeName "create-user-guard") $
          "create-user-guard: expected function application of a top-level function"
    CTry catchExpr tryExpr -> do
      chargeTryNodeWork info
      let env' = readOnlyEnv env
      catchRecoverable (evaluate env' tryExpr) (\_ _ -> evaluate env catchExpr)
    CEnforceOne str (ListLit conds _) ->
      go conds
      where
      go (x:xs) = do
        cond <- catchRecoverable (enforceBool info =<< evaluate env x) (\_ _ -> pure False)
        chargeUnconsWork info
        if cond then return (VBool True)
        else go xs
      go [] = do
        msg <- enforceString info =<< evaluate env str
        throwUserRecoverableError info (UserEnforceError msg)
    CEnforceOne _ _ ->
      throwExecutionError info $ NativeExecutionError (NativeName "enforce-one") $
            "enforce-one: expected a list of conditions"
  ListLit ts info -> do
    chargeGasArgs info (GConcat (ListConcat (GasListLength (length ts))))
    args <- traverse (evaluate env >=> enforcePactValue info) ts
    return (VList (V.fromList args))
  ObjectLit o info -> do
    chargeGasArgs info (GConcat (ObjConcat (length o)))
    args <- traverse go o
    return (VObject (M.fromList args))
    where
    go (f, e) = do
      v <- evaluate env e
      (f,) <$> enforcePactValue info v
  InlineValue v _ ->
    return (VPactValue v)

-- | Our main workhorse for "Evaluate a capability, then do something else"
-- `evalCap` handles
--   - with-capability
--   - test-capability
--   - compose-capability
-- In all cases, evalCap checks if the capability is in scope
-- if it is, it is a no-op and does simply evaluates `contbody` with the current continuation
--
-- If it is not inscope, it pushes the `contbody` into a new continuation that will
-- evaluate it after cap aquisition, with the cap in scope.
-- Then:
--   - If the cap is unmanaged, simply evaluate the cap body with the new continuation
--   - If the cap is @event, set the event to emit after cap body evaluation, then eval the cap body
--   - If the cap is managed, install the cap (If possible) then evaluate the body, and if
--     the cap is user managed, ensure that the manager function run after the cap body
evalCap
  :: (IsBuiltin b)
  => i
  -> DirectEnv e b i
  -> FQCapToken
  -> CapPopState
  -> EvalCapType
  -> EvalTerm b i
  -> EvalM e b i (EvalValue e b i)
evalCap info env origToken@(CapToken fqn args) popType ecType contbody = do
  capInStack <- isCapInStack' origToken
  if not capInStack then go else evaluate env contbody
  where
  go = do
    d <- getDefCap info fqn
    when (length args /= length (_dcapArgs d)) $ failInvariant info $
      (InvariantArgLengthMismatch fqn (length args) (length (_dcapArgs d)))
    let newLocals = RAList.fromList $ fmap VPactValue (reverse args)
        capBody = _dcapTerm d
    -- Todo: clean up the staircase of doom.
    case _dcapMeta d of
      -- Managed capability, so we should look for it in the set of csmanaged
      DefManaged mdm -> do
        case mdm of
          -- | Not automanaged, so it must have a defmeta
          -- We are handling user-managed caps
          DefManagedMeta (cix,_) _ -> do
            let filteredCap = CapToken qualCapName (filterIndex cix args)
            -- Find the capability post-filtering
            mgdCaps <- use (esCaps . csManaged)
            case find ((==) filteredCap . _mcCap) mgdCaps of
              Nothing -> do
                msgCaps <- S.unions <$> viewEvalEnv eeMsgSigs
                case find (findMsgSigCap cix filteredCap) msgCaps of
                  Just c -> do
                    let c' = set ctName fqn c
                        emittedEvent = fqctToPactEvent origToken <$ guard (ecType == NormalCapEval)
                    installCap info env c' False >>= evalUserManagedCap newLocals capBody emittedEvent
                  Nothing ->
                    throwExecutionError info (CapNotInstalled qualCapToken)
              Just managedCap -> do
                let emittedEvent = fqctToPactEvent origToken <$ guard (ecType == NormalCapEval)
                evalUserManagedCap newLocals capBody emittedEvent managedCap
          -- handle autonomous caps
          AutoManagedMeta -> do
            -- Find the capability post-filtering
            let emittedEvent = fqctToPactEvent origToken <$ guard (ecType == NormalCapEval)
            mgdCaps <- use (esCaps . csManaged)
            case find ((==) qualCapToken . _mcCap) mgdCaps of
              Nothing -> do
                msgCaps <- S.unions <$> viewEvalEnv eeMsgSigs
                case find (== qualCapToken) msgCaps of
                  Just c -> do
                    let c' = set ctName fqn c
                    installCap info env c' False >>= evalAutomanagedCap emittedEvent newLocals capBody
                  Nothing ->
                    throwExecutionError info (CapNotInstalled qualCapToken)
              Just managedCap ->
                evalAutomanagedCap emittedEvent newLocals capBody managedCap
      DefEvent -> do
        oldCapsBeingEvaluated <- use (esCaps.csCapsBeingEvaluated)
        let event = Just (fqctToPactEvent origToken)
        let inCapEnv = set ceInCap True $ set ceLocal newLocals env
        (esCaps . csSlots) %= (CapSlot qualCapToken []:)
        (esCaps . csCapsBeingEvaluated) %= S.insert qualCapToken
        _ <- evalWithStackFrame info capStackFrame Nothing (evaluate inCapEnv capBody)
        (esCaps . csCapsBeingEvaluated) .= oldCapsBeingEvaluated
        evalWithCapBody info popType Nothing event env contbody
      -- Not automanaged _nor_ user managed.
      Unmanaged -> do
        let inCapEnv = set ceInCap True $ set ceLocal newLocals env
        oldCapsBeingEvaluated <- use (esCaps.csCapsBeingEvaluated)
        (esCaps . csSlots) %= (CapSlot qualCapToken []:)
        (esCaps . csCapsBeingEvaluated) %= S.insert qualCapToken
        -- we ignore the capbody here
        _ <- evalWithStackFrame info capStackFrame Nothing $ evaluate inCapEnv capBody
        (esCaps . csCapsBeingEvaluated) .= oldCapsBeingEvaluated
        case ecType of
          NormalCapEval -> do
            evalWithCapBody info popType Nothing Nothing env contbody
          TestCapEval ->
            -- todo: check with prod the return type of testCap
            return VUnit
  qualCapName = fqnToQualName fqn
  qualCapToken = CapToken qualCapName args
  capStackFrame = StackFrame fqn args SFDefcap info
  -- This function is handles both evaluating the manager function for the installed parameter
  -- and continuing evaluation for the actual capability body.
  evalUserManagedCap env' capBody emitted managedCap = case _mcManaged managedCap of
    ManagedParam mpfqn oldV managedIx -> do
      dfun <- getDefun info mpfqn
      dfunClo <- mkDefunClosure dfun mpfqn env
      newV <- maybe (failInvariant info (InvariantInvalidManagedCapIndex managedIx fqn)) pure (args ^? ix managedIx)
      -- Set the mgr fun to evaluate after we apply the capability body
      -- NOTE: test-capability doesn't actually run the manager function, it just runs the cap pop then
      -- pops it. It would be great to do without this, but a lot of our regressions rely on this.
      let inCapEnv = set ceInCap True $ set ceLocal env' $ env
      let inCapBodyToken = _mcOriginalCap managedCap
      oldCapsBeingEvaluated <- use (esCaps.csCapsBeingEvaluated)
      -- BIG SEMANTICS NOTE HERE
      -- the cap slot here that we push should NOT be the qualified original token.
      -- Instead, it's the original token from the installed from the static cap. Otherwise, enforce checks
      -- within the cap body will fail (That is, keyset enforcement). Instead, once we are evaluating the body,
      -- we pop the current cap stack, then replace the head with the original intended token.
      -- this is done in `CapBodyC` and this is the only way to do this.
      (esCaps . csSlots) %= (CapSlot inCapBodyToken []:)
      (esCaps . csCapsBeingEvaluated) %= S.insert inCapBodyToken
      _ <- evalWithStackFrame info capStackFrame Nothing (evaluate inCapEnv capBody)
      (esCaps . csCapsBeingEvaluated) .= oldCapsBeingEvaluated
      when (ecType == NormalCapEval) $ do
        updatedV <- enforcePactValue info =<< applyLam (C dfunClo) [VPactValue oldV, VPactValue newV]
        let mcap' = unsafeUpdateManagedParam updatedV managedCap
        (esCaps . csManaged) %= S.insert mcap'
      evalWithCapBody info popType (Just qualCapToken) emitted env contbody
    _ -> failInvariant info (InvariantInvalidManagedCapKind "expected user managed, received automanaged")
  evalAutomanagedCap emittedEvent env' capBody managedCap = case _mcManaged managedCap of
    AutoManaged b -> do
      if b then throwUserRecoverableError info OneShotCapAlreadyUsed
      else do
        let newManaged = AutoManaged True
        oldCapsBeingEvaluated <- use (esCaps.csCapsBeingEvaluated)
        esCaps . csManaged %= S.union (S.singleton (set mcManaged newManaged managedCap))
        esCaps . csSlots %= (CapSlot qualCapToken []:)
        (esCaps . csCapsBeingEvaluated) %= S.insert qualCapToken
        let inCapEnv = set ceLocal env' $ set ceInCap True $ env
        _ <- evalWithStackFrame info capStackFrame Nothing (evaluate inCapEnv capBody)
        (esCaps . csCapsBeingEvaluated) .= oldCapsBeingEvaluated

        evalWithCapBody info popType Nothing emittedEvent env contbody
    _ -> failInvariant info (InvariantInvalidManagedCapKind "expected automanaged, received user managed")

evalWithCapBody
  :: (IsBuiltin b)
  => i
  -> CapPopState
  -> Maybe (CapToken QualifiedName PactValue)
  -> Maybe (PactEvent PactValue)
  -> DirectEnv e b i
  -> EvalTerm b i
  -> EvalM e b i (EvalValue e b i)
evalWithCapBody info cappop mcap mevent env capbody = do
  traverse_ (emitEventUnsafe)  mevent
  case mcap of
    Nothing -> do
      v <- evaluate env capbody
      popCap info cappop v
    Just cap -> use (esCaps . csSlots) >>= \case
      (CapSlot _ tl:rest) -> do
        (esCaps . csSlots) .= (CapSlot cap tl:rest)
        v <- evaluate env capbody
        popCap info cappop v
      [] -> failInvariant info InvariantEmptyCapStackFailure

popCap
  :: i
  -> CapPopState
  -> EvalValue e b i
  -> EvalM e b i (EvalValue e b i)
popCap info cappop v = case cappop of
  PopCapInvoke -> v <$ (esCaps . csSlots %= safeTail)
  PopCapComposed -> do
    use (esCaps . csSlots) >>= \case
      cap:cs -> do
        let csList = _csCap cap : _csComposed cap
            caps' = over (_head . csComposed) (++ csList) cs
        (esCaps . csSlots) .= caps'
        return v
      [] -> failInvariant info InvariantEmptyCapStackFailure




-- Todo: should we typecheck / arity check here?
createUserGuard
  :: i
  -> FullyQualifiedName
  -> [PactValue]
  -> EvalM e b i (EvalValue e b i)
createUserGuard info fqn args =
  lookupFqName fqn >>= \case
    Just (Dfun _) ->
      return (VGuard (GUserGuard (UserGuard (fqnToQualName fqn) args)))
    Just d ->
      -- Note: this error is not recoverable in prod
      -- <interactive>:0:26:Error: User guard closure must be defun, found: defcap
      -- at <interactive>:0:7: (create-user-guard ((defcap m.g:<a> ())))
      -- at <interactive>:0:0: (try 1 (native `create-user-guard`  Defines a custom guar...)
      throwExecutionError info $ UserGuardMustBeADefun (fqnToQualName fqn) (defKind (_fqModule fqn) d)
    Nothing ->
      failInvariant info (InvariantUnboundFreeVariable fqn)

enforceNotWithinDefcap
  :: i
  -> DirectEnv e b i
  -> T.Text
  -> EvalM e b i ()
enforceNotWithinDefcap info env form =
  when (_ceInCap env) $ throwExecutionError info (FormIllegalWithinDefcap form)

enforceBool :: i -> EvalValue e b i -> EvalM e b i Bool
enforceBool info = \case
  VBool b -> pure b
  VPactValue v' -> throwExecutionError info (ExpectedBoolValue v')
  _ -> throwExecutionError info ExpectedPactValue

enforceBool' :: i -> EvalValue e b i -> EvalM e b i (EvalValue e b i)
enforceBool' info = \case
  v@VBool{} -> pure v
  VPactValue v' -> throwExecutionError info (ExpectedBoolValue v')
  _ -> throwExecutionError info ExpectedPactValue

enforceString ::i -> EvalValue e b i -> EvalM e b i Text
enforceString info = \case
  VString b -> pure b
  VPactValue v' -> throwExecutionError info $ ExpectedStringValue v'
  _ -> throwExecutionError info $ ExpectedPactValue


enforceCapToken :: i -> EvalValue e b i -> EvalM e b i (CapToken FullyQualifiedName PactValue)
enforceCapToken info = \case
  VCapToken b -> pure b
  VPactValue v' -> throwExecutionError info $ ExpectedCapToken v'
  _ -> throwExecutionError info $ ExpectedPactValue

enforceBoolValue :: i -> EvalValue e b i -> EvalM e b i (EvalValue e b i)
enforceBoolValue info = \case
  VBool b -> pure (VBool b)
  VPactValue v' -> throwExecutionError info (ExpectedBoolValue v')
  _ -> throwExecutionError info ExpectedPactValue

enforceUserAppClosure :: i -> EvalValue e b i -> EvalM e b i (CanApply e b i)
enforceUserAppClosure info = \case
  VClosure c -> case c of
    C clo -> pure (C clo)
    LC clo -> pure (LC clo)
    N clo -> pure (N clo)
    DPC clo -> pure (DPC clo)
    CT clo -> pure (CT clo)
    _ -> throwExecutionError info CannotApplyPartialClosure
  _ -> throwExecutionError info CannotApplyValueToNonClosure


enforcePactValue :: i -> EvalValue e b i -> EvalM e b i PactValue
enforcePactValue info = \case
  VPactValue pv -> pure pv
  _ -> throwExecutionError info ExpectedPactValue

enforcePactValue' :: i -> EvalValue e b i -> EvalM e b i (EvalValue e b i)
enforcePactValue' info = \case
  VPactValue pv -> pure (VPactValue pv)
  _ -> throwExecutionError info ExpectedPactValue

catchRecoverable :: forall e b i a. EvalM e b i a -> (i -> UserRecoverableError -> EvalM e b i a) -> EvalM e b i a
catchRecoverable act catch = do
  eState <- evalStateToErrorState <$> get
  catchError act (handler eState)
  where
  handler :: ErrorState i -> PactError i -> EvalM e b i a
  handler eState (PEUserRecoverableError err _ i) = do
    modify' (restoreFromErrorState eState)
    catch i err
  handler _ e = throwError e

readOnlyEnv :: DirectEnv e b i -> DirectEnv e b i
readOnlyEnv e
  | view (cePactDb . pdbPurity) e == PSysOnly = e
  | otherwise =
      let pdb = view cePactDb e
          newPactdb =
              PactDb
             { _pdbPurity = PReadOnly
             , _pdbRead = _pdbRead pdb
             , _pdbWrite = \_ _ _ _ -> dbOpDisallowed
             , _pdbKeys = \_ -> dbOpDisallowed
             , _pdbCreateUserTable = \_ -> dbOpDisallowed
             , _pdbBeginTx = \_ -> dbOpDisallowed
             , _pdbCommitTx = dbOpDisallowed
             , _pdbRollbackTx = dbOpDisallowed
             }
      in set cePactDb newPactdb e

sysOnlyEnv :: forall e b i. DirectEnv e b i -> DirectEnv e b i
sysOnlyEnv e
  | view (cePactDb . pdbPurity) e == PSysOnly = e
  | otherwise =
  let newPactdb =
          PactDb
         { _pdbPurity = PSysOnly
         , _pdbRead = read'
         , _pdbWrite = \_ _ _ _ -> dbOpDisallowed
         , _pdbKeys = const dbOpDisallowed
         , _pdbCreateUserTable = \_ -> dbOpDisallowed
         , _pdbBeginTx = const dbOpDisallowed
         , _pdbCommitTx = dbOpDisallowed
         , _pdbRollbackTx = dbOpDisallowed
         }
  in set cePactDb newPactdb e
  where
  pdb = view cePactDb e
  read' :: Domain k v b i -> k -> GasM b i (Maybe v)
  read' dom k = case dom of
    DUserTables _ -> dbOpDisallowed
    _ -> _pdbRead pdb dom k

evalWithStackFrame :: i -> StackFrame i -> Maybe Type -> EvalM e b i (EvalValue e b i) -> EvalM e b i (EvalValue e b i)
evalWithStackFrame info sf mty act = do
  esStack %= (sf:)
#ifdef WITH_FUNCALL_TRACING
  timeEnter <- liftIO $ getTime ProcessCPUTime
  esTraceOutput %= (TraceFunctionEnter timeEnter sf info:)
#endif
  v <- act
  esStack %= safeTail
  pv <- enforcePactValue info v
  rtcEnabled <- isExecutionFlagSet FlagDisableRuntimeRTC
  unless rtcEnabled $ maybeTCType info mty pv
#ifdef WITH_FUNCALL_TRACING
  timeExit <- liftIO $ getTime ProcessCPUTime
  esTraceOutput %= (TraceFunctionExit timeExit sf info:)
#endif
  return (VPactValue pv)
{-# INLINE evalWithStackFrame #-}

applyLamUnsafe
  :: (IsBuiltin b)
  => CanApply e b i
  -> [EvalValue e b i]
  -> EvalM e b i (EvalValue e b i)
applyLamUnsafe = applyLam

applyLam
  :: (IsBuiltin b)
  => CanApply e b i
  -> [EvalValue e b i]
  -> EvalM e b i (EvalValue e b i)
applyLam nclo@(N (NativeFn b env fn arity i)) args
  | arity == argLen = do
    chargeFlatNativeGas i b
    fn i b env args
  | argLen > arity = throwExecutionError i ClosureAppliedToTooManyArgs
  | null args = return (VClosure nclo)
  | otherwise =
    apply' arity [] args
  where
  argLen = length args
  apply' !a pa (x:xs) = apply' (a - 1) (x:pa) xs
  apply' !a pa [] =
    return (VPartialNative (PartialNativeFn b env fn a pa i))
applyLam (CT (CapTokenClosure fqn argtys arity i)) args
  | arity == argLen = do
    chargeGasArgs i (GAApplyLam (Just fqn) (fromIntegral argLen))
    args' <- traverse (enforcePactValue i) args
    zipWithM_ (\arg ty -> maybeTCType i ty arg) args' argtys
    return (VPactValue (PCapToken (CapToken fqn args')))
  | otherwise = throwExecutionError i ClosureAppliedToTooManyArgs
  where
  argLen = length args
applyLam vc@(C (Closure fqn ca arity term mty env cloi)) args
  | arity == argLen = case ca of
    ArgClosure cloargs -> do
      chargeGasArgs cloi (GAApplyLam (Just fqn) argLen)
      args' <- traverse (enforcePactValue cloi) args
      zipWithM_ (\arg (Arg _ ty _) -> maybeTCType cloi ty arg) args' (NE.toList cloargs)
      let sf = StackFrame fqn args' SFDefun cloi
          varEnv = RAList.fromList (reverse args)
      evalWithStackFrame cloi sf mty (evaluate (set ceLocal varEnv env) term)
    NullaryClosure -> do
      evalWithStackFrame cloi (StackFrame fqn [] SFDefun cloi) mty $ evaluate (set ceLocal mempty env) term
  | argLen > arity = throwExecutionError cloi ClosureAppliedToTooManyArgs
  | otherwise = case ca of
    NullaryClosure -> throwExecutionError cloi ClosureAppliedToTooManyArgs
    ArgClosure cloargs
      | null args ->
        return (VClosure vc)
      | otherwise -> do
        chargeGasArgs cloi (GAApplyLam (Just fqn) argLen)
        apply' mempty (NE.toList cloargs) args
  where
  argLen = length args
  -- Here we enforce an argument to a user fn is a
  apply' e (Arg _ ty _:tys) (x:xs) = do
    x' <- enforcePactValue cloi x
    maybeTCType cloi ty x'
    apply' (RAList.cons (VPactValue x') e) tys xs
  apply' e (ty:tys) [] = do
    let env' = set ceLocal e env
        -- Todo: fix partial SF args
        pclo = PartialClosure (Just (StackFrame fqn [] SFDefun cloi)) (ty :| tys) (length tys + 1) term mty env' cloi
    return (VPartialClosure pclo)
  apply' _ [] _ = throwExecutionError cloi ClosureAppliedToTooManyArgs

applyLam (LC (LamClosure ca arity term mty env cloi)) args
  | arity == argLen = case ca of
    ArgClosure _ -> do
      -- Todo: maybe lambda application should mangle some sort of name?
      chargeGasArgs cloi (GAApplyLam Nothing argLen)
      let locals = view ceLocal env
          locals' = foldl' (flip RAList.cons) locals args
      evaluate (set ceLocal locals' env) term
    NullaryClosure -> do
      evaluate env term >>= enforcePactValue' cloi
  | argLen > arity = throwExecutionError cloi ClosureAppliedToTooManyArgs
  | otherwise = case ca of
      NullaryClosure -> throwExecutionError cloi ClosureAppliedToTooManyArgs
      ArgClosure cloargs -> do
        chargeGasArgs cloi (GAApplyLam Nothing argLen)
        apply' (view ceLocal env) (NE.toList cloargs) args
  where
  argLen = length args
  -- Todo: runtime TC here
  apply' e (Arg _ ty _:tys) (x:xs) = do
    x' <- enforcePactValue cloi x
    maybeTCType cloi ty x'
    apply' (RAList.cons (VPactValue x') e) tys xs
  apply' e [] [] = do
    evaluate (set ceLocal e env) term
  apply' e (ty:tys) [] =
    return (VPartialClosure (PartialClosure Nothing (ty :| tys) (length tys + 1) term mty (set ceLocal e env) cloi))
  apply' _ [] _ = throwExecutionError cloi ClosureAppliedToTooManyArgs
applyLam (PC (PartialClosure li argtys _ term mty env cloi)) args = do
  chargeGasArgs cloi (GAApplyLam (_sfName <$> li) (length args))
  apply' (view ceLocal env) (NE.toList argtys) args
  where
  apply' e (Arg _ ty _:tys) (x:xs) = do
    x' <- enforcePactValue cloi x
    maybeTCType cloi ty x'
    apply' (RAList.cons (VPactValue x') e) tys xs
  apply' e [] [] = do
    case li of
      Just sf -> do
        evalWithStackFrame cloi sf mty $ evaluate (set ceLocal e env) term
      Nothing -> do
        evaluate (set ceLocal e env) term >>= enforcePactValue' cloi
  apply' e (ty:tys) [] = do
    let pclo = PartialClosure li (ty :| tys) (length tys + 1) term mty (set ceLocal e env) cloi
    return (VPartialClosure pclo)
  apply' _ [] _ = throwExecutionError cloi ClosureAppliedToTooManyArgs

applyLam (PN (PartialNativeFn b env fn arity pArgs i)) args
  | arity == argLen = do
    chargeFlatNativeGas i b
    fn i b env (reverse pArgs ++ args)
  | argLen > arity = throwExecutionError i ClosureAppliedToTooManyArgs
  | otherwise = apply' arity [] args
  where
  argLen = length args
  apply' !a pa (x:xs) = apply' (a - 1) (x:pa) xs
  apply' !a pa [] =
    return (VPartialNative (PartialNativeFn b env fn a pa i))
applyLam (DPC (DefPactClosure fqn argtys arity env i)) args
  | arity == argLen = case argtys of
    ArgClosure cloargs -> do
      -- Todo: defpact has much higher overhead, we must charge a bit more gas for this
      chargeGasArgs i (GAApplyLam (Just fqn) (fromIntegral argLen))
      args' <- traverse (enforcePactValue i) args
      zipWithM_ (\arg (Arg _ ty _) -> maybeTCType i ty arg) args' (NE.toList cloargs)
      let pc = DefPactContinuation (fqnToQualName fqn) args'
          env' = set ceLocal (RAList.fromList (reverse args)) env
      initPact i pc env'
    NullaryClosure -> do
      chargeGasArgs i (GAApplyLam (Just fqn) (fromIntegral argLen))
      let pc = DefPactContinuation (fqnToQualName fqn) []
          env' = set ceLocal mempty env
      -- Todo: defpact has much higher overhead, we must charge a bit more gas for this
      initPact i pc env'
  | otherwise = throwExecutionError i ClosureAppliedToTooManyArgs
  where
  argLen = length args



------------------------------------------------------
-- Guards
------------------------------------------------------

enforceGuard
  :: (IsBuiltin b)
  => i
  -> DirectEnv e b i
  -> Guard QualifiedName PactValue
  -> EvalM e b i Bool
enforceGuard info env g = case g of
  GKeyset ks -> do
    isKeysetInSigs info env ks
  GKeySetRef ksn -> do
    isKeysetNameInSigs info  env ksn
  GUserGuard ug -> runUserGuard info env ug
  GCapabilityGuard cg -> enforceCapGuard info cg
  GModuleGuard (ModuleGuard mn _) -> do
    emitPactWarning info ModuleGuardEnforceDetected
    calledByModule mn >>= \case
      True -> return True
      False -> do
        acquireModuleAdminCapability info env mn
        return True
  GDefPactGuard (DefPactGuard dpid _) -> do
    curDpid <- getDefPactId info
    if curDpid == dpid
       then return True
       else throwUserRecoverableError info $
         CapabilityPactGuardInvalidPactId curDpid dpid

-- | Acquires module admin for a known module
-- NOTE: This function should only be called _after_
-- checking whether `esCaps . csModuleAdmin` for the particular
-- module is in scope
acquireModuleAdmin
  :: (IsBuiltin b)
  => i
  -> DirectEnv e b i
  -> EvalModule b i
  -> EvalM e b i ()
acquireModuleAdmin i env mdl = do
  case _mGovernance mdl of
    KeyGov ksn -> do
      () <$ isKeysetNameInSigs i env ksn
    CapGov (FQName fqn) -> do
      let wcapBody = Constant LUnit i
      () <$ evalCap i env (CapToken fqn []) PopCapInvoke NormalCapEval wcapBody
  (esCaps . csModuleAdmin) %= S.insert (_mName mdl)


acquireModuleAdminCapability
  :: (IsBuiltin b)
  => i
  -> DirectEnv e b i
  -> ModuleName
  -> EvalM e b i ()
acquireModuleAdminCapability i env mname = do
  sc <- S.member mname <$> use (esCaps . csModuleAdmin)
  unless sc $ getModule i mname >>= acquireModuleAdmin i env


runUserGuard
  :: (IsBuiltin b)
  => i
  -> DirectEnv e b i
  -> UserGuard QualifiedName PactValue
  -> EvalM e b i Bool
runUserGuard info env (UserGuard qn args) =
  getModuleMemberWithHash info qn >>= \case
    (Dfun d, mh) -> do
      when (length (_dfunArgs d) /= length args) $ throwExecutionError info CannotApplyPartialClosure
      let env' = sysOnlyEnv env
      clo <- mkDefunClosure d (qualNameToFqn qn mh) env'
      -- Todo: sys only here
      True <$ (applyLam (C clo) (VPactValue <$> args) >>= enforcePactValue info)
    (d, _) -> throwExecutionError info (UserGuardMustBeADefun qn (defKind (_qnModName qn) d))

enforceCapGuard
  :: i
  -> CapabilityGuard QualifiedName PactValue
  -> EvalM e b i Bool
enforceCapGuard info cg@(CapabilityGuard qn args mpid) = case mpid of
  Nothing -> enforceCap
  Just pid -> do
    currPid <- getDefPactId info
    if currPid == pid then enforceCap
    else throwUserRecoverableError info $
      CapabilityPactGuardInvalidPactId currPid pid
  where
  enforceCap = do
    cond <- isCapInStack (CapToken qn args)
    if cond then return True
    else do
      throwUserRecoverableError info $ CapabilityGuardNotAcquired cg

-- Keyset Code
isKeysetInSigs
  :: (IsBuiltin b)
  => i
  -> DirectEnv e b i
  -> KeySet
  -> EvalM e b i Bool
isKeysetInSigs info env (KeySet kskeys ksPred) = do
  matchedSigs <- M.filterWithKey matchKey <$> viewEvalEnv eeMsgSigs
  sigs <- checkSigCaps matchedSigs
  runPred (M.size sigs)
  where
  matchKey k _ = k `elem` kskeys
  atLeast t m = m >= t
  count = S.size kskeys
  run p matched =
    if p count matched then pure True
    else
      throwUserRecoverableError info $ KeysetPredicateFailure ksPred kskeys
  runPred matched =
    case ksPred of
      KeysAll -> run atLeast matched
      KeysAny -> run (\_ m -> atLeast 1 m) matched
      Keys2 -> run (\_ m -> atLeast 2 m) matched
      CustomPredicate n -> runCustomPred matched n
  runCustomPred matched = \case
    TQN qn -> do
      getModuleMemberWithHash info qn >>= \case
        (Dfun d, mh) -> do
          clo <- mkDefunClosure d (qualNameToFqn qn mh) env
          p <- enforceBool info =<< applyLam (C clo) [VInteger (fromIntegral count), VInteger (fromIntegral matched)]
          unless p $ throwUserRecoverableError info $ KeysetPredicateFailure ksPred kskeys
          pure p
        _ -> throwExecutionError info (InvalidCustomKeysetPredicate "expected defun")
    TBN (BareName bn) -> do
      m <- viewEvalEnv eeNatives
      case M.lookup bn m of
        Just b -> do
          let builtins = view ceBuiltins env
          let nativeclo = builtins info b env
          p <- enforceBool info =<< applyLam (N nativeclo) [VInteger (fromIntegral count), VInteger (fromIntegral matched)]
          unless p $ throwUserRecoverableError info $ KeysetPredicateFailure ksPred kskeys
          pure p
        Nothing ->
          throwExecutionError info (InvalidCustomKeysetPredicate "expected native")

isKeysetNameInSigs
  :: (IsBuiltin b)
  => i
  -> DirectEnv e b i
  -> KeySetName
  -> EvalM e b i Bool
isKeysetNameInSigs info env ksn = do
  pdb <- viewEvalEnv eePactDb
  liftGasM info (_pdbRead pdb DKeySets ksn) >>= \case
    Just ks -> isKeysetInSigs info env ks
    Nothing ->
      throwExecutionError info (NoSuchKeySet ksn)


------------------------------------------------------
-- Capabilities
------------------------------------------------------

requireCap
  :: i
  -> FQCapToken
  -> EvalM e b i (EvalValue e b i)
requireCap info (CapToken fqn args) = do
  let qualCapToken = CapToken (fqnToQualName fqn) args
  capInStack <- isCapInStack qualCapToken
  if capInStack then return (VBool True)
  else throwUserRecoverableError info (CapabilityNotGranted qualCapToken)

isCapInStack
  :: CapToken QualifiedName PactValue
  -> EvalM e b i Bool
isCapInStack ct = do
  capSet <- getAllStackCaps
  pure $ S.member ct capSet


isCapInStack'
  :: CapToken FullyQualifiedName PactValue
  -> EvalM e b i Bool
isCapInStack' (CapToken fqn args) =
  isCapInStack (CapToken (fqnToQualName fqn) args)

composeCap
  :: (IsBuiltin b)
  => i
  -> DirectEnv e b i
  -> FQCapToken
  -> EvalM e b i (EvalValue e b i)
composeCap info env origToken =
  isCapInStack' origToken >>= \case
    False ->
      evalCap info env origToken PopCapComposed NormalCapEval (Constant (LBool True) info)
    True ->
      return (VBool True)

filterIndex :: Int -> [a] -> [a]
filterIndex i xs = [x | (x, i') <- zip xs [0..], i /= i']

findMsgSigCap :: Int -> CapToken QualifiedName PactValue -> CapToken QualifiedName PactValue -> Bool
findMsgSigCap cix ct1 ct2 =
  _ctName ct1 == _ctName ct2 && (_ctArgs ct1 == filterIndex cix (_ctArgs ct2))

-- Todo:
-- `capAutonomous` are what we should use to match semantics accurately.
installCap
  :: i
  -> DirectEnv e b i
  -> FQCapToken
  -> Bool
  -> EvalM e b i (ManagedCap QualifiedName PactValue)
installCap info _env (CapToken fqn args) autonomous = do
  let ct = CapToken (fqnToQualName fqn) args
  d <- getDefCap info fqn
  case _dcapMeta d of
    DefManaged m -> case m of
      DefManagedMeta (paramIx,_) (FQName fqnMgr) -> do
        managedParam <- maybe (throwExecutionError info (InvalidManagedCap fqn)) pure (args ^? ix paramIx)
        let mcapType = ManagedParam fqnMgr managedParam paramIx
            ctFiltered = CapToken (fqnToQualName fqn) (filterIndex paramIx args)
            mcap = ManagedCap ctFiltered ct mcapType
        capAlreadyInstalled <- S.member mcap <$> use (esCaps . csManaged)
        when capAlreadyInstalled $ throwExecutionError info (CapAlreadyInstalled ct)
        (esCaps . csManaged) %= S.insert mcap
        when autonomous $
          (esCaps . csAutonomous) %= S.insert ct
        pure mcap
      AutoManagedMeta -> do
        let mcapType = AutoManaged False
            mcap = ManagedCap ct ct mcapType
        capAlreadyInstalled <- S.member mcap <$> use (esCaps . csManaged)
        when capAlreadyInstalled $ throwExecutionError info (CapAlreadyInstalled ct)
        (esCaps . csManaged) %= S.insert mcap
        when autonomous $
          (esCaps . csAutonomous) %= S.insert ct
        pure mcap
    DefEvent ->
      throwExecutionError info (InvalidManagedCap fqn)
    Unmanaged -> throwExecutionError info (InvalidManagedCap fqn)




------------------------------------------------------
-- DefPacts
------------------------------------------------------
initPact
  :: (IsBuiltin b)
  => i
  -> DefPactContinuation QualifiedName PactValue
  -> DirectEnv e b i
  -> EvalM e b i (EvalValue e b i)
initPact i pc cenv = do
  case view ceDefPactStep cenv of
    Nothing -> do
      pHash <- viewEvalEnv eeHash
      let
        pStep = DefPactStep 0 False (hashToDefPactId pHash) Nothing
        cenv' = set ceDefPactStep (Just pStep) cenv
      applyPact i pc pStep cenv' mempty
    Just ps ->
      let
        DefPactId p = _psDefPactId ps
        npId = hashToDefPactId (pactHash (T.encodeUtf8 p <> ":" <> encodeStable pc))
        pStep = DefPactStep (_psStep ps) (_psRollback ps) npId Nothing
      in applyNestedPact i pc pStep cenv
  where
    hashToDefPactId = DefPactId . hashToText

-- | Important check for nested pacts:
--   Nested step must be equal to the parent step after execution.
nestedPactsNotAdvanced :: DefPactExec -> DefPactStep -> Bool
nestedPactsNotAdvanced resultState ps =
  any (\npe -> _npeStep npe /= _psStep ps) (_peNestedDefPactExec resultState)
{-# INLINE nestedPactsNotAdvanced #-}

applyPact
  :: (IsBuiltin b)
  => i
  -> DefPactContinuation QualifiedName PactValue
  -> DefPactStep
  -> DirectEnv e b i
  -> M.Map DefPactId NestedDefPactExec
  -> EvalM e b i (EvalValue e b i)
applyPact i pc ps cenv nested = use esDefPactExec >>= \case
  Just pe -> throwExecutionError i (MultipleOrNestedDefPactExecFound pe)
  Nothing -> getModuleMemberWithHash i (pc ^. pcName) >>= \case
    (DPact defPact, mh) -> do
      let nSteps = NE.length (_dpSteps defPact)

      -- `applyPact` is only called from `initPact` or `resumePact`.
      -- `initPact` ensures that the step is 0,
      -- and there are guaranteed more than 0 steps due to how the parser is written.
      -- `resumePact` does a similar check before calling this function.
      step <- maybe (throwExecutionError i (InvalidDefPactStepSupplied ps nSteps)) pure
        $ _dpSteps defPact ^? ix (ps ^. psStep)

      let pe = DefPactExec
               { _peYield = Nothing
               , _peStepHasRollback = hasRollback step
               , _peStepCount = nSteps
               , _peStep = _psStep ps
               , _peDefPactId = _psDefPactId ps
               , _peContinuation = pc
               , _peNestedDefPactExec = nested
               }

      esDefPactExec .= (Just pe)
      let sf = StackFrame (qualNameToFqn (pc ^. pcName) mh) (pc ^. pcArgs) SFDefPact i

      result <- case (ps ^. psRollback, step) of
        (False, _) ->
          evalWithStackFrame i sf Nothing $ evaluate cenv (ordinaryDefPactStepExec step)
        (True, StepWithRollback _ rollbackExpr) ->
          evalWithStackFrame i sf Nothing $ evaluate cenv rollbackExpr
        (True, Step{}) ->
          throwExecutionError i (DefPactStepHasNoRollback ps)

      -- After evaluation, check the result state
      use esDefPactExec >>= \case
        Nothing -> failInvariant i $ InvariantPactExecNotInEnv Nothing
        Just resultExec -> case cenv ^. ceDefPactStep of
          Nothing -> failInvariant i (InvariantPactStepNotInEnv Nothing)
          Just ps' -> do
            let
              pdb = view cePactDb cenv
              isLastStep = _psStep ps' == pred (_peStepCount resultExec)
              done = (not (_psRollback ps') && isLastStep) || _psRollback ps'
            when (nestedPactsNotAdvanced resultExec ps') $
              throwExecutionError i (NestedDefpactsNotAdvanced (_peDefPactId resultExec))
            sz <- sizeOf i SizeOfV0 resultExec
            chargeGasArgs i (GWrite sz)
            evalWrite i pdb Write DDefPacts (_psDefPactId ps') (if done then Nothing else Just resultExec)
            emitXChainEvents (_psResume ps') resultExec
            return result

    (_, mh) -> failInvariant i (InvariantExpectedDefPact (qualNameToFqn (pc ^. pcName) mh))

applyNestedPact
  :: (IsBuiltin b)
  => i
  -> DefPactContinuation QualifiedName PactValue
  -> DefPactStep
  -> DirectEnv e b i
  -> EvalM e b i (EvalValue e b i)
applyNestedPact i pc ps cenv = use esDefPactExec >>= \case
  Nothing -> failInvariant i $ InvariantPactExecNotInEnv Nothing

  Just pe -> getModuleMemberWithHash i (pc ^. pcName) >>= \case
    (DPact defPact, mh) -> do
      step <- maybe (throwExecutionError i (InvalidDefPactStepSupplied ps (_peStepCount pe))) pure
        $ _dpSteps defPact ^? ix (ps ^. psStep)

      let
        stepCount = NE.length (_dpSteps defPact)
        isRollback = hasRollback step

      when (stepCount /= _peStepCount pe) $
        throwExecutionError i (NestedDefPactParentStepCountMismatch (_peDefPactId pe) stepCount (_peStepCount pe))

      when (isRollback /= _peStepHasRollback pe) $
        throwExecutionError i (NestedDefPactParentRollbackMismatch (_peDefPactId pe) isRollback (_peStepHasRollback pe))

      exec <- case pe ^. peNestedDefPactExec . at (_psDefPactId ps) of
        Nothing
          | _psStep ps == 0 -> pure $ DefPactExec
                               { _peStepCount = stepCount
                               , _peYield = Nothing
                               , _peStep = _psStep ps
                               , _peDefPactId = _psDefPactId ps
                               , _peContinuation = pc
                               , _peStepHasRollback = isRollback
                               , _peNestedDefPactExec = mempty
                               }
          | otherwise ->
            throwExecutionError i (NestedDefPactDoubleExecution ps)
        Just npe
          | _psStep ps >= 0 && isRollback && _npeStep npe == _psStep ps ->
            pure (fromNestedPactExec isRollback npe)
          | _psStep ps >  0 && _npeStep npe + 1 == _psStep ps ->
            pure (over peStep (+1) $ fromNestedPactExec isRollback npe)
          | otherwise ->
            throwExecutionError i (NestedDefPactNeverStarted ps)

      esDefPactExec .= (Just exec)
      let
        psWithYield = set psResume (_peYield exec) ps
        cenv' = set ceDefPactStep (Just psWithYield) cenv
      let contFqn = qualNameToFqn (pc ^. pcName) mh
          sf = StackFrame contFqn (pc ^. pcArgs) SFDefPact i
      result <- case (ps ^. psRollback, step) of
        (False, _) ->
          evalWithStackFrame i sf Nothing $ evaluate cenv' (ordinaryDefPactStepExec step)
        (True, StepWithRollback _ rollbackExpr) ->
          evalWithStackFrame i sf Nothing $ evaluate cenv' rollbackExpr
        (True, Step{}) -> throwExecutionError i (DefPactStepHasNoRollback ps)

      use esDefPactExec >>= \case
        Nothing -> failInvariant i $ InvariantPactExecNotInEnv Nothing
        Just resultExec -> do
          when (nestedPactsNotAdvanced resultExec ps) $
            throwExecutionError i (NestedDefpactsNotAdvanced (_peDefPactId resultExec))
          let npe = pe & peNestedDefPactExec %~ M.insert (_psDefPactId ps) (toNestedPactExec resultExec)
          esDefPactExec .= (Just npe)
          return result
    (_, mh) -> failInvariant i (InvariantExpectedDefPact (qualNameToFqn (pc ^. pcName) mh))

resumePact
  :: (IsBuiltin b)
  => i
  -> DirectEnv e b i
  -> Maybe DefPactExec
  -> EvalM e b i (EvalValue e b i)
resumePact i env crossChainContinuation = viewEvalEnv eeDefPactStep >>= \case
  Nothing -> throwExecutionError i DefPactStepNotInEnvironment
  Just ps -> do
    pdb <- viewEvalEnv eePactDb
    dbState <- liftGasM i (_pdbRead pdb DDefPacts (_psDefPactId ps))
    case (dbState, crossChainContinuation) of
      (Just Nothing, _) -> throwExecutionError i (DefPactAlreadyCompleted ps)
      (Nothing, Nothing) -> throwExecutionError i (NoPreviousDefPactExecutionFound ps)
      (Nothing, Just ccExec) -> resumeDefPactExec ccExec
      (Just (Just dbExec), Nothing) -> resumeDefPactExec dbExec
      (Just (Just dbExec), Just ccExec) -> do

        -- Validate CC execution environment progressed far enough
        unless (_peStep ccExec > succ (_peStep dbExec)) $
          throwExecutionError i
            (CCDefPactContinuationError ps ccExec dbExec)

        -- Validate continuation db state
        when (_peContinuation dbExec /= _peContinuation ccExec) $
          throwExecutionError i (CCDefPactContinuationError ps ccExec dbExec)

        -- Validate step count against db state
        when (_peStepCount dbExec /= _peStepCount ccExec) $
          throwExecutionError i (CCDefPactContinuationError ps ccExec dbExec)

        resumeDefPactExec ccExec
      where
        --resumeDefPactExec :: CEKEval step e b i, IsBuiltin b => DefPactExec -> m (CEKEvalResult step e b i)
        resumeDefPactExec pe = do
          when (_psDefPactId ps /= _peDefPactId pe) $
            throwExecutionError i (DefPactIdMismatch (_psDefPactId ps) (_peDefPactId pe))

          when (_psStep ps < 0 || _psStep ps >= _peStepCount pe) $
            throwExecutionError i (InvalidDefPactStepSupplied ps (_peStepCount pe))

          if _psRollback ps
            then when (_psStep ps /= _peStep pe) $
                 throwExecutionError i (DefPactRollbackMismatch ps pe)
            else when (_psStep ps /= succ (_peStep pe)) $
                 throwExecutionError i (DefPactStepMismatch ps pe)

          let pc = view peContinuation pe
              args = VPactValue <$> _pcArgs pc
              resume = case _psResume ps of
                         r@Just{} -> r
                         Nothing -> _peYield pe
              newPactStep = set psResume resume ps
              env' = set ceLocal (RAList.fromList (reverse args)) $ set ceDefPactStep (Just newPactStep) env
          applyPact i pc ps env' (_peNestedDefPactExec pe)

emitXChainEvents
  :: Maybe Yield
  -- ^ from '_psResume', indicating a cross-chain resume.
  -> DefPactExec
   -- ^ tested for yield provenance to indicate a cross-chain yield.
  -> EvalM e b i ()
emitXChainEvents mResume dpe = do
  forM_ mResume $ \r -> case r of
    (Yield _ (Just (Provenance _ mh)) (Just sc)) ->
      emitXEvent "X_RESUME" sc mh
    _ -> return ()
  forM_ (_peYield dpe) $ \y -> case y of
    (Yield _ (Just (Provenance tc mh)) _) ->
      emitXEvent "X_YIELD" tc mh
    _ -> return ()
  where
    emitXEvent eName (ChainId cid) mh = emitReservedEvent eName
      [ PString cid
      , PString (renderQualName (view (peContinuation . pcName) dpe))
      , PList (V.fromList (view (peContinuation . pcArgs) dpe)) ]
      mh
