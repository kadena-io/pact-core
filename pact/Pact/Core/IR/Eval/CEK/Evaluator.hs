{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP #-}

module Pact.Core.IR.Eval.CEK.Evaluator
  ( eval
  , interpretGuard
  , applyLam
  , mkDefPactClosure
  , resumePact
  , evalCap
  , isKeysetInSigs
  , isKeysetNameInSigs
  , requireCap
  , installCap
  , composeCap
  , mkDefunClosure
  , enforceNotWithinDefcap
  , acquireModuleAdmin
  , isCapInStack
  , filterIndex
  , findMsgSigCap
  , evalWithStackFrame
  , emitCapability
  , guardForModuleCall
  , enforceGuard
  , evalResumePact
  , evalCEK
  , returnCEKValue
  , returnCEK
  , applyLamUnsafe
  , module Pact.Core.IR.Eval.CEK.Types
  , module Pact.Core.IR.Eval.CEK.Utils
  , returnCEKError
  , evalWithinCap
  ) where


import Control.Lens
import Control.Monad
import Control.Monad.State.Strict
import Data.List.NonEmpty(NonEmpty(..))
import Data.Foldable(find, traverse_)
import qualified Data.RAList as RAList
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Vector as V
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.List.NonEmpty as NE
#if !MIN_VERSION_base(4,20,0)
import Data.List(foldl')
#endif
import Pact.Core.Builtin
import Pact.Core.Names
import Pact.Core.Errors
import Pact.Core.Gas
import Pact.Core.Literal
import Pact.Core.PactValue
import Pact.Core.Capabilities
import Pact.Core.Type
import Pact.Core.Guards
import Pact.Core.ModRefs
import Pact.Core.Environment
import Pact.Core.Persistence
import Pact.Core.Hash
import Pact.Core.StableEncoding

import Pact.Core.IR.Term
import Pact.Core.IR.Eval.Runtime
import Pact.Core.Namespace
import Pact.Core.DefPacts.Types
import Pact.Core.SizeOf

import Pact.Core.IR.Eval.CEK.Types
import Pact.Core.IR.Eval.CEK.Utils



{-
  Our CEKH Machine's transitions when reducing terms.
  `evaluateTerm` reduces a term and either directly produces a value,
  or grows the continuation with the information about evaluation of its subterms

  Our machine's state is an n-tuple <C,E,K,H> where:
    - C: (C)ontrol, which either corresponds to:
        - A term to evaluate (EvalTerm b i) for some builtin set b, and tree annotation i
        - A reduced value (Closure, Table or PactValue)
    - E: (E)nvironment, which corresponds to our variable environment, the current pact db state,
      an optional defpact step (during defpact execution), our natives lookup environment, as well as
      a variable for whether we are within a defcap
    - K: (K)ontinuation, which corresponds to the current evaluation context. This may be enriched
    during term reduction
    - H: (H)andler, which holds the topmost installed error handler installed via `try`
    - The reader monad of `MonadEvalEnv` and the state within `MonadEvalState`
  Our machine corresponds to a function: <C, E, K, H> -> <C, E, K, H> that terminates when
  K=Mt and H=NoHandler and returns a semantic value, or an error
-}
evaluateTerm
  :: Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> EvalTerm b i
  -> EvalM e b i (EvalResult e b i)
-- | ------ From ------ | ------ To ------ |
--   <Var n, E, K, H>      <E(n), E, K, H>
--
-- Handles free variable lookups as well as module reference dynamic invokes
evaluateTerm cont handler env (Var n info) = do
  case _nKind n of
    NBound i -> do
      case RAList.lookup (_ceLocal env) i of
        Just v -> returnCEKValue cont handler v
        Nothing -> failInvariant info (InvariantInvalidBoundVariable (_nName n))
    -- Top level names are not closures, so we wipe the env
    NTopLevel mname mh -> do
      let fqn = FullyQualifiedName mname (_nName n) mh
      lookupFqName fqn >>= \case
        Just (Dfun d) -> do
          dfunClo <- VDefClosure <$> mkDefunClosure d fqn env
          returnCEKValue cont handler dfunClo
        -- Todo: this should be GADT'd out
        -- and defconsts should already be evaluated
        Just (DConst d) -> case _dcTerm d of
          -- Note: `TermConst` cannot and should not be `evalCEK`'d. This is an error
          -- this can cause semantic divergences, due to things like provided data.
          -- moreover defcosts are always evaluated in `SysOnly` mode.
          TermConst _term ->
            failInvariant info (InvariantDefConstNotEvaluated fqn)
          EvaledConst v ->
            returnCEKValue cont handler (VPactValue v)
        Just (DPact d) -> do
          let dpactClo = mkDefPactClosure info fqn d env
          returnCEKValue cont handler dpactClo
        Just (DTable d) ->
          let (ResolvedTable sc) = _dtSchema d
              tn = TableName (_dtName d) mname
              tbl = VTable (TableValue tn mh sc)
          in returnCEKValue cont handler tbl
        Just (DCap d) -> do
          let args = _argType <$> _dcapArgs d
              clo = CapTokenClosure fqn args (length args) info
          returnCEKValue cont handler (VClosure (CT clo))
        Just d ->
          failInvariant info (InvariantInvalidDefKind (defKind mname d) "in var position")
        Nothing ->
          failInvariant info (InvariantUnboundFreeVariable fqn)
    NModRef m ifs ->
        returnCEKValue cont handler (VModRef (ModRef m (S.fromList ifs)))
    NDynRef (DynamicRef dArg i) -> case RAList.lookup (view ceLocal env) i of
      Just (VModRef mr) -> do
        modRefHash <- _mHash <$> getModule info (_mrModule mr)
        let nk = NTopLevel (_mrModule mr) modRefHash
        evalCEK cont handler env (Var (Name dArg nk) info)
      Just _ ->
        throwExecutionError info (DynNameIsNotModRef (_nName n))
      Nothing -> failInvariant info (InvariantInvalidBoundVariable (_nName n))
-- | ------ From ------ | ------ To ------ |
--   <Const l, E, K, H>    <Value l, E, K, H>
--
evaluateTerm cont handler _env (Constant l _info) = do
  -- chargeGasArgs _info (GAConstant constantWorkNodeGas)
  returnCEKValue cont handler (VLiteral l)
-- | ------ From ---------- | ------ To ------ |
--   <App fn args, E, K, H>    <fn, E, Args(E,args,K), H>
--
evaluateTerm cont handler env (App fn args info) = do
  -- chargeGasArgs info (GAConstant constantWorkNodeGas)
  evalCEK (Args env info args cont) handler env fn
-- | ------ From ---------- | ------ To ------ |
--   <Nullary body, E, K, H>    <VClosure(body, E), E, K, H>
--
evaluateTerm cont handler env (Nullary body info) = do
  -- chargeGasArgs info (GAConstant constantWorkNodeGas)
  let clo = VLamClosure (LamClosure NullaryClosure 0 body Nothing env info)
  returnCEKValue cont handler clo
-- | ------ From ---------- | ------ To ------ |
--   <Let e1 e2, E, K, H>      <e1, E, LetC(E,e2,K), H>
--
evaluateTerm cont handler env (Let _ e1 e2 _info) = do
  -- chargeGasArgs _info (GAConstant constantWorkNodeGas)
  let cont' = LetC env e2 cont
  evalCEK cont' handler env e1
-- | ------ From ---------- | ------ To ------ |
--   <Lam args body, E, K, H>      <VLamClo(args, body, E), E, K, H>
--
evaluateTerm cont handler env (Lam args body info) = do
  -- chargeGasArgs info (GAConstant constantWorkNodeGas)
  let clo = VLamClosure (LamClosure (ArgClosure args) (NE.length args) body Nothing env info)
  returnCEKValue cont handler clo
-- | ------ From ------ | ------ To ------ |
--   <Builtin b, E, K, H>    <E(b), E, K, H>
--
evaluateTerm cont handler env (Builtin b info) = do
  -- chargeGasArgs info (GAConstant constantWorkNodeGas)
  let builtins = view ceBuiltins env
  returnCEKValue cont handler (VNative (builtins info b env))
-- | ------ From ------ | ------ To ----------------- |
--   <Seq e1 e2, E, K, H>    <e1, E, SeqC(E, e2, K), H>
--
evaluateTerm cont handler env (Sequence e1 e2 _info) = do
  -- chargeGasArgs info (GAConstant constantWorkNodeGas)
  evalCEK (SeqC env e2 cont) handler env e1
-- | ------ From --------------- | ------ To ------------------------ |
--   <CAnd e1 e2, E, K, H>         <e1, E, CondC(E, AndFrame(e2),K),H>
--   <COr e1 e2, E, K, H>          <e1, E, CondC(E, OrFrame(e2),K),H>
--   <CIf cond ifc elc, E, K, H>   <cond, E, CondC(E, IfFrame(ifc,elc),K), H>
--  Todo: enforce and enforce-one
evaluateTerm cont handler env (BuiltinForm c info) = case c of
  CAnd te te' -> do
    -- chargeGasArgs info (GAConstant constantWorkNodeGas)
    evalCEK (CondC env info (AndC te') cont) handler env te
  COr te te' -> do
    -- chargeGasArgs info (GAConstant constantWorkNodeGas)
    evalCEK (CondC env info (OrC te') cont) handler env te
  CIf cond e1 e2 -> do
    -- chargeGasArgs info (GAConstant constantWorkNodeGas)
    evalCEK (CondC env info (IfC e1 e2) cont) handler env cond
  CEnforce cond str -> do
    let env' = sysOnlyEnv env
    -- chargeGasArgs info (GAConstant constantWorkNodeGas)
    evalCEK (CondC env' info (EnforceC str) cont) handler env' cond
  -- | ------ From --------------- | ------ To ------------------------ |
  --   <WithCap cap body, E, K, H>         <cap, E, CapInvokeC(E,WithCapC(body), K),H>
  CWithCapability rawCap body -> do
      enforceNotWithinDefcap info env "with-capability"
      let capFrame = WithCapC body
          cont' = CapInvokeC env info capFrame cont
      evalCEK cont' handler env rawCap
  -- | ------ From --------------- | ------ To ------------------------ |
  --   <CreateUG (n []), E, K, H>            <UGuard n [], E, K,H>
  --   <CreateUG (n (x:xs)), E, K,H>         <x, E, CapInvokeC(E,CrUGC(n, xs),K), H>
  CCreateUserGuard term -> case term of
    App (Var (Name n (NTopLevel mn mh)) _) args _ -> do
      let fqn = FullyQualifiedName mn n mh
      case args of
        [] -> createUserGuard info cont handler fqn []
        x : xs -> do
          let usrGuardFrame = CreateUserGuardC fqn xs []
          let cont' = CapInvokeC env info usrGuardFrame cont
          evalCEK cont' handler env x
    _ -> throwExecutionError info $ NativeExecutionError (NativeName "create-user-guard") $
          "create-user-guard: expected function application of a top-level function"
  CRunReadOnly term -> do
    let env' = readOnlyEnv env
    evalCEK cont handler env' term
  -- | ------ From --------------- | ------ To ------------------------ |
  --   <Try c body, E, K, H>         <body, E, Mt, CEKHandler(E,c,K,_errState,H)>
  --   _errState - callstack,granted caps,events,gas
  CTry catchExpr rest -> do
    chargeTryNodeWork info
    errState <- evalStateToErrorState <$> get
    let handler' = CEKHandler env catchExpr cont errState handler
    let env' = readOnlyEnv env
    evalCEK Mt handler' env' rest
  CEnforceOne str (ListLit conds _) -> do
    case conds of
      [] ->
        -- Note: this will simply be re-thrown within EnforceErrorC, so we don't need anything fancy here
        returnCEK cont handler (VError [] (UserEnforceError "internal CEnforceOne error") info)
      x:xs -> do
        -- Todo: is this a bit too cheap??
        chargeUnconsWork info
        errState <- evalStateToErrorState <$> get
        let env' = readOnlyEnv env
        let handler' = CEKEnforceOne env' info str xs cont errState handler
        let cont' = CondC env' info EnforceOneC Mt
        evalCEK cont' handler' env' x
  CEnforceOne _ _ ->
    throwExecutionError info $ NativeExecutionError (NativeName "enforce-one") $
          "enforce-one: expected a list of conditions"
-- | ------ From --------------- | ------ To ------------------------ |
--   <ListLit [], E, K, H>         <VList [], E, K, H>
---  <ListLit (x:xs), E, K, H>         <x, E, ListC(E,xs,K), H>
evaluateTerm cont handler env (ListLit ts info) = do
  chargeGasArgs info (GConcat (ListConcat (GasListLength (length ts))))
  case ts of
    [] -> returnCEKValue cont handler (VList mempty)
    x:xs -> evalCEK (ListC env info xs [] cont) handler env x
-- | ------ From --------------- | ------ To ------------------------ |
--   <Try c body, E, K, H>         <body, E, Mt, CEKHandler(E,c,K,_errState,H)>
--   _errState - callstack,granted caps,events,gas
evaluateTerm cont handler env (ObjectLit o info) = do
  chargeGasArgs info (GConcat (ObjConcat (length o)))
  case o of
    (f, term):rest -> do
      let cont' = ObjC env info f rest [] cont
      evalCEK cont' handler env term
    [] -> returnCEKValue cont handler (VObject mempty)

evaluateTerm cont handler _env (InlineValue v _) =
  returnCEKValue cont handler (VPactValue v)

mkDefunClosure
  :: Defun Name Type b i
  -> FullyQualifiedName
  -> CEKEnv e b i
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
  -> CEKEnv e b i
  -> CEKValue e b i
mkDefPactClosure info fqn dpact env = case _dpArgs dpact of
  [] ->
    let dpc = DefPactClosure fqn NullaryClosure 0 env info
    in VDefPactClosure dpc
  (x:xs) ->
    let dpc = DefPactClosure fqn (ArgClosure (x :| xs)) (length (x:xs)) env info
    in VDefPactClosure dpc

initPact
  :: ()
  => i
  -> DefPactContinuation QualifiedName PactValue
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> EvalM e b i (EvalResult e b i)
initPact i pc cont handler cenv = do
  case view ceDefPactStep cenv of
    Nothing -> do
      pHash <- viewEvalEnv eeHash
      let
        pStep = DefPactStep 0 False (hashToDefPactId pHash) Nothing
        cenv' = set ceDefPactStep (Just pStep) cenv
      applyPact i pc pStep cont handler cenv' mempty
    Just ps ->
      let
        DefPactId p = _psDefPactId ps
        npId = hashToDefPactId (pactHash (T.encodeUtf8 p <> ":" <> encodeStable pc))
        pStep = DefPactStep (_psStep ps) (_psRollback ps) npId Nothing
      in applyNestedPact i pc pStep cont handler cenv
  where
    hashToDefPactId = DefPactId . hashToText


applyPact
  :: ()
  => i
  -> DefPactContinuation QualifiedName PactValue
  -> DefPactStep
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> M.Map DefPactId NestedDefPactExec
  -> EvalM e b i (EvalResult e b i)
applyPact i pc ps cont handler cenv nested = use esDefPactExec >>= \case
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
      let cont' = DefPactStepC cenv i cont
          contFqn = qualNameToFqn (pc ^. pcName) mh
          sf = StackFrame contFqn (pc ^. pcArgs) SFDefPact i
      case (ps ^. psRollback, step) of
        (False, _) ->
          evalWithStackFrame i cont' handler cenv Nothing sf (ordinaryDefPactStepExec step)
        (True, StepWithRollback _ rollbackExpr) ->
          evalWithStackFrame i cont' handler cenv Nothing sf rollbackExpr
        (True, Step{}) -> throwExecutionError i (DefPactStepHasNoRollback ps)
    (_, mh) -> failInvariant i (InvariantExpectedDefPact (qualNameToFqn (pc ^. pcName) mh))

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

applyNestedPact
  :: ()
  => i
  -> DefPactContinuation QualifiedName PactValue
  -> DefPactStep
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> EvalM e b i (EvalResult e b i)
applyNestedPact i pc ps cont handler cenv = use esDefPactExec >>= \case
  Nothing -> failInvariant i $ InvariantPactExecNotInEnv (Just pc)

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
        cont' = NestedDefPactStepC cenv' i cont pe
        contFqn = FullyQualifiedName (pc ^. pcName . qnModName) (pc ^. pcName . qnName) mh
        sf = StackFrame contFqn (pc ^. pcArgs) SFDefPact i

      case (ps ^. psRollback, step) of
        (False, _) ->
          evalWithStackFrame i cont' handler cenv' Nothing sf (ordinaryDefPactStepExec step)
        (True, StepWithRollback _ rollbackExpr) ->
          evalWithStackFrame i cont' handler cenv' Nothing sf rollbackExpr
        (True, Step{}) -> throwExecutionError i (DefPactStepHasNoRollback ps)
    (_, mh) -> failInvariant i (InvariantExpectedDefPact (qualNameToFqn (pc ^. pcName) mh))


resumePact
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> Maybe DefPactExec
  -> EvalM e b i (EvalResult e b i)
resumePact i cont handler env crossChainContinuation = viewEvalEnv eeDefPactStep >>= \case
  Nothing -> throwExecutionError i DefPactStepNotInEnvironment -- TODO check with multichain
  Just ps -> do
    pdb <- viewEvalEnv eePactDb
    dbState <- liftGasM i (_pdbRead pdb DDefPacts (_psDefPactId ps))
    case (dbState, crossChainContinuation) of

      -- Terminate defpact in db: always fail
      (Just Nothing, _) -> throwExecutionError i (DefPactAlreadyCompleted ps)

      -- Nothing in db, Nothing in cross-chain continuation: fail
      (Nothing, Nothing) -> throwExecutionError i (NoPreviousDefPactExecutionFound ps)  -- TODO check with multichain

      -- Nothing in db, Just cross-chain continuation: proceed with cross-chain
      (Nothing, Just ccExec) -> resumeDefPactExec ccExec

      -- Active db record, Nothing cross-chain continuation: proceed with db
      (Just (Just dbExec), Nothing) -> resumeDefPactExec dbExec

      -- Active db record and cross-chain continuation:
      -- A valid possibility iff this is a flip-flop from another chain, e.g.
      --   0. This chain: start pact
      --   1. Other chain: continue pact
      --   2. This chain: continue pact
      -- Thus check at least one step skipped.
      (Just (Just dbExec), Just ccExec) -> do

        -- Validate CC execution environment progressed far enough
        unless (_peStep ccExec > succ (_peStep dbExec)) $
          throwExecutionError i
            (CCDefPactContinuationError ps ccExec dbExec)

        -- Validate continuation db state
        when (_peContinuation dbExec /= _peContinuation ccExec) $
          throwExecutionError i (CCDefPactContinuationError ps ccExec dbExec)    -- TODO check with multichain

        -- Validate step count against db state
        when (_peStepCount dbExec /= _peStepCount ccExec) $
          throwExecutionError i (CCDefPactContinuationError ps ccExec dbExec)    -- TODO check with multichain

        resumeDefPactExec ccExec
      where
        resumeDefPactExec pe = do
          when (_psDefPactId ps /= _peDefPactId pe) $
            throwExecutionError i (DefPactIdMismatch (_psDefPactId ps) (_peDefPactId pe))    -- TODO check with multichain

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
          applyPact i pc ps cont handler env' (_peNestedDefPactExec pe)


-- | Acquires module admin for a known module
-- NOTE: This function should only be called _after_
-- checking whether `esCaps . csModuleAdmin` for the particular
-- module is in scope
acquireModuleAdmin
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> EvalModule b i
  -> EvalM e b i (EvalResult e b i)
acquireModuleAdmin i cont handler env mdl = do
  let mname = _mName mdl
  moduleAdminAcquired <- S.member mname <$> use (esCaps . csModuleAdmin)
  if moduleAdminAcquired then returnCEKValue cont handler VUnit
  else case _mGovernance mdl of
    KeyGov ksn -> do
      let cont' = ModuleAdminC (_mName mdl) cont
      isKeysetNameInSigs i cont' handler env ksn
    CapGov (FQName fqn) -> do
      let wcapBody = Constant LUnit i
      let cont' = ModuleAdminC (_mName mdl) cont
      evalCap i cont' handler env (CapToken fqn []) PopCapInvoke NormalCapEval wcapBody

-- | Evaluate a term with all the stack manipulation logic
evalWithStackFrame
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> Maybe Type
  -> StackFrame i
  -> EvalTerm b i
  -> EvalM e b i (EvalResult e b i)
evalWithStackFrame info cont handler env mty sf body = do
  cont' <- pushStackFrame info cont mty sf
  evalCEK cont' handler env body

-- | Push a stack frame into the stack, and check it for recursion
pushStackFrame
  :: i
  -> Cont e b i
  -> Maybe Type
  -> StackFrame i
  -> EvalM e b i (Cont e b i)
pushStackFrame info cont mty sf = do
  checkRecursion
  esStack %= (sf :)
  pure (StackPopC info mty cont)
  where
  checkRecursion = do
    RecursionCheck currentCalled <- uses esCheckRecursion NE.head
    let qn = fqnToQualName (_sfName sf)
    when (S.member qn currentCalled) $ throwExecutionError info (RuntimeRecursionDetected qn)
    esCheckRecursion %= NE.cons (RecursionCheck (S.insert qn currentCalled))


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
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> FQCapToken
  -> CapPopState
  -> EvalCapType
  -> EvalTerm b i
  -> EvalM e b i (EvalResult e b i)
evalCap info currCont handler env origToken@(CapToken fqn args) popType ecType contbody = do
  capInStack <- isCapInStack' origToken
  if not capInStack then go else evalCEK currCont handler env contbody
  where
  go = do
    capsBeingEvaluated <- use (esCaps.csCapsBeingEvaluated)
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
                        cbState = CapBodyState popType (Just qualCapToken) emittedEvent contbody
                        contWithCapBody = CapBodyC env info cbState currCont
                        contWithPop = CapPopC (PopCurrCapEval capsBeingEvaluated) info contWithCapBody
                    installCap info env c' False >>= evalUserManagedCap contWithPop newLocals capBody
                  Nothing ->
                    throwExecutionError info (CapNotInstalled qualCapToken)
              Just managedCap -> do
                let emittedEvent = fqctToPactEvent origToken <$ guard (ecType == NormalCapEval)
                let cbState = CapBodyState popType (Just qualCapToken) emittedEvent contbody
                let contWithCapBody = CapBodyC env info cbState currCont
                    contWithPop = CapPopC (PopCurrCapEval capsBeingEvaluated) info contWithCapBody
                evalUserManagedCap contWithPop newLocals capBody managedCap
          -- handle autonomous caps
          AutoManagedMeta -> do
            -- Find the capability post-filtering
            let emittedEvent = fqctToPactEvent origToken <$ guard (ecType == NormalCapEval)
            let cbState = CapBodyState popType Nothing emittedEvent contbody
            let contWithCapBody = CapBodyC env info cbState currCont
                contWithPop = CapPopC (PopCurrCapEval capsBeingEvaluated) info contWithCapBody
            mgdCaps <- use (esCaps . csManaged)
            case find ((==) qualCapToken . _mcCap) mgdCaps of
              Nothing -> do
                msgCaps <- S.unions <$> viewEvalEnv eeMsgSigs
                case find (== qualCapToken) msgCaps of
                  Just c -> do
                    let c' = set ctName fqn c
                    installCap info env c' False >>= evalAutomanagedCap contWithPop newLocals capBody
                  Nothing ->
                    throwExecutionError info (CapNotInstalled qualCapToken)
              Just managedCap ->
                evalAutomanagedCap contWithPop newLocals capBody managedCap
      DefEvent -> do
        let cbState = CapBodyState popType Nothing (Just (fqctToPactEvent origToken)) contbody
        let contWithCapBody = CapBodyC env info cbState currCont
            contWithPop = CapPopC (PopCurrCapEval capsBeingEvaluated) info contWithCapBody
        let inCapEnv = set ceInCap True $ set ceLocal newLocals env
        (esCaps . csSlots) %= (CapSlot qualCapToken []:)
        (esCaps . csCapsBeingEvaluated) %= S.insert qualCapToken
        sfCont <- pushStackFrame info contWithPop Nothing capStackFrame
        evalCEK sfCont handler inCapEnv capBody
      -- Not automanaged _nor_ user managed.
      -- Todo: a type that's basically `Maybe` here would save us a lot of grief.
      Unmanaged -> do
        let cbState = CapBodyState popType Nothing Nothing contbody
        let contWithBody = if ecType == NormalCapEval then CapBodyC env info cbState currCont
                    else currCont
            contWithPop = CapPopC (PopCurrCapEval capsBeingEvaluated) info contWithBody
            inCapEnv = set ceInCap True $ set ceLocal newLocals env
        (esCaps . csCapsBeingEvaluated) %= S.insert qualCapToken
        (esCaps . csSlots) %= (CapSlot qualCapToken []:)
        evalWithStackFrame info contWithPop handler inCapEnv Nothing capStackFrame capBody
  qualCapName = fqnToQualName fqn
  qualCapToken = CapToken qualCapName args
  capStackFrame = StackFrame fqn args SFDefcap info
  -- This function is handles both evaluating the manager function for the installed parameter
  -- and continuing evaluation for the actual capability body.
  evalUserManagedCap cont' env' capBody managedCap = case _mcManaged managedCap of
    ManagedParam mpfqn oldV managedIx -> do
      dfun <- getDefun info mpfqn
      dfunClo <- mkDefunClosure dfun mpfqn env
      newV <- maybe (failInvariant info (InvariantInvalidManagedCapIndex managedIx fqn)) pure (args ^? ix managedIx)
      -- Set the mgr fun to evaluate after we apply the capability body
      -- NOTE: test-capability doesn't actually run the manager function, it just runs the cap pop then
      -- pops it. It would be great to do without this, but a lot of our regressions rely on this.
      let mgrFunCont = if ecType == NormalCapEval then
                         CapInvokeC env info (ApplyMgrFunC managedCap dfunClo oldV newV) cont'
                       else cont'
      let inCapEnv = set ceInCap True $ set ceLocal env' $ env
      let inCapBodyToken = _mcOriginalCap managedCap
      -- BIG SEMANTICS NOTE HERE
      -- the cap slot here that we push should NOT be the qualified original token.
      -- Instead, it's the original token from the installed from the static cap. Otherwise, enforce checks
      -- within the cap body will fail (That is, keyset enforcement). Instead, once we are evaluating the body,
      -- we pop the current cap stack, then replace the head with the original intended token.
      -- this is done in `CapBodyC` and this is the only way to do this.
      (esCaps . csSlots) %= (CapSlot inCapBodyToken []:)
      (esCaps . csCapsBeingEvaluated) %= S.insert inCapBodyToken
      sfCont <- pushStackFrame info mgrFunCont Nothing capStackFrame
      evalCEK sfCont handler inCapEnv capBody
    _ -> failInvariant info (InvariantInvalidManagedCapKind "expected user managed, received automanaged")
  evalAutomanagedCap cont' env' capBody managedCap = case _mcManaged managedCap of
    AutoManaged b -> do
      if b then returnCEKError info currCont handler OneShotCapAlreadyUsed
      else do
        let newManaged = AutoManaged True
        esCaps . csManaged %= S.union (S.singleton (set mcManaged newManaged managedCap))
        esCaps . csSlots %= (CapSlot qualCapToken []:)
        (esCaps . csCapsBeingEvaluated) %= S.insert qualCapToken
        let inCapEnv = set ceLocal env' $ set ceInCap True $ env
        sfCont <- pushStackFrame info cont' Nothing capStackFrame
        evalCEK sfCont handler inCapEnv capBody
    _ -> failInvariant info (InvariantInvalidManagedCapKind "expected automanaged, received user managed")

returnCEKError
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> UserRecoverableError
  -> EvalM e b i (EvalResult e b i)
returnCEKError info cont handler err = do
  stack <- use esStack
  returnCEK cont handler (VError stack err info)


enforceNotWithinDefcap
  :: i
  -> CEKEnv e b i
  -> T.Text
  -> EvalM e b i ()
enforceNotWithinDefcap info env form =
  when (_ceInCap env) $ throwExecutionError info (FormIllegalWithinDefcap form)

requireCap
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> FQCapToken
  -> EvalM e b i (EvalResult e b i)
requireCap info cont handler (CapToken fqn args) = do
  let qualCapToken = CapToken (fqnToQualName fqn) args
  capInStack <- isCapInStack qualCapToken
  if capInStack then returnCEKValue cont handler (VBool True)
  else returnCEKError info cont handler (CapabilityNotGranted qualCapToken)

isCapInStack
  :: CapToken QualifiedName PactValue
  -> EvalM e b i Bool
isCapInStack ct = S.member ct <$> getAllStackCaps

isCapInStack'
  :: CapToken FullyQualifiedName PactValue
  -> EvalM e b i Bool
isCapInStack' (CapToken fqn args) =
  isCapInStack (CapToken (fqnToQualName fqn) args)

composeCap
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> FQCapToken
  -> EvalM e b i (EvalResult e b i)
composeCap info cont handler env origToken =
  isCapInStack' origToken >>= \case
    False ->
      evalCap info cont handler env origToken PopCapComposed NormalCapEval (Constant (LBool True) info)
    True ->
      returnCEKValue cont handler (VBool True)

filterIndex :: Int -> [a] -> [a]
filterIndex i xs = [x | (x, i') <- zip xs [0..], i /= i']

findMsgSigCap :: Int -> CapToken QualifiedName PactValue -> CapToken QualifiedName PactValue -> Bool
findMsgSigCap cix ct1 ct2 =
  _ctName ct1 == _ctName ct2 && (_ctArgs ct1 == filterIndex cix (_ctArgs ct2))

-- Todo:
-- `capAutonomous` are what we should use to match semantics accurately.
installCap
  :: i
  -> CEKEnv e b i
  -> FQCapToken
  -> Bool
  -> EvalM e b i (ManagedCap QualifiedName PactValue)
installCap info _env (CapToken fqn args) autonomous = do
  let ct = CapToken (fqnToQualName fqn) args
  d <- getDefCap info fqn
  case _dcapMeta d of
    DefManaged m -> case m of
      DefManagedMeta (paramIx,_) (FQName fqnMgr) -> do
        managedParam <- maybe (failInvariant info $ InvariantInvalidManagedCapIndex paramIx fqn) pure (args ^? ix paramIx)
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

-- Todo: should we typecheck / arity check here?
createUserGuard
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> FullyQualifiedName
  -> [PactValue]
  -> EvalM e b i (EvalResult e b i)
createUserGuard info cont handler fqn args = do
  -- Note: we could use `getDefun` here, but this gives us a better error
  lookupFqName fqn >>= \case
    Just (Dfun _) ->
      returnCEKValue cont handler (VGuard (GUserGuard (UserGuard (fqnToQualName fqn) args)))
    Just d ->
      -- Note: this error is not recoverable in prod
      -- <interactive>:0:26:Error: User guard closure must be defun, found: defcap
      -- at <interactive>:0:7: (create-user-guard ((defcap m.g:<a> ())))
      -- at <interactive>:0:0: (try 1 (native `create-user-guard`  Defines a custom guar...)
      throwExecutionError info $ UserGuardMustBeADefun (fqnToQualName fqn) (defKind (_fqModule fqn) d)
    Nothing ->
      failInvariant info (InvariantUnboundFreeVariable fqn)


applyCont
  :: ()
  => Cont e b i
  -> CEKErrorHandler e b i
  -> EvalResult e b i
  -> EvalM e b i (EvalResult e b i)
applyCont Mt handler v =
  case handler of
    CEKNoHandler -> pure v
    CEKHandler env catchTerm cont' errState handler' -> case v of
      VError{} -> do
        modify' (restoreFromErrorState errState)
        evalCEK cont' handler' env catchTerm
      EvalValue v' ->
        returnCEKValue cont' handler' v'
    -- Enforce one is tricky. Not only do false results
    -- mean "continue to evaluate the list of expressions",
    -- but it also HANDLES ERRORS and continues to chug away!!!!
    -- Therefore, it has a custom handler which holds:
    --  - The last eval env
    --  - The "lazy" string expression
    --  - The remaining conditions, in case a falsy error needs to be handled
    --  - The remainder of the continuation and the old handler
    --
    -- This handler upon encountering an error has a choice to make:
    --  - Do we have unhandled expressions left? If so, resume evaluation with the head of
    --    the expression list
    --  - Are we done evaluating expressions? Then we have an enforce error: compute the
    --    error string and boom boom de boom return an unhandled error with it
    --
    --  How is the list of expressions kept up to date you may ask?
    --  EnforceOne is the only native that actualy has to _modify the handler_
    --  on successful expression evaluation in the case that it errors
    CEKEnforceOne env i str li cont errState h -> case v of
      VError{} -> case li of
        [] -> do
          modify' (restoreFromErrorState errState)
          let cont' = EnforceErrorC i cont
          evalCEK cont' h env str
        x:xs -> do
          modify' (restoreFromErrorState errState)
          let handler' = CEKEnforceOne env i str xs cont errState h
              oldFrame = CondC env i EnforceOneC Mt
          evalCEK oldFrame handler' env x
      EvalValue v' ->
        returnCEKValue cont h v'
applyCont cont handler v = case v of
  VError{} -> returnCEK Mt handler v
  EvalValue v' -> applyContToValue cont handler v'

-- | if true then 1 else 2
applyContToValue
  :: forall e b i.()
  => Cont e b i
  -> CEKErrorHandler e b i
  -> CEKValue e b i
  -> EvalM e b i (EvalResult e b i)
applyContToValue Mt handler v =
  case handler of
    CEKNoHandler -> pure (EvalValue v)
    -- Assuming no error, the caps will have been popped naturally
    CEKHandler _env _term cont' _ handler' ->
      returnCEKValue cont' handler' v
    CEKEnforceOne _ _ _ _ cont' _ handler' ->
      returnCEKValue cont' handler' v
-- Error terms that don't simply returnt the empty continuation
-- "Zero out" the continuation up to the latest handler
-- returnCEKValue _cont handler v@VError{} =
--   returnCEK Mt handler v
-- | ------ From ------------------------- | ------------ To -------------- |
--   <VClosure c, Args(E, (x:xs), K), H>     <x, E, Fn(c, E, xs, K), H>
--
applyContToValue (Args env i args cont) handler fn = do
  c <- canApply fn
  -- Argument evaluation
  case args of
    [] -> applyLam c [] cont handler
    (x:xs) -> do
      let cont' = Fn c env xs [] cont
      evalCEK cont' handler env x
  where
  canApply = \case
    -- Todo: restrict the type of closures applied to user functions
    VClosure (C clo) -> pure (C clo)
    VClosure (LC clo) -> pure (LC clo)
    VClosure (N clo) -> pure (N clo)
    VClosure (DPC clo) -> pure (DPC clo)
    VClosure (CT clo) -> pure (CT clo)
    VClosure _ ->
      throwExecutionError i CannotApplyPartialClosure
    -- Todo: this is _not_ an invariant failure. Requires a better error
    _ -> throwExecutionError i CannotApplyValueToNonClosure
-- | ------ From ------------------------- | ------ To ----------------------- |
--   <v, _, Fn(clo, E, (x:xs), acc, K), H>   <x, E, Fn(c, E, xs, (v:acc), K), H>
--   <v, _, Fn(clo, E, [], K), H>            (apply clo (reverse (v:acc)) K H)
--
applyContToValue (Fn fn env args vs cont) handler v = do
  case args of
    [] -> do
      applyLam fn (reverse (v:vs)) cont handler
    x:xs ->
      evalCEK (Fn fn env xs (v:vs) cont) handler env x
-- | ------ From ------------ | ------ To ---------------- |
--   <v, LetC(E, body, K), H>   <body, (cons v E), K, H>
--
applyContToValue (LetC env letbody cont) handler v = do
  evalCEK cont handler (over ceLocal (RAList.cons v) env) letbody
-- | ------ From ------------ | ------ To ---------------- |
--   <_, SeqC(E, e2, K), H>     <e2, E, K, H>
--
applyContToValue (SeqC env e cont) handler _ =
  evalCEK cont handler env e
-- | ------ From ------------------------ | ------ To ---------------- |
--   <VBool b, CondC(E, AndC(e2), K), H>   if b then <e2, E, EnforceBool(K), H>
--                                         else <VBool b, K, H>
--   <VBool b, CondC(E, OrC(e2), K), H>    if b then <VBool b, K, H>
--                                         else <e2, E, EnforceBool(K), H>
--
-- | ------ From ------------------------------ | ------ To ---------------- |
--   <VBool b, CondC(E, IfC(ifE, elseE), K), H>   if b then <ifE, E, K, H>
--                                                else <VBool b, K, H>
--
-- Note: we charge gas for this reduction here, as these are essentially natives
-- that match and perform an uncons/match.
applyContToValue (CondC env info frame cont) handler v = do
  case v of
    VBool b -> case frame of
      AndC te ->
        if b then evalCEK (EnforceBoolC info cont) handler env te
        else returnCEKValue cont handler v
      OrC te ->
        if b then returnCEKValue cont handler v
        else evalCEK (EnforceBoolC info cont) handler env te
      IfC ifExpr elseExpr ->
        if b then evalCEK cont handler env ifExpr
        else evalCEK cont handler env elseExpr
      EnforceC str ->
        if b then returnCEKValue cont handler v
        else do
          let cont' = EnforceErrorC info cont
          evalCEK cont' handler env str
      FilterC clo elem' rest acc -> do
        let acc' = if b then elem':acc else acc
        case rest of
          x:xs -> do
            chargeUnconsWork info
            let cont' = CondC env info (FilterC clo x xs acc') cont
            applyLam clo [VPactValue x] cont' handler
          [] -> returnCEKValue cont handler (VList (V.fromList (reverse acc')))
      EnforceOneC ->
        if b then returnCEKValue cont handler v
        else
        -- Note: this will simply be re-thrown within EnforceErrorC, so we don't need anything fancy here
        returnCEK cont handler (VError [] (UserEnforceError "internal CEnforceOne error") info)
      AndQC clo pv ->
        if b then applyLam clo [VPactValue pv] (EnforceBoolC info cont) handler
        else returnCEKValue cont handler v
      OrQC clo pv ->
        if not b then applyLam clo [VPactValue pv] (EnforceBoolC info cont) handler
        else returnCEKValue cont handler v
      NotQC -> returnCEKValue cont handler (VBool (not b))
    VPactValue v' -> throwExecutionError info (ExpectedBoolValue v')
    _ ->
      -- Note: a non-boolean value in these functions is non recoverable
      throwExecutionError info ExpectedPactValue
applyContToValue (CapInvokeC env info cf cont) handler v = case cf of
  WithCapC body -> case v of
    VCapToken ct@(CapToken fqn _) -> do
      guardForModuleCall info (_fqModule fqn) $
        evalCap info cont handler env ct PopCapInvoke NormalCapEval body
    -- Todo: this is actually more like "expected cap token"
    VPactValue v' -> throwExecutionError info $ ExpectedCapToken v'
    _ -> throwExecutionError info $ ExpectedPactValue
  CreateUserGuardC fqn terms pvs -> do
    pv <- enforcePactValue info v
    case terms of
      x:xs -> do
        let cf' = CreateUserGuardC fqn xs (pv:pvs)
            cont' = CapInvokeC env info cf' cont
        evalCEK cont' handler env x
      [] -> createUserGuard info cont handler fqn (reverse (pv:pvs))
  ApplyMgrFunC mgdCap clo old new -> do
    -- Set the manager fun to update the current managed cap.
    let cont' = EnforcePactValueC info $ CapInvokeC env info (UpdateMgrFunC mgdCap) cont
    applyLam (C clo) [VPactValue old, VPactValue new] cont' handler
  -- note: typechecking should be handled by the manager function here.
  UpdateMgrFunC mcap -> case v of
    VPactValue v' -> do
      let mcap' = unsafeUpdateManagedParam v' mcap
      (esCaps . csManaged) %= S.insert mcap'
      returnCEKValue cont handler v
    _ -> throwExecutionError info ExpectedPactValue
applyContToValue (BuiltinC env info frame cont) handler cv = do
  let pdb = _cePactDb env
  case cv of
    VPactValue v -> case frame of
      MapC closure rest acc -> do
        case rest of
          x:xs -> do
            let cont' = BuiltinC env info (MapC closure xs (v:acc)) cont
            chargeUnconsWork info
            applyLam closure [VPactValue x] cont' handler
          [] ->
            returnCEKValue cont handler (VList (V.fromList (reverse (v:acc))))
      FoldC clo rest -> do
        case rest of
          x:xs -> do
            let cont' = BuiltinC env info (FoldC clo xs) cont
            chargeUnconsWork info
            applyLam clo [VPactValue v, VPactValue x] cont' handler
          [] -> returnCEKValue cont handler cv
      ZipC clo (l, r) acc -> do
        case (l, r) of
          (x:xs, y:ys) -> do
            let cont' = BuiltinC env info (ZipC clo (xs, ys) (v:acc)) cont
            chargeUnconsWork info
            applyLam clo [VPactValue x, VPactValue y] cont' handler
          (_, _) ->
            returnCEKValue cont handler (VList (V.fromList (reverse (v:acc))))
      ---------------------------------------------------------
      -- Db frames
      -- Todo: gas costs if post-read actions
      ---------------------------------------------------------
      SelectC tv clo rdata remaining acc mf -> case v of
        PBool b -> do
          let acc' = if b then rdata:acc else acc
          selectRead tv clo remaining acc' mf
        _ -> throwExecutionError info $ ExpectedBoolValue v
      FoldDbFilterC tv queryClo appClo (rk, ObjectData om) remaining accum -> case v of
        PBool b -> do
          let accum' = if b then (rk, PObject om):accum else accum
          foldDBRead tv queryClo appClo remaining accum'
        _ ->
          throwExecutionError info (ExpectedBoolValue v)
      FoldDbMapC tv appClo remaining acc -> case remaining of
        (RowKey rk, pv):xs -> do
          let rdf = FoldDbMapC tv appClo xs (v:acc)
              cont' = BuiltinC env info rdf cont
          applyLam appClo [VString rk, VPactValue pv] cont' handler
        [] -> returnCEKValue cont handler (VList (V.fromList (v:acc)))
      DefineKeysetC ksn newKs -> do
        newKsSize <- sizeOf info SizeOfV0 newKs
        chargeGasArgs info (GWrite newKsSize)
        evalWrite info pdb Write DKeySets ksn newKs
        returnCEKValue cont handler (VString "Keyset write success")
      DefineNamespaceC ns -> case v of
        PBool allow ->
          if allow then do
            let nsn = _nsName ns
            nsSize <- sizeOf info SizeOfV0 ns
            chargeGasArgs info (GWrite nsSize)
            evalWrite info pdb Write DNamespaces nsn ns
            returnCEKValue cont handler $ VString $ "Namespace defined: " <> (_namespaceName nsn)
          -- injecting the NativeName directly here as to not have to unnecessarily thread `b` around in the
          -- cont
          else throwExecutionError info $ NativeExecutionError (NativeName "define-namespace") $ "Namespace definition not permitted"
        _ ->
          throwExecutionError info $ NativeExecutionError (NativeName "define-namespace") $ "Namespace manager function returned an invalid value"
      RunKeysetPredC (KeySet ksKeys ksPred) -> case v of
        PBool allow ->
          if allow then returnCEKValue cont handler (VBool True)
          else returnCEKError info cont handler $
            KeysetPredicateFailure ksPred ksKeys
        _ ->
          throwExecutionError info (ExpectedBoolValue v)
      where
      foldDBRead tv queryClo appClo remaining acc =
        case remaining of
          rk@(RowKey raw):remaining' -> liftGasM info (_pdbRead pdb (tvToDomain tv) rk) >>= \case
            Just (RowData row) -> do
              let rdf = FoldDbFilterC tv queryClo appClo (rk, ObjectData row) remaining' acc
                  cont' = BuiltinC env info rdf cont
              applyLam queryClo [VString raw, VObject row] cont' handler
            Nothing ->
              failInvariant info (InvariantNoSuchKeyInTable (_tvName tv) rk)
          [] -> case acc of
            (RowKey rk, pv):xs -> do
              let rdf = FoldDbMapC tv appClo xs []
                  cont' = BuiltinC env info rdf cont
              applyLam appClo [VString rk, VPactValue pv] cont' handler
            [] -> returnCEKValue cont handler (VList mempty)
      selectRead tv clo keys acc mf = case keys of
        k:ks -> liftGasM info (_pdbRead pdb (tvToDomain tv) k) >>= \case
          Just (RowData r) -> do
            let bf = SelectC tv clo (ObjectData r) ks acc mf
                cont' = BuiltinC env info bf cont
            applyLam clo [VObject r] cont' handler
          Nothing ->
            failInvariant info (InvariantNoSuchKeyInTable (_tvName tv) k)
        [] -> case mf of
          Just fields ->
            let acc' = PObject . (`M.restrictKeys` S.fromList fields) . _objectData <$> reverse acc
            in returnCEKValue cont handler (VList (V.fromList acc'))
          Nothing ->
            let acc' = PObject . _objectData <$> reverse acc
            in returnCEKValue cont handler (VList (V.fromList acc'))
    _ ->
      throwExecutionError info ExpectedPactValue
applyContToValue (CapBodyC env info (CapBodyState cappop mcap mevent capbody) cont) handler _ = do
  traverse_ (emitEventLegacyUnsafe info) mevent
  case mcap of
    Nothing -> do
      let cont' = CapPopC cappop info cont
      evalCEK cont' handler env capbody
    -- We're in a managed cap! We gotta do some quick stack manipulation.
    Just cap -> use (esCaps . csSlots) >>= \case
      (CapSlot _ tl:rest) -> do
        (esCaps . csSlots) .= (CapSlot cap tl:rest)
        let cont' = CapPopC cappop info cont
        evalCEK cont' handler env capbody
      [] -> failInvariant info InvariantEmptyCapStackFailure

applyContToValue (CapPopC st info cont) handler v = case st of
  PopCurrCapEval oldSet -> do
    esCaps . csCapsBeingEvaluated .= oldSet
    returnCEKValue cont handler v
  PopCapInvoke -> do
    esCaps . csSlots %= safeTail
    returnCEKValue cont handler v
  PopCapComposed -> do
    use (esCaps . csSlots) >>= \case
      cap:cs -> do
        let csList = _csCap cap : _csComposed cap
            caps' = over (_head . csComposed) (++ csList) cs
        (esCaps . csSlots) .= caps'
        returnCEKValue cont handler v
      [] -> failInvariant info InvariantEmptyCapStackFailure

applyContToValue (ListC env info args vals cont) handler v = do
  pv <- enforcePactValue info v
  case args of
    [] ->
      returnCEKValue cont handler (VList (V.fromList (reverse (pv:vals))))
    e:es ->
      evalCEK (ListC env info es (pv:vals) cont) handler env e

applyContToValue (ObjC env info currfield fs vs cont) handler v = do
  v' <- enforcePactValue info v
  let fields = (currfield,v'):vs
  case fs of
    (f', term):fs' ->
      let cont' = ObjC env info f' fs' fields cont
      in evalCEK cont' handler env term
    [] ->
      returnCEKValue cont handler (VObject (M.fromList (reverse fields)))

applyContToValue (EnforceErrorC info _) handler v = case v of
  VString err ->
    returnCEKError info Mt handler $ UserEnforceError err
  VPactValue v' -> throwExecutionError info $ ExpectedStringValue v'
  _ -> throwExecutionError info $ ExpectedPactValue
-- Discard the value of running a user guard, no error occured, so
applyContToValue (IgnoreValueC v cont) handler _v =
  returnCEKValue cont handler (VPactValue v)

applyContToValue (StackPopC i mty cont) handler v = do
  v' <- enforcePactValue i v
  rtcEnabled <- isExecutionFlagSet FlagDisableRuntimeRTC
  unless rtcEnabled $ maybeTCType i mty v'
  esStack %= safeTail
  esCheckRecursion %= getPrevRecCheck
  returnCEKValue cont handler (VPactValue v')
  where
  getPrevRecCheck (_ :| l) = case l of
    top : rest -> top :| rest
    [] -> (RecursionCheck mempty) :| []

applyContToValue (DefPactStepC env info cont) handler v =
  use esDefPactExec >>= \case
    Nothing -> failInvariant info $ InvariantPactExecNotInEnv Nothing
    Just pe -> case env ^. ceDefPactStep of
      Nothing -> failInvariant info (InvariantPactStepNotInEnv Nothing)
      Just ps -> do
        let
          pdb = view cePactDb env
          isLastStep = _psStep ps == pred (_peStepCount pe)
          done = (not (_psRollback ps) && isLastStep) || _psRollback ps
        when (nestedPactsNotAdvanced pe ps) $
          throwExecutionError info (NestedDefpactsNotAdvanced (_peDefPactId pe))
        sz <- sizeOf info SizeOfV0 pe
        chargeGasArgs info (GWrite sz)
        evalWrite info pdb Write DDefPacts (_psDefPactId ps)
            (if done then Nothing else Just pe)
        emitXChainEvents (_psResume ps) pe
        returnCEKValue cont handler v

applyContToValue (NestedDefPactStepC env info cont parentDefPactExec) handler v =
  use esDefPactExec >>= \case
    Nothing -> failInvariant info $ InvariantPactExecNotInEnv Nothing
    Just pe ->  case env ^. ceDefPactStep of
      Nothing -> failInvariant info (InvariantPactStepNotInEnv Nothing)
      Just ps -> do
        when (nestedPactsNotAdvanced pe ps) $
          throwExecutionError info (NestedDefpactsNotAdvanced (_peDefPactId pe))
        let npe = parentDefPactExec & peNestedDefPactExec %~ M.insert (_psDefPactId ps) (toNestedPactExec pe)
        esDefPactExec .= (Just npe)
        returnCEKValue cont handler v

applyContToValue (EnforcePactValueC info cont) handler v = case v of
  VPactValue{} -> returnCEKValue cont handler v
  _ -> throwExecutionError info ExpectedPactValue

applyContToValue (EnforceBoolC info cont) handler v = case v of
  VBool{} -> returnCEKValue cont handler v
  VPactValue v' -> throwExecutionError info (ExpectedBoolValue v')
  _ -> throwExecutionError info ExpectedPactValue

applyContToValue (ModuleAdminC mn cont) handler v = do
  (esCaps . csModuleAdmin) %= S.insert mn
  returnCEKValue cont handler v


-- | Important check for nested pacts:
--   Nested step must be equal to the parent step after execution.
nestedPactsNotAdvanced :: DefPactExec -> DefPactStep -> Bool
nestedPactsNotAdvanced resultState ps =
  any (\npe -> _npeStep npe /= _psStep ps) (_peNestedDefPactExec resultState)
{-# INLINE nestedPactsNotAdvanced #-}

-- | Apply a closure to its arguments,
--   dispatching based on closure type.
applyLam
  :: ()
  => CanApply e b i
  -> [CEKValue e b i]
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> EvalM e b i (EvalResult e b i)
applyLam vc@(C (Closure fqn ca arity term mty env cloi)) args cont handler
  -- Fully apply closure and evaluate
  | arity == argLen = case ca of
    ArgClosure cloargs -> do
      chargeGasArgs cloi (GAApplyLam (Just fqn) argLen)
      args' <- traverse (enforcePactValue cloi) args
      zipWithM_ (\arg (Arg _ ty _) -> maybeTCType cloi ty arg) args' (NE.toList cloargs)
      let varEnv = RAList.fromList (reverse args)
      evalWithStackFrame cloi cont handler (set ceLocal varEnv env) mty (StackFrame fqn args' SFDefun cloi) term
    NullaryClosure -> do
      let varEnv = mempty
      evalWithStackFrame cloi cont handler (set ceLocal varEnv env) mty (StackFrame fqn [] SFDefun cloi) term
  | argLen > arity =
    throwExecutionError cloi ClosureAppliedToTooManyArgs
  | otherwise = case ca of
    NullaryClosure ->
      throwExecutionError cloi ClosureAppliedToTooManyArgs
    ArgClosure cloargs
      | null args ->
        returnCEKValue cont handler (VClosure vc)
      | otherwise -> do
        chargeGasArgs cloi (GAApplyLam (Just fqn) argLen)
        apply' mempty (NE.toList cloargs) args
  where
  argLen = length args
  -- Here we enforce an argument to a user fn is a pact value
  apply' e (Arg _ ty _:tys) (x:xs) = do
    x' <- enforcePactValue cloi x
    maybeTCType cloi ty x'
    apply' (RAList.cons (VPactValue x') e) tys xs
  apply' e (ty:tys) [] = do
    let env' = set ceLocal e env
        -- Todo: fix partial SF args
        pclo = PartialClosure (Just (StackFrame fqn [] SFDefun cloi)) (ty :| tys) (length tys + 1) term mty env' cloi
    returnCEKValue cont handler (VPartialClosure pclo)
  apply' _ [] _ =
    throwExecutionError cloi ClosureAppliedToTooManyArgs

applyLam (LC (LamClosure ca arity term mty env cloi)) args cont handler
  | arity == argLen = case ca of
    ArgClosure _ -> do
      -- Todo: maybe lambda application should mangle some sort of name?
      chargeGasArgs cloi (GAApplyLam Nothing argLen)
      let locals = view ceLocal env
          locals' = foldl' (flip RAList.cons) locals args
          cont' = EnforcePactValueC cloi cont
      evalCEK cont' handler (set ceLocal locals' env) term
    NullaryClosure -> do
      let cont' = EnforcePactValueC cloi cont
      evalCEK cont' handler env term
  | argLen > arity = do
    throwExecutionError cloi ClosureAppliedToTooManyArgs
  | otherwise = case ca of
      NullaryClosure -> do
        throwExecutionError cloi ClosureAppliedToTooManyArgs
      ArgClosure cloargs -> do
        chargeGasArgs cloi (GAApplyLam Nothing argLen)
        apply' (view ceLocal env) (NE.toList cloargs) args
  where
  argLen = length args
  apply' e (Arg _ ty _:tys) (x:xs) = do
    x' <- enforcePactValue cloi x
    maybeTCType cloi ty x'
    apply' (RAList.cons (VPactValue x') e) tys xs
  apply' e [] [] = do
    evalCEK cont handler (set ceLocal e env) term
  apply' e (ty:tys) [] =
    returnCEKValue cont handler
    (VPartialClosure (PartialClosure Nothing (ty :| tys) (length tys + 1) term mty (set ceLocal e env) cloi))
  apply' _ [] _ = do
    throwExecutionError cloi ClosureAppliedToTooManyArgs

applyLam (PC (PartialClosure li argtys _ term mty env cloi)) args cont handler = do
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
        evalWithStackFrame cloi cont handler (set ceLocal e env) mty sf term
      Nothing -> do
        let cont' = EnforcePactValueC cloi cont
        evalCEK cont' handler (set ceLocal e env) term
  apply' e (ty:tys) [] = do
    let pclo = PartialClosure li (ty :| tys) (length tys + 1) term mty (set ceLocal e env) cloi
    returnCEKValue cont handler (VPartialClosure pclo)
  apply' _ [] _ = do
    throwExecutionError cloi ClosureAppliedToTooManyArgs

applyLam nclo@(N (NativeFn b env fn arity i)) args cont handler
  | arity == argLen = do
    chargeFlatNativeGas i b
    fn i b cont handler env args
  | argLen > arity = do
    throwExecutionError i ClosureAppliedToTooManyArgs
  | null args = returnCEKValue cont handler (VClosure nclo)
  | otherwise =
    apply' arity [] args
  where
  argLen = length args
  apply' !a pa (x:xs) = apply' (a - 1) (x:pa) xs
  apply' !a pa [] =
    returnCEKValue cont handler (VPartialNative (PartialNativeFn b env fn a pa i))

applyLam (PN (PartialNativeFn b env fn arity pArgs i)) args cont handler
  | arity == argLen = do
    chargeFlatNativeGas i b
    fn i b cont handler env (reverse pArgs ++ args)
  | argLen > arity = do
    throwExecutionError i ClosureAppliedToTooManyArgs
  | otherwise = apply' arity [] args
  where
  argLen = length args
  apply' !a pa (x:xs) = apply' (a - 1) (x:pa) xs
  apply' !a pa [] =
    returnCEKValue cont handler (VPartialNative (PartialNativeFn b env fn a pa i))

applyLam (DPC (DefPactClosure fqn argtys arity env i)) args cont handler
  | arity == argLen = case argtys of
    ArgClosure cloargs -> do
      -- Todo: defpact has much higher overhead, we must charge a bit more gas for this
      chargeGasArgs i (GAApplyLam (Just fqn) (fromIntegral argLen))
      args' <- traverse (enforcePactValue i) args
      zipWithM_ (\arg (Arg _ ty _) -> maybeTCType i ty arg) args' (NE.toList cloargs)
      let pc = DefPactContinuation (fqnToQualName fqn) args'
          env' = set ceLocal (RAList.fromList (reverse args)) env
      initPact i pc cont handler env'
    NullaryClosure -> do
      chargeGasArgs i (GAApplyLam (Just fqn) (fromIntegral argLen))
      let pc = DefPactContinuation (fqnToQualName fqn) []
          env' = set ceLocal mempty env
      -- Todo: defpact has much higher overhead, we must charge a bit more gas for this
      initPact i pc cont handler env'
  | otherwise = do
    throwExecutionError i ClosureAppliedToTooManyArgs
  where
  argLen = length args
applyLam (CT (CapTokenClosure fqn argtys arity i)) args cont handler
  | arity == argLen = do
    chargeGasArgs i (GAApplyLam (Just fqn) (fromIntegral argLen))
    args' <- traverse (enforcePactValue i) args
    zipWithM_ (\arg ty -> maybeTCType i ty arg) args' argtys
    returnCEKValue cont handler (VPactValue (PCapToken (CapToken fqn args')))
  | otherwise = do
    throwExecutionError i ClosureAppliedToTooManyArgs
  where
  argLen = length args


returnCEKValue :: Cont e b i -> CEKErrorHandler e b i -> CEKValue e b i -> EvalM e b i (EvalResult e b i)
returnCEKValue = applyContToValue
{-# INLINE returnCEKValue #-}

returnCEK :: Cont e b i -> CEKErrorHandler e b i -> EvalResult e b i -> EvalM e b i (EvalResult e b i)
returnCEK = applyCont
{-# INLINE returnCEK #-}

evalCEK :: Cont e b i -> CEKErrorHandler e b i -> CEKEnv e b i -> EvalTerm b i -> EvalM e b i (EvalResult e b i)
evalCEK = evaluateTerm
{-# INLINE evalCEK #-}

applyLamUnsafe :: CanApply e b i -> [CEKValue e b i] -> Cont e b i -> CEKErrorHandler e b i -> EvalM e b i (EvalResult e b i)
applyLamUnsafe = applyLam
{-# INLINE applyLamUnsafe #-}

evalNormalForm :: CEKEnv e b i -> EvalTerm b i -> EvalM e b i (EvalResult e b i)
evalNormalForm = evaluateTerm Mt CEKNoHandler
{-# INLINE evalNormalForm #-}

-- | The main logic of enforcing a guard.
--
-- The main difference to `coreEnforceGuard` is this function's type doesn't need to be a `NativeFunction e b i`,
-- thus there's no need to wrap/unwrap the guard into a `VPactValue`,
-- and moreover it does not need to take a `b` which it does not use anyway.
enforceGuard
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> Guard QualifiedName PactValue
  -> EvalM e b i (EvalResult e b i)
enforceGuard info cont handler env g = case g of
  GKeyset ks -> do
    isKeysetInSigs info cont handler env ks
  GKeySetRef ksn -> do
    isKeysetNameInSigs info cont handler env ksn
  GUserGuard ug -> runUserGuard info cont handler env ug
  GCapabilityGuard cg -> enforceCapGuard info cont handler cg
  GModuleGuard (ModuleGuard mn _) -> do
    emitPactWarning info ModuleGuardEnforceDetected
    calledByModule mn >>= \case
      True -> returnCEKValue cont handler (VBool True)
      False -> do
        md <- getModule info mn
        let cont' = IgnoreValueC (PBool True) cont
        acquireModuleAdmin info cont' handler env md
  GDefPactGuard (DefPactGuard dpid _) -> do
    curDpid <- getDefPactId info
    if curDpid == dpid
       then returnCEKValue cont handler (VBool True)
       else returnCEKError info cont handler $
         CapabilityPactGuardInvalidPactId curDpid dpid

enforceCapGuard
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CapabilityGuard QualifiedName PactValue
  -> EvalM e b i (EvalResult e b i)
enforceCapGuard info cont handler cg@(CapabilityGuard qn args mpid) = case mpid of
  Nothing -> enforceCap
  Just pid -> do
    currPid <- getDefPactId info
    if currPid == pid then enforceCap
    else returnCEKError info cont handler $
         CapabilityPactGuardInvalidPactId currPid pid
  where
  enforceCap = do
    cond <- isCapInStack (CapToken qn args)
    if cond then returnCEKValue cont handler (VBool True)
    else returnCEKError info cont handler $
      CapabilityGuardNotAcquired cg


runUserGuard
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> UserGuard QualifiedName PactValue
  -> EvalM e b i (EvalResult e b i)
runUserGuard info cont handler env (UserGuard qn args) =
  getModuleMemberWithHash info qn >>= \case
    (Dfun d, mh) -> do
      when (length (_dfunArgs d) /= length args) $ throwExecutionError info CannotApplyPartialClosure
      let env' = sysOnlyEnv env
      clo <- mkDefunClosure d (qualNameToFqn qn mh) env'
      -- Todo: sys only here
      applyLam (C clo) (VPactValue <$> args) (IgnoreValueC (PBool True) cont) handler
    (d, _) -> throwExecutionError info (UserGuardMustBeADefun qn (defKind (_qnModName qn) d))


eval
  :: forall e b i
  .  ()
  => Purity
  -> BuiltinEnv e b i
  -> EvalTerm b i
  -> EvalM e b i PactValue
eval purity benv term = do
  ee <- viewEvalEnv id
  let cekEnv = envFromPurity purity (CEKEnv mempty (_eePactDb ee) benv (_eeDefPactStep ee) False)
  evalNormalForm cekEnv term >>= \case
    VError stack err i ->
      throwUserRecoverableError' i stack err
    EvalValue v -> do
      case v of
        VPactValue pv -> pure pv
        _ ->
          throwExecutionError (view termInfo term) (EvalError "Evaluation did not reduce to a value")

evalWithinCap
  :: forall e b i
  .  ()
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
  let cekEnv = envFromPurity purity (CEKEnv mempty (_eePactDb ee) benv (_eeDefPactStep ee) False)
  evalCap (view termInfo term) Mt CEKNoHandler cekEnv ct PopCapInvoke NormalCapEval term
    >>= \case
    VError stack err i ->
      throwUserRecoverableError' i stack err
    EvalValue v -> do
      case v of
        VPactValue pv -> pure pv
        _ ->
          throwExecutionError (view termInfo term) (EvalError "Evaluation did not reduce to a value")

interpretGuard
  :: forall e b i
  .  ()
  => i
  -> BuiltinEnv e b i
  -> Guard QualifiedName PactValue
  -> EvalM e b i PactValue
interpretGuard info bEnv g = do
  ee <- viewEvalEnv id
  let cekEnv = CEKEnv mempty (_eePactDb ee) bEnv (_eeDefPactStep ee) False
  enforceGuard info Mt CEKNoHandler cekEnv g >>= \case
    VError stack err i ->
      throwUserRecoverableError' i stack err
    EvalValue v -> do
      case v of
        VPactValue pv -> pure pv
        _ ->
          throwExecutionError info (EvalError "Evaluation did not reduce to a value")

evalResumePact
  :: forall e b i
  . ()
  => i
  -> BuiltinEnv e b i
  -> Maybe DefPactExec
  -> EvalM e b i PactValue
evalResumePact info bEnv mdpe = do
  ee <- viewEvalEnv id
  let pdb = _eePactDb ee
  let env = CEKEnv mempty pdb bEnv (_eeDefPactStep ee) False
  resumePact info Mt CEKNoHandler env mdpe >>= \case
    VError stack err i ->
      throwUserRecoverableError' i stack err
    EvalValue v -> do
      case v of
        VPactValue pv -> pure pv
        _ ->
          throwExecutionError info (EvalError "Evaluation did not reduce to a value")


-- Keyset Code
isKeysetInSigs
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> KeySet
  -> EvalM e b i (EvalResult e b i)
isKeysetInSigs info cont handler env ks@(KeySet kskeys ksPred) = do
  matchedSigs <- M.filterWithKey matchKey <$> viewEvalEnv eeMsgSigs
  sigs <- checkSigCaps matchedSigs
  runPred (M.size sigs)
  where
  matchKey k _ = k `elem` kskeys
  atLeast t m = m >= t
  count = S.size kskeys
  run p matched =
    if p count matched then returnCEKValue cont handler (VBool True)
    else returnCEKError info cont handler $
      KeysetPredicateFailure ksPred kskeys
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
          let cont' = BuiltinC env info (RunKeysetPredC ks) cont
          applyLam (C clo) [VInteger (fromIntegral count), VInteger (fromIntegral matched)] cont' handler
        _ ->
          throwExecutionError info (InvalidCustomKeysetPredicate "expected defun")
    TBN (BareName bn) -> do
      m <- viewEvalEnv eeNatives
      case M.lookup bn m of
        Just b -> do
          let builtins = view ceBuiltins env
          let nativeclo = builtins info b env
          let cont' = BuiltinC env info (RunKeysetPredC ks) cont
          applyLam (N nativeclo) [VInteger (fromIntegral count), VInteger (fromIntegral matched)] cont' handler
        Nothing ->
          throwExecutionError info (InvalidCustomKeysetPredicate "expected native")

isKeysetNameInSigs
  :: ()
  => i
  -> Cont e b i
  -> CEKErrorHandler e b i
  -> CEKEnv e b i
  -> KeySetName
  -> EvalM e b i (EvalResult e b i)
isKeysetNameInSigs info cont handler env ksn = do
  pdb <- viewEvalEnv eePactDb
  liftGasM info (_pdbRead pdb DKeySets ksn) >>= \case
    Just ks -> isKeysetInSigs info cont handler env ks
    Nothing ->
      throwExecutionError info (NoSuchKeySet ksn)
