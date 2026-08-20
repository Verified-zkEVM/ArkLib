/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SMonitoredState

/-!
# Monitored D2SQuery

The revised Section 5.4 specification runs `Monitor` after every trace occurrence. This module
places that check above the legacy low-level transition implementation: `BadEvents` defines the
trace-only predicate `E`, while `ProverTransform` defines the raw transition. The wrapper is the
revised *return-state* interface: a step whose newly appended trace makes `E` true aborts before
exposing its state. The raw trace experiment remains separate, because it is what Lemma 5.8 uses
to charge the first bad occurrence.

The **boundary types** `D2SNormalState`, `D2SPostOccurrenceStopRecord`, and `D2SRevisedStepResult`
(and their handler-free projections) live in the lower shared module `D2SMonitoredState`, which
both the executable layer and the statement layer import as the single source of truth.  This
module re-uses them and adds only the `BadEvents`-dependent functionality lemmas.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

open DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- Revised `D2SQuery`: run the underlying Step 2--4 transition, then run the trace-only
`Monitor`.  The monitor is deliberately outside the raw table transition, because a failed step
has no observable successor state. -/
noncomputable def d2sQueryImplMonitored
    {m : Type → Type} [Monad m] [Alternative m]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) m)
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) m) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        m) := by
  classical
  exact fun q st => do
    let result ← d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st
    if BadEventDS.E result.2.trace then failure else pure result

/-- On every reusable state, the exact trace/table mirror and `Monitor` invariant recover
forward input functionality of the normalized permutation table. -/
lemma D2SNormalState.table_inputFunctional
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    TraceTableOps.InputFunctional normal.state.trΔ.p :=
  BadEventDS.table_inputFunctional_of_mirror_of_not_E normal.state.trace
    normal.state.h_mirror normal.monitorPassed

/-- The dual output-functionality fact for every reusable normalized permutation table. -/
lemma D2SNormalState.table_outputFunctional
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    TraceTableOps.OutputFunctional normal.state.trΔ.p :=
  BadEventDS.table_outputFunctional_of_mirror_of_not_E normal.state.trace
    normal.state.h_mirror normal.monitorPassed


/-- Proof-only result of a trace-preserving stopped D2S transition.  `stopped st'` retains the
post-occurrence state whose trace first fails `Monitor`; this is intentionally different from the
public `OptionT` interface, whose observable result is merely `none`. -/
inductive D2SStoppedResult (α σ : Type) where
  | continue : α → σ → D2SStoppedResult α σ
  | stopped : σ → D2SStoppedResult α σ
  | underlyingAbort : D2SStoppedResult α σ

/-- The two absorbing outcomes of the multi-query proof runner.  Both retain the current state:
the monitor branch therefore retains exactly the trace containing the first bad occurrence. -/
inductive D2SStopReason (σ : Type) where
  | monitorStop : σ → D2SStopReason σ
  | rawAbort : σ → D2SStopReason σ

/-- Classify the raw result of one D2S transition for the proof-only stopped runner.  This is
the entire difference between the raw and stopped one-step distributions: no randomness is
resampled and the post-occurrence state is retained on a monitor stop. -/
noncomputable def classifyD2SStop
    {α : Type}
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (α × D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) →
      Except (D2SStopReason
        (D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
        (α × D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := by
  classical
  exact fun
    | none => .error (.rawAbort st)
    | some (a, st') =>
        if BadEventDS.E st'.trace then .error (.monitorStop st') else .ok (a, st')

/-- `simulateQ`-ready form of the stopped interface.  An exception absorbs the enclosing oracle
computation; its payload preserves the state which ordinary `OptionT` execution would hide. -/
noncomputable def d2sQueryImplStopping
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (ExceptT
          (D2SStopReason
            (D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
          ProbComp)) := by
  classical
  exact fun q st => do
    let result ← ExceptT.lift ((d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run)
    match result with
    | none => throw (D2SStopReason.rawAbort st)
    | some (a, st') =>
        if BadEventDS.E st'.trace then throw (D2SStopReason.monitorStop st')
        else pure (a, st')

/-- The stopped implementation on the exact `[]ₒ + DS` oracle interface used by the prover and
verifier experiments.  The left summand is empty, so this merely lets `simulateQ` execute their
original computations without introducing a second wrapper or a logging state. -/
noncomputable def d2sStoppingCombinedImpl
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp)) :
    QueryImpl ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (ExceptT
          (D2SStopReason
            (D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
          ProbComp)) := by
  exact fun q => match q with
  | .inl e => PEmpty.elim e
  | .inr q' => d2sQueryImplStopping
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q'

/-- The proof-facing stopped version of one D2S query.  It executes exactly the raw transition,
then turns a monitor failure into a trace-carrying stop record.  It is not a public query
implementation: the public monitored interface above still returns `⊥` on that branch. -/
noncomputable def d2sQueryImplStopped
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (D2SStoppedResult
      ((duplexSpongeChallengeOracle StmtIn U).Range q)
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) := by
  classical
  exact do
    let result ← (d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run
    match result with
    | none => pure .underlyingAbort
    | some (a, st') =>
        if BadEventDS.E st'.trace then pure (.stopped st') else pure (.continue a st')

end DuplexSpongeFS.ProverTransform
