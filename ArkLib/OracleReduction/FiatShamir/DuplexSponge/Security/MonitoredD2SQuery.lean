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
  [codec : Codec pSpec U] {δ : Nat}
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

/-- Exact one-step raw/stopped coupling.  The stopped query is the pushforward of the raw
transition by `classifyD2SStop`; consequently the first monitored bad occurrence has exactly
the same probability as in the raw transition, rather than merely the same support. -/
lemma d2sQueryImplStopping_run_eq_map_classify
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ((d2sQueryImplStopping
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q).run st).run =
      (classifyD2SStop (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) st) <$>
      ((d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run) := by
  classical
  simp only [d2sQueryImplStopping, StateT.run]
  simp only [ExceptT.run_bind, ExceptT.run_lift]
  rw [bind_map_left]
  apply bind_congr
  intro raw
  unfold Function.comp
  unfold classifyD2SStop
  cases raw with
  | none => rfl
  | some pair =>
      rcases pair with ⟨a, st'⟩
      by_cases hE : BadEventDS.E st'.trace <;> simp only [hE, ↓reduceIte] <;> rfl

/-- Exact monitor-stop probability at one query.  The retained stop state has the same
distribution as the raw successful successor restricted to the branch on which `Monitor` first
observes `E`; no conditioning or union bound is hidden in this conversion. -/
lemma probEvent_d2sQueryImplStopping_monitorStop_eq
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (P : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) → Prop) :
    Pr[ (fun result => match result with
      | Except.error (.monitorStop st') => P st'
      | _ => False) |
      ((d2sQueryImplStopping
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q).run st).run] =
    Pr[ (fun raw => match raw with
      | some (_, st') => BadEventDS.E st'.trace ∧ P st'
      | none => False) |
      (d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run] := by
  classical
  rw [d2sQueryImplStopping_run_eq_map_classify
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st]
  rw [probEvent_map]
  apply probEvent_congr' (fun raw _ => ?_) rfl
  unfold Function.comp
  unfold classifyD2SStop
  cases raw with
  | none => rfl
  | some pair =>
      rcases pair with ⟨a, st'⟩
      by_cases hE : BadEventDS.E st'.trace <;> simp [hE]

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

/-- An ordinary result of the `ExceptT` stopped interface has passed `Monitor`.  This is the
multi-query runner's local continuation invariant. -/
lemma d2sQueryImplStopping_support_ok_not_E
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {a : (duplexSpongeChallengeOracle StmtIn U).Range q}
    {st' : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hr : Except.ok (a, st') ∈ support
      ((d2sQueryImplStopping
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q).run st).run) :
    ¬ BadEventDS.E st'.trace := by
  classical
  unfold d2sQueryImplStopping at hr
  change Except.ok (a, st') ∈ support ((do
    let result ← ExceptT.lift ((d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run)
    match result with
    | none => throw (D2SStopReason.rawAbort st)
    | some (a₀, st₀) =>
        if BadEventDS.E st₀.trace then throw (D2SStopReason.monitorStop st₀)
        else pure (a₀, st₀)).run) at hr
  simp only [ExceptT.run_bind, ExceptT.run_lift, mem_support_bind_iff] at hr
  obtain ⟨raw, hraw, hr⟩ := hr
  cases raw with
  | error e =>
      simp only [ExceptT.run_lift, support_map] at hraw
      obtain ⟨raw, _, hEq⟩ := hraw
      cases hEq
  | ok raw =>
      cases raw with
      | none =>
          simp only [ExceptT.run_throw, mem_support_pure_iff] at hr
          contradiction
      | some result =>
          rcases result with ⟨a₀, st₀⟩
          by_cases hE : BadEventDS.E st₀.trace
          · simp only [hE, ↓reduceIte, ExceptT.run_throw, mem_support_pure_iff] at hr
            contradiction
          · simp only [hE, ↓reduceIte, ExceptT.run_pure, mem_support_pure_iff] at hr
            have hpair : (a, st') = (a₀, st₀) := Except.ok.inj hr
            injection hpair with ha hs
            subst ha
            subst hs
            exact hE

/-- A retained monitor stop carries precisely a post-occurrence bad trace. -/
lemma d2sQueryImplStopping_support_monitorStop_E
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {st' : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hr : Except.error (D2SStopReason.monitorStop st') ∈ support
      ((d2sQueryImplStopping
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q).run st).run) :
    BadEventDS.E st'.trace := by
  classical
  unfold d2sQueryImplStopping at hr
  change Except.error (D2SStopReason.monitorStop st') ∈ support ((do
    let result ← ExceptT.lift ((d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run)
    match result with
    | none => throw (D2SStopReason.rawAbort st)
    | some (a₀, st₀) =>
        if BadEventDS.E st₀.trace then throw (D2SStopReason.monitorStop st₀)
        else pure (a₀, st₀)).run) at hr
  simp only [ExceptT.run_bind, ExceptT.run_lift, mem_support_bind_iff] at hr
  obtain ⟨raw, hraw, hr⟩ := hr
  cases raw with
  | error e =>
      simp only [ExceptT.run_lift, support_map] at hraw
      obtain ⟨raw, _, hEq⟩ := hraw
      cases hEq
  | ok raw =>
      cases raw with
      | none =>
          simp only [ExceptT.run_throw, mem_support_pure_iff] at hr
          have hne : D2SStopReason.monitorStop st' = D2SStopReason.rawAbort st :=
            Except.error.inj hr
          cases hne
      | some result =>
          rcases result with ⟨a₀, st₀⟩
          by_cases hE : BadEventDS.E st₀.trace
          · simp only [hE, ↓reduceIte, ExceptT.run_throw, mem_support_pure_iff] at hr
            have hstate : st' = st₀ := D2SStopReason.monitorStop.inj (Except.error.inj hr)
            subst st'
            exact hE
          · simp only [hE, ↓reduceIte, ExceptT.run_pure, mem_support_pure_iff] at hr
            contradiction

/-- The state retained by a monitor stop is supported by the identical raw transition.  Thus a
stopped execution discards only the future continuation, never the first bad occurrence itself. -/
lemma d2sQueryImplStopping_support_monitorStop_raw
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {st' : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hr : Except.error (D2SStopReason.monitorStop st') ∈ support
      ((d2sQueryImplStopping
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q).run st).run) :
    ∃ a, some (a, st') ∈ support ((d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run) := by
  classical
  unfold d2sQueryImplStopping at hr
  change Except.error (D2SStopReason.monitorStop st') ∈ support ((do
    let result ← ExceptT.lift ((d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run)
    match result with
    | none => throw (D2SStopReason.rawAbort st)
    | some (a₀, st₀) =>
        if BadEventDS.E st₀.trace then throw (D2SStopReason.monitorStop st₀)
        else pure (a₀, st₀)).run) at hr
  simp only [ExceptT.run_bind, ExceptT.run_lift, mem_support_bind_iff] at hr
  obtain ⟨raw, hraw, hr⟩ := hr
  cases raw with
  | error e =>
      simp only [ExceptT.run_lift, support_map] at hraw
      obtain ⟨raw, _, hEq⟩ := hraw
      cases hEq
  | ok raw =>
      cases raw with
      | none =>
          simp only [ExceptT.run_throw, mem_support_pure_iff] at hr
          have hne : D2SStopReason.monitorStop st' = D2SStopReason.rawAbort st :=
            Except.error.inj hr
          cases hne
      | some result =>
          rcases result with ⟨a₀, st₀⟩
          by_cases hE : BadEventDS.E st₀.trace
          · simp only [hE, ↓reduceIte, ExceptT.run_throw, mem_support_pure_iff] at hr
            have hstate : st' = st₀ :=
              D2SStopReason.monitorStop.inj (Except.error.inj hr)
            subst st'
            simp only [ExceptT.run_lift, support_map] at hraw
            obtain ⟨raw, hraw, hEq⟩ := hraw
            have hrawEq : raw = some (a₀, st₀) := by
              simpa using hEq
            subst raw
            exact ⟨a₀, hraw⟩
          · simp only [hE, ↓reduceIte, ExceptT.run_pure, mem_support_pure_iff] at hr
            contradiction

/-- A successful call of the revised interface has passed `Monitor`.  This is intentionally
stated on the concrete probabilistic support: a failed monitor branch produces no returned
state, while every returned state is a sound prefix for the subsequent stopped-run analysis. -/
lemma d2sQueryImplMonitored_support_not_E
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((d2sQueryImplMonitored
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      gImpl auxImpl q st).run)) :
    ∀ a st', r = some (a, st') → ¬ BadEventDS.E st'.trace := by
  intro a st' hrEq
  rw [d2sQueryImplMonitored] at hr
  simp only [OptionT.run_bind, OptionT.run_failure, OptionT.run_pure,
    Option.elimM, mem_support_bind_iff] at hr
  obtain ⟨result, hresult, hr⟩ := hr
  cases result with
  | none =>
    have hr' : r ∈ support (pure none : ProbComp
      (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
        D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
      simpa using hr
    rw [mem_support_pure_iff] at hr'
    rw [hrEq] at hr'
    simp at hr'
  | some result =>
    rcases result with ⟨a₀, st₀⟩
    by_cases hE : BadEventDS.E st₀.trace
    · have hr' : r ∈ support (pure none : ProbComp
        (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
          D2SQueryState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
        simpa [hE] using hr
      rw [mem_support_pure_iff] at hr'
      rw [hrEq] at hr'
      simp at hr'
    · have hr' : r ∈ support (pure (some (a₀, st₀)) : ProbComp
        (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
          D2SQueryState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
        simpa [hE] using hr
      rw [mem_support_pure_iff] at hr'
      have hpair : (a, st') = (a₀, st₀) := by
        rw [hrEq] at hr'
        exact Option.some.inj hr'
      injection hpair with ha hs
      subst ha
      subst hs
      exact hE

/-- A continuing stopped result is exactly an E-good raw successor. -/
lemma d2sQueryImplStopped_support_continue_not_E
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : D2SStoppedResult
      ((duplexSpongeChallengeOracle StmtIn U).Range q)
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support (d2sQueryImplStopped
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st)) :
    ∀ a st', r = .continue a st' → ¬ BadEventDS.E st'.trace := by
  classical
  intro a st' hrEq
  rw [d2sQueryImplStopped] at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨result, hresult, hr⟩ := hr
  cases result with
  | none =>
      have hr' : r ∈ support (pure .underlyingAbort : ProbComp
          (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
            (D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
        simpa using hr
      rw [mem_support_pure_iff] at hr'
      rw [hrEq] at hr'
      contradiction
  | some result =>
      rcases result with ⟨a₀, st₀⟩
      by_cases hE : BadEventDS.E st₀.trace
      · have hr' : r ∈ support (pure (.stopped st₀) : ProbComp
            (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
              (D2SQueryState
                (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
          simpa [hE] using hr
        rw [mem_support_pure_iff] at hr'
        rw [hrEq] at hr'
        contradiction
      · have hr' : r ∈ support (pure (.continue a₀ st₀) : ProbComp
            (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
              (D2SQueryState
                (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
          simpa [hE] using hr
        rw [mem_support_pure_iff] at hr'
        rw [hrEq] at hr'
        injection hr' with ha hs
        subst ha
        subst hs
        exact hE

/-- A stopped result is the first transition's raw post-state together with a monitor witness. -/
lemma d2sQueryImplStopped_support_stopped_E
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : D2SStoppedResult
      ((duplexSpongeChallengeOracle StmtIn U).Range q)
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support (d2sQueryImplStopped
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st)) :
    ∀ st', r = .stopped st' → BadEventDS.E st'.trace := by
  classical
  intro st' hrEq
  rw [d2sQueryImplStopped] at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨result, hresult, hr⟩ := hr
  cases result with
  | none =>
      have hr' : r ∈ support (pure .underlyingAbort : ProbComp
          (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
            (D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
        simpa using hr
      rw [mem_support_pure_iff] at hr'
      rw [hrEq] at hr'
      contradiction
  | some result =>
      rcases result with ⟨a, st₀⟩
      by_cases hE : BadEventDS.E st₀.trace
      · have hr' : r ∈ support (pure (.stopped st₀) : ProbComp
            (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
              (D2SQueryState
                (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
          simpa [hE] using hr
        rw [mem_support_pure_iff] at hr'
        rw [hrEq] at hr'
        have hstate : st' = st₀ := D2SStoppedResult.stopped.inj hr'
        subst st'
        exact hE
      · have hr' : r ∈ support (pure (.continue a st₀) : ProbComp
            (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
              (D2SQueryState
                (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
          simpa [hE] using hr
        rw [mem_support_pure_iff] at hr'
        rw [hrEq] at hr'
        contradiction

/-- A continuing stopped result is supported by the identical raw transition. -/
lemma d2sQueryImplStopped_support_continue_raw
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : D2SStoppedResult
      ((duplexSpongeChallengeOracle StmtIn U).Range q)
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support (d2sQueryImplStopped
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st)) :
    ∀ a st', r = .continue a st' →
      some (a, st') ∈ support ((d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run) := by
  classical
  intro a st' hrEq
  rw [d2sQueryImplStopped] at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨result, hresult, hr⟩ := hr
  cases result with
  | none =>
      have hr' : r ∈ support (pure .underlyingAbort : ProbComp
          (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
            (D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
        simpa using hr
      rw [mem_support_pure_iff] at hr'
      rw [hrEq] at hr'
      contradiction
  | some result =>
      rcases result with ⟨a₀, st₀⟩
      by_cases hE : BadEventDS.E st₀.trace
      · have hr' : r ∈ support (pure (.stopped st₀) : ProbComp
            (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
              (D2SQueryState
                (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
          simpa [hE] using hr
        rw [mem_support_pure_iff] at hr'
        rw [hrEq] at hr'
        contradiction
      · have hr' : r ∈ support (pure (.continue a₀ st₀) : ProbComp
            (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
              (D2SQueryState
                (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
          simpa [hE] using hr
        rw [mem_support_pure_iff] at hr'
        rw [hrEq] at hr'
        injection hr' with ha hs
        subst ha
        subst hs
        exact hresult

/-- A trace-carrying stop record is supported by the raw post-occurrence transition. -/
lemma d2sQueryImplStopped_support_stopped_raw
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : D2SStoppedResult
      ((duplexSpongeChallengeOracle StmtIn U).Range q)
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support (d2sQueryImplStopped
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st)) :
    ∀ st', r = .stopped st' →
      ∃ a, some (a, st') ∈ support ((d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run) := by
  classical
  intro st' hrEq
  rw [d2sQueryImplStopped] at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨result, hresult, hr⟩ := hr
  cases result with
  | none =>
      have hr' : r ∈ support (pure .underlyingAbort : ProbComp
          (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
            (D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
        simpa using hr
      rw [mem_support_pure_iff] at hr'
      rw [hrEq] at hr'
      contradiction
  | some result =>
      rcases result with ⟨a, st₀⟩
      by_cases hE : BadEventDS.E st₀.trace
      · have hr' : r ∈ support (pure (.stopped st₀) : ProbComp
            (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
              (D2SQueryState
                (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
          simpa [hE] using hr
        rw [mem_support_pure_iff] at hr'
        rw [hrEq] at hr'
        have hstate : st' = st₀ := D2SStoppedResult.stopped.inj hr'
        subst st'
        exact ⟨a, hresult⟩
      · have hr' : r ∈ support (pure (.continue a st₀) : ProbComp
            (D2SStoppedResult ((duplexSpongeChallengeOracle StmtIn U).Range q)
              (D2SQueryState
                (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
          simpa [hE] using hr
        rw [mem_support_pure_iff] at hr'
        rw [hrEq] at hr'
        contradiction

/-- Every successful raw `D2SQuery` transition appends exactly the narrow oracle occurrence
that was issued.  This is the operational trace bridge behind the stopped-runner: even though the
legacy raw implementation returns only a successor state, its support points retain enough
information to recover the exact final `h`, `p`, or `p⁻¹` occurrence.

The result is deliberately phrased before `Monitor`.  It is therefore reusable by both the
ordinary/raw coupling and the revised post-occurrence-stop conversion below. -/
lemma d2sQueryImpl_support_trace_append
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st st' : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (a : (duplexSpongeChallengeOracle StmtIn U).Range q)
    (h : some (a, st') ∈ support ((d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run)) :
    st'.trace = st.trace ++ [⟨q, a⟩] := by
  rw [d2sQueryImpl] at h
  simp only [OptionT.run_bind, Option.elimM] at h
  rw [mem_support_bind_iff] at h
  obtain ⟨raw, hraw, hresult⟩ := h
  cases raw with
  | none => cases hresult
  | some result =>
      cases result with
      | none =>
          simp only [Option.elim_some, OptionT.run_failure] at hresult
          rw [mem_support_pure_iff] at hresult
          cases hresult
      | some pair =>
          rcases pair with ⟨a0, st0⟩
          simp only [Option.elim_some, OptionT.run_pure] at hresult
          rw [mem_support_pure_iff] at hresult
          injection hresult with hpair
          injection hpair with ha hs
          subst ha
          subst hs
          exact d2sQueryStep_support_trace_append
            (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) gImpl auxImpl q st hraw a st' rfl

/-- A retained `Monitor` stop from the executable stopped runner canonically determines the
revised post-occurrence record.  The reconstructed record has the same visible trace as the raw
post-state, so first-bad-event arguments never lose the final queried occurrence.

This lemma handles **Monitor** stops only.  A legacy raw `Install = conflict` still appears as
`underlyingAbort`; converting that branch to a post-occurrence record remains the responsibility
of the revised-install handlers, rather than being silently conflated here. -/
lemma d2sQueryImplStopped_support_stopped_postOccurrenceRecord
    [Fintype U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st' : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hr : D2SStoppedResult.stopped st' ∈ support
      (d2sQueryImplStopped
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        gImpl auxImpl q normal.state)) :
    ∃ (a : (duplexSpongeChallengeOracle StmtIn U).Range q)
      (hE : BadEventDS.E (normal.state.trace ++ [⟨q, a⟩])),
      (D2SPostOccurrenceStopRecord.trace
        (⟨q, a, hE⟩ : D2SPostOccurrenceStopRecord
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal)) = st'.trace := by
  obtain ⟨a, hraw⟩ := d2sQueryImplStopped_support_stopped_raw
    (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
    (pSpec := pSpec) (U := U) gImpl auxImpl q normal.state hr st' rfl
  have htrace := d2sQueryImpl_support_trace_append
    (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
    (pSpec := pSpec) (U := U) gImpl auxImpl q normal.state st' a hraw
  have hE := d2sQueryImplStopped_support_stopped_E
    (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn)
    (pSpec := pSpec) (U := U) gImpl auxImpl q normal.state hr st' rfl
  rw [htrace] at hE
  exact ⟨a, hE, htrace.symm⟩

end DuplexSpongeFS.ProverTransform
