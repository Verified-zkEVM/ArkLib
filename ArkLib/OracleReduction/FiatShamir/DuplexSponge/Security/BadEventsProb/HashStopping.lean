/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.HashCredit
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.MonitoredD2SQuery

/-!
# Hash stopping-time runner for Lemma 5.8

This module contains the structural `OracleComp` induction that lifts the one-step hash-miss
calculation in `HashCredit` to an arbitrary simulator computation.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U] {δ : ℕ}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

section HashStopping

variable [Fintype U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- The fixed eager `g` implementation captured by the sigma-side D2S simulator. -/
noncomputable def sigmaGImpl
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier) :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp) :=
  fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)

/-- The fixed auxiliary implementation captured by the sigma-side D2S simulator. -/
noncomputable def sigmaAuxImpl [SampleableType U] :
    QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp) :=
  fun aux => OptionT.lift
    ((ProverTransform.d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux)

/-- The raw combined lazy-simulator execution used by the hash stopping-time proof. -/
noncomputable def sigmaHashRun
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    ProbComp (Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))) :=
  ((simulateQ (lemma5_8CombinedImpl
    (ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (gImpl := sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
      (auxImpl := sigmaAuxImpl (U := U)))) oa).run).run
    (st, log)

/-- Proof-only first-bad execution of the same oracle program.  Unlike `sigmaHashRun`, a
monitor failure retains the post-occurrence state in `monitorStop` and prevents the continuation
from issuing another query.  This is the formal counterpart of paper-side `StopD2SQuery`; it is
not a public D2SQuery interface. -/
noncomputable def sigmaStoppedRun
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (Except
      (ProverTransform.D2SStopReason
        (ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
      (α × ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) :=
  ((simulateQ (ProverTransform.d2sStoppingCombinedImpl
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
    (sigmaAuxImpl (U := U))) oa).run st).run

/-- The stopped runner has the expected terminal form. -/
lemma sigmaStoppedRun_pure_eq
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type} (x : α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    sigmaStoppedRun (T_H := T_H) (T_P := T_P) k_g (pure x) st =
      pure (.ok (x, st)) := by
  unfold sigmaStoppedRun
  rw [simulateQ_pure]
  rfl

/-- One stopped query either propagates its stop reason or supplies its ordinary answer to the
continuation.  This is the sole structural equation needed for the forthcoming raw/stopped
prefix coupling. -/
lemma sigmaStoppedRun_query_bind_eq
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q) →
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    sigmaStoppedRun (T_H := T_H) (T_P := T_P) k_g
      (liftM (OracleSpec.query (Sum.inr q)) >>= mx) st =
      ((ProverTransform.d2sQueryImplStopping
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U)) q).run st).run >>= fun first =>
          match first with
          | .error stop => pure (.error stop)
          | .ok (a, st') => sigmaStoppedRun (T_H := T_H) (T_P := T_P) k_g
              (mx ((OracleSpec.query (Sum.inr q)).cont a)) st' := by
  unfold sigmaStoppedRun
  rw [simulateQ_query_bind, StateT.run_bind]
  simp only [OracleQuery.input_query, monadLift_self, ExceptT.run_bind,
    ProverTransform.d2sStoppingCombinedImpl]
  apply bind_congr
  intro first
  cases first <;> rfl

/-- Every ordinary terminal result of a stopped execution is an `E`-good state, provided its
initial state was good.  A monitor failure is represented only by `Except.error`, hence cannot
reach the continuation. -/
lemma sigmaStoppedRun_support_ok_not_E
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    {α : Type}
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hgood : ¬ E st.trace)
    {r : Except
      (ProverTransform.D2SStopReason
        (ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
      (α × ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support (sigmaStoppedRun (T_H := T_H) (T_P := T_P) k_g oa st)) :
    ∀ a st', r = Except.ok (a, st') → ¬ E st'.trace := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x =>
      rw [sigmaStoppedRun_pure_eq (T_H := T_H) (T_P := T_P) k_g x st] at hr
      rw [mem_support_pure_iff] at hr
      intro a st' hrEq
      have hpair : (a, st') = (x, st) := Except.ok.inj (hrEq.symm.trans hr)
      injection hpair with _ hs
      subst st'
      exact hgood
  | query_bind t mx ih =>
      match t with
      | Sum.inl e => exact PEmpty.elim e
      | Sum.inr q =>
          rw [sigmaStoppedRun_query_bind_eq (T_H := T_H) (T_P := T_P)
            k_g q mx st] at hr
          rw [mem_support_bind_iff] at hr
          obtain ⟨first, hfirst, hrest⟩ := hr
          cases first with
          | error stop =>
              rw [mem_support_pure_iff] at hrest
              intro a st' hrEq
              rw [hrest] at hrEq
              contradiction
          | ok pair =>
              rcases pair with ⟨answer, stMid⟩
              have hmid : ¬ E stMid.trace :=
                ProverTransform.d2sQueryImplStopping_support_ok_not_E
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                  (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                  (sigmaAuxImpl (U := U)) q st hfirst
              exact ih ((OracleSpec.query (Sum.inr q)).cont answer) stMid hmid hrest

/-- A multi-query `monitorStop` retains an E-bad post-occurrence state.  Together with
`sigmaStoppedRun_support_ok_not_E`, this is the reusable first-bad boundary: continuations are
good, and the first non-continuation monitor record contains the bad occurrence. -/
lemma sigmaStoppedRun_support_monitorStop_E
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    {α : Type}
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hgood : ¬ E st.trace)
    {r : Except
      (ProverTransform.D2SStopReason
        (ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
      (α × ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hr : r ∈ support (sigmaStoppedRun (T_H := T_H) (T_P := T_P) k_g oa st))
    (hrStop : r = Except.error (ProverTransform.D2SStopReason.monitorStop st')) :
    E st'.trace := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x =>
      rw [sigmaStoppedRun_pure_eq (T_H := T_H) (T_P := T_P) k_g x st] at hr
      rw [mem_support_pure_iff] at hr
      rw [hr] at hrStop
      contradiction
  | query_bind t mx ih =>
      match t with
      | Sum.inl e => exact PEmpty.elim e
      | Sum.inr q =>
          rw [sigmaStoppedRun_query_bind_eq (T_H := T_H) (T_P := T_P)
            k_g q mx st] at hr
          rw [mem_support_bind_iff] at hr
          obtain ⟨first, hfirst, hrest⟩ := hr
          cases first with
          | error stop =>
              rw [mem_support_pure_iff] at hrest
              rw [hrest] at hrStop
              have hstop : stop = ProverTransform.D2SStopReason.monitorStop st' :=
                Except.error.inj hrStop
              cases stop with
              | monitorStop stMid =>
                  have hstate : st' = stMid := ProverTransform.D2SStopReason.monitorStop.inj hstop.symm
                  subst st'
                  exact ProverTransform.d2sQueryImplStopping_support_monitorStop_E
                    (δ := δ) (T_H := T_H) (T_P := T_P)
                    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                    (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                    (sigmaAuxImpl (U := U)) q st hfirst
              | rawAbort stMid =>
                  cases hstop
          | ok pair =>
              rcases pair with ⟨answer, stMid⟩
              have hmid : ¬ E stMid.trace :=
                ProverTransform.d2sQueryImplStopping_support_ok_not_E
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                  (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                  (sigmaAuxImpl (U := U)) q st hfirst
              exact ih ((OracleSpec.query (Sum.inr q)).cont answer) stMid hmid hrest

/-- The relative bound for one atom, kept opaque while structurally recursing over an
`OracleComp`.  This avoids re-elaborating the full simulator executor in every induction
hypothesis. -/
def hashCreditBound
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C) : Prop :=
  Pr[ fun r => hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1 |
    sigmaHashRun (T_H := T_H) (T_P := T_P) k_g oa st log]
    ≤ Pr[ fun r => hashCreditTarget (T_H := T_H) (T_P := T_P) j i c r.2.1 |
      sigmaHashRun (T_H := T_H) (T_P := T_P) k_g oa st log] /
      capacitySpaceSize (U := U)

-- Keep the stopping invariant opaque to unification.  Its proofs explicitly unfold it only at
-- the one query step where the probability inequality is exposed.
attribute [irreducible] hashCreditBound

/-- The continuation invariant threaded through one D2S query in the hash stopping-time
runner.  A structure, rather than a reducible abbreviation, keeps its projection opaque while
the branch lemmas apply it; this avoids re-normalizing `sigmaHashRun` at every induction step. -/
structure HashCreditContinuation
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q) →
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C) : Prop where
  run : ∀ a
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)),
    TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ →
    (getBaseTrace st.trace).length ≤ j →
    hashCreditBound (T_H := T_H) (T_P := T_P) k_g (mx a) st log j i c

/-- A pure terminal state cannot contain the fixed atom while the incoming base trace has not
passed its index. -/
lemma hashCreditA_prob_pure_state_eq_zero
    {α : Type}
    (x : Option α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hlen : (getBaseTrace st.trace).length ≤ j) :
    Pr[ fun r : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) =>
      hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1 |
      (pure (x, (st, log)) : ProbComp (Option α ×
        (ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))))] = 0 := by
  apply probEvent_eq_zero
  intro r hr hcredit
  rw [mem_support_pure_iff] at hr
  subst r
  change hashCreditA (T_H := T_H) (T_P := T_P) j i c st at hcredit
  rcases hcredit with ⟨hj, _⟩
  omega

/-- A pure `OracleComp` has the expected terminal lazy-simulator execution. -/
lemma sigmaHashRun_pure_eq
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type} (x : α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (pure x) st log =
      pure (some x, (st, log)) := by
  unfold sigmaHashRun sigmaGImpl sigmaAuxImpl
  simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure]

set_option maxHeartbeats 400000 in
/-- The combined execution equation in the compact `sigmaHashRun` notation. -/
lemma sigmaHashRun_query_bind_rel_le_of_step
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q) →
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (A B : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) → Prop)
    (D : ℝ≥0∞)
    (hstep : ∀ first ∈ support
        ((ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
          (sigmaAuxImpl (U := U))
          q st).run),
      Pr[ A | (match first with
        | none => pure (none, (st, log))
        | some (a, st') => sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (mx a) st'
            (log ++ QueryLog.singleton (Sum.inr q) a))]
        ≤ Pr[ B | (match first with
          | none => pure (none, (st, log))
          | some (a, st') => sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (mx a) st'
              (log ++ QueryLog.singleton (Sum.inr q) a))] / D) :
    Pr[ A | sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
      (liftM (OracleSpec.query (Sum.inr q)) >>= mx) st log]
      ≤ Pr[ B | sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
        (liftM (OracleSpec.query (Sum.inr q)) >>= mx) st log] / D := by
  unfold sigmaHashRun at *
  exact combinedImpl_query_bind_rel_le_of_step
    (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
    (sigmaAuxImpl (U := U))
    q mx st log A B D hstep

set_option maxHeartbeats 400000 in
/-- A compact induction rule for `hashCreditBound`.  The continuation premise is itself stated
in the opaque stopping-time invariant, so applying an induction hypothesis does not re-elaborate
the full combined executor. -/
lemma hashCreditBound_query_bind_of_step
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q) →
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hnone : Pr[ fun r => hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1 |
      (pure (none, (st, log)) : ProbComp (Option α ×
        (ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))))]
      ≤ Pr[ fun r => hashCreditTarget (T_H := T_H) (T_P := T_P) j i c r.2.1 |
        (pure (none, (st, log)) : ProbComp (Option α ×
          (ProverTransform.D2SQueryState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
            QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))))] /
          capacitySpaceSize (U := U))
    (hsome : ∀ a st', some (a, st') ∈ support
      ((ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U))
        q st).run) →
      hashCreditBound (T_H := T_H) (T_P := T_P) k_g (mx a) st'
        (log ++ QueryLog.singleton (Sum.inr q) a) j i c) :
    hashCreditBound (T_H := T_H) (T_P := T_P) k_g
      (liftM (OracleSpec.query (Sum.inr q)) >>= mx) st log j i c := by
  unfold hashCreditBound
  apply sigmaHashRun_query_bind_rel_le_of_step k_g q mx st log
    (fun r => hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1)
    (fun r => hashCreditTarget (T_H := T_H) (T_P := T_P) j i c r.2.1)
    (capacitySpaceSize (U := U))
  intro first hfirst
  cases first with
  | none => exact hnone
  | some pair =>
      rcases pair with ⟨a, st'⟩
      unfold hashCreditBound at hsome
      exact hsome a st' hfirst

set_option maxHeartbeats 400000 in
/-- The exceptional fresh-hash crossing branch in compact runner notation. -/
lemma sigmaHashRun_hash_miss_credit_rel_le
    [Nonempty U] [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = none)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hlen : (getBaseTrace st.trace).length = j)
    {α : Type}
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range
      (Sum.inr (dsHashQuery stmt)) →
        OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    Pr[ fun r => hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1 |
      sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
        (liftM (OracleSpec.query (Sum.inr (dsHashQuery stmt))) >>= mx) st log]
      ≤ Pr[ fun r => hashCreditTarget (T_H := T_H) (T_P := T_P) j i c r.2.1 |
        sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
          (liftM (OracleSpec.query (Sum.inr (dsHashQuery stmt))) >>= mx) st log] /
        capacitySpaceSize (U := U) := by
  unfold sigmaHashRun
  exact hashMiss_combinedImpl_credit_rel_le
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g st hwf hLookup j i c hlen mx log

set_option maxHeartbeats 400000 in
/-- The hash-miss branch of the stopping-time runner.  A miss either creates the distinguished
`j`-th entry (handled by the one-step fresh-sample estimate) or leaves a strictly earlier prefix
for the continuation invariant. -/
lemma hashCreditBound_hash_miss_branch
    [Nonempty U] [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type} (stmt : StmtIn)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range
      (Sum.inr (dsHashQuery stmt)) →
        OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hlen : (getBaseTrace st.trace).length ≤ j)
    (hmiss : TraceTableOps.inlu st.trΔ.h stmt = none)
    (hrec : HashCreditContinuation (T_H := T_H) (T_P := T_P) k_g
      (dsHashQuery stmt) mx j i c) :
    hashCreditBound (T_H := T_H) (T_P := T_P) k_g
      (liftM (OracleSpec.query (Sum.inr (dsHashQuery stmt))) >>= mx) st log j i c := by
  by_cases hcross : (getBaseTrace st.trace).length = j
  · unfold hashCreditBound
    exact sigmaHashRun_hash_miss_credit_rel_le
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) k_g st hwf hmiss j i c hcross mx log
  · refine hashCreditBound_query_bind_of_step
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) k_g (dsHashQuery stmt) mx st log j i c ?_ ?_
    · rw [hashCreditA_prob_pure_state_eq_zero (T_H := T_H) (T_P := T_P)
        (x := none) (st := st) log j i c hlen]
      exact zero_le
    · intro a st' hfirst
      have hbase := d2sQueryImpl_hash_miss_support_baseTrace_eq
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U))
        st hwf hmiss hfirst rfl
      have hlt : (getBaseTrace st.trace).length < j := by omega
      have hlen' : (getBaseTrace st'.trace).length ≤ j := by
        rw [hbase, List.length_append]
        simp only [List.length_singleton]
        omega
      have hwf' := d2sQueryImpl_support_hash_wf
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U))
        (dsHashQuery stmt) st hwf hfirst a st' rfl
      exact hrec.run a st' (log ++ QueryLog.singleton (Sum.inr (dsHashQuery stmt)) a) hwf' hlen'

set_option maxHeartbeats 400000 in
/-- A hash-table hit adds no base entry, so the stopping invariant passes directly to its
continuation. -/
lemma hashCreditBound_hash_hit_branch
    [Nonempty U] [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type} (stmt : StmtIn)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range
      (Sum.inr (dsHashQuery stmt)) →
        OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hlen : (getBaseTrace st.trace).length ≤ j)
    {cap : Vector U SpongeSize.C}
    (hlookup : TraceTableOps.inlu st.trΔ.h stmt = some cap)
    (hrec : HashCreditContinuation (T_H := T_H) (T_P := T_P) k_g
      (dsHashQuery stmt) mx j i c) :
    hashCreditBound (T_H := T_H) (T_P := T_P) k_g
      (liftM (OracleSpec.query (Sum.inr (dsHashQuery stmt))) >>= mx) st log j i c := by
  refine hashCreditBound_query_bind_of_step
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g (dsHashQuery stmt) mx st log j i c ?_ ?_
  · rw [hashCreditA_prob_pure_state_eq_zero (T_H := T_H) (T_P := T_P)
      (x := none) (st := st) log j i c hlen]
    exact zero_le
  · intro a st' hfirst
    have hbase := d2sQueryImpl_hash_hit_support_baseTrace_eq
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ)
      (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
      (sigmaAuxImpl (U := U))
      st hlookup hfirst rfl
    have hlen' : (getBaseTrace st'.trace).length ≤ j := by
      rw [hbase]
      exact hlen
    have hwf' := d2sQueryImpl_support_hash_wf
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ)
      (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
      (sigmaAuxImpl (U := U))
      (dsHashQuery stmt) st hwf hfirst a st' rfl
    exact hrec.run a st' (log ++ QueryLog.singleton (Sum.inr (dsHashQuery stmt)) a) hwf' hlen'

set_option maxHeartbeats 400000 in
/-- A forward-permutation query either remains before the distinguished base index and recurs,
or crosses it, in which case the fixed hash atom is impossible. -/
lemma hashCreditBound_perm_fwd_branch
    [Nonempty U] [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type} (sIn : CanonicalSpongeState U)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range
      (Sum.inr (dsPermQuery sIn)) →
        OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hlen : (getBaseTrace st.trace).length ≤ j)
    (hrec : HashCreditContinuation (T_H := T_H) (T_P := T_P) k_g
      (dsPermQuery sIn) mx j i c) :
    hashCreditBound (T_H := T_H) (T_P := T_P) k_g
      (liftM (OracleSpec.query (Sum.inr (dsPermQuery sIn))) >>= mx) st log j i c := by
  refine hashCreditBound_query_bind_of_step
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g (dsPermQuery sIn) mx st log j i c ?_ ?_
  · rw [hashCreditA_prob_pure_state_eq_zero (T_H := T_H) (T_P := T_P)
      (x := none) (st := st) log j i c hlen]
    exact zero_le
  · intro sOut' st' hfirst
    have hstep := d2sQueryImpl_support_baseTrace_length_le_succ
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ)
      (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
      (sigmaAuxImpl (U := U))
      (dsPermQuery sIn) st hfirst rfl
    by_cases hlen' : (getBaseTrace st'.trace).length ≤ j
    · have hwf' := d2sQueryImpl_support_hash_wf
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U))
        (dsPermQuery sIn) st hwf hfirst sOut' st' rfl
      exact hrec.run sOut' (st')
        (log ++ QueryLog.singleton (Sum.inr (dsPermQuery sIn)) sOut') hwf' hlen'
    · have hcross : (getBaseTrace st.trace).length = j := by omega
      have hj' : j < (getBaseTrace st'.trace).length := by omega
      have hnot := d2sQueryImpl_support_hashCreditA_false_of_perm_at_base_length
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U))
        sIn st hfirst rfl (i := i) (c := c) hcross
      unfold hashCreditBound sigmaHashRun
      have hzero := combinedImpl_hashCreditA_prob_eq_zero_of_index_lt
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U)) st'
        (log ++ QueryLog.singleton (Sum.inr (dsPermQuery sIn)) sOut')
        (j := j) i c hj' hnot (oa := mx sOut')
      rw [hzero]
      exact zero_le

set_option maxHeartbeats 400000 in
-- The inverse branch performs the same crossed-index analysis as the forward branch.
/-- The inverse-permutation analogue of `hashCreditBound_perm_fwd_branch`. -/
lemma hashCreditBound_perm_bwd_branch
    [Nonempty U] [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type} (sOut : CanonicalSpongeState U)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range
      (Sum.inr (dsPermInvQuery sOut)) →
        OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hlen : (getBaseTrace st.trace).length ≤ j)
    (hrec : HashCreditContinuation (T_H := T_H) (T_P := T_P) k_g
      (dsPermInvQuery sOut) mx j i c) :
    hashCreditBound (T_H := T_H) (T_P := T_P) k_g
      (liftM (OracleSpec.query (Sum.inr (dsPermInvQuery sOut))) >>= mx) st log j i c := by
  refine hashCreditBound_query_bind_of_step
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g (dsPermInvQuery sOut) mx st log j i c ?_ ?_
  · rw [hashCreditA_prob_pure_state_eq_zero (T_H := T_H) (T_P := T_P)
      (x := none) (st := st) log j i c hlen]
    exact zero_le
  · intro sIn' st' hfirst
    have hstep := d2sQueryImpl_support_baseTrace_length_le_succ
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ)
      (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
      (sigmaAuxImpl (U := U))
      (dsPermInvQuery sOut) st hfirst rfl
    by_cases hlen' : (getBaseTrace st'.trace).length ≤ j
    · have hwf' := d2sQueryImpl_support_hash_wf
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U))
        (dsPermInvQuery sOut) st hwf hfirst sIn' st' rfl
      exact hrec.run sIn' st'
        (log ++ QueryLog.singleton (Sum.inr (dsPermInvQuery sOut)) sIn') hwf' hlen'
    · have hcross : (getBaseTrace st.trace).length = j := by omega
      have hj' : j < (getBaseTrace st'.trace).length := by omega
      have hnot := d2sQueryImpl_support_hashCreditA_false_of_permInv_at_base_length
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U))
        sOut st hfirst rfl (i := i) (c := c) hcross
      unfold hashCreditBound sigmaHashRun
      have hzero := combinedImpl_hashCreditA_prob_eq_zero_of_index_lt
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U)) st'
        (log ++ QueryLog.singleton (Sum.inr (dsPermInvQuery sOut)) sIn')
        (j := j) i c hj' hnot (oa := mx sIn')
      rw [hzero]
      exact zero_le

set_option maxHeartbeats 400000 in
-- The query-family work is factored into separate lemmas so the outer `OracleComp` induction
-- only transports the named continuation invariant rather than repeatedly normalizing the full
-- simulator execution.
/-- The complete lazy-simulator stopping-time bound for one fixed hash-collision atom. -/
lemma combinedImpl_hashCredit_rel_le_of_base_length_le
    [Nonempty U] [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hlen : (getBaseTrace st.trace).length ≤ j) :
    hashCreditBound (T_H := T_H) (T_P := T_P) k_g oa st log j i c := by
  classical
  induction oa using OracleComp.inductionOn generalizing st log with
  | pure x =>
      unfold hashCreditBound
      rw [sigmaHashRun_pure_eq (T_H := T_H) (T_P := T_P) k_g x st log]
      rw [hashCreditA_prob_pure_state_eq_zero (T_H := T_H) (T_P := T_P)
        (x := some x) (st := st) log j i c hlen]
      exact zero_le
  | query_bind t mx ih =>
      match t with
      | Sum.inl e => exact PEmpty.elim e
      | Sum.inr q =>
          rcases q with stmt | (sIn | sOut)
          · by_cases hmiss : TraceTableOps.inlu st.trΔ.h stmt = none
            · refine hashCreditBound_hash_miss_branch
                (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ) k_g stmt mx st log hwf j i c hlen hmiss ?_
              refine ⟨?_⟩
              intro a st' log' hwf' hlen'
              exact ih a st' log' hwf' hlen'
            · cases hlookup : TraceTableOps.inlu st.trΔ.h stmt with
              | none => exact (hmiss hlookup).elim
              | some cap =>
                  refine hashCreditBound_hash_hit_branch
                    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                    (U := U) (δ := δ) k_g stmt mx st log hwf j i c hlen hlookup ?_
                  refine ⟨?_⟩
                  intro a st' log' hwf' hlen'
                  exact ih a st' log' hwf' hlen'
          · refine hashCreditBound_perm_fwd_branch
              (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) k_g sIn mx st log hwf j i c hlen ?_
            refine ⟨?_⟩
            intro sOut' st' log' hwf' hlen'
            exact ih sOut' st' log' hwf' hlen'
          · refine hashCreditBound_perm_bwd_branch
              (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) k_g sOut mx st log hwf j i c hlen ?_
            refine ⟨?_⟩
            intro sIn' st' log' hwf' hlen'
            exact ih sIn' st' log' hwf' hlen'

set_option maxHeartbeats 400000 in
-- This structural equality unfolds one query layer on both sides and therefore needs the same
-- local elaboration budget as the stopping-time runner.
/-- One wrapped D2S query is insensitive to the incoming wrapper-log prefix. -/
lemma sigmaWrappedDSImpl_run_log_append
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (logPrefix : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    ((lemma5_8WrappedDSImpl
      (ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U))) q).run).run (st, logPrefix) =
      (fun r => (r.1, (r.2.1, logPrefix ++ r.2.2))) <$>
        ((lemma5_8WrappedDSImpl
          (ProverTransform.d2sQueryImpl
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
            (sigmaAuxImpl (U := U))) q).run).run (st, []) := by
  rw [wrappedDSImpl_run_eq_d2sQuery_bind]
  rw [wrappedDSImpl_run_eq_d2sQuery_bind]
  rw [map_bind]
  apply bind_congr
  intro first
  cases first with
  | none =>
      rw [map_pure]
      rw [List.append_nil]
  | some pair =>
      rcases pair with ⟨a, st'⟩
      rw [map_pure]
      simp only [List.nil_append]

/-- Resetting the external wrapper log does not change D2S execution.  It only factors the final
log into its old prefix and the new suffix. -/
lemma sigmaHashRun_log_append_eq
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (logPrefix : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    sigmaHashRun (T_H := T_H) (T_P := T_P) k_g oa st logPrefix =
      (fun r => (r.1, (r.2.1, logPrefix ++ r.2.2))) <$>
        sigmaHashRun (T_H := T_H) (T_P := T_P) k_g oa st [] := by
  induction oa using OracleComp.inductionOn generalizing st logPrefix with
  | pure x =>
      rw [sigmaHashRun_pure_eq (T_H := T_H) (T_P := T_P) k_g x st logPrefix]
      rw [sigmaHashRun_pure_eq (T_H := T_H) (T_P := T_P) k_g x st []]
      simp only [map_pure]
      rw [List.append_nil]
  | query_bind t mx ih =>
      match t with
      | Sum.inl e => exact PEmpty.elim e
      | Sum.inr q =>
          unfold sigmaHashRun
          rw [combinedImpl_run_query_bind_eq]
          rw [combinedImpl_run_query_bind_eq]
          rw [sigmaWrappedDSImpl_run_log_append
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) k_g q st logPrefix]
          rw [wrappedDSImpl_run_eq_d2sQuery_bind]
          simp only [map_bind, bind_assoc, bind_map_left]
          apply bind_congr
          intro first
          cases first with
          | none =>
              simp only [pure_bind, map_pure, List.append_nil]
          | some pair =>
              rcases pair with ⟨a, st'⟩
              change sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (mx a) st'
                  (logPrefix ++ QueryLog.singleton (Sum.inr q) a) =
                (fun r => (r.1, (r.2.1, logPrefix ++ r.2.2))) <$>
                  sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (mx a) st'
                    (QueryLog.singleton (Sum.inr q) a)
              calc
                sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (mx a) st'
                    (logPrefix ++ QueryLog.singleton (Sum.inr q) a) =
                  (fun r => (r.1, (r.2.1,
                    (logPrefix ++ QueryLog.singleton (Sum.inr q) a) ++ r.2.2))) <$>
                    sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (mx a) st' [] :=
                  ih a st' (logPrefix ++ QueryLog.singleton (Sum.inr q) a)
                _ = (fun r => (r.1, (r.2.1, logPrefix ++ r.2.2))) <$>
                    sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (mx a) st'
                      (QueryLog.singleton (Sum.inr q) a) := by
                  rw [ih a st' (QueryLog.singleton (Sum.inr q) a)]
                  simp only [Functor.map_map]
                  congr 1
                  funext r
                  rcases r with ⟨answer, rest⟩
                  rcases rest with ⟨st'', log'⟩
                  rw [List.append_assoc]

/-- The raw lazy-simulator runner preserves the ordinary sequential semantics of `OracleComp`.
The continuation sees the same D2S state and the accumulated wrapper log. -/
lemma sigmaHashRun_bind_eq
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α β : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (f : α → OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) β)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (oa >>= f) st log =
      sigmaHashRun (T_H := T_H) (T_P := T_P) k_g oa st log >>= fun first =>
        match first with
        | (none, (st', log')) => pure (none, (st', log'))
        | (some a, (st', log')) =>
            sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (f a) st' log' := by
  unfold sigmaHashRun
  rw [simulateQ_bind]
  rw [OptionT.run_bind]
  rw [Option.elimM]
  rw [StateT.run_bind]
  apply bind_congr
  intro first
  rcases first with ⟨answer, rest⟩
  rcases rest with ⟨st', log'⟩
  cases answer <;> rfl

/-- Every raw simulator execution extends its incoming base trace.  Redundant D2S occurrences
contribute the empty suffix; retained representatives contribute a singleton, and the induction
only needs their concatenation.  This is the trace-side invariant needed to transport a first-bad
witness from a raw final state back to the stopped prefix where it first appeared. -/
lemma sigmaHashRun_support_baseTrace_append
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    {r : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))}
    (hr : r ∈ support (sigmaHashRun (T_H := T_H) (T_P := T_P) k_g oa st log)) :
    ∃ extra : QueryLog (duplexSpongeChallengeOracle StmtIn U),
      getBaseTrace r.2.1.trace = getBaseTrace st.trace ++ extra := by
  classical
  induction oa using OracleComp.inductionOn generalizing st log r with
  | pure x =>
      rw [sigmaHashRun_pure_eq (T_H := T_H) (T_P := T_P) k_g x st log] at hr
      rw [mem_support_pure_iff] at hr
      subst r
      exact ⟨[], by simp⟩
  | query_bind t mx ih =>
      match t with
      | Sum.inl e => exact PEmpty.elim e
      | Sum.inr q =>
          unfold sigmaHashRun at hr
          rw [combinedImpl_run_query_bind_eq, wrappedDSImpl_run_eq_d2sQuery_bind] at hr
          rw [mem_support_bind_iff] at hr
          obtain ⟨first, hfirst, hrest⟩ := hr
          rw [mem_support_bind_iff] at hfirst
          obtain ⟨raw, hraw, hfirstEq⟩ := hfirst
          cases raw with
          | none =>
              rw [mem_support_pure_iff] at hfirstEq
              subst first
              rw [mem_support_pure_iff] at hrest
              subst r
              exact ⟨[], by simp⟩
          | some pair =>
              rcases pair with ⟨a, stMid⟩
              rw [mem_support_pure_iff] at hfirstEq
              subst first
              obtain ⟨extra₁, hbase₁⟩ := d2sQueryImpl_support_baseTrace_append
                (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ)
                (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                (sigmaAuxImpl (U := U)) q st hraw rfl
              obtain ⟨extra₂, hbase₂⟩ := ih a stMid
                (log ++ QueryLog.singleton (Sum.inr q) a) hrest
              refine ⟨extra₁ ++ extra₂, ?_⟩
              rw [hbase₂, hbase₁, List.append_assoc]

/-- Forgetting the wrapper log makes a fixed simulator run independent of its initial log
prefix.  This is the state part of `sigmaHashRun_log_append_eq`. -/
lemma sigmaHashRun_stateMarginal_log_independent
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (logPrefix : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    (fun r => r.2.1) <$> sigmaHashRun (T_H := T_H) (T_P := T_P) k_g oa st logPrefix =
      (fun r => r.2.1) <$> sigmaHashRun (T_H := T_H) (T_P := T_P) k_g oa st [] := by
  rw [sigmaHashRun_log_append_eq
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g oa st logPrefix]
  simp only [Functor.map_map]

/-- Fixed-`g` two-phase simulator execution.  It keeps the final D2S state together with the
separate prover and verifier wrapper logs used by `lemma5_8ProjectedTraceDistAbortable`. -/
noncomputable def sigmaTwoPhaseRun
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :=
  sigmaHashRun (T_H := T_H) (T_P := T_P) k_g maliciousProver default [] >>= fun proverResult =>
    match proverResult with
    | (none, (stP, trP)) => pure (stP, trP, [])
    | (some ⟨stmtIn, proof⟩, (stP, trP)) =>
        sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
          (runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof) stP [] >>= fun verifierResult =>
        pure (verifierResult.2.1, trP, verifierResult.2.2)

/-- Projecting the two retained wrapper logs in `sigmaTwoPhaseRun` is exactly the fixed-`g`
instance of the public abortable trace experiment. -/
lemma sigmaTwoPhaseRun_projected_eq
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    (fun r =>
      (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) r.2.1,
        lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) r.2.2)) <$>
      sigmaTwoPhaseRun (T_H := T_H) (T_P := T_P) k_g V maliciousProver =
      lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (δ := δ) (init := pure default)
        (spongeImpl := ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (gImpl := sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
          (auxImpl := sigmaAuxImpl (U := U))) V maliciousProver := by
  unfold sigmaTwoPhaseRun lemma5_8ProjectedTraceDistAbortable
  rw [pure_bind]
  rw [map_bind]
  apply bind_congr
  intro proverResult
  rcases proverResult with ⟨proverOut, rest⟩
  rcases rest with ⟨stP, trP⟩
  cases proverOut with
  | none =>
      rw [map_pure]
      rfl
  | some stmtProof =>
      rcases stmtProof with ⟨stmtIn, proof⟩
      rw [map_bind]
      apply bind_congr
      intro verifierResult
      rcases verifierResult with ⟨verifierOut, verifierRest⟩
      rcases verifierRest with ⟨stV, trV⟩
      rw [map_pure]

/-- Every two-phase raw outcome couples its final simulator trace to the concatenation of the
two projected public logs. -/
lemma sigmaTwoPhaseRun_support_trace_eq
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (r : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
      QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (hr : r ∈ support
      (sigmaTwoPhaseRun (T_H := T_H) (T_P := T_P) k_g V maliciousProver)) :
    r.1.trace =
      lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) r.2.1 ++
        lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) r.2.2 := by
  classical
  unfold sigmaTwoPhaseRun at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨proverResult, hpr, hr⟩ := hr
  rcases proverResult with ⟨proverOut, proverRest⟩
  rcases proverRest with ⟨stP, trP⟩
  have hP : stP.trace = lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP := by
    unfold sigmaHashRun at hpr
    exact sigma_prover_run_support_d2sTrace_bridge
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) k_g maliciousProver
      (proverResult := (proverOut, (stP, trP))) hpr
  cases proverOut with
  | none =>
      rw [mem_support_pure_iff] at hr
      subst r
      change stP.trace = lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP ++ []
      rw [List.append_nil]
      exact hP
  | some stmtProof =>
      rcases stmtProof with ⟨stmtIn, proof⟩
      rw [mem_support_bind_iff] at hr
      obtain ⟨verifierResult, hvr, hr⟩ := hr
      rw [mem_support_pure_iff] at hr
      rcases verifierResult with ⟨verifierOut, verifierRest⟩
      rcases verifierRest with ⟨stV, trV⟩
      subst r
      have hV : stV.trace = stP.trace ++
          lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trV := by
        unfold sigmaHashRun at hvr
        exact sigma_verifier_run_support_d2sTrace_bridge
          (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) k_g stP
          (oa := runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof)
          (verifierResult := (verifierOut, (stV, trV))) hvr
      rw [hV, hP]

/-- Keeping only the final D2S state turns the fresh-log two-phase runner into the single
continuous execution of `lemma5_8TraceExperiment`. -/
lemma sigmaTwoPhaseRun_state_eq_continuous
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    (fun r => r.1) <$>
      sigmaTwoPhaseRun (T_H := T_H) (T_P := T_P) k_g V maliciousProver =
      (fun r => r.2.1) <$>
        sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
          (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default [] := by
  unfold sigmaTwoPhaseRun
  rw [map_bind]
  unfold lemma5_8TraceExperiment
  rw [sigmaHashRun_bind_eq]
  rw [map_bind]
  apply bind_congr
  intro proverResult
  rcases proverResult with ⟨proverOut, proverRest⟩
  rcases proverRest with ⟨stP, trP⟩
  cases proverOut with
  | none =>
      simp only [map_pure]
  | some stmtProof =>
      rcases stmtProof with ⟨stmtIn, proof⟩
      simp only [map_bind, map_pure]
      rw [bind_pure_comp]
      exact (sigmaHashRun_stateMarginal_log_independent
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) k_g
        (runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof) stP trP).symm

/-- Fixed-`g` phase bridge at probability level.  The public abortable experiment evaluates its
event on the concatenation of projected phase logs, while the continuous runner evaluates the
same event on the final internal trace. -/
lemma probEvent_sigmaProjectedTrace_eq_continuousRunner
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (Q : QueryLog (duplexSpongeChallengeOracle StmtIn U) → Prop) :
    Pr[ fun tr => Q (tr.1 ++ tr.2) |
      lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (δ := δ) (init := pure default)
        (spongeImpl := ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (gImpl := sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
          (auxImpl := sigmaAuxImpl (U := U))) V maliciousProver] =
      Pr[ fun r => Q r.2.1.trace |
        sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
          (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] := by
  have hstate := sigmaTwoPhaseRun_state_eq_continuous
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) k_g V maliciousProver
  have htrace :
      (fun r => r.1.trace) <$>
        sigmaTwoPhaseRun (T_H := T_H) (T_P := T_P) k_g V maliciousProver =
      (fun r => r.2.1.trace) <$>
        sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
          (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default [] := by
    have h := congrArg (fun comp =>
      (fun st : ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) => st.trace) <$> comp) hstate
    simp only [Functor.map_map] at h
    exact h
  calc
    Pr[ fun tr => Q (tr.1 ++ tr.2) |
      lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (δ := δ) (init := pure default)
        (spongeImpl := ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (gImpl := sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
          (auxImpl := sigmaAuxImpl (U := U))) V maliciousProver] =
      Pr[ (fun tr => Q (tr.1 ++ tr.2)) ∘
        (fun r =>
          (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) r.2.1,
            lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) r.2.2)) |
        sigmaTwoPhaseRun (T_H := T_H) (T_P := T_P) k_g V maliciousProver] := by
          rw [← sigmaTwoPhaseRun_projected_eq
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ) k_g V maliciousProver]
          rw [probEvent_map]
    _ = Pr[ (fun r => Q r.1.trace) |
        sigmaTwoPhaseRun (T_H := T_H) (T_P := T_P) k_g V maliciousProver] := by
          apply probEvent_congr' (fun r hr => ?_) rfl
          change Q
              (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) r.2.1 ++
                lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) r.2.2) ↔
            Q r.1.trace
          rw [← sigmaTwoPhaseRun_support_trace_eq
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ) k_g V maliciousProver r hr]
    _ = Pr[ Q | (fun r => r.1.trace) <$>
        sigmaTwoPhaseRun (T_H := T_H) (T_P := T_P) k_g V maliciousProver] := by
          rw [probEvent_map]
          rfl
    _ = Pr[ Q | (fun r => r.2.1.trace) <$>
        sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
          (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] := by
          rw [htrace]
    _ = Pr[ fun r => Q r.2.1.trace |
        sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
          (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] := by
          rw [probEvent_map]
          rfl

end HashStopping

end BadEventDS

end DuplexSpongeFS
