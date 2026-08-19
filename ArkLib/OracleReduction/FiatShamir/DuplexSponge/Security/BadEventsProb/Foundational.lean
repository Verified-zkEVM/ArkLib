/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.FiniteTarget
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.CapacityTargets
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Representatives
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermTraceFacts
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermNoReplacement
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.HashStopping
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermInverseCredit

/-!
# Foundational probability bridges for Lemma 5.8

This module isolates the remaining non-local probability/semantic bridges used by the
paper-facing bad-event bounds.  The downstream files `Hash`, `PermForward`, and `PermInverse`
should depend on named, reusable bridge statements rather than carrying anonymous gaps in the
middle of the Lemma 5.8 reductions.

The three statements below are intentionally phrased at the current DSFS trace-distribution
boundary:

* the sigma hash lazy-sampling lift from the local `d2sHandle*` handler lemmas in
  `Representatives` to the full `lemma5_8SigmaTraceDist`;
* the remaining sigma forward-permutation lazy-sampling bridge; and
* the proved sigma inverse-permutation bridge.

They are simulator bridges, not paper-specific union-bound algebra.  The remaining gap should
proceed by a generic simulator induction that extracts the fresh capacity sample.
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

section FoundationalBridges

variable [Fintype U] [Nonempty U]

/-- The default D2S simulator state has a wellformed hash table. -/
lemma default_d2s_hash_wf :
    TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U)
      (default : ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)).trΔ := by
  change TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (U := U)
    (⟨TraceTableOps.empty, TraceTableOps.empty⟩ :
      TraceNabla T_H T_P StmtIn U)
  exact TraceHashTableWellformed.empty

/-- Foundational sigma hash atom freshness bridge.

This is the global lift of the local `d2sHandleHashQuery_miss_sigma_atom_le` handler fact through
the complete `lemma5_8SigmaTraceDist` execution. -/
lemma foundational_sigma_hashTargetAtom_contract
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C) :
    Pr[ fun tr =>
        hashOutCapAt (getBaseTrace (tr.1 ++ tr.2)) j = some c ∧
          priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ Pr[ fun tr =>
          priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
          lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
        / capacitySpaceSize (U := U) := by
  classical
  let rest : (D_Sigma (U := U) StmtIn pSpec δ).Carrier →
      ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
        QueryLog (duplexSpongeChallengeOracle StmtIn U)) := fun k_g =>
    lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) (init := pure default)
      (spongeImpl := ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (gImpl := sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) k_g)
        (auxImpl := sigmaAuxImpl (U := U))) V maliciousProver
  change Pr[ fun tr =>
      hashOutCapAt (getBaseTrace (tr.1 ++ tr.2)) j = some c ∧
        priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
      (D_Sigma (U := U) StmtIn pSpec δ).sample >>= rest]
    ≤ Pr[ fun tr =>
        priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
        (D_Sigma (U := U) StmtIn pSpec δ).sample >>= rest] /
      capacitySpaceSize (U := U)
  refine probEvent_bind_rel_div_le
    (D_Sigma (U := U) StmtIn pSpec δ).sample rest
    (fun tr =>
      hashOutCapAt (getBaseTrace (tr.1 ++ tr.2)) j = some c ∧
        priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c)
    (fun tr =>
      priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c)
    (capacitySpaceSize (U := U)) ?_
  intro k_g _
  have hlen :
      (getBaseTrace
        (default : ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)).trace).length ≤ j := by
    change 0 ≤ j
    omega
  have hRunner := combinedImpl_hashCredit_rel_le_of_base_length_le
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g
    (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver)
    default [] (default_d2s_hash_wf
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ)) j i c hlen
  unfold hashCreditBound at hRunner
  have hAtom := probEvent_sigmaProjectedTrace_eq_continuousRunner
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) k_g V maliciousProver
    (fun tr =>
      hashOutCapAt (getBaseTrace tr) j = some c ∧
        priorCapacityTargetAt (getBaseTrace tr) j i = some c)
  have hTarget := probEvent_sigmaProjectedTrace_eq_continuousRunner
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) k_g V maliciousProver
    (fun tr => priorCapacityTargetAt (getBaseTrace tr) j i = some c)
  have hNum :
      Pr[ fun tr =>
        hashOutCapAt (getBaseTrace (tr.1 ++ tr.2)) j = some c ∧
          priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
        lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) (δ := δ) (init := pure default)
          (spongeImpl := ProverTransform.d2sQueryImpl
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (gImpl := sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) k_g)
            (auxImpl := sigmaAuxImpl (U := U))) V maliciousProver] =
        Pr[ fun r => hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1 |
          sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
            (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
              (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] := by
    calc
      Pr[ fun tr =>
        hashOutCapAt (getBaseTrace (tr.1 ++ tr.2)) j = some c ∧
          priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
        lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) (δ := δ) (init := pure default)
          (spongeImpl := ProverTransform.d2sQueryImpl
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (gImpl := sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) k_g)
            (auxImpl := sigmaAuxImpl (U := U))) V maliciousProver] =
          Pr[ fun r =>
            hashOutCapAt (getBaseTrace r.2.1.trace) j = some c ∧
              priorCapacityTargetAt (getBaseTrace r.2.1.trace) j i = some c |
            sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
              (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
                (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] := hAtom
      _ = Pr[ fun r => hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1 |
          sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
            (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
              (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] := by
            apply probEvent_congr' (fun r _ => ?_) rfl
            exact (hashCreditA_iff_hash_atom
              (T_H := T_H) (T_P := T_P) (j := j) (i := i) (c := c) r.2.1).symm
  have hDen :
      Pr[ fun tr => priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
        lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) (δ := δ) (init := pure default)
          (spongeImpl := ProverTransform.d2sQueryImpl
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (gImpl := sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) k_g)
            (auxImpl := sigmaAuxImpl (U := U))) V maliciousProver] =
        Pr[ fun r => hashCreditTarget (T_H := T_H) (T_P := T_P) j i c r.2.1 |
          sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
            (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
              (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] := by
    calc
      Pr[ fun tr => priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
        lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) (δ := δ) (init := pure default)
          (spongeImpl := ProverTransform.d2sQueryImpl
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (gImpl := sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) k_g)
            (auxImpl := sigmaAuxImpl (U := U))) V maliciousProver] =
          Pr[ fun r => priorCapacityTargetAt (getBaseTrace r.2.1.trace) j i = some c |
            sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
              (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
                (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] := hTarget
      _ = Pr[ fun r => hashCreditTarget (T_H := T_H) (T_P := T_P) j i c r.2.1 |
          sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
            (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
              (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] := by
            rfl
  calc
    Pr[ fun tr =>
      hashOutCapAt (getBaseTrace (tr.1 ++ tr.2)) j = some c ∧
        priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
      lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (δ := δ) (init := pure default)
        (spongeImpl := ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (gImpl := sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) k_g)
          (auxImpl := sigmaAuxImpl (U := U))) V maliciousProver] =
        Pr[ fun r => hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1 |
          sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
            (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
              (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] := hNum
    _ ≤ Pr[ fun r => hashCreditTarget (T_H := T_H) (T_P := T_P) j i c r.2.1 |
          sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
            (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
              (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] /
          capacitySpaceSize (U := U) := hRunner
    _ = Pr[ fun tr => priorCapacityTargetAt (getBaseTrace (tr.1 ++ tr.2)) j i = some c |
        lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) (δ := δ) (init := pure default)
          (spongeImpl := ProverTransform.d2sQueryImpl
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (gImpl := sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) k_g)
            (auxImpl := sigmaAuxImpl (U := U))) V maliciousProver] /
          capacitySpaceSize (U := U) := by
            rw [hDen]

/-- Foundational sigma forward-permutation lazy-sampling bridge, stated at the first bad base
position exactly as Lemma 5.8 uses it.  Earlier malformed/redundant raw occurrences are outside
this stopped-prefix event and must not be treated as fresh materializations at `j`. -/
lemma foundational_sigma_permFwdFreshHit_contract
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧
        permFwdFreshHitAt (getBaseTrace (tr.1 ++ tr.2)) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U) := by
  sorry

/-- Foundational sigma inverse-permutation lazy-sampling bridge. -/
lemma foundational_sigma_permBwdFreshHit_contract
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => permBwdFreshHitAt (getBaseTrace (tr.1 ++ tr.2)) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U) := by
  classical
  rw [lemma5_8SigmaTraceDist]
  apply probEvent_bind_le_of_forall_le
  intro k_g _
  have hbridge := probEvent_sigmaProjectedTrace_eq_continuousRunner
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) k_g V maliciousProver
    (fun trace => permBwdFreshHitAt (getBaseTrace trace) j)
  unfold sigmaGImpl sigmaAuxImpl at hbridge
  rw [hbridge]
  have hbound := permBwdCreditBound_of_base_length_le
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g
    (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver)
    (default : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) [] j (by
        change 0 ≤ j
        omega)
  unfold permBwdCreditBound at hbound
  calc
    Pr[ fun r => permBwdFreshHitAt (getBaseTrace r.2.1.trace) j |
      sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
        (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
          (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []]
        = Pr[ fun r => permBwdCredit (T_H := T_H) (T_P := T_P) j r.2.1 |
          sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
            (lemma5_8TraceExperiment (StmtIn := StmtIn) (StmtOut := StmtOut)
              (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver) default []] := by
            apply probEvent_congr'
            · intro r _
              exact (permBwdCredit_iff_freshHit (T_H := T_H) (T_P := T_P)
                (j := j) r.2.1).symm
            · rfl
    _ ≤ ((2 * j + 1 : ℕ) : ℝ≥0∞) / capacitySpaceSize (U := U) := hbound
    _ = (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U) := by
      norm_num

end FoundationalBridges

end BadEventDS

end DuplexSpongeFS
