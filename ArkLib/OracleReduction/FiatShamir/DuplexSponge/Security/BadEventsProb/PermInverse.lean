/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Infrastructure

/-!
# Inverse permutation collision bounds for Lemma 5.8
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))

variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : CodecCore pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

section PerIndexCollisionBounds

variable [Fintype U] [Nonempty U]

/-! #### Forward-permutation output-capacity duplication (E_p) reductioninv (inverse-permutation range-capacity duplication)

Symmetric to E_p: \`E_pinv_at·j\` fires when the *range* (pre-image) capacity of the bwd-perm entry
at \`j\` duplicates a capacity — covered by ≤ 2j prior collisions plus one self collision (its own
domain capacity equals its range capacity — the \`j' = j\` case of the fifth disjunct). -/
section ForwardPermutationCollisionReductioninv

/-! The capacity readout and eager-trace uniqueness facts used here are shared
between the forward and inverse reductions; see CapacityTargets and PermTraceFacts. -/

/-- Sponge \`E_pinv\` bound, refined to the earliest bad index. -/
lemma lemma5_8_sponge_E_pinv_first_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_pinv_at (tr.1 ++ tr.2) j |
        lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
          (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
          (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U) := by
  let exp := lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
    (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
    (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver
  change Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_pinv_at (tr.1 ++ tr.2) j | exp]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U)
  calc
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_pinv_at (tr.1 ++ tr.2) j | exp]
      ≤ Pr[ fun tr =>
          E_first_at (tr.1 ++ tr.2) j ∧ permBwdFreshHitAt (getBaseTrace (tr.1 ++ tr.2)) j |
          exp] := by
      apply probEvent_mono
      intro tr _ h
      rcases h with ⟨hFirst, hEp⟩
      exact ⟨hFirst, E_pinv_at_imp_permBwdFreshHitAt _ _ hEp⟩
    _ ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U) :=
      sponge_permBwdFreshHit_first_noReplacement_contract
        (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver j

end ForwardPermutationCollisionReductioninv

end PerIndexCollisionBounds

end BadEventDS

end DuplexSpongeFS
