/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Alexander Hicks
-/

import ArkLibTest.ProofSystem.RingSwitching.Conformance.BiniusComposition
import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.General

/-!
# Unrolled FRI-Binius regression checks

The checks use the `GF(16)/GF(2)` instance of the separate-sum-check composition test: two packed
variables, one retained variable, the nonconstant source `X₀ + X₂` and its honest first oracle.

* Both compositions are stated for the same input relation.
* The honest source is accepted with probability one.
* The unrolled bound is the separate-sum-check bound minus `2ℓ'/|L|`, and is below one.
* The Binary Basefold final check multiplies by the multiplier value: with a zero multiplier it
  still requires a zero target, and at `evalMultiplier` it is the `eq̃` check.
-/

open OracleComp OracleSpec ProtocolSpec Module MvPolynomial
open RingSwitching RingSwitching.Packing Sumcheck.Structured Binius.BinaryBasefold
open scoped NNReal
noncomputable section
namespace ArkLibTest.FRIBinius.Unrolled

open ArkLibTest.RingSwitchingConformance.BiniusComposition BbfGf16Parameters
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fintype Gf16 := Fintype.ofFinite Gf16
local instance : DecidableEq Gf16 := Classical.decEq Gf16
local instance : SampleableType Gf16 := SampleableType.ofFintype Gf16
local instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨by simp⟩
local instance : Fact ((1 : ℕ) ∣ 1) := ⟨by decide⟩
local instance : Fact (basis 0 = 1) := ⟨betaBasis_zero⟩
local instance : Fact (Nat.Prime (ringChar (ZMod 2))) :=
  ⟨CharP.prime_ringChar (ZMod 2)⟩

/-- The unrolled composition is secure for the input relation of the separate-sum-check
composition. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((Binius.FRIBinius.Unrolled.fullVerifier 2 (ZMod 2) basis
      (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
      (TensorPrefix.relIn profile rfl interface) acceptRejectOracleRel
      (Binius.FRIBinius.Unrolled.fullError 2 (ZMod 2) basis (ϑ := 1) (by decide) 8) :=
  Binius.FRIBinius.Unrolled.fullVerifier_rbrKnowledgeSoundness 2 (ZMod 2) basis
    (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8 init impl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  Binius.FRIBinius.Unrolled.fullReduction_perfectCompleteness_and_knowledgeSoundness 2 (ZMod 2)
    basis (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8 init impl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  Binius.FRIBinius.Unrolled.fullVerifier_soundness 2 (ZMod 2) basis
    (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8 init impl

/-- The unrolled composite accepts the nonconstant honest source with probability one. -/
theorem honest_probability {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let R := OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (Binius.FRIBinius.Unrolled.fullReduction 2 (ZMod 2) basis
        (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8)
    let pSpec := Binius.FRIBinius.Unrolled.pSpec 2 (ZMod 2) basis
      (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) 8
    let pImpl : QueryImpl ([]ₒ + [pSpec.Challenge]ₒ'challengeOracleInterface)
      (StateT σ ProbComp) := QueryImpl.addLift impl challengeQueryImpl
    Pr{let out ← OptionT.mk do
      let st ← init
      (simulateQ pImpl (R.run ((point, aeval point source.val), honestOracle) source).run).run' st}[
        (out.2, out.1.2.2) ∈ acceptRejectOracleRel ∧ out.1.2.1 = out.2] = 1 := by
  have h := Binius.FRIBinius.Unrolled.fullReduction_perfectCompleteness 2 (ZMod 2) basis
    (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8 init impl
  change Reduction.perfectCompleteness init impl
    (TensorPrefix.relIn profile rfl interface.strictView)
    acceptRejectOracleRel (OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (Binius.FRIBinius.Unrolled.fullReduction 2 (ZMod 2) basis
        (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8)) at h
  rw [Reduction.perfectCompleteness_eq_prob_one] at h
  exact h ((point, aeval point source.val), honestOracle) source honest_input_actual

/-- The bound is `8/16 + (3/4)^8 < 1`, and one sum-check term `2/16` below the separate-sum-check
bound. -/
theorem concreteError_lt :
    Binius.FRIBinius.Unrolled.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8 =
        8 / 16 + (3 / 4 : ℝ≥0) ^ 8 ∧
      Binius.FRIBinius.Unrolled.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8 < 1 ∧
      Binius.FRIBinius.Unrolled.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8 <
        (2 : ℝ≥0) / Fintype.card Gf16 + (1 : ℝ≥0) * (2 / Fintype.card Gf16) +
          Binius.BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError
            Gf16 1 1 8 := by
  have hadd := Binius.FRIBinius.Unrolled.concreteError_add_eq 2 (L := Gf16) (ℓ' := 1) (R := 1) 8
  refine ⟨?_, ?_, ?_⟩
  · norm_num [Binius.FRIBinius.Unrolled.concreteError, card_gf16]
  · norm_num [Binius.FRIBinius.Unrolled.concreteError, card_gf16]
  · have hpos : 0 < ((1 : ℕ) : ℝ≥0) * (2 / Fintype.card Gf16) := by
      rw [card_gf16]
      norm_num
    have h := lt_add_of_pos_right
      (Binius.FRIBinius.Unrolled.concreteError 2 (L := Gf16) (ℓ' := 1) (R := 1) 8) hpos
    rw [hadd] at h
    exact_mod_cast h

/-! ### The Binary Basefold final check -/

section FinalCheck
variable (mult : Multiplier Unit Gf16 1)

private theorem one_add_one_lt_two_pow_two : 1 + 1 < 2 ^ 2 := by decide

/-- A zero multiplier value does not make the final check vacuous: it requires a zero target. -/
example (h0 : ∀ r', mult.evaluate () r' = 0)
    (s : Statement (L := Gf16) Unit (Fin.last 1) × ∀ j, OracleStatement (ZMod 2) basis
      (h_ℓ_add_R_rate := one_add_one_lt_two_pow_two) 1 (Fin.last 1) j)
    (tr : (pSpecFinalSumcheckStep (L := Gf16)).FullTranscript) :
    (CoreInteraction.finalSumcheckVerifierGuardedForm (ZMod 2) basis mult (ϑ := 1)
      (h_ℓ_add_R_rate := one_add_one_lt_two_pow_two) (𝓑 := boolEmbedding Gf16)).check s tr =
      decide (s.1.sumcheck_target = 0) := by
  rw [CoreInteraction.finalSumcheckVerifierGuardedForm_check, h0]
  exact decide_eq_decide.mpr ⟨fun h => h.trans (zero_mul _), fun h => h.trans (zero_mul _).symm⟩

/-- At `evalMultiplier`, the final check is the evaluation-claim check `s = eq̃(r, r') · c`. -/
example (s : Statement (L := Gf16) (SumcheckBaseContext Gf16 1) (Fin.last 1) ×
      ∀ j, OracleStatement (ZMod 2) basis
        (h_ℓ_add_R_rate := one_add_one_lt_two_pow_two) 1 (Fin.last 1) j)
    (tr : (pSpecFinalSumcheckStep (L := Gf16)).FullTranscript) :
    (CoreInteraction.finalSumcheckVerifierGuardedForm (ZMod 2) basis evalMultiplier (ϑ := 1)
      (h_ℓ_add_R_rate := one_add_one_lt_two_pow_two) (𝓑 := boolEmbedding Gf16)).check s tr =
      decide (s.1.sumcheck_target =
        eqTilde s.1.ctx.t_eval_point s.1.challenges * (show Gf16 from tr.messages ⟨0, rfl⟩)) :=
  CoreInteraction.finalSumcheckVerifierGuardedForm_check (ZMod 2) basis evalMultiplier s tr

end FinalCheck

end ArkLibTest.FRIBinius.Unrolled

/--
info: 'Binius.FRIBinius.Unrolled.fullVerifier_rbrKnowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Unrolled.fullVerifier_rbrKnowledgeSoundness

/--
info: 'Binius.FRIBinius.Unrolled.fullReduction_perfectCompleteness_and_knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Unrolled.fullReduction_perfectCompleteness_and_knowledgeSoundness

/--
info: 'Binius.FRIBinius.Unrolled.fullVerifier_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Unrolled.fullVerifier_soundness

/--
info: 'Binius.FRIBinius.Unrolled.fullError_sum_le_concrete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.Unrolled.fullError_sum_le_concrete
