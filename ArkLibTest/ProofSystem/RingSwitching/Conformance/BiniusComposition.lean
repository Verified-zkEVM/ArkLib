/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLibTest.ProofSystem.RingSwitching.Conformance.Binius
import ArkLibTest.ProofSystem.Binius.BinaryBasefold.Opening
import ArkLib.ProofSystem.Binius.FRIBinius.Conformance

/-!
# Shared prefix ring switching with the Binary Basefold opening

The small orientation fixture has an inhabited shared frontend and exact error sum `3/4`.
The full consumer uses `GF(16)/GF(2)`, two packed variables and one retained variable, a
nonconstant source, an honest first-codeword encoding, and the Binary Basefold opening.
Its challenge-error sum is bounded strictly below one. Completeness uses the exact encoding;
round-by-round security uses the relaxed unique-radius relation.
-/

open OracleComp OracleSpec ProtocolSpec Module MvPolynomial
open RingSwitching RingSwitching.Packing Sumcheck.Structured
open scoped NNReal
noncomputable section
namespace ArkLibTest.RingSwitchingConformance.BiniusComposition

section Orientation
open ConcreteBinaryTower
open ArkLibTest.RingSwitchingOrientation renaming K → GF2, L → GF4, p → P₄
open ArkLibTest.RingSwitchingConformance.Binius
attribute [local instance] ArkLibTest.RingSwitchingOrientation.algebraKL
local instance : SampleableType GF4 := SampleableType.ofFintype GF4

example : ∑ i, TensorPrefix.rbrError (ℓ' := 1) P₄ i = (3 : ℝ≥0) / 4 := by
  rw [TensorPrefix.rbrError_sum]
  norm_num [show Fintype.card GF4 = 4 from (ConcreteBinaryTower.getBTFResult 1).fieldFintypeCard]

example : ((claimAt 0, oStmt₀), ArkLibTest.RingSwitchingOrientation.t) ∈
    TensorPrefix.relIn P₄ rfl exactOStmtIn := honest_input
end Orientation

section Actual
open BbfGf16Parameters
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fintype Gf16 := Fintype.ofFinite Gf16
local instance : DecidableEq Gf16 := Classical.decEq Gf16
local instance : SampleableType Gf16 := SampleableType.ofFintype Gf16
local instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨by simp⟩
local instance : Fact ((1 : ℕ) ∣ 1) := ⟨by decide⟩
abbrev basis : Basis (Fin (2 ^ 2)) (ZMod 2) Gf16 := betaBasis
local instance : Fact (basis 0 = 1) := ⟨betaBasis_zero⟩
local instance : Fact (Nat.Prime (ringChar (ZMod 2))) :=
  ⟨CharP.prime_ringChar (ZMod 2)⟩

abbrev profile := Binius.FRIBinius.biniusProfile 2 Gf16 (ZMod 2) basis
abbrev interface := Binius.FRIBinius.RingSwitch.inputInterface 2 (ZMod 2) basis
  (ℓ' := 1) (R := 1) (ϑ := 1) (by decide)

def source : MultilinearPoly (ZMod 2) 3 :=
  ⟨MvPolynomial.X 0 + MvPolynomial.X 2, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro i
    exact (degreeOf_add_le i _ _).trans (max_le (degreeOf_X_le i 0) (degreeOf_X_le i 2))⟩

example : source.val.eval ![0, 0, 0] = 0 ∧ source.val.eval ![1, 0, 0] = 1 := by
  simp [source]

def point : Fin 3 → Gf16 := ![0, 0, 1]

example : aeval point source.val = (1 : Gf16) := by simp [point, source]
def packed := packMLE 2 Gf16 (ZMod 2) 3 1 rfl profile.basis source
def honestOracle := Binius.FRIBinius.honestPackedOracle 2 Gf16 (ZMod 2) basis
  1 1 1 (by decide) packed

theorem honest_input_actual :
    (((point, aeval point source.val), honestOracle), source) ∈
      TensorPrefix.relIn profile rfl interface.strictView :=
  Binius.FRIBinius.Conformance.mem_relIn_strictView_honestPackedOracle 2 (ZMod 2) basis
    (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) rfl source point

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  Binius.FRIBinius.RingSwitch.fullReduction_perfectCompleteness 2 (ZMod 2) basis
    (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8 init impl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  Binius.FRIBinius.RingSwitch.fullVerifier_rbrKnowledgeSoundness 2 (ZMod 2) basis
    (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8 init impl

/-- The composite accepts its nonconstant honest source with probability one. -/
theorem honest_probability {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let R := OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (Binius.FRIBinius.RingSwitch.fullReduction 2 (ZMod 2) basis
        (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8)
    let pSpec := Binius.FRIBinius.RingSwitch.pSpec 2 (ZMod 2) basis
      (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) 8
    let pImpl : QueryImpl ([]ₒ + [pSpec.Challenge]ₒ'challengeOracleInterface)
      (StateT σ ProbComp) := QueryImpl.addLift impl challengeQueryImpl
    Pr{let out ← OptionT.mk do
      let st ← init
      (simulateQ pImpl (R.run ((point, aeval point source.val), honestOracle) source).run).run' st}[
        (out.2, out.1.2.2) ∈ acceptRejectOracleRel ∧ out.1.2.1 = out.2] = 1 := by
  have h := Binius.FRIBinius.RingSwitch.fullReduction_perfectCompleteness 2 (ZMod 2) basis
    (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8 init impl
  change Reduction.perfectCompleteness init impl
    (TensorPrefix.relIn profile rfl interface.strictView)
    acceptRejectOracleRel (OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (Binius.FRIBinius.RingSwitch.fullReduction 2 (ZMod 2) basis
        (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) (ℓ := 3) rfl 8)) at h
  rw [Reduction.perfectCompleteness_eq_prob_one] at h
  exact h ((point, aeval point source.val), honestOracle) source honest_input_actual

/-- The bound concerns the full challenge-index sum, including the opening. -/
theorem full_error_sum_lt_one :
    (∑ j, Binius.FRIBinius.RingSwitch.fullError 2 (ZMod 2) basis
      (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) 8 j) < 1 := by
  apply lt_of_le_of_lt (Binius.FRIBinius.RingSwitch.fullError_sum_le 2 (ZMod 2) basis
    (ℓ' := 1) (R := 1) (ϑ := 1) (by decide) 8)
  rw [card_gf16]
  norm_num [Binius.BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError,
    card_gf16]

end Actual
end ArkLibTest.RingSwitchingConformance.BiniusComposition

/--
info: 'Binius.FRIBinius.RingSwitch.fullReduction_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.RingSwitch.fullReduction_perfectCompleteness

/--
info: 'Binius.FRIBinius.RingSwitch.fullVerifier_rbrKnowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.RingSwitch.fullVerifier_rbrKnowledgeSoundness

/--
info: 'Binius.FRIBinius.RingSwitch.fullError_sum_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.RingSwitch.fullError_sum_le
