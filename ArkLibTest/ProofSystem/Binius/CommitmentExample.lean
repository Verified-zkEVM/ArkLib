/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.FRIBinius.Commitment

/-!
# Binius commitment regression

The old diagonal witness table confused `X 0` with `X 1`. The production Boolean table and honest
oracle encoding distinguish them. The actual strict unique-radius relation cannot accept both for
one oracle, and honest coverage holds for both nonconstant sources.
-/

noncomputable section

namespace Binius.CommitmentExample

open MvPolynomial Module AdditiveNTT Sumcheck.Structured

variable {L : Type} [Field L]

private def coordinate (j : Fin 2) : MultilinearPoly L 2 :=
  ⟨X j, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro i
    rw [degreeOf_X]
    split <;> omega⟩

private theorem coordinates_distinct : coordinate (L := L) 0 ≠ coordinate 1 := by
  intro h
  have hc := congrArg (fun t => BinaryBasefold.witnessNovelCoeffs t ⟨1, by norm_num⟩) h
  have h0 : Nat.getBit 0 1 = 1 := rfl
  have h1 : Nat.getBit 1 1 = 0 := rfl
  simp only [BinaryBasefold.witnessNovelCoeffs, coordinate, eval_X, Fin.val_zero, Fin.val_one,
    h0, h1, Nat.cast_one, Nat.cast_zero] at hc
  exact one_ne_zero hc

variable [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K]
variable [Fact (Nat.Prime (ringChar K))] [Fact (Fintype.card K = 2)] [Algebra K L]
variable {r 𝓡 : ℕ} [NeZero r] (β : Fin r → L) [Fact (LinearIndependent K β)]
variable (h : 2 + 𝓡 < r)

local instance : Fact (1 ∣ 2) := ⟨one_dvd 2⟩

example : BinaryBasefold.firstOracleEncoding K β (h_ℓ_add_R_rate := h) (coordinate 0) ≠
    BinaryBasefold.firstOracleEncoding K β (h_ℓ_add_R_rate := h) (coordinate 1) :=
  fun he => coordinates_distinct (BinaryBasefold.firstOracleEncoding_injective K β he)

example (f₀ : sDomain K β h 0 → L) :
    ¬ (BinaryBasefold.firstOracleWitnessConsistencyProp K β (coordinate 0) f₀ ∧
      BinaryBasefold.firstOracleWitnessConsistencyProp K β (coordinate 1) f₀) := by
  rintro ⟨h0, h1⟩
  exact coordinates_distinct
    (BinaryBasefold.firstOracleWitnessConsistencyProp_functional K β f₀ _ _ h0 h1)

example :
    BinaryBasefold.firstOracleWitnessConsistencyProp K β (coordinate 0)
      (BinaryBasefold.getFirstOracle K β
        (BinaryBasefold.honestInitialOracleStatement K β 1 (h_ℓ_add_R_rate := h)
          (coordinate 0))) ∧
    BinaryBasefold.firstOracleWitnessConsistencyProp K β (coordinate 1)
      (BinaryBasefold.getFirstOracle K β
        (BinaryBasefold.honestInitialOracleStatement K β 1 (h_ℓ_add_R_rate := h)
          (coordinate 1))) := by
  constructor <;> exact BinaryBasefold.honestInitialOracleStatement_consistent K β 1 _

/--
info: 'Binius.BinaryBasefold.firstOracleWitnessConsistencyProp_functional'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BinaryBasefold.firstOracleWitnessConsistencyProp_functional

/--
info: 'Binius.BinaryBasefold.honestInitialOracleStatement_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BinaryBasefold.honestInitialOracleStatement_consistent

/--
info: 'Binius.FRIBinius.binaryBasefold_initialCompatibility_functional'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FRIBinius.binaryBasefold_initialCompatibility_functional

/--
info: 'Binius.FRIBinius.binaryBasefold_initialCompatibility_coverage'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FRIBinius.binaryBasefold_initialCompatibility_coverage

end Binius.CommitmentExample
