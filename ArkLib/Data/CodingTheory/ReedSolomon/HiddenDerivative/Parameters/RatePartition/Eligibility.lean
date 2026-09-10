/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Basis
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Interpolation
/-! # Rate-partition witnesses in the executable finite support -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open scoped BigOperators

/-- The paper's weak jet cap is enumerated by the independent strict budget `ν + 1`. -/
theorem ratePartition_witness_eligible {F : Type*} [Field F] {D d W m A ν : ℕ}
    (hD : 0 < D) (Q : DifferentialPolynomial F d)
    (hQ : Q ∈ ratePartitionSpace F D d W (m * A : ℕ) hD)
    (hdegree : ∀ u, RatePartitionEligible D d W (m * A : ℕ) u → totalJetDegree u ≤ ν) :
    NonzeroInterpolationMachine.EligibleWithBudget D m (ν + 1) A Q := by
  apply (NonzeroInterpolationMachine.eligibleWithBudget_iff D m (ν + 1) A Q).mpr
  intro u hu
  have he := mem_ratePartitionSpace_iff.mp hQ u hu
  have ht := hdegree u he
  have hsum : (∑ j : Fin (d + 1), u (some j)) = totalJetDegree u := by
    simp [totalJetDegree, Finsupp.degree_eq_sum]
  refine ⟨?_, ?_⟩
  · rw [hsum]
    omega
  · have hw : u none + D * totalJetDegree u < m * A := by exact_mod_cast he.2
    apply lt_of_le_of_lt _ hw
    apply Nat.add_le_add_left
    rw [← hsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ ↦ Nat.mul_le_mul_right _ (Nat.sub_le D j.val)

/-- The actual finite source surplus supplies a successful executable interpolation candidate. -/
theorem exists_ratePartition_eligible_candidate {F : Type*} [Field F]
    {D d W m n A ν : ℕ} (hD : 0 < D)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hdegree : ∀ u, RatePartitionEligible D d W (m * A : ℕ) u → totalJetDegree u ≤ ν)
    (hsurplus : n * ratePartitionRankBound d m W <
      (ratePartitionExponents D d W (m * A : ℕ) hD).card) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧
      NonzeroInterpolationMachine.EligibleWithBudget D m (ν + 1) A Q ∧
      ∀ row ∈ List.ofFn (fun i ↦ (domain i, received i)),
        localConstraintAt m row.1 row.2 Q = 0 := by
  obtain ⟨Q, hQ, hspace, hlocal⟩ := exists_nonzero_ratePartition_interpolant hD
    (fun i ↦ domain i) received (by simpa only [Fintype.card_fin] using hsurplus)
  refine ⟨Q, hQ, ratePartition_witness_eligible hD Q hspace hdegree, ?_⟩
  intro row hrow
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  exact hlocal i

end ReedSolomon.HiddenDerivative
