/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Rank
public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional

/-!
# Interpolation from the finite partition surplus

The rank bound applies to the actual local constraint maps. A surplus therefore
produces a nonzero polynomial retaining both its support and every local equation.
These equations are the witness needed by executable interpolation search.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open scoped BigOperators

/-- A strict source surplus yields an interpolant in the derivative-order support. -/
theorem exists_nonzero_ratePartition_interpolant
    {F ι : Type*} [Field F] [Fintype ι] {D d m W : ℕ} {L : ℝ}
    (hD : 0 < D) (centers received : ι → F)
    (hdim : Fintype.card ι * ratePartitionRankBound d m W <
      (ratePartitionExponents D d W L hD).card) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧
      Q ∈ ratePartitionSpace F D d W L hD ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  classical
  let V := ratePartitionSpace F D d W L hD
  let b := MvPolynomial.basisRestrictSupport (R := F)
    (↑(ratePartitionExponents D d W L hD) : Set (JetVariable d →₀ ℕ))
  let _ : Module.Finite F V := Module.Finite.of_basis b
  let φ := fun i ↦ ratePartitionLocalConstraint (d := d) (W := W)
    (L := L) m hD (centers i) (received i)
  have hsum : (∑ i, Module.finrank F (φ i).range) < Module.finrank F V := by
    calc
      _ ≤ ∑ _i : ι, ratePartitionRankBound d m W :=
        Finset.sum_le_sum fun i _ ↦ finrank_ratePartitionLocalConstraint_le
          hD (centers i) (received i)
      _ = Fintype.card ι * ratePartitionRankBound d m W := by simp
      _ < _ := by
        change _ < Module.finrank F (ratePartitionSpace F D d W L hD)
        rw [finrank_ratePartitionSpace_eq_card hD]
        exact hdim
  obtain ⟨Q, hQ, hlocal⟩ := LinearMap.exists_ne_zero_of_sum_finrank_range_lt φ hsum
  exact ⟨Q.1, fun h ↦ hQ (Subtype.ext h), Q.2, hlocal⟩

end ReedSolomon.HiddenDerivative
