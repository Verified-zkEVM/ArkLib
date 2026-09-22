/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Interpolation
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.CertifiedRankBound
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Dimension

/-!
# Global interpolation acceptance tests

Concrete interpolants from the counting criterion, with the local ranks bounded by
`finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound` and the dimension computed by
`finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount`: no received points, one
point, and four points. An interpolant through infinitely many copies of one point shows that the
rank criterion needs no finite index type. A case where the rank equals the dimension and no
nonzero interpolant exists shows that the strict inequality is needed.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- `D = 2`, `A = 2`, `d = 1`, `m = 1`, `M = 1`, `W = 0`: the exact space is spanned by `1`, `X`,
and `Y₁`. -/
private theorem finrank_small :
    Module.finrank ℚ (exactInterpolationSpace ℚ 2 2 1 1 1 0 (by norm_num)) = 3 := by
  rw [finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount ℚ (by norm_num)]
  decide

/-- At `d = 1`, `m = 1`, `M = 1`, `W = 0` the certified local rank bound is `2`, for every `A`
and every point. -/
private theorem localRank_small (A : ℕ) (center received : ℚ) :
    Module.finrank ℚ (LinearMap.range (exactLocalConstraintAt (D := 2) (A := A) (M := 1) (W := 0)
      (d := 1) (by norm_num) 1 center received)) ≤ 2 :=
  (finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound (by norm_num) _ _ _).trans_eq
    (by decide)

/-- With no received points the only requirement is a nonzero exact space. -/
example : ∃ Q : DifferentialPolynomial ℚ 1,
    Q ≠ 0 ∧ Q ∈ exactInterpolationSpace ℚ 2 2 1 1 1 0 (by norm_num) ∧
      ∀ i : Fin 0, SatisfiesLocalConstraints 1 (Fin.elim0 i) (Fin.elim0 i) Q :=
  exists_nonzero_global_interpolant_of_uniform_local_rank_bound (by norm_num) _ _ 0
    (fun i => Fin.elim0 i) (by rw [finrank_small]; decide)

/-- Through any one point: the local rank is at most `2 < 3`. -/
example (center received : ℚ) : ∃ Q : DifferentialPolynomial ℚ 1,
    Q ≠ 0 ∧ Q ∈ exactInterpolationSpace ℚ 2 2 1 1 1 0 (by norm_num) ∧
      ∀ _ : Fin 1, SatisfiesLocalConstraints 1 center received Q :=
  exists_nonzero_global_interpolant_of_uniform_local_rank_bound (by norm_num)
    (fun _ => center) (fun _ => received) 2
    (fun _ => localRank_small _ _ _)
    (by rw [finrank_small]; decide)

/-- Through any four points with `A = 4`: the exact space has dimension `10`, and four local ranks
of at most `2` sum to `8 < 10`. -/
example (centers received : Fin 4 → ℚ) : ∃ Q : DifferentialPolynomial ℚ 1,
    Q ≠ 0 ∧ Q ∈ exactInterpolationSpace ℚ 2 4 1 1 1 0 (by norm_num) ∧
      ∀ i, SatisfiesLocalConstraints 1 (centers i) (received i) Q := by
  have hdim : Module.finrank ℚ (exactInterpolationSpace ℚ 2 4 1 1 1 0 (by norm_num)) = 10 := by
    rw [finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount ℚ (by norm_num)]
    decide
  exact exists_nonzero_global_interpolant_of_local_rank_bounds (by norm_num) centers received
    (fun _ => 2)
    (fun _ => localRank_small _ _ _)
    (by rw [hdim]; decide)

/-- Infinitely many copies of one point, indexed by `ℕ`. The global map is the local map followed
by the diagonal, so its rank is at most the local rank `2 < 3`. The criterion
`exists_nonzero_global_interpolant_of_rank_lt` needs no `Fintype` instance. -/
example (center received : ℚ) : ∃ Q : DifferentialPolynomial ℚ 1,
    Q ≠ 0 ∧ Q ∈ exactInterpolationSpace ℚ 2 2 1 1 1 0 (by norm_num) ∧
      ∀ _ : ℕ, SatisfiesLocalConstraints 1 center received Q := by
  have hdiag : globalExactCoefficientConstraintMap (D := 2) (A := 2) (m := 1) (M := 1) (W := 0)
      (d := 1) (by norm_num) (fun _ : ℕ => center) (fun _ => received) =
      (LinearMap.pi fun _ => LinearMap.id) ∘ₗ
        exactCoefficientLocalConstraintAt (by norm_num) 1 center received := rfl
  apply exists_nonzero_global_interpolant_of_rank_lt (by norm_num) _ _
  rw [hdiag, LinearMap.range_comp, finrank_small]
  calc _ ≤ Module.finrank ℚ (LinearMap.range
          (exactCoefficientLocalConstraintAt (A := 2) (M := 1) (W := 0) (d := 1) (D := 2)
            (by norm_num) 1 center received)) := Submodule.finrank_map_le _ _
    _ ≤ 2 := by
      rw [range_exactCoefficientLocalConstraintAt]
      exact localRank_small _ _ _
    _ < 3 := by norm_num

/-- The strict inequality is needed. For `D = 2`, `A = 1`, `d = 1`, `m = 1`, `M = 1`, `W = 0`
every variable has positive specialization weight, so the exact space is the constants, of
dimension `1`. A nonzero constant fails the multiplicity-one constraint at every point, so there
is no nonzero interpolant through one point; hence the global rank equals the dimension `1`. -/
example (center received : ℚ) : ¬ ∃ Q : DifferentialPolynomial ℚ 1,
    Q ≠ 0 ∧ Q ∈ exactInterpolationSpace ℚ 2 1 1 1 1 0 (by norm_num) ∧
      SatisfiesLocalConstraints 1 center received Q := by
  rintro ⟨Q, hQ0, hQ, hsat⟩
  have hsupp : ∀ u ∈ Q.support, u = 0 := by
    intro u hu
    have hw := (mem_exactInterpolationSpace_iff.mp hQ u hu).2.2
    rw [weight_differentialWeight_eq, Fin.sum_univ_two] at hw
    simp only [Fin.val_zero, Fin.val_one, Nat.sub_zero, one_mul] at hw
    ext v
    rcases v with _ | j
    · simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    · simp only [Finsupp.coe_zero, Pi.zero_apply]
      fin_cases j
      · change u (some 0) = 0
        omega
      · change u (some 1) = 0
        omega
  have hC : Q = C (Q.coeff 0) := by
    ext u
    rw [coeff_C]
    split_ifs with h
    · rw [h]
    · by_contra hne
      exact h (hsupp u (mem_support_iff.mpr hne)).symm
  have h0 := (satisfiesLocalConstraints_iff_coeff_eq_zero 1 center received Q).mp hsat 0
    (by simp [localContactOrder])
  rw [hC, algHom_C, algebraMap_eq, coeff_C, ite_eq_left_iff.mpr (fun h => absurd rfl h)] at h0
  exact hQ0 (by rw [hC, h0, C_0])
