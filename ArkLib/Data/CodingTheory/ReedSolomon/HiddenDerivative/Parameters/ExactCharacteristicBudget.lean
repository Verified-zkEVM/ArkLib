/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Index
/-!
# Characteristic budgets for exact hidden-derivative interpolation

This file derives the characteristic bounds needed by root finding directly from the exact
interpolation band.  A monomial of exact weight less than `m * A` has exponent at `Y_j` at most

```text
(m * A - 1) / (D - j).
```

Thus every polynomial in `exactInterpolationSpace` satisfies the same coordinatewise bound.  In
particular, all jet degrees lie below the characteristic once the coarser global floor
`exactInterpolationJetDegreeFloor D A d m` does.  These consequences use only the exact weighted
support predicate; they do not import the total-degree cap of the coarse interpolation space.

The coefficient-facing endpoints apply directly to `exactInterpolationPolynomial`, so a kernel
vector in exact interpolation coordinates can be passed to the root-finding interface without
repackaging its support certificate.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

variable {F : Type*} {d D A m M W : ℕ}

/-- The exact coordinatewise floor `floor((mA - 1) / (D - j))` for the jet `Y_j`. -/
def exactInterpolationJetDegreeFloorAt (D A m : ℕ) (j : Fin (d + 1)) : ℕ :=
  (m * A - 1) / (D - j.val)

/-- A single jet's weighted contribution is at most the exact weight of its monomial. -/
private theorem jet_weight_mul_exponent_le_exactInterpolationMonomialWeight
    (D : ℕ) (u : JetVariable d →₀ ℕ) (j : Fin (d + 1)) :
    u.some j * (D - j.val) ≤ exactInterpolationMonomialWeight D u := by
  classical
  rw [exactInterpolationMonomialWeight_eq]
  apply le_trans ?_ (Nat.le_add_left _ _)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [nsmul_eq_mul]
  exact Finset.single_le_sum
    (f := fun i : Fin (d + 1) ↦ u.some i * (D - i.val))
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)

/-- Membership in the exact interpolation space gives the sharp floor for each jet coordinate. -/
theorem jetDegree_le_exactInterpolationJetDegreeFloorAt_of_mem_exactInterpolationSpace
    [CommSemiring F] (Q : DifferentialPolynomial F d) {hdD : d < D}
    (hQ : Q ∈ exactInterpolationSpace F D A d m M W hdD) (j : Fin (d + 1)) :
    jetDegree Q j ≤ exactInterpolationJetDegreeFloorAt D A m j := by
  rw [jetDegree, MvPolynomial.degreeOf_le_iff]
  intro u hu
  rw [exactInterpolationJetDegreeFloorAt]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < D - j.val)).2
  calc
    u (some j) * (D - j.val) = u.some j * (D - j.val) := rfl
    _ ≤ exactInterpolationMonomialWeight D u :=
      jet_weight_mul_exponent_le_exactInterpolationMonomialWeight D u j
    _ ≤ m * A - 1 :=
      exactInterpolationMonomialWeight_le_pred_of_lt
        (mem_exactInterpolationSpace_iff.mp hQ u hu).2.2

/-- The coordinatewise floor is no larger than the global exact jet-degree floor. -/
theorem exactInterpolationJetDegreeFloorAt_le (hdD : d < D) (j : Fin (d + 1)) :
    exactInterpolationJetDegreeFloorAt D A m j ≤
      exactInterpolationJetDegreeFloor D A d m := by
  rw [exactInterpolationJetDegreeFloorAt, exactInterpolationJetDegreeFloor]
  apply Nat.div_le_div_left
  · have hj : j.val ≤ d := Nat.le_of_lt_succ j.isLt
    omega
  · omega

/-- Jet-degree spelling of the existing global exact-space degree bound. -/
theorem jetDegree_le_exactInterpolationJetDegreeFloor_of_mem_exactInterpolationSpace
    [CommSemiring F] (Q : DifferentialPolynomial F d) {hdD : d < D}
    (hQ : Q ∈ exactInterpolationSpace F D A d m M W hdD) (j : Fin (d + 1)) :
    jetDegree Q j ≤ exactInterpolationJetDegreeFloor D A d m := by
  simpa [jetDegree] using
    degreeOf_jet_le_floor_of_mem_exactInterpolationSpace hdD hQ j

/-- A polynomial in the exact interpolation space is below characteristic once its ambient
degree and the global exact jet-degree floor are. -/
theorem isBelowCharacteristic_of_mem_exactInterpolationSpace [CommSemiring F]
    (Q : DifferentialPolynomial F d) {hdD : d < D}
    (hQ : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hD : D < ringChar F)
    (hfloor : exactInterpolationJetDegreeFloor D A d m < ringChar F) :
    IsBelowCharacteristic D Q := by
  refine ⟨hD, fun j ↦ ?_⟩
  exact (jetDegree_le_exactInterpolationJetDegreeFloor_of_mem_exactInterpolationSpace
    Q hQ j).trans_lt hfloor

/-! ### Coefficient-facing endpoints -/

/-- Exact interpolation coefficients reconstruct a polynomial satisfying the sharp
coordinatewise jet-degree floor. -/
theorem jetDegree_exactInterpolationPolynomial_le_floorAt [CommSemiring F]
    {hdD : d < D} (c : ExactInterpolationCoefficients F D A d m M W hdD)
    (j : Fin (d + 1)) :
    jetDegree (exactInterpolationPolynomial hdD c : DifferentialPolynomial F d) j ≤
      exactInterpolationJetDegreeFloorAt D A m j :=
  jetDegree_le_exactInterpolationJetDegreeFloorAt_of_mem_exactInterpolationSpace
    (exactInterpolationPolynomial hdD c : DifferentialPolynomial F d)
    (exactInterpolationPolynomial hdD c).property j

/-- Exact interpolation coefficients reconstruct a polynomial satisfying the global exact
jet-degree floor. -/
theorem jetDegree_exactInterpolationPolynomial_le_floor [CommSemiring F]
    {hdD : d < D} (c : ExactInterpolationCoefficients F D A d m M W hdD)
    (j : Fin (d + 1)) :
    jetDegree (exactInterpolationPolynomial hdD c : DifferentialPolynomial F d) j ≤
      exactInterpolationJetDegreeFloor D A d m :=
  jetDegree_le_exactInterpolationJetDegreeFloor_of_mem_exactInterpolationSpace
    (exactInterpolationPolynomial hdD c : DifferentialPolynomial F d)
    (exactInterpolationPolynomial hdD c).property j

/-- Direct characteristic bridge for a polynomial reconstructed from exact interpolation
coefficients. -/
theorem isBelowCharacteristic_exactInterpolationPolynomial [CommSemiring F]
    {hdD : d < D} (c : ExactInterpolationCoefficients F D A d m M W hdD)
    (hD : D < ringChar F)
    (hfloor : exactInterpolationJetDegreeFloor D A d m < ringChar F) :
    IsBelowCharacteristic D
      (exactInterpolationPolynomial hdD c : DifferentialPolynomial F d) :=
  isBelowCharacteristic_of_mem_exactInterpolationSpace
    (exactInterpolationPolynomial hdD c : DifferentialPolynomial F d)
    (exactInterpolationPolynomial hdD c).property hD hfloor

end

end HiddenDerivative
end ReedSolomon
