/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Coordinates
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Local coordinate acceptance tests

The coordinates of a concrete exponent; a concrete residual budget and the rank bound it gives on
an exact interpolation space; the source statements with a real jet-degree cutoff, derived from
the natural-number statements through `⌈T⌉₊`; and a generator image that shows the weight
transport needs a nonnegative weight on `X`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- For `d = 3`, the exponent `T² U Y₁ Y₃⁴` has coordinates `(2, 1, 1, (0, 4))`. -/
example : localExponentCoordinatesEquiv (d := 3) (by norm_num)
    (Finsupp.single (localT 3) 2 + Finsupp.single (localU 3) 1 +
      Finsupp.single (localY 0) 1 + Finsupp.single (localY 2) 4) = (2, 1, 1, ![0, 4]) := by
  simp only [localExponentCoordinatesEquiv_apply, Prod.mk.injEq]
  refine ⟨by simp [localT, localU, localAux, localY], by simp [localT, localU, localAux, localY],
    by simp [localT, localU, localAux, localY], ?_⟩
  funext i
  fin_cases i <;> simp [localT, localU, localAux, localY]

/-- For `d = 1`, `m = 2`, `W = 0`, `B = 2`: one value of `h` for each residual `r ∈ {0, 1}`,
one (empty) higher-jet exponent, and two values of the `Y₁`-degree. -/
example : localResidualCoordinateBudget 1 2 0 2 = 4 := by decide

/-- The coarse budget at the same parameters is also `4`: for `d = 1` there are no higher jets, so
every higher-jet exponent has degree `0` and the two budgets agree. -/
example : localCoordinateBudget 1 2 0 2 = 4 := by decide

/-- At `d = 1`, `D = 2`, `A = 1`, `m = 2`, `W = 0` the jet-degree floor is `1`, so the local
constraint map on the exact space has rank at most `4`. -/
example (M : ℕ) (center received : ℚ) :
    Module.finrank ℚ (LinearMap.range (exactLocalConstraintAt (A := 1) (M := M) (W := 0)
      (by norm_num : 1 < 2) 2 center received)) ≤ 4 :=
  (finrank_range_exactLocalConstraintAt_le_localResidualCoordinateBudget (by norm_num) _ 2
    center received).trans (by decide)

/-- Source shape (`unscaled_jet_degree_lt_of_support`): a real strict cutoff on the source's total
jet degree is a strict cutoff on the image. -/
example {R : Type*} [CommRing R] {d : ℕ} (center received : R) {Q : DifferentialPolynomial R d}
    {T : ℝ} (hsource : ∀ u ∈ Q.support, (totalJetDegree u : ℝ) < T) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    (e.weight (localJetDegreeWeight d) : ℝ) < T :=
  Nat.lt_ceil.mp (localJetDegree_lt_of_mem_support center received
    (fun u hu => Nat.lt_ceil.mpr (hsource u hu)) he)

/-- Source shape (`localConstraint_support_of_weight_bounds` followed by
`mem_localResidualExponents_of_bounds`), with a real cutoff `T`. -/
example {d m W : ℕ} (hd : 0 < d) (center received : ℚ) {Q : DifferentialPolynomial ℚ d} {T : ℝ}
    (hweight : ∀ u ∈ Q.support, fullHigherJetWeight u ≤ W)
    (htotal : ∀ u ∈ Q.support, (totalJetDegree u : ℝ) < T)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e ∈ localResidualExponents hd m W ⌈T⌉₊ := by
  obtain ⟨h1, h2, h3, h4⟩ := localConstraintAt_support_of_weight_bounds center received hweight
    (fun u hu => Nat.lt_ceil.mpr (htotal u hu)) he
  exact mem_localResidualExponents_of_bounds hd h1 h2 h3 h4

/-- The transport needs `0 ≤ v X`: with every weight `-1`, the image `1 + T` of `X` contains the
constant monomial, of weight `0 > -1`. -/
example : unscaledLocalImage 0 (1 : ℚ) 0 none ∉
    restrictWeightAtMost (fun _ : LocalVariable 0 => (-1 : ℤ)) (-1) := by
  intro h
  have := mem_restrictWeightAtMost.mp h 0 (by
    rw [mem_support_iff]
    simp [unscaledLocalImage, coeff_X, localT])
  simp at this
