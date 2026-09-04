/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

/-!
# Finite forward Hasse--Taylor truncations

This file packages the first `m` coefficients of Mathlib's forward Taylor shift `p(X + a)` as an
explicit polynomial.  Unlike `Polynomial.sum_taylor_eq`, which reconstructs `p` after shifting
back by `a`, this API stays in the displacement variable `X`.  It is intended for consumers that
need a finite jet plus a remainder divisible by `X ^ m`.

Construction and coefficient lemmas require only a semiring.  Subtraction, the remainder, and its
canonical quotient by the monic polynomial `X ^ m` are isolated in the `Ring` section.
-/

namespace Polynomial

noncomputable section

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- The polynomial consisting of Hasse--Taylor orders strictly below `m` at `a`.

It is expressed in the forward displacement variable: coefficient `i < m` is `D⁽ⁱ⁾ p(a)`. -/
def forwardTaylorTruncation (m : ℕ) (a : R) (p : R[X]) : R[X] :=
  ∑ i ∈ Finset.range m, C (hasseCoeffAt a i p) * X ^ i

/-- Coefficients of the finite forward Taylor truncation. -/
@[simp]
theorem coeff_forwardTaylorTruncation (m : ℕ) (a : R) (p : R[X]) (i : ℕ) :
    (forwardTaylorTruncation m a p).coeff i =
      if i < m then hasseCoeffAt a i p else 0 := by
  simp [forwardTaylorTruncation, finsetSum_coeff]

/-- Forward Taylor truncation as an ambient-polynomial linear map, before restricting its
codomain to `degreeLT`. -/
private def forwardTaylorTruncationToPolynomial (m : ℕ) (a : R) : R[X] →ₗ[R] R[X] where
  toFun := forwardTaylorTruncation m a
  map_add' p q := by
    ext i
    simp only [coeff_add, coeff_forwardTaylorTruncation]
    split_ifs <;> simp
  map_smul' c p := by
    ext i
    simp only [coeff_smul, coeff_forwardTaylorTruncation]
    split_ifs <;> simp

/-- At the origin, Hasse coefficients are ordinary polynomial coefficients. -/
theorem hasseCoeffAt_zero_eq_coeff (i : ℕ) (p : R[X]) :
    hasseCoeffAt (0 : R) i p = p.coeff i := by
  rw [hasseCoeffAt_apply, ← taylor_coeff, taylor_zero]

/-- Below the truncation order, the finite polynomial agrees coefficientwise with `p(X + a)`. -/
theorem coeff_forwardTaylorTruncation_of_lt (m : ℕ) (a : R) (p : R[X]) {i : ℕ}
    (hi : i < m) : (forwardTaylorTruncation m a p).coeff i = (taylor a p).coeff i := by
  rw [coeff_forwardTaylorTruncation, if_pos hi, hasseCoeffAt_apply, taylor_coeff]

/-- At and above the truncation order, the finite forward Taylor truncation has zero coefficient. -/
theorem coeff_forwardTaylorTruncation_of_le (m : ℕ) (a : R) (p : R[X]) {i : ℕ}
    (hi : m ≤ i) : (forwardTaylorTruncation m a p).coeff i = 0 := by
  rw [coeff_forwardTaylorTruncation, if_neg (not_lt_of_ge hi)]

/-- The forward Taylor truncation has degree strictly less than its truncation order. -/
theorem forwardTaylorTruncation_mem_degreeLT (m : ℕ) (a : R) (p : R[X]) :
    forwardTaylorTruncation m a p ∈ degreeLT R m := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  exact fun i hi ↦ coeff_forwardTaylorTruncation_of_le m a p hi

/-- Forward Taylor truncation as a linear map whose codomain records the strict degree bound. -/
def forwardTaylorTruncationLinearMap (m : ℕ) (a : R) :
    R[X] →ₗ[R] degreeLT R m :=
  (forwardTaylorTruncationToPolynomial m a).codRestrict
    (degreeLT R m) (forwardTaylorTruncation_mem_degreeLT m a)

@[simp]
theorem forwardTaylorTruncationLinearMap_apply_coe (m : ℕ) (a : R) (p : R[X]) :
    (forwardTaylorTruncationLinearMap m a p : R[X]) = forwardTaylorTruncation m a p :=
  rfl

/-- The coefficient coordinates of the degree-bounded truncation are exactly the Hasse jet. -/
theorem forwardTaylorTruncationLinearMap_coordinates (m : ℕ) (a : R) (p : R[X]) :
    degreeLTEquiv R m (forwardTaylorTruncationLinearMap m a p) = hasseJet m a p := by
  ext i
  change (forwardTaylorTruncation m a p).coeff i = hasseJet m a p i
  rw [coeff_forwardTaylorTruncation, if_pos i.isLt]
  rfl

/-- Once `m` is a strict degree bound for `p`, its finite forward truncation is the full Taylor
shift.  Stating the hypothesis with `degreeLT` includes the zero polynomial even at `m = 0`. -/
theorem forwardTaylorTruncation_eq_taylor_of_mem_degreeLT (m : ℕ) (a : R) (p : R[X])
    (hp : p ∈ degreeLT R m) : forwardTaylorTruncation m a p = taylor a p := by
  ext i
  by_cases hi : i < m
  · exact coeff_forwardTaylorTruncation_of_lt m a p hi
  · rw [coeff_forwardTaylorTruncation_of_le m a p (not_lt.mp hi)]
    have hdeg : (taylor a p).degree < (i : WithBot ℕ) := by
      rw [degree_taylor]
      exact (mem_degreeLT.mp hp).trans_le
        (WithBot.coe_le_coe.mpr (not_lt.mp hi))
    exact (coeff_eq_zero_of_degree_lt hdeg).symm

@[simp]
theorem forwardTaylorTruncation_zero (a : R) (p : R[X]) :
    forwardTaylorTruncation 0 a p = 0 := by
  simp [forwardTaylorTruncation]

@[simp]
theorem forwardTaylorTruncation_one (a : R) (p : R[X]) :
    forwardTaylorTruncation 1 a p = C (p.eval a) := by
  simp [forwardTaylorTruncation, hasseCoeffAt_apply]

/-- At the origin, truncating a monomial either keeps the monomial or discards it. -/
theorem forwardTaylorTruncation_X_pow (m n : ℕ) :
    forwardTaylorTruncation m (0 : R) (X ^ n) = if n < m then X ^ n else 0 := by
  ext i
  have hcoeff : hasseCoeffAt (0 : R) i (X ^ n) = (X ^ n : R[X]).coeff i := by
    rw [hasseCoeffAt_apply, ← taylor_coeff, taylor_zero]
  rw [coeff_forwardTaylorTruncation, hcoeff]
  by_cases hin : i = n
  · subst i
    by_cases hn : n < m
    · rw [if_pos hn, if_pos hn, coeff_X_pow_self]
    · rw [if_neg hn, if_neg hn, coeff_zero]
  · by_cases hn : n < m
    · rw [if_pos hn, coeff_X_pow, if_neg hin]
      simp
    · rw [if_neg hn, coeff_zero]
      simp [hin]

/-- Re-truncating the coefficient polynomial at zero composes the two bounds by `min`. -/
theorem forwardTaylorTruncation_zero_comp (m n : ℕ) (a : R) (p : R[X]) :
    forwardTaylorTruncation m 0 (forwardTaylorTruncation n a p) =
      forwardTaylorTruncation (min m n) a p := by
  ext i
  rw [coeff_forwardTaylorTruncation, hasseCoeffAt_zero_eq_coeff,
    coeff_forwardTaylorTruncation, coeff_forwardTaylorTruncation]
  simp only [lt_min_iff]
  split_ifs <;> simp_all

end Semiring

section Ring

variable [Ring R]

/-- The part of the forward Taylor shift left after removing all orders below `m`. -/
def forwardTaylorRemainder (m : ℕ) (a : R) (p : R[X]) : R[X] :=
  taylor a p - forwardTaylorTruncation m a p

/-- Every coefficient of the forward Taylor remainder below `m` vanishes. -/
theorem coeff_forwardTaylorRemainder_of_lt (m : ℕ) (a : R) (p : R[X]) {i : ℕ}
    (hi : i < m) : (forwardTaylorRemainder m a p).coeff i = 0 := by
  rw [forwardTaylorRemainder, coeff_sub, coeff_forwardTaylorTruncation_of_lt m a p hi,
    sub_self]

/-- The forward Taylor remainder is divisible by `X ^ m`. -/
theorem X_pow_dvd_forwardTaylorRemainder (m : ℕ) (a : R) (p : R[X]) :
    X ^ m ∣ forwardTaylorRemainder m a p := by
  rw [X_pow_dvd_iff]
  exact fun i hi ↦ coeff_forwardTaylorRemainder_of_lt m a p hi

/-- The canonical monic-division quotient of the forward Taylor remainder by `X ^ m`. -/
def forwardTaylorQuotient (m : ℕ) (a : R) (p : R[X]) : R[X] :=
  forwardTaylorRemainder m a p /ₘ (X ^ m)

/-- Multiplying the canonical quotient by `X ^ m` recovers the forward Taylor remainder. -/
theorem X_pow_mul_forwardTaylorQuotient (m : ℕ) (a : R) (p : R[X]) :
    X ^ m * forwardTaylorQuotient m a p = forwardTaylorRemainder m a p := by
  have hmod : forwardTaylorRemainder m a p %ₘ (X ^ m) = 0 :=
    (modByMonic_eq_zero_iff_dvd (monic_X_pow m)).2
      (X_pow_dvd_forwardTaylorRemainder m a p)
  simpa [forwardTaylorQuotient, hmod] using
    modByMonic_add_div (forwardTaylorRemainder m a p) (X ^ m)

/-- Finite forward Hasse--Taylor reconstruction with a canonical quotient remainder. -/
theorem taylor_eq_forwardTaylorTruncation_add_X_pow_mul_quotient
    (m : ℕ) (a : R) (p : R[X]) :
    taylor a p =
      forwardTaylorTruncation m a p + X ^ m * forwardTaylorQuotient m a p := by
  rw [X_pow_mul_forwardTaylorQuotient, forwardTaylorRemainder]
  rw [sub_eq_add_neg]
  calc
    taylor a p = 0 + taylor a p := (zero_add _).symm
    _ = (forwardTaylorTruncation m a p + -forwardTaylorTruncation m a p) + taylor a p := by
      rw [add_neg_cancel]
    _ = forwardTaylorTruncation m a p + (taylor a p + -forwardTaylorTruncation m a p) := by
      ac_rfl

@[simp]
theorem forwardTaylorRemainder_zero (a : R) (p : R[X]) :
    forwardTaylorRemainder 0 a p = taylor a p := by
  simp [forwardTaylorRemainder]

/-- A truncation past the degree of `p` has zero forward remainder. -/
theorem forwardTaylorRemainder_eq_zero_of_mem_degreeLT (m : ℕ) (a : R) (p : R[X])
    (hp : p ∈ degreeLT R m) : forwardTaylorRemainder m a p = 0 := by
  rw [forwardTaylorRemainder, forwardTaylorTruncation_eq_taylor_of_mem_degreeLT m a p hp,
    sub_self]

@[simp]
theorem forwardTaylorRemainder_one (a : R) (p : R[X]) :
    forwardTaylorRemainder 1 a p = taylor a p - C (p.eval a) := by
  simp [forwardTaylorRemainder]

@[simp]
theorem forwardTaylorQuotient_zero (a : R) (p : R[X]) :
    forwardTaylorQuotient 0 a p = taylor a p := by
  simp [forwardTaylorQuotient]

/-- A truncation past the degree of `p` also has zero canonical quotient. -/
theorem forwardTaylorQuotient_eq_zero_of_mem_degreeLT (m : ℕ) (a : R) (p : R[X])
    (hp : p ∈ degreeLT R m) : forwardTaylorQuotient m a p = 0 := by
  rw [forwardTaylorQuotient, forwardTaylorRemainder_eq_zero_of_mem_degreeLT m a p hp,
    zero_divByMonic]

end Ring

end


end Polynomial
