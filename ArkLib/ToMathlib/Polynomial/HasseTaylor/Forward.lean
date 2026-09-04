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

/-! ### Finite truncation and degree-bounded coordinates -/

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

/-- The degree-bounded forward truncation map is obtained by decoding Hasse-jet coordinates. -/
theorem forwardTaylorTruncationLinearMap_eq_degreeLTEquiv_symm_comp_hasseJet
    (m : ℕ) (a : R) :
    forwardTaylorTruncationLinearMap m a =
      (degreeLTEquiv R m).symm.toLinearMap.comp (hasseJet m a) := by
  apply LinearMap.ext
  intro p
  apply (degreeLTEquiv R m).injective
  rw [forwardTaylorTruncationLinearMap_coordinates]
  simp

/-- Forward Taylor truncation is natural under coefficient-ring homomorphisms. -/
theorem map_forwardTaylorTruncation {S : Type*} [Semiring S] (f : R →+* S)
    (m : ℕ) (a : R) (p : R[X]) :
    (forwardTaylorTruncation m a p).map f =
      forwardTaylorTruncation m (f a) (p.map f) := by
  ext i
  simp only [coeff_map, coeff_forwardTaylorTruncation]
  by_cases hi : i < m
  · rw [if_pos hi, if_pos hi]
    exact map_hasseCoeffAt f a i p
  · rw [if_neg hi, if_neg hi, map_zero]

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

section CommSemiring

variable [CommSemiring R]

/-! ### Change of center and affine substitution -/

/-- Successive changes of origin add their centers before finite forward truncation. -/
theorem forwardTaylorTruncation_taylor (m : ℕ) (a b : R) (p : R[X]) :
    forwardTaylorTruncation m b (taylor a p) =
      forwardTaylorTruncation m (b + a) p := by
  ext i
  simp only [coeff_forwardTaylorTruncation]
  split_ifs
  · rw [hasseCoeffAt_taylor]
  · rfl

/-- Finite forward truncation commutes with an affine substitution, with the output variable
scaled by the same factor. -/
theorem forwardTaylorTruncation_taylor_comp_C_mul_X
    (m : ℕ) (a b c : R) (p : R[X]) :
    forwardTaylorTruncation m b ((taylor a p).comp (C c * X)) =
      (forwardTaylorTruncation m (c * b + a) p).comp (C c * X) := by
  ext i
  rw [coeff_forwardTaylorTruncation, comp_C_mul_X_coeff,
    coeff_forwardTaylorTruncation]
  by_cases hi : i < m
  · rw [if_pos hi, if_pos hi, hasseCoeffAt_taylor_comp_C_mul_X]
  · rw [if_neg hi, if_neg hi, zero_mul]

end CommSemiring

section Ring

variable [Ring R]

/-! ### Canonical forward remainders and tail quotients -/

/-- The part of the forward Taylor shift left after removing all orders below `m`. -/
def forwardTaylorRemainder (m : ℕ) (a : R) (p : R[X]) : R[X] :=
  taylor a p - forwardTaylorTruncation m a p

/-- Forward Taylor remainders are natural under coefficient-ring homomorphisms. -/
theorem map_forwardTaylorRemainder {S : Type*} [Ring S] (f : R →+* S)
    (m : ℕ) (a : R) (p : R[X]) :
    (forwardTaylorRemainder m a p).map f =
      forwardTaylorRemainder m (f a) (p.map f) := by
  rw [forwardTaylorRemainder, forwardTaylorRemainder, Polynomial.map_sub, map_taylor,
    map_forwardTaylorTruncation]

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

/-- Coefficient `i` of the canonical quotient is Hasse--Taylor order `i + m` of `p` at `a`. -/
@[simp]
theorem coeff_forwardTaylorQuotient (m : ℕ) (a : R) (p : R[X]) (i : ℕ) :
    (forwardTaylorQuotient m a p).coeff i = hasseCoeffAt a (i + m) p := by
  have h := congrArg (fun q : R[X] ↦ q.coeff (i + m))
    (X_pow_mul_forwardTaylorQuotient m a p)
  rw [coeff_X_pow_mul, forwardTaylorRemainder, coeff_sub,
    coeff_forwardTaylorTruncation_of_le m a p (Nat.le_add_left m i), sub_zero,
    taylor_coeff] at h
  exact h

/-- The final `n` coordinates of an order-`m + n` jet are the order-`n` jet at zero of the
order-`m` forward Taylor quotient.  The canonical `Fin.natAdd` embedding selects this tail. -/
theorem hasseJet_natAdd_eq_forwardTaylorQuotient
    (m n : ℕ) (a : R) (p : R[X]) :
    (fun i : Fin n ↦ hasseJet (m + n) a p (Fin.natAdd m i)) =
      hasseJet n 0 (forwardTaylorQuotient m a p) := by
  ext i
  change hasseCoeffAt a (m + (i : ℕ)) p =
    hasseCoeffAt 0 (i : ℕ) (forwardTaylorQuotient m a p)
  rw [hasseCoeffAt_zero_eq_coeff, coeff_forwardTaylorQuotient]
  congr 2
  omega

/-- Removing the first `m` Taylor coefficients lowers natural degree by at least `m`.

This formulation is zero-aware: it remains meaningful for `p = 0` and when `m` exceeds the
degree of `p`. -/
theorem natDegree_forwardTaylorQuotient_le (m : ℕ) (a : R) (p : R[X]) :
    (forwardTaylorQuotient m a p).natDegree ≤ p.natDegree - m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_forwardTaylorQuotient, hasseCoeffAt_apply,
    hasseDeriv_eq_zero_of_lt_natDegree p (i + m) (by omega), eval_zero]

/-- A strict degree bound on `p` descends by `m` to its canonical forward Taylor quotient. -/
theorem forwardTaylorQuotient_mem_degreeLT (m d : ℕ) (a : R) (p : R[X])
    (hp : p ∈ degreeLT R d) :
    forwardTaylorQuotient m a p ∈ degreeLT R (d - m) := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hp ⊢
  intro i hi
  rw [coeff_forwardTaylorQuotient, hasseCoeffAt_apply]
  have hderiv : hasseDeriv (i + m) p = 0 := by
    ext j
    rw [hasseDeriv_coeff, hp (j + (i + m)) (by omega), mul_zero, coeff_zero]
  rw [hderiv, eval_zero]

/-- Removing `m + n` Taylor coefficients at once is the same as dropping another `n`
coefficients from the order-`m` quotient. -/
theorem forwardTaylorQuotient_add_eq_iterate_divX (m n : ℕ) (a : R) (p : R[X]) :
    forwardTaylorQuotient (m + n) a p =
      divX^[n] (forwardTaylorQuotient m a p) := by
  ext i
  rw [coeff_forwardTaylorQuotient]
  have coeff_iterate_divX (f : R[X]) (k j : ℕ) :
      (divX^[k] f).coeff j = f.coeff (j + k) := by
    induction k generalizing f j with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply, coeff_divX, ih]
      congr 1
      omega
  rw [coeff_iterate_divX, coeff_forwardTaylorQuotient]
  congr 2
  omega

/-- Canonical Taylor quotients form a tail tower: taking an order-`n` quotient at zero from the
order-`m` quotient is the order-`m + n` quotient of the original polynomial. -/
theorem forwardTaylorQuotient_zero_comp (m n : ℕ) (a : R) (p : R[X]) :
    forwardTaylorQuotient n 0 (forwardTaylorQuotient m a p) =
      forwardTaylorQuotient (m + n) a p := by
  ext i
  rw [coeff_forwardTaylorQuotient, hasseCoeffAt_zero_eq_coeff,
    coeff_forwardTaylorQuotient, coeff_forwardTaylorQuotient]
  congr 2
  omega

/-- Canonical forward Taylor quotients are natural under coefficient-ring homomorphisms. -/
theorem map_forwardTaylorQuotient {S : Type*} [Ring S] (f : R →+* S)
    (m : ℕ) (a : R) (p : R[X]) :
    (forwardTaylorQuotient m a p).map f =
      forwardTaylorQuotient m (f a) (p.map f) := by
  ext i
  rw [coeff_map, coeff_forwardTaylorQuotient, coeff_forwardTaylorQuotient]
  exact map_hasseCoeffAt f a (i + m) p

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

section CommRing

variable [CommRing R]

/-! ### Change of center and affine substitution for remainders -/

/-- Successive changes of origin add their centers before taking the forward remainder. -/
theorem forwardTaylorRemainder_taylor (m : ℕ) (a b : R) (p : R[X]) :
    forwardTaylorRemainder m b (taylor a p) =
      forwardTaylorRemainder m (b + a) p := by
  rw [forwardTaylorRemainder, forwardTaylorRemainder, taylor_taylor,
    forwardTaylorTruncation_taylor]

/-- Successive changes of origin add their centers before taking the canonical tail quotient. -/
theorem forwardTaylorQuotient_taylor (m : ℕ) (a b : R) (p : R[X]) :
    forwardTaylorQuotient m b (taylor a p) =
      forwardTaylorQuotient m (b + a) p := by
  rw [forwardTaylorQuotient, forwardTaylorQuotient, forwardTaylorRemainder_taylor]

/-- Forward Taylor remainders commute with affine substitution. -/
theorem forwardTaylorRemainder_taylor_comp_C_mul_X
    (m : ℕ) (a b c : R) (p : R[X]) :
    forwardTaylorRemainder m b ((taylor a p).comp (C c * X)) =
      (forwardTaylorRemainder m (c * b + a) p).comp (C c * X) := by
  rw [forwardTaylorRemainder, forwardTaylorRemainder, sub_comp,
    forwardTaylorTruncation_taylor_comp_C_mul_X]
  congr 1
  ext i
  rw [taylor_coeff, comp_C_mul_X_coeff, taylor_coeff]
  exact hasseCoeffAt_taylor_comp_C_mul_X a b c i p

/-- Under affine substitution, the canonical tail quotient scales by the `m`-th power of the
linear coefficient, in addition to scaling its output variable. -/
theorem forwardTaylorQuotient_taylor_comp_C_mul_X
    (m : ℕ) (a b c : R) (p : R[X]) :
    forwardTaylorQuotient m b ((taylor a p).comp (C c * X)) =
      C (c ^ m) * (forwardTaylorQuotient m (c * b + a) p).comp (C c * X) := by
  ext i
  rw [coeff_forwardTaylorQuotient, coeff_C_mul, comp_C_mul_X_coeff,
    coeff_forwardTaylorQuotient, hasseCoeffAt_taylor_comp_C_mul_X, pow_add]
  ac_rfl

end CommRing

end


end Polynomial
