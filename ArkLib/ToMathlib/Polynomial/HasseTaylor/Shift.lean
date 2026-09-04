/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Sum

/-!
# Hasse--Taylor shifts and backward residuals

Characteristic-independent shift, vanishing, and moving-point backward Hasse identities. The
elementary shift increment quotient and the paper's truncation-dependent backward error are
different constructions and are named separately.

The moving-point API formalizes the finite form of the backward identity used as Equation (13)
and its normalized remainder from Equation (16) in BCPZZ26. For truncation order `d`, correction
term `j` has Hasse order `j + 1`, sign `(-1)^j`, and derivative evaluated at the moving point
`a + X`. The numerator is divisible by `X ^ (d + 1)` and its normalized error by `X ^ d`.

## Main declarations

* `X_pow_dvd_taylor_iff`: truncated Hasse vanishing as divisibility.
* `hasseDeriv_taylor`: Hasse derivatives commute with Taylor shifts.
* `backwardTaylorReconstruction`: finite moving-point backward reconstruction.
* `X_pow_succ_dvd_backwardTaylorResidual`: divisibility of the unnormalized numerator.
* `X_pow_dvd_normalizedBackwardTaylorError`: divisibility after removing one factor of `X`.
* `X_mul_normalizedBackwardTaylorError`: the normalized-error identity itself.
-/

namespace Polynomial

noncomputable section

private theorem map_divX {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (p : R[X]) : p.divX.map f = (p.map f).divX := by
  ext n
  simp [coeff_divX]

section Semiring

variable {R : Type*} [Semiring R]

/-! ### Elementary shift quotients -/

/-- Removing the leading `X` from `X * p` recovers `p`. -/
private theorem divX_X_mul (p : R[X]) : (X * p).divX = p := by
  ext n
  simp [coeff_divX, coeff_X_mul]

/-- `X ^ m` divides the Taylor expansion at `a` iff the first `m` Hasse derivatives vanish. -/
theorem X_pow_dvd_taylor_iff (p : R[X]) (a : R) (m : ℕ) :
    X ^ m ∣ taylor a p ↔ ∀ i < m, (hasseDeriv i p).eval a = 0 := by
  rw [X_pow_dvd_iff]
  simp only [taylor_coeff]

/-- The quotient of the shifted increment `p(a + X) - p(a)` by `X`.

This is not the moving-point backward error defined later in this file. -/
def shiftIncrementQuotient (a : R) (p : R[X]) : R[X] :=
  (taylor a p).divX

/-- Decompose a Taylor shift into its center value and shifted increment quotient. -/
theorem taylor_eq_C_add_X_mul_shiftIncrementQuotient (p : R[X]) (a : R) :
    taylor a p = C (p.eval a) + X * shiftIncrementQuotient a p := by
  simpa only [shiftIncrementQuotient, taylor_coeff_zero, add_comm] using
    (X_mul_divX_add (taylor a p)).symm

/-- Decomposition with a caller-supplied center value. -/
theorem taylor_eq_C_add_X_mul_shiftIncrementQuotient_of_eval_eq {p : R[X]} {a y : R}
    (h : p.eval a = y) :
    taylor a p = C y + X * shiftIncrementQuotient a p := by
  simpa only [h] using taylor_eq_C_add_X_mul_shiftIncrementQuotient p a

/-- Coefficient `i` is Hasse derivative `i + 1`; normalization introduces an off-by-one. -/
theorem coeff_shiftIncrementQuotient (p : R[X]) (a : R) (i : ℕ) :
    (shiftIncrementQuotient a p).coeff i = (hasseDeriv (i + 1) p).eval a := by
  rw [shiftIncrementQuotient, coeff_divX, taylor_coeff]

/-- The increment quotient has degree one below the original polynomial. -/
theorem natDegree_shiftIncrementQuotient (p : R[X]) (a : R) :
    (shiftIncrementQuotient a p).natDegree = p.natDegree - 1 := by
  rw [shiftIncrementQuotient, natDegree_divX_eq_natDegree_tsub_one, natDegree_taylor]

/-- Vanishing orders one through `m` are equivalent to `X ^ m` dividing the increment quotient. -/
theorem X_pow_dvd_shiftIncrementQuotient_iff (p : R[X]) (a : R) (m : ℕ) :
    X ^ m ∣ shiftIncrementQuotient a p ↔
      ∀ i < m, (hasseDeriv (i + 1) p).eval a = 0 := by
  rw [X_pow_dvd_iff]
  simp only [coeff_shiftIncrementQuotient]

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-! ### Hasse derivatives under shifts -/

/-- Hasse differentiation commutes with shifting the polynomial's input. -/
theorem hasseDeriv_taylor (p : R[X]) (a : R) (k : ℕ) :
    hasseDeriv k (taylor a p) = taylor a (hasseDeriv k p) := by
  ext n
  rw [hasseDeriv_coeff, taylor_coeff, taylor_coeff]
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := R) n k) p
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  rw [h, eval_smul, Nat.choose_symm_add]
  simp [nsmul_eq_mul]

end CommSemiring

section Ring

variable {R : Type*} [Ring R]

/-! ### Shifted-difference congruences -/

/-- Matching Hasse coefficients through order `m - 1` are equivalent to a shifted congruence
modulo `X ^ m`. -/
theorem X_pow_dvd_taylor_sub_iff (p q : R[X]) (a : R) (m : ℕ) :
    X ^ m ∣ taylor a p - taylor a q ↔
      ∀ i < m, (hasseDeriv i p).eval a = (hasseDeriv i q).eval a := by
  rw [← LinearMap.map_sub, X_pow_dvd_taylor_iff]
  simp only [LinearMap.map_sub, eval_sub, sub_eq_zero]

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/-! ### Scalar Hasse vanishing and root multiplicity -/

private theorem divX_sub (p q : R[X]) : (p - q).divX = p.divX - q.divX := by
  ext n
  simp [coeff_divX]

private theorem hasseDeriv_comp_C_mul_X (p : R[X]) (c : R) (k : ℕ) :
    hasseDeriv k (p.comp (C c * X)) =
      C (c ^ k) * (hasseDeriv k p).comp (C c * X) := by
  ext n
  simp only [hasseDeriv_coeff, coeff_C_mul, comp_C_mul_X_coeff, pow_add]
  ring

private theorem taylor_comp_C_mul_X (p : R[X]) (a c : R) :
    taylor a (p.comp (C c * X)) = (taylor (c * a) p).comp (C c * X) := by
  simp only [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, mul_comp]
  congr 2
  rw [map_mul]
  ring

private theorem divX_comp_C_mul_X (q : R[X]) (c : R) :
    (q.comp (C c * X)).divX = C c * q.divX.comp (C c * X) := by
  ext n
  simp only [coeff_divX, comp_C_mul_X_coeff, coeff_C_mul, pow_succ]
  ring

/-- Hasse vanishing at `a` is equivalent to divisibility by the corresponding root factor. -/
theorem X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero (p : R[X]) (a : R) (m : ℕ) :
    (X - C a) ^ m ∣ p ↔ ∀ i < m, (hasseDeriv i p).eval a = 0 := by
  rw [X_sub_C_pow_dvd_iff]
  change X ^ m ∣ taylor a p ↔ ∀ i < m, (hasseDeriv i p).eval a = 0
  exact X_pow_dvd_taylor_iff p a m

/-- Hasse vanishing characterizes root multiplicity for a nonzero polynomial. -/
theorem hasseDeriv_eval_eq_zero_iff_le_rootMultiplicity {p : R[X]} (hp : p ≠ 0)
    (a : R) (m : ℕ) :
    (∀ i < m, (hasseDeriv i p).eval a = 0) ↔ m ≤ p.rootMultiplicity a :=
  (X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero p a m).symm.trans
    (le_rootMultiplicity_iff hp).symm

/-! ### Generic backward correction in shifted coordinates -/

private theorem Int.alternating_sum_choose_succ {n : ℕ} (hn : n ≠ 0) :
    (∑ j ∈ Finset.range n, (-1 : ℤ) ^ j * (n.choose (j + 1) : ℤ)) = 1 := by
  have h := Int.alternating_sum_range_choose_of_ne hn
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.choose_zero_right, Int.natCast_one, pow_zero, one_mul] at h
  rw [show (∑ x ∈ Finset.range n, (-1 : ℤ) ^ (x + 1) * ↑(n.choose (x + 1))) =
      -(∑ x ∈ Finset.range n, (-1 : ℤ) ^ x * ↑(n.choose (x + 1))) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring] at h
  omega

private theorem alternating_sum_choose_succ {n : ℕ} (hn : n ≠ 0) :
    (∑ j ∈ Finset.range n, (-1 : R) ^ j * (n.choose (j + 1) : R)) = 1 := by
  have h := congrArg (Int.castRingHom R) (Int.alternating_sum_choose_succ hn)
  simpa using h

/-- First `d` moving-Hasse correction terms for a polynomial in shifted coordinates. -/
def backwardHasseSum (d : ℕ) (q : R[X]) : R[X] :=
  ∑ j ∈ Finset.range d,
    C ((-1 : R) ^ j) * (X ^ (j + 1) * hasseDeriv (j + 1) q)

/-- Through degree `d`, the correction sum reproduces every nonconstant coefficient. -/
theorem coeff_backwardHasseSum {d n : ℕ} (q : R[X]) (hn : n ≠ 0) (hnd : n ≤ d) :
    (backwardHasseSum d q).coeff n = q.coeff n := by
  rw [backwardHasseSum, finsetSum_coeff]
  rw [← Finset.sum_subset (Finset.range_mono hnd)]
  · have hterm : ∀ j ∈ Finset.range n,
        (C ((-1 : R) ^ j) * (X ^ (j + 1) * hasseDeriv (j + 1) q)).coeff n =
          ((-1 : R) ^ j * (n.choose (j + 1) : R)) * q.coeff n := by
      intro j hj
      rw [coeff_C_mul, coeff_X_pow_mul', if_pos]
      · rw [hasseDeriv_coeff]
        have hsub : n - (j + 1) + (j + 1) = n := by
          have := Finset.mem_range.mp hj
          omega
        rw [hsub]
        simp [mul_assoc]
      · have := Finset.mem_range.mp hj
        omega
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
      alternating_sum_choose_succ hn, one_mul]
  · intro j hjd hjn
    rw [coeff_C_mul, coeff_X_pow_mul', if_neg]
    · simp
    · have hjd' := Finset.mem_range.mp hjd
      have hjn' : ¬j < n := by simpa using hjn
      omega

/-- Coefficients of the correction sum above the degree of `q` vanish. -/
theorem coeff_backwardHasseSum_eq_zero_of_natDegree_lt {d n : ℕ} (q : R[X])
    (hn : q.natDegree < n) : (backwardHasseSum d q).coeff n = 0 := by
  rw [backwardHasseSum, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  rw [coeff_C_mul, coeff_X_pow_mul']
  split_ifs with h
  · rw [hasseDeriv_coeff]
    have heq : n - (j + 1) + (j + 1) = n := Nat.sub_add_cancel h
    rw [heq, coeff_eq_zero_of_natDegree_lt hn]
    simp
  · simp

/-- The backward correction sum does not increase natural degree. -/
theorem natDegree_backwardHasseSum_le (d : ℕ) (q : R[X]) :
    (backwardHasseSum d q).natDegree ≤ q.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact coeff_backwardHasseSum_eq_zero_of_natDegree_lt q hn

/-- Numerator remaining after the constant and first `d` moving-Hasse terms are removed. -/
def backwardHasseResidual (d : ℕ) (q : R[X]) : R[X] :=
  q - C (q.coeff 0) - backwardHasseSum d q

/-- The generic backward residual does not increase natural degree. -/
theorem natDegree_backwardHasseResidual_le (d : ℕ) (q : R[X]) :
    (backwardHasseResidual d q).natDegree ≤ q.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hn0 : n ≠ 0 := by omega
  rw [backwardHasseResidual, coeff_sub, coeff_sub, coeff_C, if_neg hn0,
    coeff_eq_zero_of_natDegree_lt hn,
    coeff_backwardHasseSum_eq_zero_of_natDegree_lt q hn]
  simp

/-- The generic backward numerator is divisible by `X ^ (d + 1)`. -/
theorem X_pow_succ_dvd_backwardHasseResidual (d : ℕ) (q : R[X]) :
    X ^ (d + 1) ∣ backwardHasseResidual d q := by
  rw [X_pow_dvd_iff]
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [backwardHasseResidual, backwardHasseSum]
  · rw [backwardHasseResidual, coeff_sub, coeff_sub, coeff_C, if_neg hn0, sub_zero,
      coeff_backwardHasseSum q hn0 (by omega), sub_self]

/-- Once `d` reaches the degree of `q`, the finite backward expansion is exact. -/
theorem backwardHasseResidual_eq_zero_of_natDegree_le (d : ℕ) (q : R[X])
    (hdeg : q.natDegree ≤ d) : backwardHasseResidual d q = 0 := by
  ext n
  by_cases hn : n ≤ d
  · by_cases hn0 : n = 0
    · subst n
      simp [backwardHasseResidual, backwardHasseSum]
    · rw [backwardHasseResidual, coeff_sub, coeff_sub, coeff_C, if_neg hn0, sub_zero,
        coeff_backwardHasseSum q hn0 hn, sub_self, coeff_zero]
  · have hqn : q.natDegree < n := hdeg.trans_lt (Nat.lt_of_not_ge hn)
    have hn0 : n ≠ 0 := by omega
    rw [backwardHasseResidual, coeff_sub, coeff_sub, coeff_C, if_neg hn0,
      coeff_eq_zero_of_natDegree_lt hqn,
      coeff_backwardHasseSum_eq_zero_of_natDegree_lt q hqn, coeff_zero]
    simp

/-- Backward residual after removing its guaranteed factor of `X`. -/
def normalizedBackwardHasseResidual (d : ℕ) (q : R[X]) : R[X] :=
  (backwardHasseResidual d q).divX

/-- Removing one `X` leaves a residual divisible by `X ^ d`. -/
theorem X_pow_dvd_normalizedBackwardHasseResidual (d : ℕ) (q : R[X]) :
    X ^ d ∣ normalizedBackwardHasseResidual d q := by
  rw [X_pow_dvd_iff]
  intro n hn
  rw [normalizedBackwardHasseResidual, coeff_divX]
  exact X_pow_dvd_iff.mp (X_pow_succ_dvd_backwardHasseResidual d q) (n + 1) (by omega)

/-- Multiplication by `X` reconstructs the generic backward numerator. -/
theorem X_mul_normalizedBackwardHasseResidual (d : ℕ) (q : R[X]) :
    X * normalizedBackwardHasseResidual d q = backwardHasseResidual d q := by
  have hzero := X_pow_dvd_iff.mp (X_pow_succ_dvd_backwardHasseResidual d q) 0 (by omega)
  simpa only [normalizedBackwardHasseResidual, hzero, C_0, add_zero] using
    X_mul_divX_add (backwardHasseResidual d q)

/-! ### Moving-point backward reconstruction -/

/-- Paper-facing correction sum. Derivatives are evaluated at moving point `a + X`. -/
def movingHasseSum (a : R) (p : R[X]) (d : ℕ) : R[X] :=
  ∑ j ∈ Finset.range d,
    C ((-1 : R) ^ j) * (X ^ (j + 1) * taylor a (hasseDeriv (j + 1) p))

/-- The moving-Hasse correction sum is natural under coefficient-ring homomorphisms. -/
theorem map_movingHasseSum {S : Type*} [CommRing S] (f : R →+* S)
    (a : R) (p : R[X]) (d : ℕ) :
    (movingHasseSum a p d).map f = movingHasseSum (f a) (p.map f) d := by
  rw [movingHasseSum, movingHasseSum, Polynomial.map_sum f]
  apply Finset.sum_congr rfl
  intro j _
  simp [map_hasseDeriv, map_taylor]

/-- Successive changes of origin add their centers in the moving-Hasse correction sum. -/
theorem movingHasseSum_taylor (a b : R) (p : R[X]) (d : ℕ) :
    movingHasseSum b (taylor a p) d = movingHasseSum (b + a) p d := by
  rw [movingHasseSum, movingHasseSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hasseDeriv_taylor, taylor_taylor]

/-- Scaling the input variable scales every moving Hasse order by the corresponding power. -/
theorem movingHasseSum_comp_C_mul_X (a c : R) (p : R[X]) (d : ℕ) :
    movingHasseSum a (p.comp (C c * X)) d =
      (movingHasseSum (c * a) p d).comp (C c * X) := by
  rw [movingHasseSum, movingHasseSum, sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comp, mul_comp, C_comp, pow_comp, X_comp, hasseDeriv_comp_C_mul_X,
    taylor_mul, taylor_C, taylor_comp_C_mul_X, mul_pow, C_pow]
  simp only [map_pow]
  ring

/-- An affine change of variable sends observation center `b` to `c * b + a`. -/
theorem movingHasseSum_taylor_comp_C_mul_X (a b c : R) (p : R[X]) (d : ℕ) :
    movingHasseSum b ((taylor a p).comp (C c * X)) d =
      (movingHasseSum (c * b + a) p d).comp (C c * X) := by
  rw [movingHasseSum_comp_C_mul_X, movingHasseSum_taylor]

/-- Adding one truncation order appends exactly the next alternating moving-Hasse term. -/
theorem movingHasseSum_succ (a : R) (p : R[X]) (d : ℕ) :
    movingHasseSum a p (d + 1) = movingHasseSum a p d +
      C ((-1 : R) ^ d) * (X ^ (d + 1) * taylor a (hasseDeriv (d + 1) p)) := by
  rw [movingHasseSum, movingHasseSum, Finset.sum_range_succ]

/-- The moving-Hasse correction sum is additive in the input polynomial. -/
theorem movingHasseSum_add (a : R) (p q : R[X]) (d : ℕ) :
    movingHasseSum a (p + q) d = movingHasseSum a p d + movingHasseSum a q d := by
  simp only [movingHasseSum, LinearMap.map_add, mul_add, Finset.sum_add_distrib]

/-- The moving-Hasse correction sum respects coefficient scalar multiplication. -/
theorem movingHasseSum_smul (c a : R) (p : R[X]) (d : ℕ) :
    movingHasseSum a (c • p) d = c • movingHasseSum a p d := by
  simp only [movingHasseSum, smul_eq_C_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show C c * p = c • p by rw [smul_eq_C_mul]]
  rw [LinearMap.map_smul, LinearMap.map_smul]
  simp only [smul_eq_C_mul]
  ring

@[simp]
theorem movingHasseSum_zero (a : R) (d : ℕ) : movingHasseSum a 0 d = 0 := by
  simp [movingHasseSum]

/-- Moving derivatives of `p` are ordinary Hasse derivatives of its Taylor shift. -/
theorem movingHasseSum_eq_backwardHasseSum (a : R) (p : R[X]) (d : ℕ) :
    movingHasseSum a p d = backwardHasseSum d (taylor a p) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [hasseDeriv_taylor]

/-- The correction sum reproduces each nonconstant Taylor coefficient through order `d`. -/
theorem coeff_movingHasseSum {a : R} {p : R[X]} {d n : ℕ} (hn : n ≠ 0) (hnd : n ≤ d) :
    (movingHasseSum a p d).coeff n = (hasseDeriv n p).eval a := by
  rw [movingHasseSum_eq_backwardHasseSum,
    coeff_backwardHasseSum (taylor a p) hn hnd, taylor_coeff]

/-- At order one, the moving-Hasse sum is the shifted ordinary derivative times `X`. -/
theorem movingHasseSum_one (a : R) (p : R[X]) :
    movingHasseSum a p 1 = X * taylor a p.derivative := by
  simp [movingHasseSum]

/-- Numerator left by the finite paper-facing moving-Hasse correction sum. -/
def backwardTaylorResidual (a : R) (p : R[X]) (d : ℕ) : R[X] :=
  taylor a p - C (p.eval a) - movingHasseSum a p d

/-- The moving-point backward numerator is natural under coefficient-ring homomorphisms. -/
theorem map_backwardTaylorResidual {S : Type*} [CommRing S] (f : R →+* S)
    (a : R) (p : R[X]) (d : ℕ) :
    (backwardTaylorResidual a p d).map f =
      backwardTaylorResidual (f a) (p.map f) d := by
  simp [backwardTaylorResidual, map_taylor, eval_map, map_movingHasseSum]

/-- Successive changes of origin add their centers in the moving-point backward numerator. -/
theorem backwardTaylorResidual_taylor (a b : R) (p : R[X]) (d : ℕ) :
    backwardTaylorResidual b (taylor a p) d =
      backwardTaylorResidual (b + a) p d := by
  rw [backwardTaylorResidual, backwardTaylorResidual, taylor_taylor, taylor_eval,
    movingHasseSum_taylor]

/-- The backward numerator commutes with scaling the input variable. -/
theorem backwardTaylorResidual_comp_C_mul_X (a c : R) (p : R[X]) (d : ℕ) :
    backwardTaylorResidual a (p.comp (C c * X)) d =
      (backwardTaylorResidual (c * a) p d).comp (C c * X) := by
  rw [backwardTaylorResidual, backwardTaylorResidual, sub_comp, sub_comp,
    C_comp, taylor_comp_C_mul_X, movingHasseSum_comp_C_mul_X]
  congr 2
  rw [eval_comp]
  simp

/-- The backward numerator commutes with an affine change of variable. -/
theorem backwardTaylorResidual_taylor_comp_C_mul_X (a b c : R) (p : R[X]) (d : ℕ) :
    backwardTaylorResidual b ((taylor a p).comp (C c * X)) d =
      (backwardTaylorResidual (c * b + a) p d).comp (C c * X) := by
  rw [backwardTaylorResidual_comp_C_mul_X, backwardTaylorResidual_taylor]

/-- Increasing the truncation order subtracts the next moving-Hasse term from the residual. -/
theorem backwardTaylorResidual_succ (a : R) (p : R[X]) (d : ℕ) :
    backwardTaylorResidual a p (d + 1) = backwardTaylorResidual a p d -
      C ((-1 : R) ^ d) * (X ^ (d + 1) * taylor a (hasseDeriv (d + 1) p)) := by
  rw [backwardTaylorResidual, backwardTaylorResidual, movingHasseSum_succ]
  ring

/-- The moving-point backward numerator is additive in the input polynomial. -/
theorem backwardTaylorResidual_add (a : R) (p q : R[X]) (d : ℕ) :
    backwardTaylorResidual a (p + q) d =
      backwardTaylorResidual a p d + backwardTaylorResidual a q d := by
  rw [backwardTaylorResidual, backwardTaylorResidual, backwardTaylorResidual,
    LinearMap.map_add, eval_add, map_add, movingHasseSum_add]
  ring

/-- The moving-point backward numerator respects coefficient scalar multiplication. -/
theorem backwardTaylorResidual_smul (c a : R) (p : R[X]) (d : ℕ) :
    backwardTaylorResidual a (c • p) d = c • backwardTaylorResidual a p d := by
  rw [backwardTaylorResidual, backwardTaylorResidual]
  simp only [LinearMap.map_smul, eval_smul, movingHasseSum_smul]
  simp only [smul_eq_C_mul, smul_eq_mul, map_mul]
  ring

@[simp]
theorem backwardTaylorResidual_zero (a : R) (d : ℕ) : backwardTaylorResidual a 0 d = 0 := by
  simp [backwardTaylorResidual]

/-- The moving-point backward numerator as an `R`-linear map in the input polynomial. -/
def backwardTaylorResidualLinearMap (a : R) (d : ℕ) : R[X] →ₗ[R] R[X] where
  toFun p := backwardTaylorResidual a p d
  map_add' p q := backwardTaylorResidual_add a p q d
  map_smul' c p := backwardTaylorResidual_smul c a p d

@[simp]
theorem backwardTaylorResidualLinearMap_apply (a : R) (d : ℕ) (p : R[X]) :
    backwardTaylorResidualLinearMap a d p = backwardTaylorResidual a p d := rfl

/-- The order-one residual recovers the earlier derivative-contact identity exactly. -/
theorem backwardTaylorResidual_one (a : R) (p : R[X]) :
    backwardTaylorResidual a p 1 =
      taylor a p - C (p.eval a) - X * taylor a p.derivative := by
  rw [backwardTaylorResidual, movingHasseSum_one]

/-- The paper-facing residual is the generic residual applied to the shifted polynomial. -/
theorem backwardTaylorResidual_eq (a : R) (p : R[X]) (d : ℕ) :
    backwardTaylorResidual a p d = backwardHasseResidual d (taylor a p) := by
  rw [backwardTaylorResidual, backwardHasseResidual, movingHasseSum_eq_backwardHasseSum,
    taylor_coeff_zero]

/-- The paper-facing backward numerator does not increase the degree of `p`. -/
theorem natDegree_backwardTaylorResidual_le (a : R) (p : R[X]) (d : ℕ) :
    (backwardTaylorResidual a p d).natDegree ≤ p.natDegree := by
  rw [backwardTaylorResidual_eq, ← natDegree_taylor p a]
  exact natDegree_backwardHasseResidual_le d (taylor a p)

/-- The paper-facing numerator has a zero of order at least `d + 1`. -/
theorem X_pow_succ_dvd_backwardTaylorResidual (a : R) (p : R[X]) (d : ℕ) :
    X ^ (d + 1) ∣ backwardTaylorResidual a p d := by
  rw [backwardTaylorResidual_eq]
  exact X_pow_succ_dvd_backwardHasseResidual d (taylor a p)

/-- The order-one contact residual is divisible by `X²`. -/
theorem X_sq_dvd_taylor_sub_C_sub_X_mul_derivative (a : R) (p : R[X]) :
    X ^ 2 ∣ taylor a p - C (p.eval a) - X * taylor a p.derivative := by
  simpa only [backwardTaylorResidual_one, Nat.reduceAdd] using
    X_pow_succ_dvd_backwardTaylorResidual a p 1

/-- Every coefficient below degree `d + 1` of the numerator vanishes. -/
theorem coeff_backwardTaylorResidual_eq_zero (a : R) (p : R[X]) (d n : ℕ)
    (hn : n < d + 1) : (backwardTaylorResidual a p d).coeff n = 0 :=
  X_pow_dvd_iff.mp (X_pow_succ_dvd_backwardTaylorResidual a p d) n hn

/-- At or above the polynomial degree, the moving-point backward expansion has no error. -/
theorem backwardTaylorResidual_eq_zero_of_natDegree_le (a : R) (p : R[X]) (d : ℕ)
    (hdeg : p.natDegree ≤ d) : backwardTaylorResidual a p d = 0 := by
  rw [backwardTaylorResidual_eq]
  apply backwardHasseResidual_eq_zero_of_natDegree_le
  simpa only [natDegree_taylor] using hdeg

/-- Canonical normalized moving-point error; unlike the increment quotient, this depends on `d`. -/
def normalizedBackwardTaylorError (a : R) (p : R[X]) (d : ℕ) : R[X] :=
  (backwardTaylorResidual a p d).divX

/-- The normalized moving-point error is natural under coefficient-ring homomorphisms. -/
theorem map_normalizedBackwardTaylorError {S : Type*} [CommRing S] (f : R →+* S)
    (a : R) (p : R[X]) (d : ℕ) :
    (normalizedBackwardTaylorError a p d).map f =
      normalizedBackwardTaylorError (f a) (p.map f) d := by
  simp [normalizedBackwardTaylorError, map_divX, map_backwardTaylorResidual]

/-- Successive changes of origin add their centers in the normalized moving-point error. -/
theorem normalizedBackwardTaylorError_taylor (a b : R) (p : R[X]) (d : ℕ) :
    normalizedBackwardTaylorError b (taylor a p) d =
      normalizedBackwardTaylorError (b + a) p d := by
  rw [normalizedBackwardTaylorError, normalizedBackwardTaylorError,
    backwardTaylorResidual_taylor]

/-- Scaling the input variable contributes one extra factor of `c` after normalization by `X`. -/
theorem normalizedBackwardTaylorError_comp_C_mul_X (a c : R) (p : R[X]) (d : ℕ) :
    normalizedBackwardTaylorError a (p.comp (C c * X)) d =
      C c * (normalizedBackwardTaylorError (c * a) p d).comp (C c * X) := by
  rw [normalizedBackwardTaylorError, normalizedBackwardTaylorError,
    backwardTaylorResidual_comp_C_mul_X, divX_comp_C_mul_X]

/-- The normalized error gains one factor of `c` under an affine change of variable. -/
theorem normalizedBackwardTaylorError_taylor_comp_C_mul_X
    (a b c : R) (p : R[X]) (d : ℕ) :
    normalizedBackwardTaylorError b ((taylor a p).comp (C c * X)) d =
      C c * (normalizedBackwardTaylorError (c * b + a) p d).comp (C c * X) := by
  rw [normalizedBackwardTaylorError_comp_C_mul_X, normalizedBackwardTaylorError_taylor]

/-- Increasing the truncation order subtracts the next normalized moving-Hasse term. -/
theorem normalizedBackwardTaylorError_succ (a : R) (p : R[X]) (d : ℕ) :
    normalizedBackwardTaylorError a p (d + 1) = normalizedBackwardTaylorError a p d -
      C ((-1 : R) ^ d) * (X ^ d * taylor a (hasseDeriv (d + 1) p)) := by
  rw [normalizedBackwardTaylorError, normalizedBackwardTaylorError,
    backwardTaylorResidual_succ, divX_sub]
  have hterm :
      C ((-1 : R) ^ d) * (X ^ (d + 1) * taylor a (hasseDeriv (d + 1) p)) =
        X * (C ((-1 : R) ^ d) * (X ^ d * taylor a (hasseDeriv (d + 1) p))) := by
    rw [pow_succ]
    ring
  rw [hterm, divX_X_mul]

/-- Normalization lowers the residual degree by one. -/
theorem natDegree_normalizedBackwardTaylorError_le (a : R) (p : R[X]) (d : ℕ) :
    (normalizedBackwardTaylorError a p d).natDegree ≤ p.natDegree - 1 := by
  rw [normalizedBackwardTaylorError, natDegree_divX_eq_natDegree_tsub_one]
  exact Nat.sub_le_sub_right (natDegree_backwardTaylorResidual_le a p d) 1

/-- The normalized moving-point error is divisible by `X ^ d`. -/
theorem X_pow_dvd_normalizedBackwardTaylorError (a : R) (p : R[X]) (d : ℕ) :
    X ^ d ∣ normalizedBackwardTaylorError a p d := by
  rw [normalizedBackwardTaylorError, backwardTaylorResidual_eq]
  exact X_pow_dvd_normalizedBackwardHasseResidual d (taylor a p)

/-- Every coefficient below degree `d` of the normalized error vanishes. -/
theorem coeff_normalizedBackwardTaylorError_eq_zero (a : R) (p : R[X]) (d n : ℕ)
    (hn : n < d) : (normalizedBackwardTaylorError a p d).coeff n = 0 :=
  X_pow_dvd_iff.mp (X_pow_dvd_normalizedBackwardTaylorError a p d) n hn

/-- Equation (16): multiplying the normalized moving error by `X` recovers its numerator. -/
theorem X_mul_normalizedBackwardTaylorError (a : R) (p : R[X]) (d : ℕ) :
    X * normalizedBackwardTaylorError a p d = backwardTaylorResidual a p d := by
  rw [normalizedBackwardTaylorError, backwardTaylorResidual_eq]
  exact X_mul_normalizedBackwardHasseResidual d (taylor a p)

/-- Coefficients of the normalized error are shifted numerator coefficients. -/
theorem coeff_normalizedBackwardTaylorError (a : R) (p : R[X]) (d n : ℕ) :
    (normalizedBackwardTaylorError a p d).coeff n =
      (backwardTaylorResidual a p d).coeff (n + 1) := by
  rw [normalizedBackwardTaylorError, coeff_divX]

/-- The normalized moving-point error is additive in the input polynomial. -/
theorem normalizedBackwardTaylorError_add (a : R) (p q : R[X]) (d : ℕ) :
    normalizedBackwardTaylorError a (p + q) d =
      normalizedBackwardTaylorError a p d + normalizedBackwardTaylorError a q d := by
  ext n
  simp only [coeff_normalizedBackwardTaylorError, backwardTaylorResidual_add, coeff_add]

/-- The normalized moving-point error respects coefficient scalar multiplication. -/
theorem normalizedBackwardTaylorError_smul (c a : R) (p : R[X]) (d : ℕ) :
    normalizedBackwardTaylorError a (c • p) d =
      c • normalizedBackwardTaylorError a p d := by
  ext n
  simp only [coeff_normalizedBackwardTaylorError, backwardTaylorResidual_smul, coeff_smul]

@[simp]
theorem normalizedBackwardTaylorError_zero_poly (a : R) (d : ℕ) :
    normalizedBackwardTaylorError a 0 d = 0 := by
  ext n
  simp [coeff_normalizedBackwardTaylorError]

/-- The normalized moving-point error as an `R`-linear map in the input polynomial. -/
def normalizedBackwardTaylorErrorLinearMap (a : R) (d : ℕ) : R[X] →ₗ[R] R[X] where
  toFun p := normalizedBackwardTaylorError a p d
  map_add' p q := normalizedBackwardTaylorError_add a p q d
  map_smul' c p := normalizedBackwardTaylorError_smul c a p d

@[simp]
theorem normalizedBackwardTaylorErrorLinearMap_apply (a : R) (d : ℕ) (p : R[X]) :
    normalizedBackwardTaylorErrorLinearMap a d p =
      normalizedBackwardTaylorError a p d := rfl

/-- Finite moving-point backward reconstruction, with signs `+,-,+,...` from Hasse order one. -/
theorem backwardTaylorReconstruction (a : R) (p : R[X]) (d : ℕ) :
    taylor a p = C (p.eval a) + movingHasseSum a p d +
      X * normalizedBackwardTaylorError a p d := by
  calc
    taylor a p = C (p.eval a) + movingHasseSum a p d + backwardTaylorResidual a p d := by
      simp only [backwardTaylorResidual]
      ring
    _ = _ := by rw [X_mul_normalizedBackwardTaylorError]

/-- Reconstruction with a caller-supplied center value `y`. -/
theorem backwardTaylorReconstruction_of_eval_eq {a y : R} {p : R[X]} (d : ℕ)
    (h : p.eval a = y) :
    taylor a p = C y + movingHasseSum a p d + X * normalizedBackwardTaylorError a p d := by
  simpa only [h] using backwardTaylorReconstruction a p d

/-- At order zero, the moving error specializes to the elementary increment quotient. -/
theorem normalizedBackwardTaylorError_zero (a : R) (p : R[X]) :
    normalizedBackwardTaylorError a p 0 = shiftIncrementQuotient a p := by
  ext n
  simp [normalizedBackwardTaylorError, backwardTaylorResidual, movingHasseSum,
    shiftIncrementQuotient, coeff_divX]

/-- The first update subtracts the shifted ordinary derivative from the increment quotient. -/
theorem normalizedBackwardTaylorError_one (a : R) (p : R[X]) :
    normalizedBackwardTaylorError a p 1 =
      shiftIncrementQuotient a p - taylor a p.derivative := by
  simpa [normalizedBackwardTaylorError_zero] using normalizedBackwardTaylorError_succ a p 0

/-- The reconstruction determines its normalized error uniquely. -/
theorem normalizedBackwardTaylorError_unique (a : R) (p : R[X]) (d : ℕ) {e : R[X]}
    (h : taylor a p = C (p.eval a) + movingHasseSum a p d + X * e) :
    e = normalizedBackwardTaylorError a p d := by
  have hres : backwardTaylorResidual a p d = X * e := by
    rw [backwardTaylorResidual, h]
    ring
  rw [← divX_X_mul e, ← hres]
  rfl

/-- At or above the polynomial degree, the normalized moving error is zero. -/
theorem normalizedBackwardTaylorError_eq_zero_of_natDegree_le (a : R) (p : R[X]) (d : ℕ)
    (hdeg : p.natDegree ≤ d) : normalizedBackwardTaylorError a p d = 0 := by
  rw [normalizedBackwardTaylorError,
    backwardTaylorResidual_eq_zero_of_natDegree_le a p d hdeg, divX_zero]

/-- At or above the polynomial degree, the finite reconstruction is exact without a remainder. -/
theorem backwardTaylorReconstruction_of_natDegree_le (a : R) (p : R[X]) (d : ℕ)
    (hdeg : p.natDegree ≤ d) :
    taylor a p = C (p.eval a) + movingHasseSum a p d := by
  simpa only [normalizedBackwardTaylorError_eq_zero_of_natDegree_le a p d hdeg,
    mul_zero, add_zero] using backwardTaylorReconstruction a p d

end CommRing

end


end Polynomial
