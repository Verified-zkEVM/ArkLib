/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

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

section Semiring

variable {R : Type*} [Semiring R]

/-- Removing the leading `X` from `X * p` recovers `p`. -/
theorem divX_X_mul (p : R[X]) : (X * p).divX = p := by
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

theorem taylor_eq_C_add_X_mul_shiftIncrementQuotient (p : R[X]) (a : R) :
    taylor a p = C (p.eval a) + X * shiftIncrementQuotient a p := by
  simpa only [shiftIncrementQuotient, taylor_coeff_zero, add_comm] using
    (X_mul_divX_add (taylor a p)).symm

theorem taylor_eq_C_add_X_mul_shiftIncrementQuotient_of_eval_eq {p : R[X]} {a y : R}
    (h : p.eval a = y) :
    taylor a p = C y + X * shiftIncrementQuotient a p := by
  simpa only [h] using taylor_eq_C_add_X_mul_shiftIncrementQuotient p a

/-- Coefficient `i` is Hasse derivative `i + 1`; normalization introduces an off-by-one. -/
theorem coeff_shiftIncrementQuotient (p : R[X]) (a : R) (i : ℕ) :
    (shiftIncrementQuotient a p).coeff i = (hasseDeriv (i + 1) p).eval a := by
  rw [shiftIncrementQuotient, coeff_divX, taylor_coeff]

theorem natDegree_shiftIncrementQuotient (p : R[X]) (a : R) :
    (shiftIncrementQuotient a p).natDegree = p.natDegree - 1 := by
  rw [shiftIncrementQuotient, natDegree_divX_eq_natDegree_tsub_one, natDegree_taylor]

theorem X_pow_dvd_shiftIncrementQuotient_iff (p : R[X]) (a : R) (m : ℕ) :
    X ^ m ∣ shiftIncrementQuotient a p ↔
      ∀ i < m, (hasseDeriv (i + 1) p).eval a = 0 := by
  rw [X_pow_dvd_iff]
  simp only [coeff_shiftIncrementQuotient]

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R]

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

section CommRing

variable {R : Type*} [CommRing R]

theorem X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero (p : R[X]) (a : R) (m : ℕ) :
    (X - C a) ^ m ∣ p ↔ ∀ i < m, (hasseDeriv i p).eval a = 0 := by
  rw [X_sub_C_pow_dvd_iff]
  change X ^ m ∣ taylor a p ↔ ∀ i < m, (hasseDeriv i p).eval a = 0
  exact X_pow_dvd_taylor_iff p a m

theorem X_pow_dvd_taylor_sub_iff (p q : R[X]) (a : R) (m : ℕ) :
    X ^ m ∣ taylor a p - taylor a q ↔
      ∀ i < m, (hasseDeriv i p).eval a = (hasseDeriv i q).eval a := by
  rw [← LinearMap.map_sub, X_pow_dvd_taylor_iff]
  simp only [LinearMap.map_sub, eval_sub, sub_eq_zero]

theorem hasseDeriv_eval_eq_zero_iff_le_rootMultiplicity {p : R[X]} (hp : p ≠ 0)
    (a : R) (m : ℕ) :
    (∀ i < m, (hasseDeriv i p).eval a = 0) ↔ m ≤ p.rootMultiplicity a :=
  (X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero p a m).symm.trans
    (le_rootMultiplicity_iff hp).symm

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

/-- Numerator remaining after the constant and first `d` moving-Hasse terms are removed. -/
def backwardHasseResidual (d : ℕ) (q : R[X]) : R[X] :=
  q - C (q.coeff 0) - backwardHasseSum d q

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

theorem X_pow_dvd_normalizedBackwardHasseResidual (d : ℕ) (q : R[X]) :
    X ^ d ∣ normalizedBackwardHasseResidual d q := by
  rw [X_pow_dvd_iff]
  intro n hn
  rw [normalizedBackwardHasseResidual, coeff_divX]
  exact X_pow_dvd_iff.mp (X_pow_succ_dvd_backwardHasseResidual d q) (n + 1) (by omega)

theorem X_mul_normalizedBackwardHasseResidual (d : ℕ) (q : R[X]) :
    X * normalizedBackwardHasseResidual d q = backwardHasseResidual d q := by
  have hzero := X_pow_dvd_iff.mp (X_pow_succ_dvd_backwardHasseResidual d q) 0 (by omega)
  simpa only [normalizedBackwardHasseResidual, hzero, C_0, add_zero] using
    X_mul_divX_add (backwardHasseResidual d q)

/-- Paper-facing correction sum. Derivatives are evaluated at moving point `a + X`. -/
def movingHasseSum (a : R) (p : R[X]) (d : ℕ) : R[X] :=
  ∑ j ∈ Finset.range d,
    C ((-1 : R) ^ j) * (X ^ (j + 1) * taylor a (hasseDeriv (j + 1) p))

theorem movingHasseSum_eq_backwardHasseSum (a : R) (p : R[X]) (d : ℕ) :
    movingHasseSum a p d = backwardHasseSum d (taylor a p) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [hasseDeriv_taylor]

def backwardTaylorResidual (a : R) (p : R[X]) (d : ℕ) : R[X] :=
  taylor a p - C (p.eval a) - movingHasseSum a p d

theorem backwardTaylorResidual_eq (a : R) (p : R[X]) (d : ℕ) :
    backwardTaylorResidual a p d = backwardHasseResidual d (taylor a p) := by
  rw [backwardTaylorResidual, backwardHasseResidual, movingHasseSum_eq_backwardHasseSum,
    taylor_coeff_zero]

/-- The paper-facing numerator has a zero of order at least `d + 1`. -/
theorem X_pow_succ_dvd_backwardTaylorResidual (a : R) (p : R[X]) (d : ℕ) :
    X ^ (d + 1) ∣ backwardTaylorResidual a p d := by
  rw [backwardTaylorResidual_eq]
  exact X_pow_succ_dvd_backwardHasseResidual d (taylor a p)

/-- At or above the polynomial degree, the moving-point backward expansion has no error. -/
theorem backwardTaylorResidual_eq_zero_of_natDegree_le (a : R) (p : R[X]) (d : ℕ)
    (hdeg : p.natDegree ≤ d) : backwardTaylorResidual a p d = 0 := by
  rw [backwardTaylorResidual_eq]
  apply backwardHasseResidual_eq_zero_of_natDegree_le
  simpa only [natDegree_taylor] using hdeg

/-- Canonical normalized moving-point error; unlike the increment quotient, this depends on `d`. -/
def normalizedBackwardTaylorError (a : R) (p : R[X]) (d : ℕ) : R[X] :=
  (backwardTaylorResidual a p d).divX

theorem X_pow_dvd_normalizedBackwardTaylorError (a : R) (p : R[X]) (d : ℕ) :
    X ^ d ∣ normalizedBackwardTaylorError a p d := by
  rw [normalizedBackwardTaylorError, backwardTaylorResidual_eq]
  exact X_pow_dvd_normalizedBackwardHasseResidual d (taylor a p)

/-- Equation (16): multiplying the normalized moving error by `X` recovers its numerator. -/
theorem X_mul_normalizedBackwardTaylorError (a : R) (p : R[X]) (d : ℕ) :
    X * normalizedBackwardTaylorError a p d = backwardTaylorResidual a p d := by
  rw [normalizedBackwardTaylorError, backwardTaylorResidual_eq]
  exact X_mul_normalizedBackwardHasseResidual d (taylor a p)

theorem coeff_normalizedBackwardTaylorError (a : R) (p : R[X]) (d n : ℕ) :
    (normalizedBackwardTaylorError a p d).coeff n =
      (backwardTaylorResidual a p d).coeff (n + 1) := by
  rw [normalizedBackwardTaylorError, coeff_divX]

/-- Finite moving-point backward reconstruction, with signs `+,-,+,...` from Hasse order one. -/
theorem backwardTaylorReconstruction (a : R) (p : R[X]) (d : ℕ) :
    taylor a p = C (p.eval a) + movingHasseSum a p d +
      X * normalizedBackwardTaylorError a p d := by
  calc
    taylor a p = C (p.eval a) + movingHasseSum a p d + backwardTaylorResidual a p d := by
      simp only [backwardTaylorResidual]
      ring
    _ = _ := by rw [X_mul_normalizedBackwardTaylorError]

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
