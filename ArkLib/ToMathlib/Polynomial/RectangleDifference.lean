/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Polynomial.EventualGrowth
public import Mathlib.RingTheory.Polynomial.HilbertPoly

/-!
# Rectangle-difference polynomials

Let `F` be a field of characteristic zero and write `q = Polynomial.preHilbertPoly F s 0`, so that
`q.eval n = (n + s).choose s` counts the monomials of total degree at most `n` in `s` variables.
For `a b h v : F` the rectangle difference is

```text
rectangleDifference s a b h v = (a X + 1) q(b X) - (a X - h + 1) q(b X - v).
```

At a natural number `N` with `h ≤ a N` and `v ≤ b N` it evaluates to

```text
(a N + 1) * (b N + s).choose s - (a N - h + 1) * (b N - v + s).choose s,
```

the number of exponent vectors in the product of an interval of length `a N + 1` with the
`s`-variable simplex of size `b N`, minus the number in its translate by `(h, v)`.

Although both products have natural degree `s + 1`, their top terms cancel: the rectangle difference
has natural degree at most `s`, and its coefficient in degree `s` is
`(h * b ^ s + s * v * a * b ^ (s - 1)) / s!`. The proof writes the difference as
`(a X + 1) * D(b X) + h * q(b X - v)`, where `D = q(X) - q(X - v)` is the backward difference of
`q` with step `v`, of natural degree `s - 1` and top coefficient `v * s / s!`.

## Main statements

* `Polynomial.rectangleDifference`: the definition.
* `Polynomial.rectangleDifference_eq_add`: the decomposition through a backward difference.
* `Polynomial.natDegree_rectangleDifference_le`: the natural degree is at most `s`.
* `Polynomial.coeff_rectangleDifference_self`: the coefficient in degree `s`.
* `Polynomial.eval_rectangleDifference_natCast`: the value at a natural number.
-/

@[expose] public section

noncomputable section

namespace Polynomial

variable {F : Type*} [Field F]

/-- The rectangle difference `(a X + 1) q(b X) - (a X - h + 1) q(b X - v)`, where
`q = preHilbertPoly F s 0` counts the monomials of bounded total degree in `s` variables. -/
def rectangleDifference (s : ℕ) (a b h v : F) : F[X] :=
  (C a * X + 1) * (preHilbertPoly F s 0).comp (C b * X) -
    (C a * X - C h + 1) * (preHilbertPoly F s 0).comp (C b * X - C v)

/-- Composing with `C b * X - C v` is a Taylor shift by `-v` followed by scaling by `b`. -/
private theorem comp_C_mul_X_sub_C (p : F[X]) (b v : F) :
    p.comp (C b * X - C v) = (taylor (-v) p).comp (C b * X) := by
  rw [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, map_neg, ← sub_eq_add_neg]

/-- The rectangle difference is `(a X + 1) * D(b X) + h * q(b X - v)`, where `D` is the backward
difference of `q = preHilbertPoly F s 0` with step `v`. -/
theorem rectangleDifference_eq_add (s : ℕ) (a b h v : F) :
    rectangleDifference s a b h v =
      (C a * X + 1) * (backwardDifference v (preHilbertPoly F s 0)).comp (C b * X) +
        C h * (taylor (-v) (preHilbertPoly F s 0)).comp (C b * X) := by
  rw [rectangleDifference, comp_C_mul_X_sub_C, backwardDifference, sub_comp]
  ring

/-- The coefficients of `(C a * X + 1) * P` in positive degrees. -/
private theorem coeff_C_mul_X_add_one_mul_succ (a : F) (P : F[X]) (m : ℕ) :
    ((C a * X + 1) * P).coeff (m + 1) = a * P.coeff m + P.coeff (m + 1) := by
  rw [add_mul, one_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul]

variable [CharZero F]

/-- The backward difference of `preHilbertPoly F s 0` has no coefficient in degrees `≥ s`. -/
private theorem coeff_backwardDifference_preHilbertPoly_of_le (s : ℕ) (v : F) {m : ℕ}
    (hm : s ≤ m) : (backwardDifference v (preHilbertPoly F s 0)).coeff m = 0 := by
  have hdeg := natDegree_backwardDifference_le v (preHilbertPoly F s 0)
  rw [natDegree_preHilbertPoly] at hdeg
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have hcoeff := coeff_backwardDifference_natDegree_sub_one v (preHilbertPoly F 0 0)
    rw [natDegree_preHilbertPoly, Nat.cast_zero, mul_zero, zero_mul] at hcoeff
    rw [eq_C_of_natDegree_le_zero hdeg, coeff_C]
    split_ifs <;> simp_all
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The rectangle difference has natural degree at most `s`: the degree-`(s + 1)` terms of the two
products cancel. -/
theorem natDegree_rectangleDifference_le (s : ℕ) (a b h v : F) :
    (rectangleDifference s a b h v).natDegree ≤ s := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsm : s ≤ m := by omega
  rw [rectangleDifference_eq_add, coeff_add, coeff_C_mul_X_add_one_mul_succ, coeff_C_mul,
    comp_C_mul_X_coeff, comp_C_mul_X_coeff, comp_C_mul_X_coeff,
    coeff_backwardDifference_preHilbertPoly_of_le s v hsm,
    coeff_backwardDifference_preHilbertPoly_of_le s v (hsm.trans (Nat.le_succ m)),
    coeff_eq_zero_of_natDegree_lt (p := taylor (-v) (preHilbertPoly F s 0))
      (by rw [natDegree_taylor, natDegree_preHilbertPoly]; omega)]
  simp

/-- The coefficient of the rectangle difference in degree `s` is
`(h * b ^ s + s * v * a * b ^ (s - 1)) / s!`. -/
theorem coeff_rectangleDifference_self (s : ℕ) (a b h v : F) :
    (rectangleDifference s a b h v).coeff s =
      (h * b ^ s + s * v * a * b ^ (s - 1)) / (s.factorial : F) := by
  have htaylor : (taylor (-v) (preHilbertPoly F s 0)).coeff s = (s.factorial : F)⁻¹ := by
    rw [coeff_taylor_of_natDegree_le _ (natDegree_preHilbertPoly F s 0).le,
      coeff_preHilbertPoly_self]
  rcases s with _ | m
  · rw [rectangleDifference_eq_add, coeff_add, coeff_C_mul, comp_C_mul_X_coeff, htaylor,
      mul_coeff_zero, comp_C_mul_X_coeff, coeff_backwardDifference_preHilbertPoly_of_le 0 v le_rfl]
    simp
  · have hD : (backwardDifference v (preHilbertPoly F (m + 1) 0)).coeff m =
        v * (m + 1 : ℕ) * ((m + 1).factorial : F)⁻¹ := by
      have h := coeff_backwardDifference_natDegree_sub_one v (preHilbertPoly F (m + 1) 0)
      rwa [natDegree_preHilbertPoly, leadingCoeff_preHilbertPoly, Nat.add_sub_cancel] at h
    rw [rectangleDifference_eq_add, coeff_add, coeff_C_mul_X_add_one_mul_succ, coeff_C_mul,
      comp_C_mul_X_coeff, comp_C_mul_X_coeff, comp_C_mul_X_coeff, htaylor, hD,
      coeff_backwardDifference_preHilbertPoly_of_le (m + 1) v le_rfl, Nat.add_sub_cancel]
    push_cast
    ring

/-- At a natural number `N` with `h ≤ a * N` and `v ≤ b * N`, the rectangle difference counts the
exponents of the rectangle of sides `a * N` and `b * N` that are not in its translate by
`(h, v)`: its value is `(a N + 1) * (b N + s).choose s - (a N - h + 1) * (b N - v + s).choose s`. -/
theorem eval_rectangleDifference_natCast (s a b h v N : ℕ) (hh : h ≤ a * N) (hv : v ≤ b * N) :
    (rectangleDifference s (a : F) b h v).eval (N : F) =
      (((a * N + 1) * (b * N + s).choose s -
        (a * N - h + 1) * (b * N - v + s).choose s : ℕ) : F) := by
  have hle : (a * N - h + 1) * (b * N - v + s).choose s ≤ (a * N + 1) * (b * N + s).choose s :=
    Nat.mul_le_mul (by omega) (Nat.choose_le_choose s (by omega))
  have hb : (b : F) * N = ((b * N : ℕ) : F) := by push_cast; ring
  have hbv : (b : F) * N - v = ((b * N - v : ℕ) : F) := by rw [Nat.cast_sub hv]; push_cast; ring
  have hq (n : ℕ) : (preHilbertPoly F s 0).eval (n : F) = ((n + s).choose s : F) := by
    rw [preHilbertPoly_eq_choose_add_sub F s (Nat.zero_le _), Nat.sub_zero]
  simp only [rectangleDifference, eval_sub, eval_mul, eval_add, eval_comp, eval_C, eval_X,
    eval_one]
  rw [hbv, hb, hq, hq, Nat.cast_sub hle]
  push_cast [Nat.cast_sub hh]
  ring

end Polynomial
