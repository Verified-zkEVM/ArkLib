/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Taylor expansion of a Frobenius pullback

Let `R` have exponential characteristic `p` and let `q = p ^ e`. Then `(X + C t) ^ q = X ^ q +
C (t ^ q)`, so translating the pullback `expand R q P` by `t` is the pullback of `P` translated by
`t ^ q`. Consequently the Taylor coefficients of `expand R q P` at `t` vanish at indices not
divisible by `q`, and the coefficient at `q * r` is the `r`-th Hasse derivative of `P` evaluated at
`t ^ q`.

## Main statements

* `Polynomial.taylor_expand_expChar_pow`: `taylor t (expand R (p ^ e) P) =
  expand R (p ^ e) (taylor (t ^ p ^ e) P)`.
* `Polynomial.coeff_taylor_expand_expChar_pow_mul` and
  `Polynomial.coeff_taylor_expand_expChar_pow_eq_zero`: the Taylor coefficients of a pullback.

## References

Ported from `ToMathlib/Polynomial/FrobeniusTaylor.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source theorems `taylor_expand_primePow`,
`coeff_taylor_expand_primePow_mul` and `coeff_taylor_expand_primePow_eq_zero` are renamed with
`expChar_pow` in place of `primePow`, since `p` is an exponential characteristic and may be `1`,
and hold over every commutative semiring instead of every commutative ring.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommSemiring R] (p e : ℕ) [ExpChar R p]

/-- Translation by `t` commutes with the pullback `X ↦ X ^ (p ^ e)` once the center is raised to
`t ^ (p ^ e)`. The hypothesis that `p` is the exponential characteristic of `R` is needed: over
`ℤ`, for `P = X`, `t = 1` and exponent `2`, the left side is `(X + 1) ^ 2 = X ^ 2 + 2 * X + 1`
while the right side is `X ^ 2 + 1`. -/
theorem taylor_expand_expChar_pow (P : R[X]) (t : R) :
    taylor t (expand R (p ^ e) P) = expand R (p ^ e) (taylor (t ^ (p ^ e)) P) := by
  simp only [taylor_apply, expand_eq_comp_X_pow, comp_assoc, pow_comp, X_comp, add_comp, C_comp]
  rw [add_pow_expChar_pow, ← C_pow]

/-- At an index `p ^ e * r`, the Taylor coefficient of the pullback at `t` is the `r`-th Hasse
derivative of `P` evaluated at `t ^ (p ^ e)`. -/
theorem coeff_taylor_expand_expChar_pow_mul (P : R[X]) (t : R) (r : ℕ) :
    (taylor t (expand R (p ^ e) P)).coeff (p ^ e * r) = (hasseDeriv r P).eval (t ^ (p ^ e)) := by
  rw [taylor_expand_expChar_pow, coeff_expand_mul' (pow_pos (expChar_pos R p) e), taylor_coeff]

/-- The Taylor coefficients of the pullback at indices not divisible by `p ^ e` vanish. -/
theorem coeff_taylor_expand_expChar_pow_eq_zero (P : R[X]) (t : R) {r : ℕ}
    (hr : ¬p ^ e ∣ r) : (taylor t (expand R (p ^ e) P)).coeff r = 0 := by
  simp [taylor_expand_expChar_pow, coeff_expand (pow_pos (expChar_pos R p) e), hr]

end Polynomial
