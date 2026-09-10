/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Sparse Taylor coefficients after Frobenius pullback

Pulling a polynomial back by `X ↦ X ^ (p ^ e)` and expanding at `t` retains precisely the
Taylor coefficients of the original polynomial at `t ^ (p ^ e)`, at indices divisible by
`p ^ e`. This is the coefficient projection used by the ordinary Frobenius chart.
-/

@[expose] public section

namespace Polynomial

noncomputable section

variable {R : Type*} [CommRing R] (p e : ℕ) [ExpChar R p]

/-- Translation commutes with Frobenius pullback after raising the center to the same power. -/
theorem taylor_expand_primePow (P : R[X]) (t : R) :
    taylor t (expand R (p ^ e) P) =
      expand R (p ^ e) (taylor (t ^ (p ^ e)) P) := by
  simp only [taylor_apply, expand_eq_comp_X_pow, comp_assoc, pow_comp, X_comp,
    add_comp, C_comp]
  rw [add_pow_expChar_pow, ← C_pow]

/-- At a retained index, the pulled Taylor coefficient is the original Hasse derivative. -/
theorem coeff_taylor_expand_primePow_mul (P : R[X]) (t : R) (r : ℕ) :
    (taylor t (expand R (p ^ e) P)).coeff ((p ^ e) * r) =
      (hasseDeriv r P).eval (t ^ (p ^ e)) := by
  rw [taylor_expand_primePow, coeff_expand_mul' (pow_pos (expChar_pos R p) e), taylor_coeff]

/-- Taylor coefficients outside the retained prime-power multiples vanish. -/
theorem coeff_taylor_expand_primePow_eq_zero (P : R[X]) (t : R) (r : ℕ)
    (hr : ¬p ^ e ∣ r) :
    (taylor t (expand R (p ^ e) P)).coeff r = 0 := by
  rw [taylor_expand_primePow, coeff_expand (pow_pos (expChar_pos R p) e), if_neg hr]

end

end Polynomial
