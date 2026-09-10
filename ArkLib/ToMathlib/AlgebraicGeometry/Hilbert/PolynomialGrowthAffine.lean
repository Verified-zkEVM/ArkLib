/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.PolynomialGrowthRescaling

/-!
# Polynomial degree comparison with affine rescaling

A positive scalar multiplier and an affine change of the natural input preserve
the degree comparison needed for finite-module filtration growth bounds.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open Polynomial Filter

/-- An eventual bound with positive scalar and input multipliers controls degree. -/
theorem natDegree_le_of_eventually_eval_nat_le_mul_affine
    {P Q : ℚ[X]} (hQ : Q ≠ 0) {m c d : ℕ} (hm : 0 < m) (hc : 0 < c)
    (hQnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : ℚ))
    (hle : ∀ᶠ N : ℕ in atTop,
      Q.eval (N : ℚ) ≤ (m : ℚ) * P.eval ((c * N + d : ℕ) : ℚ)) :
    Q.natDegree ≤ P.natDegree := by
  let R : ℚ[X] := Polynomial.C (m : ℚ) *
    P.comp (Polynomial.C (c : ℚ) * Polynomial.X + Polynomial.C (d : ℚ))
  have hcomp : ∀ᶠ N : ℕ in atTop, Q.eval (N : ℚ) ≤ R.eval (N : ℚ) := by
    simpa only [R, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Nat.cast_mul, Nat.cast_add] using hle
  have hdeg := (natDegree_le_of_eventually_eval_nat_le hQ hQnonneg hcomp).1
  dsimp [R] at hdeg
  rwa [Polynomial.natDegree_C_mul (by exact_mod_cast Nat.ne_of_gt hm),
    Polynomial.natDegree_comp, Polynomial.natDegree_add_C,
    Polynomial.natDegree_C_mul_X _ (by exact_mod_cast Nat.ne_of_gt hc), mul_one] at hdeg

end AffineHilbert
