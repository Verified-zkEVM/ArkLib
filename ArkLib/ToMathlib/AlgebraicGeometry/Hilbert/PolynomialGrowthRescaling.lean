/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Degree

/-!
# Polynomial growth under linear rescaling

Comparison on a tail of the natural numbers preserves polynomial degree under a
positive linear rescaling. This supplies the growth-exponent step for filtrations
related by a fixed multiplicative change of their degree bound.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open Polynomial Filter

/-- Rescaling the input by a nonzero rational number preserves polynomial degree. -/
theorem natDegree_comp_C_mul_X (P : ℚ[X]) {c : ℚ} (hc : c ≠ 0) :
    (P.comp (Polynomial.C c * Polynomial.X)).natDegree = P.natDegree := by
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul hc,
    Polynomial.natDegree_X, mul_one]

/-- An eventual upper bound by a positively rescaled polynomial controls degree. -/
theorem natDegree_le_of_eventually_eval_nat_le_rescaled
    {P Q : ℚ[X]} (hQ : Q ≠ 0) {c : ℕ} (hc : 0 < c)
    (hQnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : ℚ))
    (hle : ∀ᶠ N : ℕ in atTop, Q.eval (N : ℚ) ≤ P.eval ((c * N : ℕ) : ℚ)) :
    Q.natDegree ≤ P.natDegree := by
  have hcomp : ∀ᶠ N : ℕ in atTop,
      Q.eval (N : ℚ) ≤ (P.comp (Polynomial.C (c : ℚ) * Polynomial.X)).eval (N : ℚ) := by
    simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Nat.cast_mul] using hle
  have hdeg := (natDegree_le_of_eventually_eval_nat_le hQ hQnonneg hcomp).1
  rwa [natDegree_comp_C_mul_X P (by exact_mod_cast Nat.ne_of_gt hc)] at hdeg

/-- A polynomial squeezed between another polynomial and a fixed rescaling of it
has exactly the same degree. -/
theorem natDegree_eq_of_eventually_eval_nat_sandwich
    {P Q : ℚ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) {c : ℕ} (hc : 0 < c)
    (hPnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ P.eval (N : ℚ))
    (hQnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : ℚ))
    (hlower : ∀ᶠ N : ℕ in atTop, P.eval (N : ℚ) ≤ Q.eval (N : ℚ))
    (hupper : ∀ᶠ N : ℕ in atTop, Q.eval (N : ℚ) ≤ P.eval ((c * N : ℕ) : ℚ)) :
    Q.natDegree = P.natDegree := by
  exact le_antisymm (natDegree_le_of_eventually_eval_nat_le_rescaled hQ hc hQnonneg hupper)
    (natDegree_le_of_eventually_eval_nat_le hP hPnonneg hlower).1

end AffineHilbert
