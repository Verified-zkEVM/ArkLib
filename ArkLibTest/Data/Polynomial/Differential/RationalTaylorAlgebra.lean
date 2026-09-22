/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for rational Taylor numerators over an algebra

The main example is the equation `y' = t y` with a parameter `t`, written as `Y₁ - t Y₀` over
`ℚ[t]`. Evaluating the parameter at `a` sends its numerators to the numerators of `y' = a y`
over `ℚ`.

The equation `t y' = y`, written as `t Y₁ - Y₀`, has separant `t`. Its numerators still
specialize at `t = 0`, where the separant vanishes, since `map_rationalTaylorNumeratorOver` has
no hypothesis on the separant.

Over `ZMod 2` the binomial pivot `(2 choose 1)` is zero, so for a first-order equation the
numerator at `l = 2` is `0`. For `l ≤ r` the common numerator is the coordinate `Y_l` times the
full power `S ^ τ` of the separant; for an exponent below `2(l - r) - 1` the padding truncates
to `S ^ 0`.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- Over a field, the numerator over the field as an algebra over itself is the field
numerator. -/
example (center : ℚ) (Q : DifferentialPolynomial ℚ 1) (l : ℕ) :
    rationalTaylorNumeratorOver ℚ center Q l = rationalTaylorNumerator center Q l :=
  rationalTaylorNumeratorOver_eq ℚ center Q l

/-- The base field and the field of the equation may differ: numerators over a field `E`
containing `ℚ`, computed with pivots inverted in `ℚ`, are the numerators over `E`. -/
example {E : Type*} [Field E] [Algebra ℚ E] (center : E) (Q : DifferentialPolynomial E 2)
    (l : ℕ) :
    rationalTaylorNumeratorOver ℚ center Q l = rationalTaylorNumerator center Q l :=
  rationalTaylorNumeratorOver_eq ℚ center Q l

/-- The equation `y' = t y`, as `Y₁ - t Y₀` over `ℚ[t]`. -/
private abbrev scaledExpEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  X (some 1) - C Polynomial.X * X (some 0)

/-- Evaluating the parameter at `a` sends the numerators of `y' = t y` to those of `y' = a y`. -/
example (a : ℚ) (l : ℕ) :
    map (Polynomial.aeval a).toRingHom (rationalTaylorNumeratorOver ℚ 0 scaledExpEquation l) =
      rationalTaylorNumerator 0 (X (some 1) - C a * X (some 0) : DifferentialPolynomial ℚ 1)
        l := by
  rw [map_rationalTaylorNumeratorOver, rationalTaylorNumeratorOver_eq]
  simp [scaledExpEquation]

/-- The equation `t y' = y`, as `t Y₁ - Y₀` over `ℚ[t]`. -/
private abbrev singularEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  C Polynomial.X * X (some 1) - X (some 0)

/-- The separant of `t Y₁ - Y₀` is the parameter `t`. -/
example : initialJetSeparant 0 singularEquation = C Polynomial.X := by
  simp [initialJetSeparant, separant, singularEquation, pderiv_X, Fin.last]

/-- At `t = 0` the separant of `t Y₁ - Y₀` vanishes. -/
example :
    initialJetSeparant 0 (map (Polynomial.aeval (0 : ℚ)).toRingHom singularEquation) = 0 := by
  simp [initialJetSeparant, separant, singularEquation, pderiv_X, Fin.last]

/-- The numerators of `t Y₁ - Y₀` still specialize at `t = 0`, where the separant vanishes. -/
example (l : ℕ) :
    map (Polynomial.aeval (0 : ℚ)).toRingHom
        (rationalTaylorNumeratorOver ℚ 0 singularEquation l) =
      rationalTaylorNumerator 0 (-X (some 0) : DifferentialPolynomial ℚ 1) l := by
  rw [map_rationalTaylorNumeratorOver, rationalTaylorNumeratorOver_eq]
  simp [singularEquation]

/-- Over `ZMod 2` the pivot `(2 choose 1)` is zero, so every first-order equation over
`(ZMod 2)[t]` has numerator `0` at `l = 2`. -/
example (center : Polynomial (ZMod 2)) (Q : DifferentialPolynomial (Polynomial (ZMod 2)) 1) :
    rationalTaylorNumeratorOver (ZMod 2) center Q 2 = 0 := by
  have hchoose : ((Nat.choose 2 1 : ℕ) : ZMod 2) = 0 := by decide
  rw [rationalTaylorNumeratorOver, dite_eq_right_of_eq_false (eq_false (by norm_num)), hchoose]
  simp

/-- For `l ≤ r` the numerator is the coordinate `Y_l`. -/
example (center : Polynomial ℚ) (Q : DifferentialPolynomial (Polynomial ℚ) 1) :
    rationalTaylorNumeratorOver ℚ center Q 1 = X 1 := by
  rw [rationalTaylorNumeratorOver, dite_eq_left_of_eq_true (eq_true (by norm_num))]
  rfl

/-- For `l ≤ r` the common numerator with exponent `4` is `Y_l * S ^ 4`. -/
example (center : Polynomial ℚ) (Q : DifferentialPolynomial (Polynomial ℚ) 1) :
    commonTaylorNumeratorOver ℚ center Q 4 0 = X 0 * initialJetSeparant center Q ^ 4 := by
  rw [commonTaylorNumeratorOver, rationalTaylorNumeratorOver,
    dite_eq_left_of_eq_true (eq_true (by norm_num))]
  rfl

/-- For `r = 1` and `l = 3`, the unpadded exponent is `2(3 - 1) - 1 = 3`; with the smaller
exponent `2` the padding truncates to `S ^ 0`, so the common numerator is the plain numerator. -/
example (center : Polynomial ℚ) (Q : DifferentialPolynomial (Polynomial ℚ) 1) :
    commonTaylorNumeratorOver ℚ center Q 2 3 = rationalTaylorNumeratorOver ℚ center Q 3 := by
  rw [commonTaylorNumeratorOver, show 2 - (2 * (3 - 1) - 1) = 0 from rfl, pow_zero, mul_one]

/-- Evaluating the parameter commutes with the common numerators at any exponent. -/
example (a : ℚ) (τ l : ℕ) :
    map (Polynomial.aeval a).toRingHom
        (commonTaylorNumeratorOver ℚ 0 scaledExpEquation τ l) =
      commonTaylorNumeratorOver ℚ 0
        (X (some 1) - C a * X (some 0) : DifferentialPolynomial ℚ 1) τ l := by
  rw [map_commonTaylorNumeratorOver]
  simp [scaledExpEquation]

end

end PolynomialDifferential
