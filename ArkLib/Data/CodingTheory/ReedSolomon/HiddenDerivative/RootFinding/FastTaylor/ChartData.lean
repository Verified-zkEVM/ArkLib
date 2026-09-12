/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Multivariate.MvPolyEquiv.Eval
public import Mathlib.Data.Matrix.Basic

/-!
# Stored output boundary for the fast Taylor constructor

Variables are ordered `[t₀, …, tᵣ₋₁, z]`. Numerator index `j` denotes the coefficient
of `Z^j` in the expansion at `center`, not the coefficient of `X^j`. This module
constructs the paper's agreement residuals from stored numerators. It does not
construct a regular chart or assert coverage of differential solutions.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor

open CPoly

variable (E : Type*) [CommRing E] [BEq E] [LawfulBEq E] (r k : ℕ)

/-- Computable chart payload. Validity and producer coverage are separate obligations.
`projection` maps the ordered chart coordinates back to the original Hasse initial jet. -/
structure ChartData where
  center : E
  projection : Matrix (Fin (r + 1)) (Fin (r + 1)) E
  inverseProjection : Matrix (Fin (r + 1)) (Fin (r + 1)) E
  equation : CMvPolynomial (r + 1) E
  separant : CMvPolynomial (r + 1) E
  denominator : CMvPolynomial (r + 1) E
  numerators : Fin k → CMvPolynomial (r + 1) E

variable {E r k}

/-- The last loop of `FastRegularTaylorFamily`, with exactly `k` coefficient terms. -/
def ChartData.agreement (chart : ChartData E r k) (alpha received : E) :
    CMvPolynomial (r + 1) E :=
  (∑ j : Fin k, chart.numerators j * CMvPolynomial.C ((alpha - chart.center) ^ j.val)) -
    CMvPolynomial.C received * chart.denominator

/-- Evaluation of the executed residual agrees with the cleared Taylor message residual,
including evaluation in extension fields and ramified projection fibers. -/
theorem ChartData.eval₂_agreement {L : Type*} [CommRing L]
    (chart : ChartData E r k) (base : E →+* L) (point : Fin (r + 1) → L)
    (alpha received : E) :
    CMvPolynomial.eval₂ base point (chart.agreement alpha received) =
      (∑ j : Fin k, CMvPolynomial.eval₂ base point (chart.numerators j) *
        (base alpha - base chart.center) ^ j.val) -
      base received * CMvPolynomial.eval₂ base point chart.denominator := by
  change CMvPolynomial.eval₂Hom base point (chart.agreement alpha received) = _
  unfold ChartData.agreement
  rw [_root_.map_sub, map_sum, _root_.map_mul]
  simp only [_root_.map_mul, CMvPolynomial.eval₂Hom_apply, eval₂_equiv,
    CMvPolynomial.fromCMvPolynomial_C, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_sub, _root_.map_pow, _root_.map_sub]

end ReedSolomon.HiddenDerivative.FastTaylor
