/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.ModularInverse
public import CompPoly.Multivariate.MvPolyEquiv.Eval

/-!
# Quotient-series data and centered residuals

The parameter modulus `h(U)` indexes possible initial values `Y(center)=U`. A `Series` is stored
as a polynomial in the centered variable `T`, with polynomial coefficients in `U`; Newton's
machine reduces those coefficients modulo `h` after each update.

`residual` substitutes `X=center+T` and the current series into `Q(X,Y)`. The initial slope
`Q_Y(center,U)` is recovered from two first-order evaluations. Its modular inverse supplies one
shared Newton seed for all represented branches, without computing any parameter roots.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.Ordinary.QuotientLift

open CompPoly CompPoly.CPolynomial
variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- A polynomial in the centered message variable, with polynomial coefficients in `U`. -/
abbrev Series (E : Type*) [CommRing E] [BEq E] [LawfulBEq E] :=
  CPolynomial (CPolynomial E)

/-- Substitute `X = center + T` and the current series for `Y` in the bivariate equation. -/
def residual (Q : CPoly.CMvPolynomial 2 E) (center : E) (series : Series E) : Series E :=
  CPoly.CMvPolynomial.eval₂ (CHom.comp CHom)
    ![CPolynomial.X + CPolynomial.C (CPolynomial.C center), series] Q

/-- Recover `Q_Y(center,U)` from two first-order residuals. The identity term in the
second input changes only the value variable, so subtracting cancels the `X`-derivative term. -/
def slope (Q : CPoly.CMvPolynomial 2 E) (center : E) : CPolynomial E :=
  (residual Q center (CPolynomial.C (CPolynomial.X : CPolynomial E) + CPolynomial.X)).coeff 1 -
    (residual Q center (CPolynomial.C (CPolynomial.X : CPolynomial E))).coeff 1

end ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
