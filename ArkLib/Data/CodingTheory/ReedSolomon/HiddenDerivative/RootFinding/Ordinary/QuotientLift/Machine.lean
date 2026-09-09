/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.ModularInverse
import CompPoly.Multivariate.MvPolyEquiv.Eval

/-!
# Simultaneous regular lifting modulo a polynomial

For a bivariate equation `Q(X,Y)`, the roots of a modulus `h(U)` index possible initial values
`Y(center)=U`. This program constructs their series together, using arithmetic on polynomial
coefficient arrays and a modular inverse of `Q_Y(center,U)`. It never computes a root of `h`.

This is the coefficient-by-coefficient functional implementation. It does not implement the
paper's fast Newton refinement or claim its near-linear arithmetic bound. The separate correctness
file proves that each regular polynomial solution is recovered by specialization.
-/

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

/-- Extend the current series by the coefficient of `T^j`. -/
def appendCoefficient (series : Series E) (j : ℕ) (a : CPolynomial E) : Series E :=
  series + CPolynomial.C a * CPolynomial.X ^ j

/-- Solve the next affine residual equation using the shared inverse of the initial slope.
The result is reduced modulo `h`, so it represents one coefficient for every root of `h`. -/
def liftCoefficient (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (modulus inverse : CPolynomial E) (series : Series E) (j : ℕ) : CPolynomial E :=
  (-(residual Q center series).coeff j * inverse).modByMonic modulus

/-- Perform the requested number of coefficient lifts, starting at unresolved degree `j`. -/
def liftSteps (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (modulus inverse : CPolynomial E) : ℕ → ℕ → Series E → Series E
  | 0, _, series => series
  | steps + 1, j, series =>
    liftSteps Q center modulus inverse steps (j+1)
      (appendCoefficient series j (liftCoefficient Q center modulus inverse series j))

/-- Recover `Q_Y(center,U)` from two first-order residuals. The identity term in the
second input changes only the value variable, so subtracting cancels the `X`-derivative term. -/
def slope (Q : CPoly.CMvPolynomial 2 E) (center : E) : CPolynomial E :=
  (residual Q center (CPolynomial.C (CPolynomial.X : CPolynomial E) + CPolynomial.X)).coeff 1 -
    (residual Q center (CPolynomial.C (CPolynomial.X : CPolynomial E))).coeff 1

/-- Invert the initial slope modulo `h` once and lift all branches simultaneously to width `k`.
The polynomial `U` supplies the initial value. Exactness below assumes `k > 0`; failure reports
a noninvertible slope, requiring the caller to split or choose another center. -/
def regularLift? (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (modulus : CPolynomial E) (k : ℕ) : Option (Series E) := do
  let inverse ← CPolynomial.inverseMod? (slope Q center) modulus
  return liftSteps Q center modulus inverse (k - 1) 1
    (CPolynomial.C (CPolynomial.X : CPolynomial E))

end ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
