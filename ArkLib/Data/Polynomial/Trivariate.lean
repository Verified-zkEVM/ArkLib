/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Short interface on Trivariate Polynomials

We define trivariate polynomials to match their representation in statements and proofs
of [BCIKS20].

## Main Definitions

### Notation for trivariate polynomials and evaluation homomorphisms
- `eval_on_Z₀`: Evaluate a rational function on a point.
- `eval_on_Z`: Ring homomorphism evaluating the `Z` variable of a trivariate polynomial.
- `toRatFuncPoly`: Maps a trivariate polynomial to a bivariate polynomial over the rational
  function field.
- `D_Y`: The `Y`-degree of a trivariate polynomial.
- `D_YZ`: The `YZ`-degree of a trivariate polynomial.

## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/

namespace Trivariate

variable {F : Type} [Field F] [DecidableEq (RatFunc F)]

open Polynomial Bivariate

/-- Evaluate a rational function on a point. -/
noncomputable def eval_on_Z₀ (p : (RatFunc F)) (z : F) : F :=
  RatFunc.eval (RingHom.id _) z p

notation3:max R "[Z][X]" => Polynomial (Polynomial R)

notation3:max R "[Z][X][Y]" => Polynomial (Polynomial (Polynomial R))

notation3:max "Y" => Polynomial.X
notation3:max "X" => Polynomial.C Polynomial.X
notation3:max "Z" => Polynomial.C (Polynomial.C Polynomial.X)

/-- A ring homomorphism mapping a trivariate polynomial with coefficients in `F` and variables
`Z, X, Y` to a bivariate polynomial with coefficients in `F` and variables in `X, Y` by evaluating
on a point `z ∈ F`. -/
noncomputable opaque eval_on_Z (p : F[Z][X][Y]) (z : F) : F[X][Y] :=
  p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))

open Polynomial.Bivariate in
/-- A ring homomorphism mapping a trivariate polynomial to an element in the field of rational
functions of polynomial ring in two variables. -/
noncomputable def toRatFuncPoly (p : F[Z][X][Y]) : (RatFunc F)[X][Y] :=
  p.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))

/-- Following [BCIKS20] this the `Y`-degree of a trivariate polynomial `Q`. -/
def D_Y (Q : F[Z][X][Y]) : ℕ := Bivariate.natDegreeY Q

/-- The `YZ`-degree of a trivariate polynomial. -/
def D_YZ (Q : F[Z][X][Y]) : ℕ :=
  Option.getD (dflt := 0) <| Finset.max
    (Finset.image
            (
              fun j =>
                Option.getD (
                  Finset.max (
                    Finset.image
                      (fun k => j + (Bivariate.coeff Q j k).natDegree)
                      (Q.coeff j).support
                  )
                ) 0
            )
            Q.support
    )

end Trivariate
