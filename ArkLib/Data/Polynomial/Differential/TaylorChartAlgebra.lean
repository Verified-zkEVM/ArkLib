/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra

/-!
# Taylor agreement equations over an algebra

The cleared agreement equation is defined over a commutative algebra containing the base field,
so its coefficients can retain symbolic parameters.

## Main statements

* `PolynomialDifferential.taylorAgreementEquationOver`: the cleared agreement equation over an
  algebra.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace PolynomialDifferential

open MvPolynomial
open scoped BigOperators

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A] {r : ℕ}

/-- The polynomial `∑ l < K, (x - center)^l * N_l - y * S ^ τ`, where `N_l` is the common Taylor
numerator and `S` is the initial separant. If `TaylorExponentSufficient r K τ` holds, `S ^ τ` is
a common denominator for all Taylor coefficients in the sum. -/
def taylorAgreementEquationOver (center : A) (Q : DifferentialPolynomial A r)
    (K τ : ℕ) (x y : A) : MvPolynomial (Fin (r + 1)) A :=
  (∑ l : Fin K, C ((x - center) ^ l.val) * commonTaylorNumeratorOver F center Q τ l.val) -
    C y * initialJetSeparant center Q ^ τ

end PolynomialDifferential
