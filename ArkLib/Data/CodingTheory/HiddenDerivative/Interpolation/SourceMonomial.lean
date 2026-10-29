/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.JetDegree
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Source monomials for hidden-derivative interpolation

A source monomial `X^x Y₀^b Y₁^(h₀) ⋯ Y_d^(h_(d-1))` has independent exponents for `X`, `Y₀`,
and the remaining jets. It is homogeneous for every weight on the jet variables, of degree
`x w(X) + b w(Y₀) + ∑_j h_j w(Y_(j+1))`; for the jet-degree weight `jetDegreeWeight` this degree
is `b + ∑_j h_j`.

## Main statements

* `sourceMonomial_isWeightedHomogeneous`: homogeneity for an arbitrary weight.
* `sourceMonomial_isWeightedHomogeneous_jetDegreeWeight`: the jet-degree case.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommSemiring R] {d : ℕ}

/-- The differential monomial `X^x Y₀^b` times the powers `Y_(j+1)^(higher j)` of the remaining
jets. -/
def sourceMonomial (x b : ℕ) (higher : Fin d → ℕ) : DifferentialPolynomial R d :=
  X none ^ x * X (some 0) ^ b * ∏ j, X (some j.succ) ^ higher j

/-- A source monomial is homogeneous for every weight `w`, of degree
`x • w X + b • w Y₀ + ∑_j higher j • w Y_(j+1)`. -/
theorem sourceMonomial_isWeightedHomogeneous {M : Type*} [AddCommMonoid M]
    (w : JetVariable d → M) (x b : ℕ) (higher : Fin d → ℕ) :
    (sourceMonomial (R := R) x b higher).IsWeightedHomogeneous w
      (x • w none + b • w (some 0) + ∑ j, higher j • w (some j.succ)) := by
  have hX := (isWeightedHomogeneous_X R w none).pow x
  have hY₀ := (isWeightedHomogeneous_X R w (some 0)).pow b
  have hhigher := IsWeightedHomogeneous.prod Finset.univ
    (fun j : Fin d => (X (some j.succ) : DifferentialPolynomial R d) ^ higher j)
    (fun j => higher j • w (some j.succ)) (w := w)
    fun j _ => (isWeightedHomogeneous_X R w (some j.succ)).pow (higher j)
  exact (hX.mul hY₀).mul hhigher

/-- For the jet-degree weight, which ignores `X`, a source monomial has degree
`b + ∑_j higher j`. -/
theorem sourceMonomial_isWeightedHomogeneous_jetDegreeWeight (x b : ℕ) (higher : Fin d → ℕ) :
    (sourceMonomial (R := R) x b higher).IsWeightedHomogeneous jetDegreeWeight
      (b + ∑ j, higher j) := by
  simpa using sourceMonomial_isWeightedHomogeneous (R := R) jetDegreeWeight x b higher

end ReedSolomon.HiddenDerivative
