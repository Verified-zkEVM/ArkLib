/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
public import ArkLib.Data.Polynomial.Differential.TaylorChart

/-!
# Agreement equations over coefficient algebras

Taylor agreement cuts are defined over any commutative algebra over the base field. This lets a
challenge remain a polynomial parameter until the equation is specialized.

## Main statements

* `PolynomialDifferential.taylorAgreementEquationOver`: a cleared Taylor agreement equation over
  an algebra of coefficients.
* `PolynomialDifferential.map_taylorAgreementEquationOver`: coefficient algebra maps preserve the
  equation.
* `PolynomialDifferential.taylorAgreementEquationOver_eq`: the field case is the existing Taylor
  agreement equation.
* `MvPolynomial.aeval_optionEquivRight_symm`: evaluation after separating a polynomial challenge
  from the jet variables.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace PolynomialDifferential

open MvPolynomial

variable {F A B : Type*} [Field F] [CommRing A] [CommRing B] [Algebra F A] {r : ℕ}

/-- The cleared Taylor agreement equation at `x` with value `y`, using a common exponent `τ` for
the first `K` rational Taylor coefficients. -/
def taylorAgreementEquationOver (F : Type*) [Field F] [Algebra F A]
    (center : A) (Q : DifferentialPolynomial A r) (K τ : ℕ) (x y : A) :
    MvPolynomial (Fin (r + 1)) A :=
  (∑ l : Fin K, C ((x - center) ^ l.val) * commonTaylorNumeratorOver F center Q τ l.val) -
    C y * initialJetSeparant center Q ^ τ

/-- Algebra maps on the coefficients preserve the cleared Taylor agreement equation. -/
theorem map_taylorAgreementEquationOver [Algebra F B] (φ : A →ₐ[F] B)
    (center : A) (Q : DifferentialPolynomial A r) (K τ : ℕ) (x y : A) :
    MvPolynomial.map φ.toRingHom (taylorAgreementEquationOver F center Q K τ x y) =
      taylorAgreementEquationOver F (φ center) (MvPolynomial.map φ.toRingHom Q) K τ
        (φ x) (φ y) := by
  simp only [taylorAgreementEquationOver, map_sub, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro l hl
    rw [map_mul, map_C, map_pow, map_sub,
      map_commonTaylorNumeratorOver (F := F) φ center Q τ l]
    rfl
  · rw [map_mul, map_C, map_pow, map_initialJetSeparant]
    rfl

/-- Over a field, the algebra-valued Taylor agreement equation is the field Taylor agreement
equation. -/
theorem taylorAgreementEquationOver_eq (center : F) (Q : DifferentialPolynomial F r)
    (K τ : ℕ) (x y : F) :
    taylorAgreementEquationOver F center Q K τ x y =
      taylorAgreementEquation center Q K τ x y := by
  simp [taylorAgreementEquationOver, taylorAgreementEquation, commonTaylorNumeratorOver,
    commonTaylorNumerator, rationalTaylorNumeratorOver_eq]

end PolynomialDifferential

namespace MvPolynomial

/-- Evaluating a polynomial after separating the challenge coordinate is evaluation at the
corresponding point of the joint challenge and jet variables. -/
theorem aeval_map_optionEquivRight {E σ : Type*} [CommSemiring E] (x : Option σ → E)
    (p : MvPolynomial (Option σ) E) :
    aeval (fun j ↦ x (some j))
      (MvPolynomial.map (Polynomial.evalRingHom (x none)) (optionEquivRight E σ p)) =
        aeval x p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    cases i <;> simp

/-- Evaluating a flattened joint polynomial is first challenge evaluation and then jet
evaluation. -/
theorem aeval_optionEquivRight_symm {E σ : Type*} [CommSemiring E] (x : Option σ → E)
    (p : MvPolynomial σ (Polynomial E)) :
    aeval x ((optionEquivRight E σ).symm p) =
      aeval (fun j ↦ x (some j))
        (MvPolynomial.map (Polynomial.evalRingHom (x none)) p) := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (aeval_map_optionEquivRight x ((optionEquivRight E σ).symm p)).symm

end MvPolynomial

end
