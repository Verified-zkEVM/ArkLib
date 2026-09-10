/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Degree
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Purity

/-!
# Refined principal-cut degree bound for actual affine components

The degree of every component is defined from its actual coordinate quotient.
Noether normalization proves purity, and finite-prime separator injections compare
leading coefficients. Together these prove the principal-cut degree sum.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial
open scoped BigOperators

variable {F σ : Type*} [Field F] [Finite σ]

/-- Cutting a prime affine component by a polynomial outside its ideal produces
minimal components whose total degree is at most the equation degree times the
parent degree. This includes the empty cut and assumes no geometric degree laws. -/
theorem principalCut_sum_affineDegree_le
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {f : MvPolynomial σ F} (hfP : f ∉ P) {b : ℕ} (hfdeg : f.totalDegree ≤ b) :
    ∑ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}), affineDegree Q ≤
      (b : ℚ) * affineDegree P := by
  classical
  have hchildren : ∀ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}),
      (hilbertPolynomial Q).natDegree = (hilbertPolynomial P).natDegree - 1 := by
    intro Q hQ
    have h := principalCut_component_hilbertPolynomial_natDegree_add_one hP hfP
      (mem_minimalPrimesFinset.mp hQ)
    omega
  calc
    ∑ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}), affineDegree Q =
        ∑ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}),
          (((hilbertPolynomial P).natDegree - 1).factorial : ℚ) *
            (hilbertPolynomial Q).leadingCoeff := by
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [affineDegree, hchildren Q hQ]
    _ ≤ (b : ℚ) * ((hilbertPolynomial P).natDegree.factorial : ℚ) *
        (hilbertPolynomial P).leadingCoeff :=
      principalCut_sum_minimalPrime_factorial_le hP hfP hfdeg hchildren
    _ = (b : ℚ) * affineDegree P := by rw [affineDegree, mul_assoc]

end AffineHilbert
