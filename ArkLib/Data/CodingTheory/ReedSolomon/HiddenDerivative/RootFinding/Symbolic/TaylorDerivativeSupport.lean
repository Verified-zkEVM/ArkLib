/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorDerivativeDegree
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.DerivativeBidegree

/-!
# The three degree bounds on first-order Taylor cuts

The usual challenge/total-jet rectangle and the separate derivative-degree bound hold
simultaneously for the same literal polynomials. Their intersection removes the unused
corner of the monomial triangle. These membership results are the interface to the
refined image-degree argument.
-/

@[expose] public section

namespace AffineHilbert

noncomputable section

open MvPolynomial

theorem derivativeWeight_eq_piSingle :
    derivativeWeight = Pi.single (some (1 : Fin 2)) 1 := by
  funext i
  cases i with
  | none => simp
  | some j => fin_cases j <;> simp [derivativeWeight]

/-- Combining the original rectangle with a derivative-degree bound automatically uses
the smaller of the total and separate bounds. -/
theorem mem_restrictDerivativeBidegree_of_bidegree {F : Type*} [Field F]
    {P : MvPolynomial (Option (Fin 2)) F} {a b c : ℕ}
    (hP : P ∈ restrictBidegree (F := F) a b) (hc : P.degreeOf (some 1) ≤ c) :
    P ∈ restrictDerivativeBidegree (F := F) a b (min b c) := by
  rw [mem_restrictBidegree] at hP
  rw [mem_restrictDerivativeBidegree]
  intro m hm
  refine ⟨(hP m hm).1, (hP m hm).2, le_min ?_ ?_⟩
  · apply le_trans ?_ (hP m hm).2
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
    apply Finset.sum_le_sum
    intro i _
    apply Nat.mul_le_mul_left
    cases i with
    | none => simp [derivativeWeight, jetWeight]
    | some j => fin_cases j <;> simp [derivativeWeight, jetWeight]
  · rw [derivativeWeight_eq_piSingle]
    exact (le_weightedTotalDegree _ hm).trans (by simpa using hc)

end

end AffineHilbert

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial Polynomial AffineHilbert

variable {F : Type*} [Field F]

/-- Specializing the independent variable does not increase derivative degree. -/
theorem degreeOf_initialJetEquationOver_firstOrder (center : F[X])
    (Q : DifferentialPolynomial F[X] 1) :
    (initialJetEquationOver center Q).degreeOf 1 ≤ Q.degreeOf (some 1) := by
  rw [← weightedTotalDegree_piSingle, ← weightedTotalDegree_piSingle (some (1 : Fin 2))]
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  cases i with
  | none => simp
  | some j => fin_cases j <;> simp [weightedTotalDegree_piSingle, degreeOf_X]

/-- The initial equation retains all three source degree bounds. -/
theorem initialJetEquationOver_mem_restrictDerivativeBidegree
    (center : F) (Q : DifferentialPolynomial F[X] 1) (h v r : ℕ)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ r) :
    flattenChallenge (initialJetEquationOver (Polynomial.C center) Q) ∈
      restrictDerivativeBidegree (F := F) h v (min v r) := by
  apply mem_restrictDerivativeBidegree_of_bidegree
    (initialJetEquationOver_mem_restrictBidegree center Q h v hheight hjet)
  exact (flattenChallenge_degreeOf_le _ _).trans
    ((degreeOf_initialJetEquationOver_firstOrder _ Q).trans hderiv)

/-- The common numerator fits the original rectangle with its unused derivative corner removed. -/
theorem commonTaylorNumeratorOver_mem_restrictDerivativeBidegree
    (center : F) (Q : DifferentialPolynomial F[X] 1) (h v r K τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hv : 0 < v) (hr : 0 < r)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ r) (l : Fin K) :
    flattenChallenge
        (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l (τ := τ)) ∈
      restrictDerivativeBidegree (F := F) (τ * h) (1 + τ * (v - 1))
        (min (1 + τ * (v - 1)) (τ * (r - 1) + (K - 1))) := by
  apply mem_restrictDerivativeBidegree_of_bidegree
    (commonTaylorNumeratorOver_mem_restrictBidegree_of_exponent
      center Q h v K τ hτ hv hheight hjet l)
  exact (flattenChallenge_degreeOf_le _ _).trans
    ((degreeOf_commonTaylorNumeratorOver_firstOrder
      (Polynomial.C center) Q r K τ hτ hr hderiv l).trans (by omega))

/-- Agreement cuts have the same separate derivative-degree bound as the common numerators. -/
theorem degreeOf_taylorAgreementEquationOver_firstOrder
    (center x : F[X]) (y : F[X]) (Q : DifferentialPolynomial F[X] 1)
    (r K τ : ℕ) (hτ : TaylorExponentSufficient 1 K τ) (hr : 0 < r)
    (hderiv : Q.degreeOf (some 1) ≤ r) :
    (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ)).degreeOf 1 ≤
      τ * (r - 1) + (K - 1) := by
  unfold taylorAgreementEquationOver
  apply (degreeOf_sub_le _ _ _).trans
  apply max_le
  · apply (degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro l _
    apply (degreeOf_mul_le _ _ _).trans
    simp only [degreeOf_C, zero_add]
    exact (degreeOf_commonTaylorNumeratorOver_firstOrder center Q r K τ hτ hr hderiv l).trans
      (by omega)
  · apply (degreeOf_mul_le _ _ _).trans
    simp only [degreeOf_C, zero_add]
    exact (degreeOf_pow_le _ _ _).trans
      ((Nat.mul_le_mul_left τ ((degreeOf_initialJetSeparantOver_firstOrder center Q).trans
        (Nat.sub_le_sub_right hderiv 1))).trans (by omega))

/-- Received-curve cuts fit all three bounds at the same common Taylor exponent. -/
theorem taylorAgreementEquationOver_mem_restrictDerivativeBidegree
    (center x : F) (y : F[X]) (Q : DifferentialPolynomial F[X] 1)
    (ell h v r K τ : ℕ) (hτ : TaylorExponentSufficient 1 K τ)
    (hy : y.natDegree ≤ ell) (hv : 0 < v) (hr : 0 < r)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ r) :
    flattenChallenge
        (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
          (Polynomial.C x) y (τ := τ)) ∈
      restrictDerivativeBidegree (F := F) (ell + τ * h) (1 + τ * (v - 1))
        (min (1 + τ * (v - 1)) (τ * (r - 1) + (K - 1))) := by
  apply mem_restrictDerivativeBidegree_of_bidegree
    (taylorAgreementEquationOver_mem_restrictBidegree_of_exponent
      center x y Q ell h v K τ hτ hy hv hheight hjet)
  exact (flattenChallenge_degreeOf_le _ _).trans
    (degreeOf_taylorAgreementEquationOver_firstOrder _ _ _ _ _ _ _ hτ hr hderiv)

end

end ReedSolomon.HiddenDerivative
