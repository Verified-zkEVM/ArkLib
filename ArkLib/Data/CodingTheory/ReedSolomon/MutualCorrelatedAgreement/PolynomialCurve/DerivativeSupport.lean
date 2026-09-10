/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.SharpRegularEquation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorDerivativeSupport
/-!
# Derivative-degree support of the polynomial-curve incidence cuts

Every polynomial used by the existing regular-stage incidence argument fits the same
three-degree filtration: the initial equation, the excluded separant, the high Taylor
coefficients, and the received-curve agreement cuts. These statements concern the actual
cuts, so the refined geometry changes only their degree estimates.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {E : Type*} [Field E] {ℓ : ℕ}

/-- The separate derivative degree used by the common first-order source cuts. -/
def sourceCurveCutDerivativeDegree (K v r : ℕ) (τ : ℕ := 2 * K) : ℕ :=
  min (sourceCurveCutJetDegree K v (τ := τ)) (τ * (r - 1) + (K - 1))

/-- The first source equation retains its original three degree bounds. -/
theorem symbolicSourceInitialEquation_mem_restrictDerivativeBidegree
    (center : E) (Q : DifferentialPolynomial E[X] 1) (h v r : ℕ)
    (hrv : r ≤ v) (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ r) :
    symbolicSourceInitialEquation center Q ∈ restrictDerivativeBidegree (F := E) h v r := by
  simpa only [symbolicSourceInitialEquation, flattenChallenge, min_eq_right hrv] using
    initialJetEquationOver_mem_restrictDerivativeBidegree center Q h v r hheight hjet hderiv

/-- The initial equation fits the same three bounds as all later incidence cuts. -/
theorem symbolicSourceInitialEquation_mem_sourceCurveCutDerivativeBidegree
    (center : E) (Q : DifferentialPolynomial E[X] 1) (ℓ K h v r τ : ℕ)
    (hK : 1 < K) (hτpos : 0 < τ) (hv : 0 < v) (hr : 0 < r)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ r) :
    symbolicSourceInitialEquation center Q ∈ restrictDerivativeBidegree (F := E)
      (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
      (sourceCurveCutJetDegree K v (τ := τ)) (sourceCurveCutDerivativeDegree K v r τ) := by
  apply mem_restrictDerivativeBidegree_of_bidegree
    (symbolicSourceInitialEquation_mem_sourceCurveCutBidegree_of_exponent
      center Q ℓ K h v τ hτpos hv hheight hjet)
  have hd := (flattenChallenge_degreeOf_le
    (initialJetEquationOver (Polynomial.C center) Q) 1).trans
    ((degreeOf_initialJetEquationOver_firstOrder _ Q).trans hderiv)
  have hr' : r - 1 ≤ τ * (r - 1) := Nat.le_mul_of_pos_left _ hτpos
  change (flattenChallenge (initialJetEquationOver (Polynomial.C center) Q)).degreeOf _ ≤ _
  omega

/-- The excluded separant fits the common three-degree filtration. -/
theorem symbolicSourceSeparant_mem_sourceCurveCutDerivativeBidegree
    (center : E) (Q : DifferentialPolynomial E[X] 1) (ℓ K h v r τ : ℕ)
    (hτpos : 0 < τ) (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ r) :
    symbolicSourceSeparant center Q ∈ restrictDerivativeBidegree (F := E)
      (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
      (sourceCurveCutJetDegree K v (τ := τ)) (sourceCurveCutDerivativeDegree K v r τ) := by
  apply mem_restrictDerivativeBidegree_of_bidegree
    (symbolicSourceSeparant_mem_sourceCurveCutBidegree_of_exponent
      center Q ℓ K h v τ hτpos hheight hjet)
  have hd := (flattenChallenge_degreeOf_le
    (initialJetSeparantOver (Polynomial.C center) Q) 1).trans
    ((degreeOf_initialJetSeparantOver_firstOrder _ Q).trans (Nat.sub_le_sub_right hderiv 1))
  have hr' : r - 1 ≤ τ * (r - 1) := Nat.le_mul_of_pos_left _ hτpos
  change (flattenChallenge (initialJetSeparantOver (Polynomial.C center) Q)).degreeOf _ ≤ _
  omega

/-- Every common numerator fits the three bounds used for all source cuts. -/
theorem commonTaylorNumeratorOver_mem_sourceCurveCutDerivativeBidegree
    (center : E) (Q : DifferentialPolynomial E[X] 1) (ℓ K h v r τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hv : 0 < v) (hr : 0 < r)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ r) (l : Fin K) :
    (optionEquivRight E _).symm
        (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ)) ∈
      restrictDerivativeBidegree (F := E)
        (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
        (sourceCurveCutJetDegree K v (τ := τ)) (sourceCurveCutDerivativeDegree K v r τ) := by
  apply mem_restrictDerivativeBidegree_of_bidegree
    (commonTaylorNumeratorOver_mem_sourceCurveCutBidegree_of_exponent
      center Q ℓ K h v τ hτ hv hheight hjet l)
  exact (flattenChallenge_degreeOf_le _ _).trans
    ((degreeOf_commonTaylorNumeratorOver_firstOrder
      (Polynomial.C center) Q r K τ hτ hr hderiv l).trans (by omega))

/-- All high-coefficient equations used by the existing source incidence argument satisfy
the refined support restriction. -/
theorem sourceCurveHighCuts_mem_sourceCurveCutDerivativeBidegree
    (center : E) (Q : DifferentialPolynomial E[X] 1) (ℓ K k h v r τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hv : 0 < v) (hr : 0 < r)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ r) :
    ∀ f ∈ sourceCurveHighCuts_of_exponent center Q K k τ,
      f ∈ restrictDerivativeBidegree (F := E)
        (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
        (sourceCurveCutJetDegree K v (τ := τ)) (sourceCurveCutDerivativeDegree K v r τ) := by
  intro f hf
  simp only [sourceCurveHighCuts_of_exponent, List.mem_map, Finset.mem_toList] at hf
  obtain ⟨l, _, rfl⟩ := hf
  exact commonTaylorNumeratorOver_mem_sourceCurveCutDerivativeBidegree
    center Q ℓ K h v r τ hτ hv hr hheight hjet hderiv l.val

/-- Each received-curve agreement equation satisfies exactly the same support restriction. -/
theorem symbolicSourceCurveAgreement_mem_sourceCurveCutDerivativeBidegree
    (center alpha : E) (values : Fin (ℓ + 1) → E)
    (Q : DifferentialPolynomial E[X] 1) (K h v r τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hv : 0 < v) (hr : 0 < r)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ r) :
    symbolicSourceCurveAgreement_of_exponent center Q K τ alpha values ∈
      restrictDerivativeBidegree (F := E)
        (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
        (sourceCurveCutJetDegree K v (τ := τ)) (sourceCurveCutDerivativeDegree K v r τ) := by
  simpa only [symbolicSourceCurveAgreement_of_exponent, flattenChallenge,
    sourceCurveCutChallengeDegree, sourceCurveCutJetDegree, sourceCurveCutDerivativeDegree] using
      taylorAgreementEquationOver_mem_restrictDerivativeBidegree center alpha
        (powerBatchedCoordinate values) Q ℓ h v r K τ hτ
        (powerBatchedCoordinate_natDegree_le values) hv hr hheight hjet hderiv

end ReedSolomon
