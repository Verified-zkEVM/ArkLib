/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.DerivativeSupport
import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.DerivativeBidegreeExcluded

/-! Derivative-capped regular first-order source incidence. -/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

private theorem span_singleton_ne_top_of_aeval_eq_zero {σ : Type*}
    (g : MvPolynomial σ E) (x : σ → E) (hx : aeval x g = 0) :
    Ideal.span ({g} : Set (MvPolynomial σ E)) ≠ ⊤ := by
  intro htop
  have hgunit : IsUnit g := Ideal.span_singleton_eq_top.mp htop
  have hevalunit : IsUnit (MvPolynomial.aeval x g) := hgunit.map (MvPolynomial.aeval x)
  rw [hx] at hevalunit
  exact not_isUnit_zero hevalunit

private theorem source_initial_ne_zero_of_regular (center z : E)
    (Q : DifferentialPolynomial E[X] 1) (jet : Fin 2 → E)
    (hs : aeval jet (initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ≠ 0) :
    symbolicSourceInitialEquation center Q ≠ 0 := by
  have hs' : initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q) ≠ 0 := by
    intro hzero
    exact hs (by rw [hzero]; simp)
  have hi := initialJetEquation_ne_zero_of_separant_ne_zero center _ hs'
  intro hzero
  have he : initialJetEquationOver (Polynomial.C center) Q = 0 := by
    apply (optionEquivRight E (Fin 2)).symm.injective
    simpa only [symbolicSourceInitialEquation, map_zero] using hzero
  have hm := congrArg (MvPolynomial.map (Polynomial.evalRingHom z)) he
  rw [map_initialJetEquationOver, map_zero,
    show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at hm
  exact hi hm

/-- Exact dimension-sensitive off-tuple incidence for a first-order source equation at a
sufficient common Taylor exponent.  The agreement cuts are linear in the bidegree presentation,
while every retained presentation prime is mapped back to the genuine source prime before the
coefficient-evaluation dimension bound is applied. -/
theorem finite_sourceCurve_points_off_tuples_card_le_derivativeCapped_of_exponent
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L A v u h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hD : 0 < ℓ + h) (hv : 0 < v) (hu : 0 < u) (huv : u ≤ v)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (S : Finset (Option (Fin 2) → E))
    (hS : ∀ x ∈ S, aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
      aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval x (symbolicSourceNumerator center Q K l (τ := τ)) = 0) ∧
      x ∉ sourceCurveTupleLocus_of_exponent domain w iota center Q K k L τ)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
      symbolicSourceCurveAgreement_of_exponent center Q K τ (iota (domain i))
        (fun t ↦ iota (w t i))) x).card) :
    (S.card : ℚ) ≤ mixedDerivativeImageDegree h v u
        (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
        (sourceCurveCutJetDegree K v (τ := τ))
        (sourceCurveCutDerivativeDegree K v u τ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let g := symbolicSourceInitialEquation center Q
  let s := symbolicSourceSeparant center Q
  let high := sourceCurveHighCuts_of_exponent center Q K k τ
  let cuts : Fin n → MvPolynomial (Option (Fin 2)) E := fun i ↦
    symbolicSourceCurveAgreement_of_exponent center Q K τ (iota (domain i))
      (fun t ↦ iota (w t i))
  have ha : 0 < sourceCurveCutChallengeDegree ℓ K h (τ := τ) := by
    unfold sourceCurveCutChallengeDegree
    by_cases hℓ : 0 < ℓ
    · omega
    · have hh : 0 < h := by omega
      exact Nat.add_pos_right ℓ (Nat.mul_pos hτpos hh)
  have hb : 0 < sourceCurveCutJetDegree K v (τ := τ) := by
    simp only [sourceCurveCutJetDegree]
    omega
  have hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) E)) ≠ ⊤ :=
    span_singleton_ne_top_of_aeval_eq_zero g x₀ (hS x₀ hx₀).1
  have hc : 0 < sourceCurveCutDerivativeDegree K v u τ := by
    unfold sourceCurveCutDerivativeDegree
    apply lt_min
    · simp only [sourceCurveCutJetDegree]
      omega
    · omega
  apply derivativeBidegreeHypersurface_source_incidence_off_excluded_hybrid_two
    ha hb hc (min_le_left _ _) huv hLA (hkL.trans hLA) hAn g s hinit hproper
      (symbolicSourceInitialEquation_mem_restrictDerivativeBidegree
        center Q h v u huv hheight hjet hderiv)
      (symbolicSourceInitialEquation_mem_sourceCurveCutDerivativeBidegree
        center Q ℓ K h v u τ hK hτpos hv hu hheight hjet hderiv)
      (symbolicSourceSeparant_mem_sourceCurveCutDerivativeBidegree
        center Q ℓ K h v u τ hτpos hheight hjet hderiv)
      high ?_ cuts ?_
      (sourceCurveTupleLocus_of_exponent domain w iota center Q K k L τ) ?_ ?_ S ?_ ?_
  · exact sourceCurveHighCuts_mem_sourceCurveCutDerivativeBidegree
      center Q ℓ K k h v u τ hτ hv hu hheight hjet hderiv
  · intro i
    exact symbolicSourceCurveAgreement_mem_sourceCurveCutDerivativeBidegree center
      (iota (domain i)) (fun t ↦ iota (w t i)) Q K h v u τ hτ hv hu
        hheight hjet hderiv
  · intro J hJ hsJ hgJ hhighJ _hdJ
    have hhigh' : ∀ l : Fin K, k ≤ l.val →
        symbolicSourceNumerator center Q K l (τ := τ) ∈ J := by
      intro l hl
      exact hhighJ _ (commonTaylorNumeratorOver_mem_sourceCurveHighCuts_of_exponent
        center Q K k τ l hl)
    have hdim := symbolicSourcePolynomial_dimensionSensitive_component_of_exponent
      center Q K k n τ hτ hK hkK J hJ hsJ hhigh' (mappedDomain domain iota)
        (fun i ↦ powerBatchedCoordinate (fun t ↦ iota (w t i)))
    simpa only [cuts, symbolicSourceCurveAgreement_of_exponent,
      symbolicSourcePolynomialAgreement, mappedDomain, Function.Embedding.trans_apply,
      Function.Embedding.coeFn_mk] using hdim
  · intro J hJ hsJ hgJ hhighJ hdJ hcutsJ
    apply principalOpen_subset_sourceCurveTupleLocus_of_exponent
      domain w iota center Q hK hkL τ hτ J hJ
    · simpa only [s] using hsJ
    · simpa only [g] using hgJ
    · intro q hq
      exact hhighJ q (by simpa only [high] using hq)
    · exact hdJ
    · simpa only [cuts] using hcutsJ
  · intro x hx
    refine ⟨(hS x hx).1, (hS x hx).2.1, ?_, (hS x hx).2.2.2⟩
    intro f hf
    simp only [high, sourceCurveHighCuts_of_exponent, List.mem_map,
      Finset.mem_toList] at hf
    obtain ⟨l, _, rfl⟩ := hf
    exact (hS x hx).2.2.1 l.val l.property
  · simpa only [cuts] using hA


/-- First-order regular MCA budget with the actual derivative degrees of the source equation
and the common Taylor cuts. -/
def regularSymbolicCurveMCADerivativeBoundTwo
    (n ℓ K k L A v u h τ : ℕ) : ℚ :=
  (mixedDerivativeImageDegree h v u
      (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
      (sourceCurveCutJetDegree K v (τ := τ))
      (sourceCurveCutDerivativeDegree K v u τ) : ℚ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) +
    ((ℓ * (n - L) : ℕ) : ℚ) * (v : ℚ) *
      (sourceCurveCutJetDegree K v (τ := τ) : ℚ) *
        dimensionSensitiveIncidenceProduct n L k 1 1

/-- Exact fixed-center first-order bad-challenge bound at a sufficient Taylor exponent.  The
joint term uses the direct dimension-sensitive factor, while the persistent-tuple term uses the
fixed-challenge coefficient-space factor. -/
theorem finite_sourceCurve_bad_challenges_card_le_derivativeCapped_of_exponent
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L A v u h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin 2 → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval (jet z) (commonTaylorNumerator center Qz K l (τ := τ)) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤ regularSymbolicCurveMCADerivativeBoundTwo n ℓ K k L A v u h τ := by
  classical
  by_cases hempty : challenges = ∅
  · subst challenges
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold regularSymbolicCurveMCADerivativeBoundTwo
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (div_nonneg (by positivity) (by positivity)))
        (div_nonneg (by positivity) (by positivity)))
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity))
        (dimensionSensitiveIncidenceProduct_nonneg _ _ _ _ _))
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinit := source_initial_ne_zero_of_regular center z₀ Q (jet z₀)
    (hchart z₀ hz₀).2.2.1
  unfold regularSymbolicCurveMCADerivativeBoundTwo
  convert (finite_sourceCurve_bad_challenges_card_le_of_source_bound_of_exponent
      domain w iota center Q K k L A v τ hτ hK hkK hk hkL hLA hAn hjet
      ((mixedDerivativeImageDegree h v u
          (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
          (sourceCurveCutJetDegree K v (τ := τ))
          (sourceCurveCutDerivativeDegree K v u τ) : ℚ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
          (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)))
      (fun S hS hA ↦ finite_sourceCurve_points_off_tuples_card_le_derivativeCapped_of_exponent
        domain w iota center Q K k L A v u h τ hτ hτpos hK hkK hkL hLA hAn hD hv
          hu huv hinit hjet hheight hderiv S hS hA)
      challenges witness jet hchart hagree hbad) using 1
  simp only [dimensionSensitiveIncidenceProduct_one, Nat.mul_one]
  push_cast
  ring


/-- Every finite set of regular first-order bad challenges satisfies the exact
dimension-sensitive bound at the supplied Taylor exponent. -/
theorem finite_regularSymbolicCurveBadChallenges_card_le_derivativeCapped_of_exponent
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (K k L A v u h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0)
    (S : Finset E)
    (hS : ↑S ⊆ regularSymbolicCurveBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤ regularSymbolicCurveMCADerivativeBoundTwo n ℓ K k L A v u h τ := by
  classical
  apply finite_regularSymbolicCurveBadChallenges_card_le_of_fixedCenter_of_exponent
    domain w iota Q K k A τ hτ hkK hbin
      (regularSymbolicCurveMCADerivativeBoundTwo n ℓ K k L A v u h τ) ?_ S hS
  intro center challenges witness jet hchart hagree hbad
  exact finite_sourceCurve_bad_challenges_card_le_derivativeCapped_of_exponent
    domain w iota center Q K k L A v u h τ hτ hτpos hK hkK hk hkL hLA hAn hD hv
      hu huv hjet hheight hderiv challenges witness jet hchart hagree hbad


private theorem set_finite_of_finset_card_le_rational {X : Type*} (T : Set X) (B : ℚ)
    (hbound : ∀ S : Finset X, ↑S ⊆ T → (S.card : ℚ) ≤ B) : T.Finite := by
  by_contra hinfinite
  obtain ⟨N, hN⟩ := exists_nat_gt B
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
  have hb := hbound S hS
  rw [hcard] at hb
  exact (not_lt_of_ge hb) hN

/-- A single dimension-sensitively bounded exceptional set works for every regular first-order
solution at the supplied Taylor exponent.  The conclusion retains the exact full agreement-set
equality through `HasExactPowerAgreement`. -/
theorem exists_exceptional_regularSymbolicCurveMCA_derivativeCapped_of_exponent
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (K k L A v u h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        regularSymbolicCurveMCADerivativeBoundTwo n ℓ K k L A v u h τ ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last 1)) P ≠ 0 →
        HasExactPowerAgreement domain w iota k z P := by
  classical
  have hfinite :
      (regularSymbolicCurveBadChallenges domain w iota Q k A).Finite := by
    apply set_finite_of_finset_card_le_rational _
      (regularSymbolicCurveMCADerivativeBoundTwo n ℓ K k L A v u h τ)
    exact finite_regularSymbolicCurveBadChallenges_card_le_derivativeCapped_of_exponent
      domain w iota Q K k L A v u h τ hτ hτpos hK hkK hk hkL hLA hAn hD hv
        hu huv hjet hheight hderiv hbin
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularSymbolicCurveBadChallenges_card_le_derivativeCapped_of_exponent
      domain w iota Q K k L A v u h τ hτ hτpos hK hkK hk hkL hLA hAn hD hv
        hu huv hjet hheight hderiv hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

end ReedSolomon
