/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.SharpRegularEquation
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.ProductBounds
/-!
# Sharp regular polynomial-curve bounds at arbitrary derivative order

For a source differential equation of order `r`, put

```text
a = ell + tau*h,
b = 1 + tau*(v-1),
J = h*b^(r+1) + (r+1)*v*a*b^r.
```

This file proves the regular-curve exceptional-set bound

```text
J * ((n-L+1)/(A-L+1)) * P_r(A)
  + ell*(n-L)*v*b^r*P_r(L),
```

where `P_r(T) = prod_{j<r} (n-k+j+1)/(T-k+j+1)`. The first term uses the
dimension-sensitive source recurrence after the terminal graph factor. The second term is the
exact `ell*(n-L)` accidental-root count for each admissible tuple, combined with the fixed-chart
coefficient-space recurrence.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

/-- Mixed affine degree of the pulled-back order-`r` initial hypersurface. -/
def sourceCurveInitialMixedDegree (r ℓ K v h : ℕ) (τ : ℕ := 2 * K) : ℕ :=
  h * sourceCurveCutJetDegree K v (τ := τ) ^ (r + 1) +
    (r + 1) * v * sourceCurveCutChallengeDegree ℓ K h (τ := τ) *
      sourceCurveCutJetDegree K v (τ := τ) ^ r

/-- Dimension-sensitive regular order-`r` MCA budget: mixed source incidence plus exact tuple
roots, with the paper's evaluation products in both terms. -/
def regularSymbolicCurveMCASharpBound
    (r n ℓ K k L A v h : ℕ) (τ : ℕ := 2 * K) : ℚ :=
  (sourceCurveInitialMixedDegree r ℓ K v h (τ := τ) : ℚ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
      dimensionSensitiveIncidenceProduct n A k 1 r +
    ((ℓ * (n - L) : ℕ) : ℚ) * (v : ℚ) *
      (sourceCurveCutJetDegree K v (τ := τ) : ℚ) ^ r *
      dimensionSensitiveIncidenceProduct n L k 1 r

private theorem span_singleton_ne_top_of_aeval_eq_zero_general {S : Type*}
    (g : MvPolynomial S E) (x : S → E) (hx : aeval x g = 0) :
    Ideal.span ({g} : Set (MvPolynomial S E)) ≠ ⊤ := by
  intro htop
  have hgunit : IsUnit g := Ideal.span_singleton_eq_top.mp htop
  have hevalunit : IsUnit (MvPolynomial.aeval x g) := hgunit.map (MvPolynomial.aeval x)
  rw [hx] at hevalunit
  exact not_isUnit_zero hevalunit

private theorem source_initial_ne_zero_of_regular_general {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E)
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
    apply (optionEquivRight E (Fin (r + 1))).symm.injective
    simpa only [symbolicSourceInitialEquation, map_zero] using hzero
  have hm := congrArg (MvPolynomial.map (Polynomial.evalRingHom z)) he
  rw [map_initialJetEquationOver, map_zero,
    show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at hm
  exact hi hm

/-- Dimension-sensitive off-tuple source incidence at an explicit sufficient Taylor exponent.
Every retained presentation prime is mapped back to the genuine source coordinates before the
hereditary coefficient-space bound or the terminal graph recognition premise is applied. -/
theorem finite_sourceCurve_points_off_tuples_card_le_sharp_of_exponent
    {r : ℕ} [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hτpos : 0 < τ)
    (hK : r < K) (hkK : k ≤ K) (hLA : L ≤ A) (hkA : k ≤ A)
    (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin (r + 1))) E),
      J.IsPrime → symbolicSourceSeparant center Q ∉ J →
      symbolicSourceInitialEquation center Q ∈ J →
      (∀ f ∈ sourceCurveHighCuts_of_exponent center Q K k τ, f ∈ J) →
      0 < (hilbertPolynomial J).natDegree →
      L ≤ (cutsInIdeal J (fun i ↦ symbolicSourceCurveAgreement_of_exponent
        center Q K τ (iota (domain i)) (fun t ↦ iota (w t i)))).card →
      principalOpenZeroLocus J (symbolicSourceSeparant center Q) ⊆
        sourceCurveTupleLocus_of_exponent domain w iota center Q K k L τ)
    (S : Finset (Option (Fin (r + 1)) → E))
    (hS : ∀ x ∈ S, aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
      aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval x ((optionEquivRight E _).symm
          (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l
            (τ := τ))) = 0) ∧
      x ∉ sourceCurveTupleLocus_of_exponent domain w iota center Q K k L τ)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
      symbolicSourceCurveAgreement_of_exponent center Q K τ (iota (domain i))
        (fun t ↦ iota (w t i))) x).card) :
    (S.card : ℚ) ≤ sourceCurveInitialMixedDegree r ℓ K v h (τ := τ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        dimensionSensitiveIncidenceProduct n A k 1 r := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r)
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let g := symbolicSourceInitialEquation center Q
  let s := symbolicSourceSeparant center Q
  let high := sourceCurveHighCuts_of_exponent center Q K k τ
  let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
    symbolicSourceCurveAgreement_of_exponent center Q K τ (iota (domain i))
      (fun t ↦ iota (w t i))
  have hproper :
      Ideal.span ({g} : Set (MvPolynomial (Option (Fin (r + 1))) E)) ≠ ⊤ :=
    span_singleton_ne_top_of_aeval_eq_zero_general g x₀ (hS x₀ hx₀).1
  have ha : 0 < sourceCurveCutChallengeDegree ℓ K h (τ := τ) := by
    unfold sourceCurveCutChallengeDegree
    by_cases hℓ : 0 < ℓ
    · omega
    · have hh : 0 < h := by omega
      exact Nat.add_pos_right ℓ (Nat.mul_pos hτpos hh)
  have hb : 0 < sourceCurveCutJetDegree K v (τ := τ) := by
    simp only [sourceCurveCutJetDegree]
    omega
  have hbound : (S.card : ℚ) ≤
      affineDegree (bidegreeHypersurfaceIdeal
        (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
        (sourceCurveCutJetDegree K v (τ := τ)) g) *
      hybridDimensionSensitiveIncidenceProduct n A L k 1
        (min ((hilbertPolynomial (Ideal.span {g})).natDegree - 1) k + 1) := by
    apply bidegreeHypersurface_source_incidence_off_excluded_hybrid
      ha hb hLA hkA hAn g s hinit hproper
        (symbolicSourceInitialEquation_mem_sourceCurveCutBidegree_of_exponent
          center Q ℓ K h v τ hτpos hv hheight hjet)
        (symbolicSourceSeparant_mem_sourceCurveCutBidegree_of_exponent
          center Q ℓ K h v τ hτpos hheight hjet)
        high ?_ cuts ?_
        (sourceCurveTupleLocus_of_exponent domain w iota center Q K k L τ) ?_ ?_ S ?_ ?_
    · exact sourceCurveHighCuts_mem_sourceCurveCutBidegree_of_exponent
        center Q ℓ K k h v τ hτ hv hheight hjet
    · intro i
      exact symbolicSourceCurveAgreement_mem_sourceCurveCutBidegree_of_exponent center
        (iota (domain i)) (fun t ↦ iota (w t i)) Q K h v τ hτ hv hheight hjet
    · intro J hJ hsJ _hgJ hhighJ _hdJ
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
      apply hterminal J hJ
      · simpa only [s] using hsJ
      · simpa only [g] using hgJ
      · intro f hf
        exact hhighJ f (by simpa only [high] using hf)
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
  have hd := hilbertPolynomial_span_singleton_natDegree_add_one hinit hproper
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hd
  have hdg : (hilbertPolynomial (Ideal.span {g})).natDegree + 1 = r + 2 := by
    simpa only [g] using hd
  have hd' : (hilbertPolynomial (Ideal.span {g})).natDegree = r + 1 := by omega
  rw [hd'] at hbound
  have hdegree := bidegreeHypersurface_affineDegree_le ha hb hinit hproper
    (symbolicSourceInitialEquation_mem_restrictBidegree center Q h v hheight hjet)
  calc
    (S.card : ℚ) ≤ affineDegree (bidegreeHypersurfaceIdeal
        (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
        (sourceCurveCutJetDegree K v (τ := τ)) g) *
      hybridDimensionSensitiveIncidenceProduct n A L k 1 (min r k + 1) := by
        simpa only [Nat.add_sub_cancel] using hbound
    _ ≤ (sourceCurveInitialMixedDegree r ℓ K v h (τ := τ) : ℚ) *
        hybridDimensionSensitiveIncidenceProduct n A L k 1 (min r k + 1) :=
      mul_le_mul_of_nonneg_right hdegree
        (hybridDimensionSensitiveIncidenceProduct_nonneg n A L k 1 (min r k + 1))
    _ ≤ (sourceCurveInitialMixedDegree r ℓ K v h (τ := τ) : ℚ) *
        ((((n - L + 1) * 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ) *
          dimensionSensitiveIncidenceProduct n A k 1 r) :=
      mul_le_mul_of_nonneg_left
        (hybridDimensionSensitiveIncidenceProduct_min_le n A L k 1 r hkA hAn
          Nat.zero_lt_one) (by positivity)
    _ = _ := by simp only [Nat.mul_one]; ring

/-- Exact fixed-center bad-challenge bound at an explicit sufficient Taylor exponent. All
source and tuple cuts use `τ`; only the dimension-sensitive terminal recognition premise is
left for the localization bridge. -/
theorem finite_sourceCurve_bad_challenges_card_le_sharp_of_exponent
    {r : ℕ} [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hτpos : 0 < τ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin (r + 1))) E),
      J.IsPrime → symbolicSourceSeparant center Q ∉ J →
      symbolicSourceInitialEquation center Q ∈ J →
      (∀ f ∈ sourceCurveHighCuts_of_exponent center Q K k τ, f ∈ J) →
      0 < (hilbertPolynomial J).natDegree →
      L ≤ (cutsInIdeal J (fun i ↦ symbolicSourceCurveAgreement_of_exponent
        center Q K τ (iota (domain i)) (fun t ↦ iota (w t i)))).card →
      principalOpenZeroLocus J (symbolicSourceSeparant center Q) ⊆
        sourceCurveTupleLocus_of_exponent domain w iota center Q K k L τ)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin (r + 1) → E)
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
    (challenges.card : ℚ) ≤
      regularSymbolicCurveMCASharpBound r n ℓ K k L A v h (τ := τ) := by
  classical
  by_cases hempty : challenges = ∅
  · subst challenges
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold regularSymbolicCurveMCASharpBound
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r))
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity))
        (dimensionSensitiveIncidenceProduct_nonneg n L k 1 r))
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinit := source_initial_ne_zero_of_regular_general center z₀ Q (jet z₀)
    (hchart z₀ hz₀).2.2.1
  simpa only [regularSymbolicCurveMCASharpBound] using
    (finite_sourceCurve_bad_challenges_card_le_of_source_bound_of_exponent
      domain w iota center Q K k L A v τ hτ hK hkK hk hkL hLA hAn hjet
      ((sourceCurveInitialMixedDegree r ℓ K v h (τ := τ) : ℚ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
          dimensionSensitiveIncidenceProduct n A k 1 r)
      (fun S hS hA ↦ finite_sourceCurve_points_off_tuples_card_le_sharp_of_exponent
        domain w iota center Q K k L A v h τ hτ hτpos hK hkK hLA
          (hkL.trans hLA) hAn hD hv hinit
          hjet hheight hterminal S hS hA)
      challenges witness jet hchart hagree hbad)

/-- Every finite family of regular bad challenges at order `r` satisfies the sharp source
bound at an explicit Taylor exponent.  Prime-to-graph recognition is discharged internally at
the same exponent. -/
theorem finite_regularSymbolicCurveBadChallenges_card_le_sharp_recognized_of_exponent
    {r : ℕ} [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hτpos : 0 < τ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (S : Finset E)
    (hS : ↑S ⊆ regularSymbolicCurveBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤
      regularSymbolicCurveMCASharpBound r n ℓ K k L A v h (τ := τ) := by
  classical
  apply finite_regularSymbolicCurveBadChallenges_card_le_of_fixedCenter_of_exponent
    domain w iota Q K k A τ hτ hkK hbin
      (regularSymbolicCurveMCASharpBound r n ℓ K k L A v h (τ := τ)) ?_ S hS
  intro center challenges witness jet hchart hagree hbad
  apply finite_sourceCurve_bad_challenges_card_le_sharp_of_exponent
    domain w iota center Q K k L A v h τ hτ hτpos hK hkK hk hkL hLA hAn hD hv
      hjet hheight ?_ challenges witness jet hchart hagree hbad
  intro J hJ hsJ hinitJ hhighJ hdJ hcutsJ
  exact principalOpen_subset_sourceCurveTupleLocus_of_exponent
    domain w iota center Q hK hkL τ hτ J hJ hsJ hinitJ hhighJ hdJ hcutsJ

private theorem set_finite_of_finset_card_le_rational_general {X : Type*} (T : Set X) (B : ℚ)
    (hbound : ∀ S : Finset X, ↑S ⊆ T → (S.card : ℚ) ≤ B) : T.Finite := by
  by_contra hinfinite
  obtain ⟨N, hN⟩ := exists_nat_gt B
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
  have hb := hbound S hS
  rw [hcard] at hb
  exact (not_lt_of_ge hb) hN

/-- A single sharply bounded exceptional set at an explicit Taylor exponent works for every
regular order-`r` solution.  The exceptional set precedes the challenge and polynomial
quantifiers, and the conclusion contains equality of the complete agreement sets. -/
theorem exists_exceptional_regularSymbolicCurveMCA_sharp_recognized_of_exponent
    {r : ℕ} [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hτpos : 0 < τ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        regularSymbolicCurveMCASharpBound r n ℓ K k L A v h (τ := τ) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last r)) P ≠ 0 →
        HasExactPowerAgreement domain w iota k z P := by
  classical
  have hfinite :
      (regularSymbolicCurveBadChallenges domain w iota Q k A).Finite := by
    apply set_finite_of_finset_card_le_rational_general _
      (regularSymbolicCurveMCASharpBound r n ℓ K k L A v h (τ := τ))
    exact finite_regularSymbolicCurveBadChallenges_card_le_sharp_recognized_of_exponent
      domain w iota Q K k L A v h τ hτ hτpos hK hkK hk hkL hLA hAn hD hv
        hjet hheight hbin
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularSymbolicCurveBadChallenges_card_le_sharp_recognized_of_exponent
      domain w iota Q K k L A v h τ hτ hτpos hK hkK hk hkL hLA hAn hD hv
        hjet hheight hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

end ReedSolomon
