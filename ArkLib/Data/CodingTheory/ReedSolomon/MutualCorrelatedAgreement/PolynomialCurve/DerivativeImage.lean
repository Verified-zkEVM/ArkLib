/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.DerivativeSupport
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.DerivativeTupleCounting
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.DerivativeBidegreeExcluded
/-! Derivative-capped regular first-order source incidence. -/

@[expose] public section

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

private theorem derivative_source_initial_eval {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceInitialEquation center Q) =
      aeval jet (initialJetEquation center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  rw [symbolicSourceInitialEquation, aeval_optionEquivRight_symm,
    map_initialJetEquationOver]
  simp only [Option.elim_none, Option.elim_some]
  rw [show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C]
  rfl

private theorem derivative_source_separant_eval {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceSeparant center Q) =
      aeval jet (initialJetSeparant center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  rw [symbolicSourceSeparant, aeval_optionEquivRight_symm,
    map_initialJetSeparantOver]
  simp only [Option.elim_none, Option.elim_some]
  rw [show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C]
  rfl

private theorem derivative_source_numerator_eval {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (K : ℕ) (l : Fin K)
    (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceNumerator center Q K l) =
      aeval jet (commonTaylorNumerator center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K l) := by
  rw [symbolicSourceNumerator, aeval_optionEquivRight_symm, eval_commonTaylorNumeratorOver]
  rfl

private theorem derivative_source_numerator_eval_of_exponent {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (K τ : ℕ) (l : Fin K)
    (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet)
        ((optionEquivRight E _).symm
          (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ))) =
      aeval jet (commonTaylorNumerator center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K l (τ := τ)) := by
  rw [aeval_optionEquivRight_symm]
  simp only [Option.elim_none, Option.elim_some]
  rw [eval_commonTaylorNumeratorOver center z Q K l τ]

private theorem derivative_source_curveAgreement_eval_of_exponent {r : ℕ} (center z alpha : E)
    (values : Fin (ℓ + 1) → E) (Q : DifferentialPolynomial E[X] r)
    (K τ : ℕ) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet)
        (symbolicSourceCurveAgreement_of_exponent center Q K τ alpha values) =
      aeval jet (taylorAgreementEquation center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K alpha
        (∑ t, z ^ t.val * values t) (τ := τ)) := by
  rw [symbolicSourceCurveAgreement_of_exponent, aeval_optionEquivRight_symm]
  simp only [Option.elim_none, Option.elim_some]
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  have hφ : φ.toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [φ]
  have hc : φ (Polynomial.C center) = center := by simp [φ]
  have hx : φ (Polynomial.C alpha) = alpha := by simp [φ]
  have hy : φ (powerBatchedCoordinate values) = ∑ t, z ^ t.val * values t := by
    change (powerBatchedCoordinate values).eval z = _
    exact powerBatchedCoordinate_eval values z
  have he := map_taylorAgreementEquationOver_eq φ
    (Polynomial.C center) Q K (Polynomial.C alpha) (powerBatchedCoordinate values) τ
  rw [hφ, hc, hx] at he
  exact congrArg (MvPolynomial.aeval jet) (he.trans (congrArg
    (fun received ↦ taylorAgreementEquation center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q) K alpha received (τ := τ))
    hy))


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


/-- Combine any source-point incidence estimate with sharp tuple counting and the exact
`ell * (n-L)` accidental-root bound.  The geometric source estimate is isolated in
`hsourceBound`; this partition and counting argument is independent of the source dimension. -/
private theorem
    finite_sourceCurve_bad_challenges_card_le_of_source_bound_derivativeCapped_of_exponent
    [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L A v u τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (offBound : ℚ)
    (hsourceBound : ∀ S : Finset (Option (Fin 2) → E),
      (∀ x ∈ S, aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
        aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval x ((optionEquivRight E _).symm
            (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l
              (τ := τ))) = 0) ∧
        x ∉ sourceCurveTupleLocus_of_exponent domain w iota center Q K k L τ) →
      (∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
        symbolicSourceCurveAgreement_of_exponent center Q K τ (iota (domain i))
          (fun t ↦ iota (w t i))) x).card) →
      (S.card : ℚ) ≤ offBound)
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
    (challenges.card : ℚ) ≤ offBound +
      ((ℓ * (n - L) : ℕ) : ℚ) *
        (firstOrderCurveFiberStageOne K v u τ : ℚ) *
          (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) := by
  classical
  let tuples := (polynomialTupleFamily domain w k).filter
    (IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ)
  have htuple (P : Fin (ℓ + 1) → F[X]) (hP : P ∈ tuples) :=
    (Finset.mem_filter.mp hP).2
  obtain ⟨exceptional, hexc, hexact⟩ := exists_exceptional_exactPowerAgreement_family
    (k := k) (L := L) domain w iota tuples
      (fun P hP ↦ (htuple P hP).degree) (fun P hP ↦ (htuple P hP).common)
  let remaining := challenges \ exceptional
  let point : E → Option (Fin 2) → E := fun z i ↦ i.elim z (jet z)
  have hpointinj : Function.Injective point := by
    intro z z' heq
    exact congrFun heq none
  let S := remaining.image point
  have hcard : S.card = remaining.card := Finset.card_image_of_injective _ hpointinj
  have hoff (z : E) (hz : z ∈ remaining) :
      point z ∉ sourceCurveTupleLocus_of_exponent domain w iota center Q K k L τ := by
    obtain ⟨hzc, hze⟩ := Finset.mem_sdiff.mp hz
    rintro ⟨P, hP, heq⟩
    have hjetEq : jet z = chartTupleJet iota center z P := by
      funext j
      exact congrFun heq (some j)
    have hs := (hchart z hzc).2.2.1
    have hregular :
        (chartTuplePullback iota center P (symbolicSourceSeparant center Q)).eval z ≠ 0 := by
      rw [chartTuplePullback, eval_polynomialGraphPullback]
      rw [← show point z = polynomialGraphPoint
        (powerBatchedJetGraph (r := 1) center (fun t ↦ (P t).map iota)) z from heq]
      rw [derivative_source_separant_eval]
      exact hs
    have hrec := (hP.specialize hτ hkK z hregular).2.2.2
    have hw : witness z = powerBatchedPolynomial (fun t ↦ (P t).map iota) z := by
      rw [← (hchart z hzc).2.2.2.2, hjetEq]
      exact hrec
    have hPmem : P ∈ tuples := by
      apply Finset.mem_filter.mpr
      exact ⟨mem_polynomialTupleFamily_of_commonAgreement domain w P k hP.degree
        (hkL.trans hP.common), hP⟩
    apply hbad z hzc
    rw [hw]
    exact hexact P hPmem z hze
  have hoffbound : (remaining.card : ℚ) ≤ offBound := by
    rw [← hcard]
    apply hsourceBound S
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      refine ⟨?_, ?_, ?_, hoff z hz⟩
      · exact (derivative_source_initial_eval center z Q (jet z)).trans (hchart z hzc).2.1
      · rw [derivative_source_separant_eval]
        exact (hchart z hzc).2.2.1
      · intro l hl
        rw [derivative_source_numerator_eval_of_exponent]
        exact (hchart z hzc).2.2.2.1 l hl
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      apply (hagree z hzc).trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices, derivative_source_curveAgreement_eval_of_exponent,
        taylorAgreementEquation_eq_zero_iff_of_exponent _ _ _ τ hτ _
          (hchart z hzc).2.2.1,
        (hchart z hzc).2.2.2.2]
      exact (Finset.mem_filter.mp hi).2
  have htuplebound := admissibleChartTuples_card_le_derivativeCapped_of_exponent
    domain w iota center Q K k L v u τ hτ hτpos hK hkK hk hkL (hLA.trans hAn)
      hu huv hjet hderiv tuples htuple
  have hexcbound : (exceptional.card : ℚ) ≤
      ((ℓ * (n - L) : ℕ) : ℚ) *
        (firstOrderCurveFiberStageOne K v u τ : ℚ) *
          (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) := by
    have he : (exceptional.card : ℚ) ≤
        (tuples.card : ℚ) * ((ℓ * (n - L) : ℕ) : ℚ) := by
      exact_mod_cast hexc
    apply he.trans
    have hm := mul_le_mul_of_nonneg_right htuplebound
      (show (0 : ℚ) ≤ ((ℓ * (n - L) : ℕ) : ℚ) by positivity)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
  have hcover : challenges.card ≤ remaining.card + exceptional.card := by
    have he := Finset.card_sdiff_add_card_inter challenges exceptional
    have hi := Finset.card_le_card (Finset.inter_subset_right :
      challenges ∩ exceptional ⊆ exceptional)
    dsimp only [remaining]
    omega
  have hcoverQ : (challenges.card : ℚ) ≤
      (remaining.card : ℚ) + (exceptional.card : ℚ) := by
    exact_mod_cast hcover
  exact hcoverQ.trans (add_le_add hoffbound hexcbound)


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
    ((ℓ * (n - L) : ℕ) : ℚ) *
      (firstOrderCurveFiberStageOne K v u τ : ℚ) *
        (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ))

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
      (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (div_nonneg (by positivity) (by positivity)))
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinit := source_initial_ne_zero_of_regular center z₀ Q (jet z₀)
    (hchart z₀ hz₀).2.2.1
  unfold regularSymbolicCurveMCADerivativeBoundTwo
  convert (finite_sourceCurve_bad_challenges_card_le_of_source_bound_derivativeCapped_of_exponent
      domain w iota center Q K k L A v u τ hτ hτpos hK hkK hk hkL hLA hAn
      hu huv hjet hderiv
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
