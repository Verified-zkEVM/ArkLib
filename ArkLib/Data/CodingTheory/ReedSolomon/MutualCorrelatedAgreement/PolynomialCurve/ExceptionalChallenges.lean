/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExceptionalSet
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.GraphCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.Incidence
/-!
# Finite bad challenges for a polynomial-curve symbolic chart

This file combines exact agreement outside the retained tuples' exceptional set with the
strong, bidegree-sensitive off-graph incidence bound.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n r ℓ : ℕ}

private theorem source_initial_eval (center z : E) (Q : DifferentialPolynomial E[X] r)
    (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceInitialEquation center Q) =
      aeval jet (initialJetEquation center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  rw [symbolicSourceInitialEquation, aeval_optionEquivRight_symm,
    map_initialJetEquationOver]
  simp only [Option.elim_none, Option.elim_some]
  rw [show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C]
  rfl

private theorem source_separant_eval (center z : E) (Q : DifferentialPolynomial E[X] r)
    (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceSeparant center Q) =
      aeval jet (initialJetSeparant center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  rw [symbolicSourceSeparant, aeval_optionEquivRight_symm,
    map_initialJetSeparantOver]
  simp only [Option.elim_none, Option.elim_some]
  rw [show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C]
  rfl

private theorem source_numerator_eval (center z : E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (l : Fin K) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceNumerator center Q K l) =
      aeval jet (commonTaylorNumerator center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K l) := by
  rw [symbolicSourceNumerator, aeval_optionEquivRight_symm, eval_commonTaylorNumeratorOver]
  rfl

private theorem source_curveAgreement_eval (center z alpha : E)
    (values : Fin (ℓ + 1) → E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet)
        (symbolicSourceCurveAgreement center Q K alpha values) =
      aeval jet (taylorAgreementEquation center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K alpha
        (∑ t, z ^ t.val * values t)) := by
  rw [symbolicSourceCurveAgreement, aeval_optionEquivRight_symm]
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
    (Polynomial.C center) Q K (Polynomial.C alpha) (powerBatchedCoordinate values)
  rw [hφ, hc, hx] at he
  exact congrArg (MvPolynomial.aeval jet) (he.trans (congrArg
    (taylorAgreementEquation center (MvPolynomial.map (Polynomial.evalRingHom z) Q) K alpha)
    hy))

private theorem source_initial_ne_zero_of_regular (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E)
    (hs : aeval jet (initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ≠ 0) :
    symbolicSourceInitialEquation center Q ≠ 0 := by
  have hs' : initialJetSeparant center (MvPolynomial.map (Polynomial.evalRingHom z) Q) ≠ 0 := by
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

/-- Bad challenges for an actual fixed-center polynomial-curve chart satisfy the sum of the
strong lifted-power off-graph bound and the exact accidental-agreement budget.  Both summands
depend at most linearly on the batching degree `ℓ`; the degree raised to `r + 1` is independent
of `ℓ`. -/
theorem finite_sourceCurve_bad_challenges_card_le
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin (r + 1) → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val → aeval (jet z) (commonTaylorNumerator center Qz K l) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤
      ((ℓ + h : ℕ) : ℚ) * ((v + 1 : ℕ) : ℚ) *
        ((((n * (2 + 2 * K * v) : ℕ) : ℚ) /
          ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1)) +
      ((ℓ * (n - L) : ℕ) : ℚ) * ((v : ℚ) *
        ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
          ((L - k + 1 : ℕ) : ℚ)) ^ r)) := by
  classical
  let τ := 2 * K
  have hτ : TaylorExponentSufficient r K τ := taylorExponentSufficient_two_mul r K
  let tuples := admissibleChartTupleFamilyAtExponent domain w iota center Q K k L τ
  have htuple (P : Fin (ℓ + 1) → F[X]) (hP : P ∈ tuples) :=
    (mem_admissibleChartTupleFamilyAtExponent_iff
      domain w iota center Q K k L τ hkL P).mp hP
  obtain ⟨exceptional, hexc, hexact⟩ := exists_exceptional_exactPowerAgreement_family
    (k := k) (L := L) domain w iota tuples
      (fun P hP ↦ (htuple P hP).degree) (fun P hP ↦ (htuple P hP).common)
  let remaining := challenges \ exceptional
  let point : E → Option (Fin (r + 1)) → E := fun z i ↦ i.elim z (jet z)
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
        (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map iota)) z from heq]
      rw [source_separant_eval]
      exact hs
    have hrec := (hP.specialize hτ hkK z hregular).2.2.2
    have hw : witness z = powerBatchedPolynomial (fun t ↦ (P t).map iota) z := by
      rw [← (hchart z hzc).2.2.2.2, hjetEq]
      exact hrec
    have hPmem : P ∈ tuples :=
      (mem_admissibleChartTupleFamilyAtExponent_iff
        domain w iota center Q K k L τ hkL P).mpr hP
    apply hbad z hzc
    rw [hw]
    exact hexact P hPmem z hze
  have hoffbound : (remaining.card : ℚ) ≤
      ((ℓ + h : ℕ) : ℚ) * ((v + 1 : ℕ) : ℚ) *
        ((((n * (2 + 2 * K * v) : ℕ) : ℚ) /
          ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1)) := by
    by_cases hempty : remaining = ∅
    · rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
    obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hzc := (Finset.mem_sdiff.mp hz₀).1
    have hi := source_initial_ne_zero_of_regular center z₀ Q (jet z₀)
      (hchart z₀ hzc).2.2.1
    have hs : symbolicSourceSeparant center Q ≠ 0 := by
      intro hzero
      have he := source_separant_eval center z₀ Q (jet z₀)
      rw [hzero] at he
      change 0 = aeval (jet z₀) (initialJetSeparant center
        (MvPolynomial.map (Polynomial.evalRingHom z₀) Q)) at he
      exact (hchart z₀ hzc).2.2.1 he.symm
    rw [← hcard]
    apply finite_sourceCurve_points_off_tuples_card_le
      domain w iota center Q hK hkL (hk.trans_le hkL) hLA hAn hD hi hs hv hjet hheight S
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (source_initial_eval center z Q (jet z)).trans (hchart z hzc).2.1
      · rw [source_separant_eval]
        exact (hchart z hzc).2.2.1
      · intro l hl
        rw [source_numerator_eval]
        exact (hchart z hzc).2.2.2.1 l hl
      · rw [← sourceCurveTupleLocus_of_exponent_two_mul_eq]
        exact hoff z hz
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      apply (hagree z hzc).trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices, source_curveAgreement_eval,
        taylorAgreementEquation_eq_zero_iff _ _ _ _ (hchart z hzc).2.2.1,
        (hchart z hzc).2.2.2.2]
      exact (Finset.mem_filter.mp hi).2
  have htuplebound := admissibleChartTupleFamilyAtExponent_card_le
    domain w iota center Q K k L v τ hτ hK hkK hk hkL (hLA.trans hAn) hjet
  have hexcbound : (exceptional.card : ℚ) ≤
      ((ℓ * (n - L) : ℕ) : ℚ) * ((v : ℚ) *
        ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
          ((L - k + 1 : ℕ) : ℚ)) ^ r)) := by
    have he : (exceptional.card : ℚ) ≤
        (tuples.card : ℚ) * ((ℓ * (n - L) : ℕ) : ℚ) := by
      exact_mod_cast hexc
    apply he.trans
    have hm := mul_le_mul_of_nonneg_right htuplebound
      (show (0 : ℚ) ≤ ((ℓ * (n - L) : ℕ) : ℚ) by positivity)
    simpa only [tuples, τ, mul_comm, mul_left_comm, mul_assoc] using hm
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

end ReedSolomon
