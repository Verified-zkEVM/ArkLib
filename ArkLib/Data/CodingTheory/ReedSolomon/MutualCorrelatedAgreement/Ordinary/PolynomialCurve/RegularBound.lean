/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Incidence
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Family
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Witness
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Symbolic.RegularEquation
public import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullback
/-!
# Regular Frobenius incidence bound for polynomial curves

Retained original-degree tuples contribute `ℓ * (n-k)` accidental challenges each.  All other
regular witnesses obey the mixed source incidence estimate with challenge degree `p ^ e * ℓ`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K ℓ : ℕ}

open Classical in
/-- A finite family of regular bad witnesses satisfies the exact free-retention bound. -/
theorem finite_frobeniusPowerRegularBadWitnesses_card_le_at [IsAlgClosed E]
    {L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hℓ : 0 < ℓ) (hb : 0 < b)
    (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (hproper : Ideal.span ({symbolicSourceInitialEquation center Q} :
      Set (MvPolynomial (Option (Fin 1)) E)) ≠ ⊤)
    (challenges : Finset E) (witness : E → E[X])
    (hdegree : ∀ z ∈ challenges, (expand E (p ^ e) (witness z)).degree < K)
    (hsol : ∀ z ∈ challenges, differentialSpecialization (challengeSpecialization Q z)
      (expand E (p ^ e) (witness z)) = 0)
    (hsep : ∀ z ∈ challenges,
      jetEvaluation (separant (challengeSpecialization Q z) (Fin.last 0)) center
        (polynomialJet center (expand E (p ^ e) (witness z))) ≠ 0)
    (hagree : ∀ z ∈ challenges, A ≤
      (polynomialAgreementSet (mappedDomain domain ι)
        (powerBatchedWord (fun t i ↦ ι (values t i)) (z ^ (p ^ e)))
        (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬HasExactPowerAgreement domain values ι k (z ^ (p ^ e)) (witness z)) :
    (challenges.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) +
      (ℓ * (n - L) * b : ℕ) := by
  classical
  let fullTuples := frobeniusRetainedPowerTupleFamily
    domain values ι roots center Q K k τ (p ^ e)
  let tuples := fullTuples.filter fun P ↦ L ≤ (commonCurveAgreementSet domain values P).card
  have htupleDegree : ∀ P ∈ tuples, ∀ t, (P t).degree < k := by
    intro P hP
    have hfull : P ∈ fullTuples := (Finset.mem_filter.mp hP).1
    exact (mem_frobeniusRetainedPowerTupleFamily_iff
      domain values ι roots center Q K k τ (p ^ e) P).mp hfull |>.degree
  have htupleCommon : ∀ P ∈ tuples,
      L ≤ (commonCurveAgreementSet domain values P).card := by
    intro P hP
    exact (Finset.mem_filter.mp hP).2
  obtain ⟨exceptional, hexc, hexact⟩ :=
    exists_exceptional_exactPowerAgreement_family (k := k) (L := L)
      domain values ι tuples htupleDegree htupleCommon
  let discarded := challenges.filter (fun z ↦ z ^ (p ^ e) ∈ exceptional)
  let remaining := challenges.filter (fun z ↦ z ^ (p ^ e) ∉ exceptional)
  let point : E → Option (Fin 1) → E := fun z ↦
    symbolicWitnessPoint center z (expand E (p ^ e) (witness z))
  have hpointinj : Function.Injective point := by
    intro z y heq
    exact congrFun heq none
  have hchart (z : E) (hz : z ∈ challenges) :=
    symbolicFrobeniusPowerWitness_equations (ℓ := ℓ) Q center z (witness z) p e K τ hτ
      (hdegree z hz) (hsol z hz) (hsep z hz)
  have hoff (z : E) (hz : z ∈ remaining) :
      point z ∉ sourceFrobeniusPowerGraphLocusAt
        domain values ι roots center Q K k L τ (p ^ e) := by
    obtain ⟨hzc, hze⟩ := Finset.mem_filter.mp hz
    rintro ⟨P, hP, hcommon, heq⟩
    have hjetEq : polynomialJet center (expand E (p ^ e) (witness z)) =
        fun j ↦ (frobeniusPowerInitialGraph center (p ^ e)
          (fun t ↦ (P t).map ι) j).eval z := by
      funext j
      exact congrFun heq (some j)
    have hregular : (polynomialGraphPullback
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι))
        (symbolicSourceSeparant center Q)).eval z ≠ 0 := by
      change point z = polynomialGraphPoint
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι)) z at heq
      rw [eval_polynomialGraphPullback, ← heq]
      exact (hchart z hzc).2.1
    have hrec := hP.specialize hroots hK hKk hτ z hregular
    have hwitness : witness z =
        powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e)) := by
      apply Polynomial.expand_injective (pow_pos (expChar_pos E p) e)
      rw [← symbolicFrobeniusPowerWitness_reconstruction Q center z (witness z) p e K
        (hdegree z hzc) (hsol z hzc) (hchart z hzc).2.1, hjetEq]
      exact hrec
    have hPfull : P ∈ fullTuples :=
      (mem_frobeniusRetainedPowerTupleFamily_iff
        domain values ι roots center Q K k τ (p ^ e) P).mpr hP
    have hPmem : P ∈ tuples := Finset.mem_filter.mpr ⟨hPfull, hcommon⟩
    apply hbad z hzc
    simpa only [hwitness] using hexact P hPmem (z ^ (p ^ e)) hze
  have hoffbound : (remaining.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) := by
    rw [← Finset.card_image_of_injective remaining hpointinj]
    apply finite_sourceFrobeniusPower_points_off_graphs_card_le_at
      domain values ι p e roots hroots center Q hK hKk τ h b A hτ hτpos hℓ hb
        hkL hLA hAn hheight hjet hinit hproper (remaining.image point)
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_filter.mp hz).1
      refine ⟨(hchart z hzc).1, (hchart z hzc).2.1, ?_, hoff z hz⟩
      intro q hq
      simp only [sourceFrobeniusPowerSparseCuts, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨l, hl, rfl⟩ := hq
      exact (hchart z hzc).2.2.1 l hl
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_filter.mp hz).1
      apply (hagree z hzc).trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices]
      apply ((hchart z hzc).2.2.2 (roots i) (fun t ↦ ι (values t i))).mpr
      rw [hroots]
      have hiAgree := (Finset.mem_filter.mp hi).2
      simpa only [mappedDomain, Function.Embedding.trans_apply,
        Function.Embedding.coeFn_mk, powerBatchedWord, pow_mul,
        Polynomial.eval_map, Polynomial.eval₂_at_apply] using hiAgree
  have hdiscarded : discarded.card ≤ exceptional.card :=
    Finset.card_le_card_of_injOn (fun z ↦ z ^ (p ^ e))
      (fun _ hz ↦ (Finset.mem_filter.mp hz).2)
      (MvPolynomial.pow_primePow_injective (K := E) p e).injOn
  have htuplecount : tuples.card ≤ b := by
    calc
      tuples.card ≤ fullTuples.card := by
        exact Finset.card_filter_le _ _
      _ ≤ (symbolicSourceInitialEquation center Q).degreeOf (some 0) :=
        frobeniusRetainedPowerTupleFamily_card_le
          domain values ι roots center Q p e τ hroots hK hKk hτ hinit
      _ ≤ b := by
        have hsupport := symbolicSourceInitialEquation_mem_restrictBidegree center Q h b
          hheight hjet
        rw [mem_restrictBidegree] at hsupport
        apply degreeOf_le_iff.mpr
        intro u hu
        exact (Finsupp.le_weight jetWeight (by decide) u).trans (hsupport u hu).2
  have hexcbound : discarded.card ≤ ℓ * (n - L) * b := by
    calc
      discarded.card ≤ exceptional.card := hdiscarded
      _ ≤ tuples.card * (ℓ * (n - L)) := hexc
      _ ≤ b * (ℓ * (n - L)) := Nat.mul_le_mul_right _ htuplecount
      _ = ℓ * (n - L) * b := by ring
  have hcover : discarded.card + remaining.card = challenges.card :=
    Finset.card_filter_add_card_filter_not (fun z ↦ z ^ (p ^ e) ∈ exceptional)
  have hcoverQ : (challenges.card : ℚ) = discarded.card + remaining.card := by
    exact_mod_cast hcover.symm
  rw [hcoverQ]
  have hdQ : (discarded.card : ℚ) ≤ (ℓ * (n - L) * b : ℕ) := by
    exact_mod_cast hexcbound
  linarith

open Classical in
/-- A finite family of actual regular bad witnesses satisfies a bound linear in `ℓ`. -/
theorem finite_frobeniusPowerRegularBadWitnesses_card_le [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hℓ : 0 < ℓ) (hb : 0 < b) (hkA : k ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (hproper : Ideal.span ({symbolicSourceInitialEquation center Q} :
      Set (MvPolynomial (Option (Fin 1)) E)) ≠ ⊤)
    (challenges : Finset E) (witness : E → E[X])
    (hdegree : ∀ z ∈ challenges, (expand E (p ^ e) (witness z)).degree < K)
    (hsol : ∀ z ∈ challenges, differentialSpecialization (challengeSpecialization Q z)
      (expand E (p ^ e) (witness z)) = 0)
    (hsep : ∀ z ∈ challenges,
      jetEvaluation (separant (challengeSpecialization Q z) (Fin.last 0)) center
        (polynomialJet center (expand E (p ^ e) (witness z))) ≠ 0)
    (hagree : ∀ z ∈ challenges, A ≤
      (polynomialAgreementSet (mappedDomain domain ι)
        (powerBatchedWord (fun t i ↦ ι (values t i)) (z ^ (p ^ e)))
        (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬HasExactPowerAgreement domain values ι k (z ^ (p ^ e)) (witness z)) :
    (challenges.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) +
      (ℓ * (n - k) * b : ℕ) := by
  classical
  let tuples := frobeniusRetainedPowerTupleFamily
    domain values ι roots center Q K k τ (p ^ e)
  obtain ⟨exceptional, hexc, hexact⟩ :=
    exists_exceptional_frobeniusRetainedPowerTupleFamily
      domain values ι roots center Q K k τ (p ^ e)
  let discarded := challenges.filter (fun z ↦ z ^ (p ^ e) ∈ exceptional)
  let remaining := challenges.filter (fun z ↦ z ^ (p ^ e) ∉ exceptional)
  let point : E → Option (Fin 1) → E := fun z ↦
    symbolicWitnessPoint center z (expand E (p ^ e) (witness z))
  have hpointinj : Function.Injective point := by
    intro z y heq
    exact congrFun heq none
  have hchart (z : E) (hz : z ∈ challenges) :=
    symbolicFrobeniusPowerWitness_equations (ℓ := ℓ) Q center z (witness z) p e K τ hτ
      (hdegree z hz) (hsol z hz) (hsep z hz)
  have hoff (z : E) (hz : z ∈ remaining) :
      point z ∉ sourceFrobeniusPowerGraphLocus
        domain values ι roots center Q K k τ (p ^ e) := by
    obtain ⟨hzc, hze⟩ := Finset.mem_filter.mp hz
    rintro ⟨P, hP, heq⟩
    have hjetEq : polynomialJet center (expand E (p ^ e) (witness z)) =
        fun j ↦ (frobeniusPowerInitialGraph center (p ^ e)
          (fun t ↦ (P t).map ι) j).eval z := by
      funext j
      exact congrFun heq (some j)
    have hregular : (polynomialGraphPullback
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι))
        (symbolicSourceSeparant center Q)).eval z ≠ 0 := by
      change point z = polynomialGraphPoint
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι)) z at heq
      rw [eval_polynomialGraphPullback, ← heq]
      exact (hchart z hzc).2.1
    have hrec := hP.specialize hroots hK hKk hτ z hregular
    have hwitness : witness z =
        powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e)) := by
      apply Polynomial.expand_injective (pow_pos (expChar_pos E p) e)
      rw [← symbolicFrobeniusPowerWitness_reconstruction Q center z (witness z) p e K
        (hdegree z hzc) (hsol z hzc) (hchart z hzc).2.1, hjetEq]
      exact hrec
    have hPmem : P ∈ tuples :=
      (mem_frobeniusRetainedPowerTupleFamily_iff
        domain values ι roots center Q K k τ (p ^ e) P).mpr hP
    apply hbad z hzc
    simpa only [hwitness] using hexact P hPmem (z ^ (p ^ e)) hze
  have hoffbound : (remaining.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
    rw [← Finset.card_image_of_injective remaining hpointinj]
    apply finite_sourceFrobeniusPower_points_off_graphs_card_le
      domain values ι p e roots hroots center Q hK hKk τ h b A hτ hτpos hℓ hb
        hkA hAn hheight hjet hinit hproper (remaining.image point)
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_filter.mp hz).1
      refine ⟨(hchart z hzc).1, (hchart z hzc).2.1, ?_, hoff z hz⟩
      intro q hq
      simp only [sourceFrobeniusPowerSparseCuts, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨l, hl, rfl⟩ := hq
      exact (hchart z hzc).2.2.1 l hl
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_filter.mp hz).1
      apply (hagree z hzc).trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices]
      apply ((hchart z hzc).2.2.2 (roots i) (fun t ↦ ι (values t i))).mpr
      rw [hroots]
      have hiAgree := (Finset.mem_filter.mp hi).2
      simpa only [mappedDomain, Function.Embedding.trans_apply,
        Function.Embedding.coeFn_mk, powerBatchedWord, pow_mul,
        Polynomial.eval_map, Polynomial.eval₂_at_apply] using hiAgree
  have hdiscarded : discarded.card ≤ exceptional.card :=
    Finset.card_le_card_of_injOn (fun z ↦ z ^ (p ^ e))
      (fun _ hz ↦ (Finset.mem_filter.mp hz).2)
      (MvPolynomial.pow_primePow_injective (K := E) p e).injOn
  have htuplecount : tuples.card ≤ b := by
    apply (frobeniusRetainedPowerTupleFamily_card_le
      domain values ι roots center Q p e τ hroots hK hKk hτ hinit).trans
    have hsupport := symbolicSourceInitialEquation_mem_restrictBidegree center Q h b
      hheight hjet
    rw [mem_restrictBidegree] at hsupport
    apply degreeOf_le_iff.mpr
    intro u hu
    exact (Finsupp.le_weight jetWeight (by decide) u).trans (hsupport u hu).2
  have hexcbound : discarded.card ≤ ℓ * (n - k) * b :=
    hdiscarded.trans (hexc.trans (Nat.mul_le_mul_left _ htuplecount))
  have hcover : discarded.card + remaining.card = challenges.card :=
    Finset.card_filter_add_card_filter_not (fun z ↦ z ^ (p ^ e) ∈ exceptional)
  have hcoverQ : (challenges.card : ℚ) = discarded.card + remaining.card := by
    exact_mod_cast hcover.symm
  rw [hcoverQ]
  have hdQ : (discarded.card : ℚ) ≤ (ℓ * (n - k) * b : ℕ) := by
    exact_mod_cast hexcbound
  linarith

end ReedSolomon
