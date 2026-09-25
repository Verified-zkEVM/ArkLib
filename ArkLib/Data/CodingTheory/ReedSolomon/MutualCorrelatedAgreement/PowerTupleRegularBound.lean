/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleIncidence
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedFrobeniusFamily
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import ArkLib.Data.Polynomial.Differential.FrobeniusTaylorWitness
public import ArkLib.Data.Polynomial.Differential.RationalTaylorBidegree
import ArkLib.Data.Polynomial.Differential.TaylorChartGeometry
public import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullback
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
/-!
# Bounds for regular Frobenius power witnesses

Finite families of regular expanded solutions with many agreements but no exact power agreement
are bounded by the incidence of regular points outside retained tuple graphs and the exceptional
challenges for retained tuples.
A common regular Taylor center can be selected from witness separants to apply this bound without
a prescribed center.

## Main statements

* `finite_frobeniusPowerRegularBadChallenges_card_le` gives the bound at any retained-agreement
  threshold `L` between `k` and the requested agreement `A`.
* `finite_frobeniusPowerRegularBadChallenges_card_le_of_separant_at` chooses a common regular
  Taylor center for a finite family and applies the bound.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential

variable {F E : Type*} [Field F] [Field E] {n k K ℓ : ℕ}

open Classical in
/-- A finite family of regular Frobenius witnesses with at least `A` agreements and no exact
power agreement satisfies the off-graph incidence bound at threshold `L`, plus the retained-tuple
exceptional-challenge bound. -/
theorem finite_frobeniusPowerRegularBadChallenges_card_le [IsAlgClosed E]
    {L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hℓ : 0 < ℓ) (hb : 0 < b)
    (hkL : k ≤ L) (hLA : L ≤ A)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ b)
    (hinit : jointInitialJetEquation center Q ≠ 0)
    (hproper : Ideal.span ({jointInitialJetEquation center Q} :
      Set (MvPolynomial (Option (Fin 1)) E)) ≠ ⊤)
    (challenges : Finset E) (witness : E → E[X])
    (hdegree : ∀ z ∈ challenges, (expand E (p ^ e) (witness z)).degree < K)
    (hsol : ∀ z ∈ challenges,
      differentialSpecialization (challengeSpecialization Q z)
        (expand E (p ^ e) (witness z)) = 0)
    (hsep : ∀ z ∈ challenges,
      jetEvaluation (separant (challengeSpecialization Q z) (Fin.last 0)) center
        (polynomialJet center (expand E (p ^ e) (witness z))) ≠ 0)
    (hagree : ∀ z ∈ challenges, A ≤
      (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
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
  let tuples := fullTuples.filter fun P ↦
    L ≤ (commonCurveAgreementSet domain values P).card
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
  let discarded := challenges.filter fun z ↦ z ^ (p ^ e) ∈ exceptional
  let remaining := challenges.filter fun z ↦ z ^ (p ^ e) ∉ exceptional
  let point : E → Option (Fin 1) → E := fun z i ↦
    i.elim z fun j ↦ (polynomialJet center (expand E (p ^ e) (witness z))) j
  have hpointinj : Function.Injective point := by
    intro z y heq
    exact congrFun heq none
  have hchart (z : E) (hz : z ∈ challenges) :=
    frobeniusExpansion_satisfies_jointTaylorCuts Q center z (witness z) p e K τ hτ
      (hdegree z hz) (hsol z hz) (by
        rw [aeval_initialJetSeparant]
        exact hsep z hz)
  have hoff (z : E) (hz : z ∈ remaining) :
      point z ∉ admissibleFrobeniusPowerTupleGraphLocus
        domain values ι roots center Q K k L τ (p ^ e) := by
    obtain ⟨hzc, hze⟩ := Finset.mem_filter.mp hz
    rintro ⟨P, hP, hcommon, heq⟩
    have hjetEq : polynomialJet center (expand E (p ^ e) (witness z)) =
        fun j ↦ (frobeniusPowerGraphMap center (p ^ e)
          (fun t ↦ (P t).map ι) (some j)).eval z := by
      funext j
      simpa only [point, Option.elim_some, Option.elim_none] using
        congrFun heq (some j)
    have hgraph : point z =
        fun i ↦ (frobeniusPowerGraphMap center (p ^ e)
          (fun t ↦ (P t).map ι) i).eval z := by
      simpa only [point, Option.elim_none] using heq
    have hregular :
        (aeval (frobeniusPowerGraphMap center (p ^ e)
          (fun t ↦ (P t).map ι)) (jointInitialJetSeparant center Q)).eval z ≠ 0 := by
      rw [MvPolynomial.polynomial_eval_aeval, ← hgraph]
      simpa only [MvPolynomial.aeval_eq_eval] using (hchart z hzc).2.1
    have hrec := hP.specialize hroots hK hKk hτ z hregular
    have hrecWitness : rationalTaylorPolynomial center
        (challengeSpecialization Q z) K
        (fun j ↦ (frobeniusPowerGraphMap center (p ^ e)
          (fun t ↦ (P t).map ι) (some j)).eval z) =
        expand E (p ^ e) (witness z) := by
      rw [← hjetEq]
      simpa only [challengeSpecialization] using
        rationalTaylorPolynomial_polynomialJet center (challengeSpecialization Q z)
        (expand E (p ^ e) (witness z)) (hsol z hzc)
        (hsep z hzc) (hdegree z hzc) (by simp)
    have hrec' : rationalTaylorPolynomial center (challengeSpecialization Q z) K
        (fun j ↦ (frobeniusPowerGraphMap center (p ^ e)
          (fun t ↦ (P t).map ι) (some j)).eval z) =
        expand E (p ^ e) (powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e))) := by
      have hchallenge : challengeSpecialization Q z =
          MvPolynomial.map (Polynomial.evalRingHom z) Q := by
        unfold challengeSpecialization
        congr 1
      rw [hchallenge]
      exact hrec
    have hwitness : witness z = powerBatchedPolynomial
        (fun t ↦ (P t).map ι) (z ^ (p ^ e)) := by
      apply Polynomial.expand_injective (pow_pos (expChar_pos E p) e)
      rw [← hrecWitness, hrec']
    have hPfull : P ∈ fullTuples :=
      (mem_frobeniusRetainedPowerTupleFamily_iff
        domain values ι roots center Q K k τ (p ^ e) P).mpr hP
    have hcommonCard : L ≤ (commonCurveAgreementSet domain values P).card := by
      have hcommonSet :
          ({i : Fin n | ∀ t, (P t).eval (domain i) = values t i} : Set (Fin n)) =
            (commonCurveAgreementSet domain values P : Set (Fin n)) := by
        ext i
        simp [commonCurveAgreementSet]
      rw [hcommonSet] at hcommon
      exact hcommon.trans_eq (Set.ncard_coe_finset _)
    have hPmem : P ∈ tuples :=
      Finset.mem_filter.mpr ⟨hPfull, hcommonCard⟩
    apply hbad z hzc
    simpa only [hwitness] using hexact P hPmem (z ^ (p ^ e)) hze
  have hoffbound : (remaining.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) := by
    rw [← Finset.card_image_of_injective remaining hpointinj]
    apply finite_frobeniusPowerTupleIncidence_off_graphs_card_le
      domain values ι p e roots hroots center Q hK hKk τ h b A hτ hτpos hℓ hb
        hkL hLA hheight hjet hinit hproper (remaining.image point)
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_filter.mp hz).1
      refine ⟨(hchart z hzc).1, (hchart z hzc).2.1, ?_, hoff z hz⟩
      intro q hq
      simp only [frobeniusPowerSparseTaylorNumerators, List.mem_map,
        Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨l, hl, rfl⟩ := hq
      exact (hchart z hzc).2.2.1 l hl
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_filter.mp hz).1
      let domainE := domain.trans ⟨ι, ι.injective⟩
      let received := powerBatchedWord (fun t i ↦ ι (values t i)) (z ^ (p ^ e))
      have hsubset :
          (polynomialAgreementSet domainE received (witness z) : Set (Fin n)) ⊆
            {i | aeval (point z) (jointTaylorAgreementEquation center Q K τ
              (Polynomial.C (roots i))
              (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i)))) = 0} := by
        intro i hi
        have hi' := (mem_polynomialAgreementSet domainE received (witness z) i).mp hi
        apply ((hchart z hzc).2.2.2 (roots i)
          (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i)))).mpr
        rw [hroots]
        simpa only [domainE, received, Function.Embedding.trans_apply,
          Function.Embedding.coeFn_mk, Polynomial.eval_map,
          Polynomial.eval₂_at_apply, frobeniusPowerCoordinate_eval,
          powerBatchedWord, pow_mul] using hi'
      have hcard :
          (polynomialAgreementSet domainE received (witness z)).card =
            (polynomialAgreementSet domainE received (witness z) : Set (Fin n)).ncard :=
        (Set.ncard_coe_finset _).symm
      calc
        A ≤ (polynomialAgreementSet domainE received (witness z)).card := hagree z hzc
        _ = (polynomialAgreementSet domainE received (witness z) : Set (Fin n)).ncard := hcard
        _ ≤ _ := Set.ncard_le_ncard hsubset
  have htuplecount : tuples.card ≤ b := by
    calc
      tuples.card ≤ fullTuples.card := Finset.card_filter_le _ _
      _ ≤ (jointInitialJetEquation center Q).degreeOf (some 0) :=
        frobeniusRetainedPowerTupleFamily_card_le
          domain values ι roots center Q p e τ hroots hK hKk hτ hinit
      _ ≤ b := by
        apply MvPolynomial.degreeOf_le_iff.mpr
        intro u hu
        have hrectangle :
            jointInitialJetEquation center Q ∈ restrictBidegree (Fin 1) E h b := by
          simpa only [jointInitialJetEquation] using
            initialJetEquation_mem_restrictBidegree center Q h b hheight hjet
        have hjetDegree :
            (jointInitialJetEquation center Q).weightedTotalDegree
              (fun v : Option (Fin 1) ↦ v.elim 0 fun _ ↦ 1) ≤ b :=
          (mem_restrictBidegree_iff_weightedTotalDegree_le.mp hrectangle).2
        exact (Finsupp.le_weight (fun v : Option (Fin 1) ↦ v.elim 0 fun _ ↦ 1)
            (by decide) u).trans
          ((MvPolynomial.le_weightedTotalDegree
            (fun v : Option (Fin 1) ↦ v.elim 0 fun _ ↦ 1) hu).trans hjetDegree)
  have hpowinj : Function.Injective (fun z : E ↦ z ^ (p ^ e)) := by
    intro z y hzy
    apply iterateFrobenius_inj E p e
    simpa only [iterateFrobenius_def] using hzy
  have hdiscarded : discarded.card ≤ exceptional.card :=
    Finset.card_le_card_of_injOn (fun z ↦ z ^ (p ^ e))
      (fun _ hz ↦ (Finset.mem_filter.mp hz).2) hpowinj.injOn
  have hexcbound : discarded.card ≤ ℓ * (n - L) * b := by
    calc
      discarded.card ≤ exceptional.card := hdiscarded
      _ ≤ tuples.card * (ℓ * (n - L)) := by simpa only [Fintype.card_fin] using hexc
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

private theorem span_singleton_ne_top_of_aeval_eq_zero {σ : Type*}
    (g : MvPolynomial σ E) (x : σ → E) (hx : aeval x g = 0) :
    Ideal.span ({g} : Set (MvPolynomial σ E)) ≠ ⊤ := by
  intro htop
  have hgunit : IsUnit g := Ideal.span_singleton_eq_top.mp htop
  have hevalunit : IsUnit (MvPolynomial.aeval x g) := hgunit.map (MvPolynomial.aeval x)
  rw [hx] at hevalunit
  exact not_isUnit_zero hevalunit

open Classical in
/-- A finite family of regular Frobenius witnesses satisfies the bound at every retained-
agreement threshold between `k` and `A`. -/
theorem finite_frobeniusPowerRegularBadChallenges_card_le_of_separant_at [IsAlgClosed E]
    {L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hℓ : 0 < ℓ) (hb : 0 < b)
    (hkL : k ≤ L) (hLA : L ≤ A)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ b)
    (challenges : Finset E) (witness : E → E[X])
    (hdegree : ∀ z ∈ challenges, (expand E (p ^ e) (witness z)).degree < K)
    (hsol : ∀ z ∈ challenges,
      differentialSpecialization (challengeSpecialization Q z)
        (expand E (p ^ e) (witness z)) = 0)
    (hsep : ∀ z ∈ challenges,
      differentialSpecialization
        (separant (challengeSpecialization Q z) (Fin.last 0))
        (expand E (p ^ e) (witness z)) ≠ 0)
    (hagree : ∀ z ∈ challenges, A ≤
      (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
        (powerBatchedWord (fun t i ↦ ι (values t i)) (z ^ (p ^ e)))
        (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬HasExactPowerAgreement domain values ι k (z ^ (p ^ e)) (witness z)) :
    (challenges.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) +
      (ℓ * (n - L) * b : ℕ) := by
  classical
  obtain hempty | ⟨z, hz⟩ := challenges.eq_empty_or_nonempty
  · subst challenges
    positivity
  obtain ⟨center, hc⟩ := exists_forall_jetEvaluation_ne_zero_of_family challenges
    (fun z ↦ separant (challengeSpecialization Q z) (Fin.last 0))
    (fun z ↦ expand E (p ^ e) (witness z)) hsep
  have hinit : jointInitialJetEquation center Q ≠ 0 := by
    apply jointInitialJetEquation_ne_zero_of_regular center z Q
      (polynomialJet center (expand E (p ^ e) (witness z)))
    rw [aeval_initialJetSeparant]
    exact hc z hz
  have hchart := frobeniusExpansion_satisfies_jointTaylorCuts Q center z (witness z)
    p e K τ hτ (hdegree z hz) (hsol z hz) (by
      rw [aeval_initialJetSeparant]
      exact hc z hz)
  have hproper := span_singleton_ne_top_of_aeval_eq_zero
    (jointInitialJetEquation center Q)
    (fun i : Option (Fin 1) ↦ i.elim z fun j ↦
      polynomialJet center (expand E (p ^ e) (witness z)) j) hchart.1
  exact finite_frobeniusPowerRegularBadChallenges_card_le
    domain values ι roots center Q p e τ h b A hroots hK hKk hτ hτpos hℓ hb hkL hLA
      hheight hjet hinit hproper challenges witness hdegree hsol hc hagree hbad

end ReedSolomon

end
