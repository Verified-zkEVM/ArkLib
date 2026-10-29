/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedGraphCounting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLineComponent
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement

/-!
# Bad challenges for power-batched polynomial charts

Regular chart points outside admissible tuple graphs and exceptional exact-agreement challenges
give a bound for finite families of challenges whose reconstructed polynomials are not exact
power agreements.

## Main statements

* `finite_powerBatchedChart_badChallenges_card_le` bounds such challenges by the sum of the
  off-graph incidence bound and the exceptional tuple bound.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential
open scoped BigOperators

noncomputable section

namespace ReedSolomon

variable {F E : Type*} [Field F] [Field E] {n r ℓ : ℕ}

open Classical in
/-- A finite family of regular power-batched charts has a bad-challenge bound from incidence
outside admissible tuple graphs and exact-agreement exceptions for the retained tuples. -/
theorem finite_powerBatchedChart_badChallenges_card_le [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L A v h : ℕ) (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin (r + 1) → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
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
  let S : Finset (Option (Fin (r + 1)) → E) := by
    classical
    exact remaining.image point
  have hcard : S.card = remaining.card := by
    classical
    exact Finset.card_image_of_injective _ hpointinj
  have hoff (z : E) (hz : z ∈ remaining) :
      point z ∉ admissibleChartTupleGraphLocus domain w iota center Q K k L τ := by
    obtain ⟨hzc, hze⟩ := Finset.mem_sdiff.mp hz
    rintro ⟨P, hP, heq⟩
    have hjetEq : jet z = chartTupleJet iota center z P := by
      funext j
      exact congrFun heq (some j)
    have hsepz := (hchart z hzc).2.2.1
    have hsepz' : aeval (chartTupleJet iota center z P)
        (initialJetSeparant center
          (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ≠ 0 := by
      rw [← hjetEq]
      exact hsepz
    have hφ : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
      ext a <;> simp [Polynomial.evalRingHom]
    have hregular :
        (chartTuplePullback iota center P (jointInitialJetSeparant center Q)).eval z ≠ 0 := by
      rw [eval_chartTuplePullback, aeval_jointInitialJetSeparant]
      simpa only [Option.elim_none, Option.elim_some, hφ] using hsepz'
    have hrec := (hP.specialize hτ hkK z hregular).2.2.2
    have hw : witness z = powerBatchedPolynomial (fun t ↦ (P t).map iota) z := by
      rw [← (hchart z hzc).2.2.2, hjetEq]
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
    have hφ : (Polynomial.aeval z₀).toRingHom = Polynomial.evalRingHom z₀ := by
      ext a <;> simp [Polynomial.evalRingHom]
    have hinit := PolynomialDifferential.jointInitialJetEquation_ne_zero_of_regular center z₀ Q
      (jet z₀) (hchart z₀ hzc).2.2.1
    have hsepPoint : aeval (point z₀) (jointInitialJetSeparant center Q) ≠ 0 := by
      rw [aeval_jointInitialJetSeparant]
      simpa only [point, Option.elim_none, Option.elim_some, hφ] using
        (hchart z₀ hzc).2.2.1
    have hsep : jointInitialJetSeparant center Q ≠ 0 := by
      intro hzero
      apply hsepPoint
      rw [hzero]
      simp
    rw [← hcard]
    apply finite_admissibleChartTupleIncidence_off_graphs
      domain w iota center Q hK hkL (hk.trans_le hkL) hLA hAn hD hinit hsep hv hjet
      hheight S
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      have hφ : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
        ext a <;> simp [Polynomial.evalRingHom]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [aeval_jointInitialJetEquation]
        simpa only [point, Option.elim_none, Option.elim_some, hφ] using
          (hchart z hzc).2.1
      · rw [aeval_jointInitialJetSeparant]
        simpa only [point, Option.elim_none, Option.elim_some, hφ] using
          (hchart z hzc).2.2.1
      · intro l hl
        rw [aeval_jointCommonTaylorNumerator]
        have hcoeff : rationalTaylorCoefficient center
            (MvPolynomial.map (Polynomial.evalRingHom z) Q) (jet z) l.val = 0 := by
          have hprefix :
              (Polynomial.taylor center
                (rationalTaylorPolynomial center
                  (MvPolynomial.map (Polynomial.evalRingHom z) Q) K (jet z))).coeff l.val =
                rationalTaylorCoefficient center
                  (MvPolynomial.map (Polynomial.evalRingHom z) Q) (jet z) l.val := by
            simp [rationalTaylorPolynomial,
              Polynomial.coeff_taylor_centeredCoefficientPrefix, l.isLt]
          rw [← hprefix, (hchart z hzc).2.2.2]
          have hkl : (k : WithBot ℕ) ≤ (l.val : WithBot ℕ) := by
            exact_mod_cast hl
          have hdegree := ((hchart z hzc).1).trans_le hkl
          have hdegree' :
              (Polynomial.taylor center (witness z)).degree < (l.val : WithBot ℕ) := by
            simpa only [Polynomial.degree_taylor] using hdegree
          exact Polynomial.coeff_eq_zero_of_degree_lt hdegree'
        simpa only [point, Option.elim_none, Option.elim_some, hφ] using
          aeval_commonTaylorNumerator_eq_zero center
            (MvPolynomial.map (Polynomial.evalRingHom z) Q) (jet z) τ
            (hchart z hzc).2.2.1 hcoeff
      · exact hoff z hz
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      let domainE : Fin n ↪ E := domain.trans ⟨iota, iota.injective⟩
      let received : Fin n → E := powerBatchedWord (fun t i ↦ iota (w t i)) z
      have hsubset : (polynomialAgreementSet domainE received (witness z) : Set (Fin n)) ⊆
          {i | aeval (point z) (jointTaylorAgreementEquation center Q K τ
            (Polynomial.C (iota (domain i)))
            (powerBatchedCoordinate fun t ↦ iota (w t i))) = 0} := by
        intro i hi
        change aeval (point z) (jointTaylorAgreementEquation center Q K τ
          (Polynomial.C (iota (domain i)))
          (powerBatchedCoordinate fun t ↦ iota (w t i))) = 0
        have hi' := (mem_polynomialAgreementSet domainE received (witness z) i).mp hi
        have hsepz := (hchart z hzc).2.2.1
        have hφ : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
          ext a <;> simp [Polynomial.evalRingHom]
        have hiff := taylorAgreementEquation_eq_zero_iff center Qz hτ (jet z) hsepz
          (iota (domain i)) (received i)
        rw [aeval_jointTaylorAgreementEquation]
        simpa only [point, Option.elim_none, Option.elim_some, hφ, Qz, domainE, received,
          Polynomial.eval_C,
          powerBatchedCoordinate_eval, powerBatchedWord] using hiff.mpr (by
            rw [(hchart z hzc).2.2.2]
            exact hi')
      calc
        A ≤ (polynomialAgreementSet domainE received (witness z)).card := hagree z hzc
        _ = (polynomialAgreementSet domainE received (witness z) : Set (Fin n)).ncard :=
          (Set.ncard_coe_finset _).symm
        _ ≤ _ := Set.ncard_le_ncard hsubset
  have htuplebound := admissibleChartTupleFamilyAtExponent_card_le_dimensionSensitive
    domain w iota center Q K k L v τ hτ hK hkK hkL (hLA.trans hAn) hjet
  have hproduct := dimensionSensitiveIncidenceProduct_le_first_pow n L k r hkL
    (hLA.trans hAn)
  have hratio :
      (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ≤
        (n : ℚ) / ((L - k + 1 : ℕ) : ℚ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (show n - k + 1 ≤ n by omega)
  have hproduct' : dimensionSensitiveIncidenceProduct n L k 1 r ≤
      ((n : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r :=
    hproduct.trans (pow_le_pow_left₀ (by positivity) hratio r)
  let B := 1 + 2 * K * (v - 1)
  have hratioPow :
      (B : ℚ) ^ r * ((n : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r =
        (((n * B : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r := by
    rw [← mul_pow]
    congr 1
    push_cast
    ring
  have htuplebound' : (tuples.card : ℚ) ≤
      (v : ℚ) * ((((n * B : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r) := by
    calc
      (tuples.card : ℚ) ≤ (v : ℚ) * (B : ℚ) ^ r *
          dimensionSensitiveIncidenceProduct n L k 1 r := by
        simpa only [tuples, τ, B] using htuplebound
      _ = (v : ℚ) * ((B : ℚ) ^ r *
          dimensionSensitiveIncidenceProduct n L k 1 r) := by ring
      _ ≤ (v : ℚ) * ((B : ℚ) ^ r *
          ((n : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hproduct' (by positivity)) (by positivity)
      _ = (v : ℚ) *
          ((((n * B : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r) := by rw [hratioPow]
  have hexcbound : (exceptional.card : ℚ) ≤
      ((ℓ * (n - L) : ℕ) : ℚ) *
        ((v : ℚ) * ((((n * B : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r)) := by
    have he : (exceptional.card : ℚ) ≤
        (tuples.card : ℚ) * ((ℓ * (n - L) : ℕ) : ℚ) := by
      have he' : exceptional.card ≤ tuples.card * (ℓ * (n - L)) := by
        simpa only [Fintype.card_fin] using hexc
      exact_mod_cast he'
    calc
      (exceptional.card : ℚ) ≤
          (tuples.card : ℚ) * ((ℓ * (n - L) : ℕ) : ℚ) := he
      _ ≤ ((v : ℚ) * ((((n * B : ℕ) : ℚ) /
          ((L - k + 1 : ℕ) : ℚ)) ^ r)) * ((ℓ * (n - L) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_right htuplebound' (by positivity)
      _ = ((ℓ * (n - L) : ℕ) : ℚ) *
          ((v : ℚ) * ((((n * B : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r)) := by ring
  have hcover : challenges.card ≤ remaining.card + exceptional.card := by
    have he := Finset.card_sdiff_add_card_inter challenges exceptional
    have hi := Finset.card_le_card (Finset.inter_subset_right :
      challenges ∩ exceptional ⊆ exceptional)
    dsimp only [remaining]
    omega
  have hcoverQ : (challenges.card : ℚ) ≤
      (remaining.card : ℚ) + (exceptional.card : ℚ) := by
    exact_mod_cast hcover
  rw [show B = 1 + 2 * K * (v - 1) by rfl] at hexcbound
  exact hcoverQ.trans (add_le_add hoffbound hexcbound)

end ReedSolomon
