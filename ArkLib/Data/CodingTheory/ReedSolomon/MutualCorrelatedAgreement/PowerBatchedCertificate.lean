/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveCertificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedSharpRegularAgreement
public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients

/-!
# Power-batched agreement from symbolic curve certificates

A symbolic curve certificate yields one exceptional challenge set outside which every sufficiently
agreeing low-degree polynomial has exact power-batched agreement. Its bound adds the certificate
height to the sharp contribution of each regular separant stage.

## Main statements

* `Certificate.exists_exceptional_powerBatchedAgreement_sharp_of_exponent`: a sharp exceptional-set
  bound from a symbolic curve certificate at any sufficient Taylor exponent.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential ReedSolomon

noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

universe u

variable {F E : Type u} [Field F] [Field E]
  {n A k ℓ ν d h : ℕ} {domain : Fin n ↪ F}

private theorem eval₂_powerBatchedCoordinate_eq_powerBatchedWord
    (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E) (z : E) (i : Fin n) :
    (powerBatchedCoordinate fun t ↦ values t i).eval₂ iota z =
      powerBatchedWord (fun t j ↦ iota (values t j)) z i := by
  rw [Polynomial.eval₂_eq_eval_map]
  have hmap : (powerBatchedCoordinate fun t ↦ values t i).map iota =
      powerBatchedCoordinate fun t ↦ iota (values t i) := by
    simp [powerBatchedCoordinate, Polynomial.map_sum]
  rw [hmap, powerBatchedCoordinate_eval]
  rfl

open Classical in
private theorem Certificate.exists_exceptional_powerBatchedAgreement_of_stage_bounds
    {values : Fin (ℓ + 1) → Fin n → F}
    (cert : Certificate.{0, u} A k ℓ ν d h domain
      (fun i : Fin n ↦
        powerBatchedCoordinate (fun t : Fin (ℓ + 1) ↦ values t i)))
    (iota : F →+* E) {stages : List (SeparantStage F[X] d)}
    {terminal : DifferentialPolynomial F[X] d}
    (hc : SeparantChain cert.Q stages terminal)
    (stageBound : SeparantStage F[X] d → ℚ)
    (hstage : ∀ stage : SeparantStage F[X] d, ∃ exceptional : Finset E,
      stage ∈ stages →
        (exceptional.card : ℚ) ≤ stageBound stage ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
          differentialSpecialization (map (Polynomial.eval₂RingHom iota z) stage.1) P = 0 →
          differentialSpecialization
            (separant (map (Polynomial.eval₂RingHom iota z) stage.1) stage.2) P ≠ 0 →
          HasExactPowerAgreement domain values iota k z P) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ (h : ℚ) +
        ∑ stage ∈ stages.toFinset, stageBound stage ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  obtain ⟨base, hbase, hcover⟩ := cert.exists_exceptional_stage_coverage hc iota
  choose ex hex using hstage
  refine ⟨base ∪ stages.toFinset.biUnion ex, ?_, ?_⟩
  · calc
      ((base ∪ stages.toFinset.biUnion ex).card : ℚ) ≤
          (base.card : ℚ) + ((stages.toFinset.biUnion ex).card : ℚ) := by
        exact_mod_cast Finset.card_union_le base (stages.toFinset.biUnion ex)
      _ ≤ (h : ℚ) +
          ∑ stage ∈ stages.toFinset, ((ex stage).card : ℚ) := by
        apply add_le_add
        · exact_mod_cast hbase
        · exact_mod_cast Finset.card_biUnion_le
      _ ≤ _ := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro stage hs
        exact (hex stage (List.mem_toFinset.mp hs)).1
  · intro z hz P hp ha
    have hzbase : z ∉ base := fun hm ↦ hz (Finset.mem_union_left _ hm)
    obtain ⟨stage, hs, hsol, hsep⟩ := hcover z hzbase
      (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (powerBatchedWord (fun t i ↦ iota (values t i)) z) P) P hp ha (by
          intro i hi
          simpa [eval₂_powerBatchedCoordinate_eq_powerBatchedWord] using hi)
    apply (hex stage hs).2 z (fun hm ↦ hz (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨stage, List.mem_toFinset.mpr hs, hm⟩))) P hp ha hsol hsep

open Classical in
/-- A symbolic curve certificate gives a sharp exceptional-set bound for exact power-batched
agreement, with each regular stage charged at its actual jet degree. -/
theorem Certificate.exists_exceptional_powerBatchedAgreement_sharp_of_exponent
    [IsAlgClosed E]
    {values : Fin (ℓ + 1) → Fin n → F}
    (cert : Certificate.{0, u} A k ℓ ν d h domain
      (fun i : Fin n ↦
        powerBatchedCoordinate (fun t : Fin (ℓ + 1) ↦ values t i)))
    (iota : F →+* E) (K L τ : ℕ)
    (hτ : ∀ r ≤ d, TaylorExponentSufficient r K τ) (hτpos : 0 < τ)
    (hK : d < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    (hchar : ringChar F = 0 ∨ ν < ringChar F)
    (hbin : ∀ r ≤ d, ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    ∃ stages terminal, SeparantChain cert.Q stages terminal ∧
      ∃ exceptional : Finset E,
        (exceptional.card : ℚ) ≤ (h : ℚ) +
          ∑ stage ∈ stages.toFinset,
            regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k L A
              (jetTotalDegree stage.1) h (τ := τ) ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
          HasExactPowerAgreement domain values iota k z P := by
  classical
  obtain ⟨stages, terminal, hc⟩ := cert.exists_separantChain hchar
  have hstage : ∀ stage : SeparantStage F[X] d, ∃ exceptional : Finset E,
      stage ∈ stages →
        (exceptional.card : ℚ) ≤
          regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k L A
            (jetTotalDegree stage.1) h (τ := τ) ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
          differentialSpecialization (map (Polynomial.eval₂RingHom iota z) stage.1) P = 0 →
          differentialSpecialization
            (separant (map (Polynomial.eval₂RingHom iota z) stage.1) stage.2) P ≠ 0 →
          HasExactPowerAgreement domain values iota k z P := by
    intro stage
    by_cases hs : stage ∈ stages
    · obtain ⟨pres, _, hpresweight, _⟩ :=
        hc.exists_jetPrefixPresentation_of_mem hs
      let Qe : DifferentialPolynomial E[X] stage.2.val :=
        MvPolynomial.map (Polynomial.mapRingHom iota) pres.equation
      have hρinj : Function.Injective (Polynomial.mapRingHom iota) :=
        Polynomial.map_injective iota iota.injective
      have hdegree : CoeffNatDegreeLE pres.equation h := by
        intro u
        exact pres.natDegree_coeff_equation_le
          (hc.natDegree_coeff_le_of_mem cert.challengeDegree_le hs) u
      have hheight : CoeffNatDegreeLE Qe h := by
        dsimp [Qe]
        exact MvPolynomial.CoeffNatDegreeLE.map_coefficients iota pres.equation hdegree
      have hjet : jetTotalDegree Qe ≤ jetTotalDegree stage.1 := by
        dsimp [Qe]
        rw [jetTotalDegree_map_eq hρinj, hpresweight]
      have hactive :=
        (isHighestActiveJet_of_highestActiveJet_eq_some (hc.highestActiveJet_eq_of_mem hs)).1
      have hstageweight : 0 < jetTotalDegree stage.1 :=
        hactive.trans_le (jetDegree_le_total stage.1 stage.2)
      have hrle : stage.2.val ≤ d := by omega
      have hKstage : stage.2.val < K := hrle.trans_lt hK
      have hbins : ∀ i, stage.2.val < i → i < K →
          (i.choose stage.2.val : E) ≠ 0 := by
        intro i hi hiK hzero
        apply hbin stage.2.val hrle i hi hiK
        apply iota.injective
        simpa only [map_natCast, map_zero] using hzero
      have hDstage : 0 < ℓ + h := by omega
      obtain ⟨ex, hb, he⟩ := exists_exceptional_regularPowerBatchedAgreement_sharp_of_exponent
        domain values iota Qe K k L A (jetTotalDegree stage.1) h τ
        (hτ stage.2.val hrle) hτpos hKstage hkK hkL hLA hAn hDstage hstageweight hjet hheight
        hbins
      refine ⟨ex, fun _ ↦ ⟨hb, ?_⟩⟩
      intro z hz P hp ha hsol hsep
      let ρ : F[X] →+* E := Polynomial.eval₂RingHom iota z
      have hspecialize (Q : DifferentialPolynomial F[X] stage.2.val) :
          MvPolynomial.map ρ Q =
            challengeSpecialization (MvPolynomial.map (Polynomial.mapRingHom iota) Q) z := by
        unfold challengeSpecialization
        have hcomp : (Polynomial.aeval z).toRingHom.comp (Polynomial.mapRingHom iota) = ρ := by
          apply Polynomial.ringHom_ext
          · intro a
            simp [ρ]
          · simp [ρ]
        rw [MvPolynomial.map_map, hcomp]
      have hsol' : differentialSpecialization (challengeSpecialization Qe z) P = 0 := by
        rw [← hspecialize pres.equation]
        exact (pres.map ρ).differentialSpecialization_equation P ▸ hsol
      have hsep' : differentialSpecialization
          (separant (challengeSpecialization Qe z) (Fin.last stage.2.val)) P ≠ 0 := by
        rw [← hspecialize pres.equation]
        exact (pres.map ρ).differentialSpecialization_separant_equation P ▸ hsep
      exact he z hz P hp ha hsol' hsep'
    · exact ⟨∅, fun hmem ↦ (hs hmem).elim⟩
  refine ⟨stages, terminal, hc, ?_⟩
  exact cert.exists_exceptional_powerBatchedAgreement_of_stage_bounds iota hc
    (fun stage ↦ regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k L A
      (jetTotalDegree stage.1) h (τ := τ)) hstage

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
