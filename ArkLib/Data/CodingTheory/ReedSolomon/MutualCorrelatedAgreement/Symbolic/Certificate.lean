/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.SeparantStages
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Symbolic.RegularEquation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.CoefficientExtension
/-!
# Symbolic certificate mutual correlated agreement

Actual separant stages of the interpolation certificate give one exceptional set for all
close polynomial witnesses. The budget retains each stage's actual differential order.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

open Polynomial MvPolynomial SymbolicSeparantChain SymbolicJetPrefix ReedSolomon

universe u

variable {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
  [IsAlgClosed E] {n A k ν d h : ℕ} {domain : Fin n ↪ F} {f g : Fin n → F}

/-- A certificate supplies its own regular stages and a single exception set, with an
explicit sum over actual stage orders and exact full agreement with a base-field pair. -/
theorem Certificate.exists_exceptional_symbolicLineMCA
    (cert : Certificate.{u, u} F A k ν d h domain f g) (iota : F →+* E)
    (K L : ℕ) (hK : d < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hν : 0 < ν)
    (hchar : ringChar F = 0 ∨ ν < ringChar F)
    (hbin : ∀ r ≤ d, ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    ∃ stages terminal, Chain cert.Q stages terminal ∧
      ∃ exceptional : Finset E,
        (exceptional.card : ℚ) ≤ ((h : ℕ) : ℚ) +
          ∑ stage ∈ stages.toFinset,
            regularSymbolicMCABound n stage.2.val K k L A ν (h) ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (mappedDomain domain iota)
            (fun i ↦ iota (f i) + z * iota (g i)) P).card →
          HasExactCorrelatedPair domain f g iota k z P := by
  classical
  obtain ⟨stages, terminal, hc⟩ := cert.exists_separant_chain hchar
  obtain ⟨base, hbase, hcover⟩ := cert.exists_exceptional_stage_coverage hc iota
  have hstage : ∀ stage : Stage F[X] d, ∃ exceptional : Finset E,
      stage ∈ stages →
        (exceptional.card : ℚ) ≤
          regularSymbolicMCABound n stage.2.val K k L A ν (h) ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (mappedDomain domain iota)
            (fun i ↦ iota (f i) + z * iota (g i)) P).card →
          differentialSpecialization (map (Polynomial.eval₂RingHom iota z) stage.1) P = 0 →
          differentialSpecialization
            (separant (map (Polynomial.eval₂RingHom iota z) stage.1) stage.2) P ≠ 0 →
          HasExactCorrelatedPair domain f g iota k z P := by
    intro stage
    by_cases hs : stage ∈ stages
    · obtain ⟨pres, _, hw, _, hh⟩ := exists_stage_presentation hc
        cert.challengeHeight_le stage hs
      have hweight : jetWeight (extendSymbolicCoefficients iota pres.equation) ≤ ν :=
        (jetWeight_extendSymbolicCoefficients_le iota pres.equation).trans
          (hw.le.trans ((hc.stage_contract stage hs).2.2.1.trans cert.jetWeight_le))
      have hbins : ∀ i, stage.2.val < i → i < K → (i.choose stage.2.val : E) ≠ 0 := by
        intro i hi hiK hzero
        apply hbin stage.2.val (Fin.is_le stage.2) i hi hiK
        apply iota.injective
        simpa only [map_natCast, map_zero] using hzero
      obtain ⟨ex, hb, he⟩ := exists_exceptional_regularSymbolicLineMCA domain f g iota
        (extendSymbolicCoefficients iota pres.equation) K k L A ν (h)
        ((Fin.is_le stage.2).trans_lt hK) hkK hk hkL hLA hAn hν hweight
        (challengeHeightLE_extendSymbolicCoefficients iota pres.equation hh) hbins
      refine ⟨ex, fun _ ↦ ⟨hb, ?_⟩⟩
      intro z hz P hp ha hsol hsep
      apply he z hz P hp ha
      · change differentialSpecialization
          (map (Polynomial.evalRingHom z) (extendSymbolicCoefficients iota pres.equation))
            P = 0
        rw [specialize_extendSymbolicCoefficients, pres.specialization]
        exact hsol
      · change differentialSpecialization
          (separant (map (Polynomial.evalRingHom z)
            (extendSymbolicCoefficients iota pres.equation)) (Fin.last stage.2.val)) P ≠ 0
        rw [specialize_extendSymbolicCoefficients, pres.separant_specialization]
        exact hsep
    · exact ⟨∅, fun h ↦ (hs h).elim⟩
  choose ex hex using hstage
  refine ⟨stages, terminal, hc, base ∪ stages.toFinset.biUnion ex, ?_, ?_⟩
  · calc
      ((base ∪ stages.toFinset.biUnion ex).card : ℚ) ≤
          (base.card : ℚ) + ((stages.toFinset.biUnion ex).card : ℚ) := by
        exact_mod_cast Finset.card_union_le base (stages.toFinset.biUnion ex)
      _ ≤ ((h : ℕ) : ℚ) +
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
      (polynomialAgreementSet (mappedDomain domain iota)
        (fun i ↦ iota (f i) + z * iota (g i)) P) P hp ha (by
          intro i hi
          simpa [polynomialAgreementSet, mappedDomain] using hi)
    apply (hex stage hs).2 z (fun hm ↦ hz (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨stage, List.mem_toFinset.mpr hs, hm⟩))) P hp ha hsol hsep

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
