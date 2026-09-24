/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition
public import ArkLib.ToMathlib.Combinatorics.Enumerative.IncidenceProduct
/-!
# Geometric transfer for power-batched agreement

Finite bounds for off-graph points and retained polynomial graphs combine into one exceptional
set outside which every covered candidate has exact power agreement. Extension-field bounds
descend to the base field by pulling the exceptional set back along the embedding.

## Main statements

* `geometricTransferBound`: the combined preliminary, incidence, and retained-graph budget.
* `exists_geometricTransfer_exceptional`: one exceptional set works for all covered candidates.
* `exists_geometricTransfer_baseField_semantic`: exact agreement descends with the same bound.

## References

* [DKTZ26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial
open scoped BigOperators

variable {F E α ν : Type*} [Field F] [Field E]
  [Fintype α] [Fintype ν]
  {k ℓ L A : ℕ}

/-- The exact three-part budget for preliminary exceptions, off-graph incidence, and retained
polynomial tuples counted through their extra agreement challenges. -/
def geometricTransferBound (preliminaryCard n k ℓ L A : ℕ)
    (r J fiberDegree : ν → ℕ) : ℚ :=
  preliminaryCard +
    (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
      ∑ s, dimensionSensitiveIncidenceProduct n A k 1 (r s) * J s +
    ((ℓ * (n - L) : ℕ) : ℚ) *
      ∑ s, dimensionSensitiveIncidenceProduct n L k 1 (r s) * fiberDegree s

open Classical in
/-- A joint-incidence bound on off-graph points and a reduced generic-fiber bound on retained
polynomial tuples give one exceptional set for all covered candidates. -/
theorem exists_geometricTransfer_exceptional
    (domain : α ↪ F) (w : Fin (ℓ + 1) → α → F) (iota : F →+* E)
    (Candidate : E → E[X] → Prop)
    (preliminary : Finset E) (r J fiberDegree : ν → ℕ)
    (offGraph : ν → Finset E)
    (retained : ν → Finset (Fin (ℓ + 1) → F[X]))
    (hoffCard : ∀ s, ((offGraph s).card : ℚ) ≤
      (((Fintype.card α - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        dimensionSensitiveIncidenceProduct (Fintype.card α) A k 1 (r s) * J s)
    (hretainedCard : ∀ s, ((retained s).card : ℚ) ≤
      dimensionSensitiveIncidenceProduct (Fintype.card α) L k 1 (r s) * fiberDegree s)
    (hdegree : ∀ s P, P ∈ retained s → ∀ t, (P t).degree < k)
    (hcommon : ∀ s P, P ∈ retained s →
      L ≤ (commonCurveAgreementSet domain w P).card)
    (hcoverage : ∀ z Q, Candidate z Q → Q.degree < k →
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) Q).card →
      z ∉ preliminary →
      (∃ s, z ∈ offGraph s) ∨
        ∃ s P, P ∈ retained s ∧
          Q = powerBatchedPolynomial (fun t ↦ (P t).map iota) z) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        geometricTransferBound preliminary.card (Fintype.card α) k ℓ L A r J fiberDegree ∧
      ∀ z ∉ exceptional, ∀ Q, Candidate z Q → Q.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) Q).card →
        HasExactPowerAgreement domain w iota k z Q := by
  classical
  let allOff := Finset.univ.biUnion offGraph
  let allRetained := Finset.univ.biUnion retained
  have hallDegree : ∀ P ∈ allRetained, ∀ t, (P t).degree < k := by
    intro P hP
    obtain ⟨s, _, hPs⟩ := Finset.mem_biUnion.mp hP
    exact hdegree s P hPs
  have hallCommon : ∀ P ∈ allRetained,
      L ≤ (commonCurveAgreementSet domain w P).card := by
    intro P hP
    obtain ⟨s, _, hPs⟩ := Finset.mem_biUnion.mp hP
    exact hcommon s P hPs
  obtain ⟨accidental, haccidentalCard, hexact⟩ :=
    exists_exceptional_exactPowerAgreement_family (k := k) (L := L)
      domain w iota allRetained hallDegree hallCommon
  refine ⟨preliminary ∪ allOff ∪ accidental, ?_, ?_⟩
  · have hoffUnionNat : allOff.card ≤ ∑ s, (offGraph s).card :=
      Finset.card_biUnion_le
    have hoffUnion : (allOff.card : ℚ) ≤
        ∑ s, (((Fintype.card α - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
          dimensionSensitiveIncidenceProduct (Fintype.card α) A k 1 (r s) * J s := by
      calc
        (allOff.card : ℚ) ≤ (∑ s, (offGraph s).card : ℕ) := by exact_mod_cast hoffUnionNat
        _ = ∑ s, ((offGraph s).card : ℚ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun s _ ↦ hoffCard s
    have hretainedUnionNat : allRetained.card ≤ ∑ s, (retained s).card :=
      Finset.card_biUnion_le
    have hretainedUnion : (allRetained.card : ℚ) ≤
        ∑ s, dimensionSensitiveIncidenceProduct (Fintype.card α) L k 1 (r s) *
          fiberDegree s := by
      calc
        (allRetained.card : ℚ) ≤ (∑ s, (retained s).card : ℕ) := by
          exact_mod_cast hretainedUnionNat
        _ = ∑ s, ((retained s).card : ℚ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun s _ ↦ hretainedCard s
    have haccidental : (accidental.card : ℚ) ≤
        ((ℓ * (Fintype.card α - L) : ℕ) : ℚ) *
          ∑ s, dimensionSensitiveIncidenceProduct (Fintype.card α) L k 1 (r s) *
            fiberDegree s := by
      have hfirst : (accidental.card : ℚ) ≤
          (allRetained.card : ℚ) * ((ℓ * (Fintype.card α - L) : ℕ) : ℚ) := by
        exact_mod_cast haccidentalCard
      calc
        (accidental.card : ℚ) ≤
            (allRetained.card : ℚ) * ((ℓ * (Fintype.card α - L) : ℕ) : ℚ) := hfirst
        _ ≤ (∑ s, dimensionSensitiveIncidenceProduct (Fintype.card α) L k 1 (r s) *
              fiberDegree s) * ((ℓ * (Fintype.card α - L) : ℕ) : ℚ) :=
          mul_le_mul_of_nonneg_right hretainedUnion (by positivity)
        _ = _ := by ring
    have hcardNat : (preliminary ∪ allOff ∪ accidental).card ≤
        preliminary.card + allOff.card + accidental.card := by
      calc
        (preliminary ∪ allOff ∪ accidental).card ≤
            (preliminary ∪ allOff).card + accidental.card :=
          Finset.card_union_le (preliminary ∪ allOff) accidental
        _ ≤ preliminary.card + allOff.card + accidental.card :=
          Nat.add_le_add_right (Finset.card_union_le preliminary allOff) accidental.card
    have hcard : ((preliminary ∪ allOff ∪ accidental).card : ℚ) ≤
        preliminary.card + (allOff.card : ℚ) + accidental.card := by
      exact_mod_cast hcardNat
    unfold geometricTransferBound
    calc
      ((preliminary ∪ allOff ∪ accidental).card : ℚ) ≤
          preliminary.card + (allOff.card : ℚ) + accidental.card := hcard
      _ ≤ preliminary.card +
          (∑ s, (((Fintype.card α - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
            dimensionSensitiveIncidenceProduct (Fintype.card α) A k 1 (r s) * J s) +
          ((ℓ * (Fintype.card α - L) : ℕ) : ℚ) *
            ∑ s, dimensionSensitiveIncidenceProduct (Fintype.card α) L k 1 (r s) *
              fiberDegree s :=
        add_le_add (add_le_add (le_refl (preliminary.card : ℚ)) hoffUnion) haccidental
      _ = _ := by simp only [Finset.mul_sum, mul_assoc]
  · intro z hz Q hCandidate hQ hA
    have hzPre : z ∉ preliminary := fun h ↦ hz (Finset.mem_union_left _
      (Finset.mem_union_left _ h))
    rcases hcoverage z Q hCandidate hQ hA hzPre with hoff | hgraph
    · obtain ⟨s, hzs⟩ := hoff
      exact False.elim (hz (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hzs⟩))))
    · obtain ⟨s, P, hPs, rfl⟩ := hgraph
      apply hexact P
      · exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hPs⟩
      · intro hza
        exact hz (Finset.mem_union_right _ hza)

/-- Pulling back an extension-field exceptional set preserves its bound and gives exact power
agreement over the base field. -/
theorem exists_geometricTransfer_baseField_semantic [DecidableEq F] [DecidableEq E]
    (domain : α ↪ F) (w : Fin (ℓ + 1) → α → F) (iota : F →+* E)
    (Candidate : F → F[X] → Prop) (exceptional : Finset E) (bound : ℚ)
    (hcard : (exceptional.card : ℚ) ≤ bound)
    (hgood : ∀ z, iota z ∉ exceptional → ∀ Q, Candidate z Q →
      HasExactPowerAgreement domain w iota k (iota z) (Q.map iota)) :
    ∃ baseExceptional : Finset F,
      (baseExceptional.card : ℚ) ≤ bound ∧
      ∀ z ∉ baseExceptional, ∀ Q, Candidate z Q →
        HasExactPowerAgreement domain w (RingHom.id F) k z Q := by
  classical
  let baseExceptional := exceptional.preimage iota iota.injective.injOn
  refine ⟨baseExceptional, ?_, ?_⟩
  · apply le_trans ?_ hcard
    exact_mod_cast Finset.card_le_card_of_injOn iota
      (fun _ hz ↦ Finset.mem_preimage.mp hz) iota.injective.injOn
  · intro z hz Q hCandidate
    exact HasExactPowerAgreement.descend
      (hgood z (fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)) Q hCandidate)

end ReedSolomon
