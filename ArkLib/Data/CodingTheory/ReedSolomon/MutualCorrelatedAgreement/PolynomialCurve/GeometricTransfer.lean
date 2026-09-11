/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExceptionalSet
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExtensionDescent
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.ProductBounds
/-!
# Geometric transfer on polynomial received curves

This module isolates the common, non-decoder transfer from geometric incidence certificates to
exact mutual correlated agreement.  A geometric application supplies, for every stage or
component, the actual off-persistent challenge set and the actual retained polynomial graphs.
The joint-incidence and reduced generic-fiber arguments are represented by separate cardinality
certificates for these two finite families.

The retained graphs are tuples of polynomials over the original field.  Thus the conclusion gives
base-field constituent messages even though the geometry and the challenge live over an
algebraically closed extension.  The accidental-agreement set is constructed only after the
retained family is fixed, and one exceptional set then works for every candidate polynomial.

The incidence product is

```text
P_r(T) = prod_{j < r} (n - k + j + 1) / (T - k + j + 1).
```

In particular `P_0(T) = 1`.  No characteristic assumption involving the curve degree `ell` is
used.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], geometric-transfer lemma.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial AffineHilbert
open scoped BigOperators

variable {F E ν : Type*} [Field F] [Field E]
  [Fintype ν] [DecidableEq E]
  {n k ℓ L A : ℕ}

/-- The dimension-sensitive evaluation product appearing in geometric transfer. -/
def geometricTransferIncidenceProduct (n T k r : ℕ) : ℚ :=
  dimensionSensitiveIncidenceProduct n T k 1 r

@[simp]
theorem geometricTransferIncidenceProduct_zero (n T k : ℕ) :
    geometricTransferIncidenceProduct n T k 0 = 1 := by
  simp [geometricTransferIncidenceProduct]

/-- The exact three-part geometric-transfer budget: preliminary exceptions, joint off-graph
incidence, and accidental agreements on graphs counted in the reduced generic fiber. -/
def geometricTransferBound (preliminaryCard n k ℓ L A : ℕ)
    (r J fiberDegree : ν → ℕ) : ℚ :=
  preliminaryCard +
    (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
      ∑ s, geometricTransferIncidenceProduct n A k (r s) * J s +
    ((ℓ * (n - L) : ℕ) : ℚ) *
      ∑ s, geometricTransferIncidenceProduct n L k (r s) * fiberDegree s

/-- Common geometric transfer for a polynomial received curve.

`offGraph s` is the projection to the challenge line of the high-agreement points at stage `s`
which do not lie on a retained persistent graph.  `retained s` is the actual family of persistent
graphs at that stage, represented by their base-field polynomial tuples.  Consequently
`hcoverage` is substantive: every covered candidate is either charged to the joint-incidence set
or is equal to the specialization of one of those retained tuples.

`J s` and `fiberDegree s` are respectively the supplied joint degree and *reduced* generic-fiber
degree budgets.  The proof only consumes the resulting cardinality certificates, so algebraic-set
models that establish those certificates can remain specific to each application. -/
theorem exists_geometricTransfer_exceptional
    [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Candidate : E → E[X] → Prop)
    (preliminary : Finset E) (r J fiberDegree : ν → ℕ)
    (offGraph : ν → Finset E)
    (retained : ν → Finset (Fin (ℓ + 1) → F[X]))
    (_hk : 0 < k) (_hkL : k ≤ L) (_hLA : L ≤ A) (_hAn : A ≤ n) (_hℓ : 0 < ℓ)
    (hoffCard : ∀ s, ((offGraph s).card : ℚ) ≤
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        geometricTransferIncidenceProduct n A k (r s) * J s)
    (hretainedCard : ∀ s, ((retained s).card : ℚ) ≤
      geometricTransferIncidenceProduct n L k (r s) * fiberDegree s)
    (hdegree : ∀ s P, P ∈ retained s → ∀ t, (P t).degree < k)
    (hcommon : ∀ s P, P ∈ retained s →
      L ≤ (commonCurveAgreementSet domain w P).card)
    (hcoverage : ∀ z Q, Candidate z Q → Q.degree < k →
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) Q).card →
      z ∉ preliminary →
      (∃ s, z ∈ offGraph s) ∨
        ∃ s P, P ∈ retained s ∧
          Q = powerBatchedPolynomial (fun t ↦ (P t).map iota) z) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        geometricTransferBound preliminary.card n k ℓ L A r J fiberDegree ∧
      ∀ z ∉ exceptional, ∀ Q, Candidate z Q → Q.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
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
  · have hoffUnionNat : allOff.card ≤ ∑ s, (offGraph s).card := by
      exact Finset.card_biUnion_le
    have hoffUnion : (allOff.card : ℚ) ≤
        ∑ s, (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
          geometricTransferIncidenceProduct n A k (r s) * J s := by
      calc
        (allOff.card : ℚ) ≤ (∑ s, (offGraph s).card : ℕ) := by exact_mod_cast hoffUnionNat
        _ = ∑ s, ((offGraph s).card : ℚ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun s _ ↦ hoffCard s
    have hretainedUnionNat : allRetained.card ≤ ∑ s, (retained s).card := by
      exact Finset.card_biUnion_le
    have hretainedUnion : (allRetained.card : ℚ) ≤
        ∑ s, geometricTransferIncidenceProduct n L k (r s) * fiberDegree s := by
      calc
        (allRetained.card : ℚ) ≤ (∑ s, (retained s).card : ℕ) := by
          exact_mod_cast hretainedUnionNat
        _ = ∑ s, ((retained s).card : ℚ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun s _ ↦ hretainedCard s
    have haccidental : (accidental.card : ℚ) ≤
        ((ℓ * (n - L) : ℕ) : ℚ) *
          ∑ s, geometricTransferIncidenceProduct n L k (r s) * fiberDegree s := by
      have hfirst : (accidental.card : ℚ) ≤
          (allRetained.card : ℚ) * ((ℓ * (n - L) : ℕ) : ℚ) := by
        exact_mod_cast haccidentalCard
      calc
        (accidental.card : ℚ) ≤
            (allRetained.card : ℚ) * ((ℓ * (n - L) : ℕ) : ℚ) := hfirst
        _ ≤ (∑ s, geometricTransferIncidenceProduct n L k (r s) * fiberDegree s) *
            ((ℓ * (n - L) : ℕ) : ℚ) :=
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
          (∑ s, (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
            geometricTransferIncidenceProduct n A k (r s) * J s) +
          ((ℓ * (n - L) : ℕ) : ℚ) *
            ∑ s, geometricTransferIncidenceProduct n L k (r s) * fiberDegree s :=
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

/-- Base-field semantic form of an extension-field transfer conclusion.  Pulling the exceptional
set back along the field embedding does not increase its size, and exact equality of the full
agreement set descends together with the base-field polynomial witnesses. -/
theorem exists_geometricTransfer_baseField_semantic
    [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
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
    apply HasExactPowerAgreement.descend domain w iota k z Q
    apply hgood z (fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)) Q hCandidate

end ReedSolomon
