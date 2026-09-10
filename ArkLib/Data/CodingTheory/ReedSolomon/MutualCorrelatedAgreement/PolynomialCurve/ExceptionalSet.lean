/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.FullAgreement
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.PointRecognition
/-!
# Exceptional challenges for a finite polynomial-tuple family

Each retained tuple contributes at most `ℓ(n-L)` accidental challenges. Their union is
chosen before the challenge and before selecting any tuple from the family. Outside it,
all tuple specializations have exact correlated agreement, over every extension field.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial

variable {F E : Type*} [Field F] [Field E] [DecidableEq E] {n k ℓ L : ℕ}

/-- A degree-bounded tuple with `L` common positions has exact power agreement outside
at most `ℓ(n-L)` extension-field challenges. -/
theorem exists_exceptional_exactPowerAgreement (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (P : Fin (ℓ + 1) → F[X]) (ι : F →+* E)
    (hdegree : ∀ t, (P t).degree < k)
    (hcommon : L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset E, exceptional.card ≤ ℓ * (n - L) ∧
      ∀ z ∉ exceptional, HasExactPowerAgreement domain w ι k z
        (powerBatchedPolynomial (fun t ↦ (P t).map ι) z) := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_powerBatched_extension domain w P ι L hcommon
  refine ⟨exceptional, hcard, fun z hz ↦ ⟨P, hdegree, rfl, ?_⟩⟩
  ext i
  have hi := congrArg (fun s : Finset (Fin n) ↦ i ∈ s) (hgood z hz)
  simpa only [polynomialAgreementSet, Finset.mem_filter] using (iff_of_eq hi)

/-- One exceptional set works for the whole retained family, with the exact accidental
budget `family.card * ℓ * (n-L)`. No assumption on the size of the extension field is needed. -/
theorem exists_exceptional_exactPowerAgreement_family (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (family : Finset (Fin (ℓ + 1) → F[X]))
    (hdegree : ∀ P ∈ family, ∀ t, (P t).degree < k)
    (hcommon : ∀ P ∈ family, L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset E, exceptional.card ≤ family.card * (ℓ * (n - L)) ∧
      ∀ P ∈ family, ∀ z ∉ exceptional, HasExactPowerAgreement domain w ι k z
        (powerBatchedPolynomial (fun t ↦ (P t).map ι) z) := by
  classical
  have hex : ∀ P ∈ family, ∃ exceptional : Finset E,
      exceptional.card ≤ ℓ * (n - L) ∧
      ∀ z ∉ exceptional, HasExactPowerAgreement domain w ι k z
        (powerBatchedPolynomial (fun t ↦ (P t).map ι) z) :=
    fun P hP ↦ exists_exceptional_exactPowerAgreement domain w P ι
      (hdegree P hP) (hcommon P hP)
  choose ex hcard hgood using hex
  let exceptions (P : Fin (ℓ + 1) → F[X]) := if hP : P ∈ family then ex P hP else ∅
  refine ⟨family.biUnion exceptions, ?_, ?_⟩
  · calc
      (family.biUnion exceptions).card ≤ ∑ P ∈ family, (exceptions P).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _P ∈ family, ℓ * (n - L) := by
        apply Finset.sum_le_sum
        intro P hP
        simpa [exceptions, hP] using hcard P hP
      _ = family.card * (ℓ * (n - L)) := by simp
  · intro P hP z hz
    apply hgood P hP z
    intro hmem
    apply hz
    exact Finset.mem_biUnion.mpr ⟨P, hP, by simpa [exceptions, hP] using hmem⟩

end ReedSolomon
