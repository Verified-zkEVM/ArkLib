/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.ProductCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveCertificate
import ArkLib.Data.Polynomial.Differential.WitnessCount
/-!
# Scalar agreement bounds from symbolic curve certificates

The certificate endpoints combine a symbolic equation, its regular separant stages, and
product-based incidence estimates. They bound the exceptional challenges for exact agreement
with a coefficient linear in the batching length and polynomial in the block length.

## Main statements

* `exists_curveMCA_of_certificate`: a characteristic-at-least-block-length certificate bound.
* `exists_curveMCA_of_certificate_of_jetCharacteristic`: a bound under a jet characteristic cap.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial PolynomialDifferential HiddenDerivative
open scoped BigOperators

universe u

open Classical in
/-- A symbolic curve certificate bounds the exceptional challenges for exact power agreement. -/
theorem exists_curveMCA_of_certificate {F E : Type u} [Field F] [Field E]
    [IsAlgClosed E] {n k A K ℓ ν d height h : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (embedding : F →+* E)
    (certificate : SymbolicReceivedCurve.Certificate.{0, u} A k ℓ ν d height domain
      (fun index ↦ powerBatchedCoordinate fun term ↦ values term index))
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hn : 0 < n) (hk : 0 < k)
    (hd : 0 < d) (hν : 0 < ν) (hh : 0 < h) (hℓ : 0 < ℓ)
    (hdK : d < K) (hkK : k ≤ K) (hKn : K ≤ n) (hνn : ν < n)
    (hkA : k ≤ A) (hAn : A ≤ n) (hgap : (k : ℝ) + δ * n ≤ A)
    (hheight : height ≤ ℓ * h) (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductAgreementConstant δ ν h d *
        (n : ℝ) ^ (d + 1) ∧
      ∀ challenge ∉ exceptional, ∀ polynomial : E[X], polynomial.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨embedding, embedding.injective⟩)
          (powerBatchedWord (fun term index ↦ embedding (values term index)) challenge)
            polynomial).card →
        HasExactPowerAgreement domain values embedding k challenge polynomial := by
  classical
  let cutoff := correlatedProductCutoff d k A
  obtain ⟨stages, terminal, hchain, exceptional, hcard, hexact⟩ :=
    certificate.exists_exceptional_powerBatchedAgreement_sharp_of_exponent
      embedding K cutoff (2 * K - 3)
      (fun order _ ↦ taylorExponentSufficient_two_mul_sub_three order K)
      (by omega) hdK hkK
      (correlatedProductCutoff_bounds d k A hkA).1
      (correlatedProductCutoff_bounds d k A hkA).2 hAn hℓ
      (hchar.imp_right (fun h ↦ hνn.trans_le h)) (by
        intro order _ index horder hindex
        have hcutChar : ringChar F = 0 ∨ K - 1 < ringChar F :=
          hchar.imp_right (fun h ↦ by omega)
        have hchoose := PolynomialDifferential.natCast_choose_ne_zero_of_ringChar
          (F := F) (D := K - 1) (s := order) hcutChar (index - order) (by omega) (by omega)
        simpa only [Nat.sub_add_cancel horder.le] using hchoose)
  refine ⟨exceptional, ?_, hexact⟩
  have hstages : stages.toFinset.card ≤ ν :=
    (List.toFinset_card_le stages).trans (hchain.length_le.trans certificate.jetTotalDegree_le)
  have hweights : ∀ stage ∈ stages,
      0 < jetTotalDegree stage.1 ∧ jetTotalDegree stage.1 ≤ ν := by
    intro stage hstage
    refine ⟨?_, (hchain.jetTotalDegree_le_of_mem hstage).trans certificate.jetTotalDegree_le⟩
    exact (isHighestActiveJet_of_highestActiveJet_eq_some
      (hchain.highestActiveJet_eq_of_mem hstage)).1.trans_le
      (jetDegree_le_total stage.1 stage.2)
  have hcardReal : (exceptional.card : ℝ) ≤ (height : ℝ) +
      ∑ stage ∈ stages.toFinset,
        (regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k cutoff A
          (jetTotalDegree stage.1) height (τ := 2 * K - 3) : ℝ) := by
    exact_mod_cast hcard
  apply hcardReal.trans
  calc
    (height : ℝ) + ∑ stage ∈ stages.toFinset,
        (regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k cutoff A
          (jetTotalDegree stage.1) height (τ := 2 * K - 3) : ℝ) ≤
      ((ℓ * h : ℕ) : ℝ) + ∑ stage ∈ stages.toFinset,
        (regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k cutoff A
          (jetTotalDegree stage.1) height (τ := 2 * K - 3) : ℝ) := by
            exact add_le_add (Nat.cast_le.mpr hheight) le_rfl
    _ ≤ _ := regularPowerBatchedAgreementSharp_product_finiteStage_le stages.toFinset
      (fun stage ↦ stage.2.val) (fun stage ↦ jetTotalDegree stage.1) (fun _ ↦ height)
      δ n K k A ℓ ν h d (2 * K - 3) hδ hδone hd hn hk hν hh hKn hgap hAn
      (Nat.sub_le _ _) hstages (fun stage _ ↦ Fin.is_le stage.2)
      (fun stage hstage ↦ (hweights stage (List.mem_toFinset.mp hstage)).1)
      (fun stage hstage ↦ (hweights stage (List.mem_toFinset.mp hstage)).2)
      (fun _ _ ↦ hheight)

open Classical in
/-- A symbolic curve certificate gives the scalar exceptional-set bound under a jet cutoff. -/
theorem exists_curveMCA_of_certificate_of_jetCharacteristic {F E : Type u} [Field F] [Field E]
    [IsAlgClosed E]
    {n k A K d ν H h ℓ : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (cert : SymbolicReceivedCurve.Certificate.{0, u} A k ℓ ν d H domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i))
    (hk : 0 < k) (hkK : k ≤ K) (hd : 0 < d) (hdK : d < K) (hKn : K ≤ n)
    (hkA : k ≤ A) (hAn : A ≤ n) (hν : 0 < ν) (hh : 0 < h)
    (hℓ : 0 < ℓ) (hH : H ≤ ℓ * h) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (K - 1) ν < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductAgreementConstant δ ν h d *
        (n : ℝ) ^ (d + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  have hn : 0 < n := hk.trans_le (hkK.trans hKn)
  have hK : 0 < K := hk.trans_le hkK
  have hcharJet : ringChar F = 0 ∨ ν < ringChar F :=
    hchar.imp_right (fun hc ↦ (Nat.le_max_right _ _).trans_lt hc)
  have hcharK : ringChar F = 0 ∨ K - 1 < ringChar F := by
    apply hchar.imp_right
    intro hc
    exact (Nat.le_max_left (K - 1) ν).trans_lt hc
  let L := correlatedProductCutoff d k A
  obtain ⟨stages, terminal, hc, exceptional, hcard, hexact⟩ :=
    cert.exists_exceptional_powerBatchedAgreement_sharp_of_exponent iota K L (2 * K)
      (fun r _ ↦ taylorExponentSufficient_two_mul r K) (by omega) hdK hkK
      (correlatedProductCutoff_bounds d k A hkA).1
      (correlatedProductCutoff_bounds d k A hkA).2 hAn hℓ hcharJet
      (by
        intro r _ i hri hi
        have hchoose := PolynomialDifferential.natCast_choose_ne_zero_of_ringChar
          (F := F) (D := K - 1) (s := r) hcharK (i - r) (by omega) (by omega)
        simpa only [Nat.sub_add_cancel hri.le] using hchoose)
  refine ⟨exceptional, ?_, hexact⟩
  have hcardR : (exceptional.card : ℝ) ≤ (H : ℝ) +
      ∑ stage ∈ stages.toFinset,
        (regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k L A
          (jetTotalDegree stage.1) H (τ := 2 * K) : ℝ) := by exact_mod_cast hcard
  apply hcardR.trans
  apply le_trans (add_le_add (Nat.cast_le.mpr hH) le_rfl)
  apply regularPowerBatchedAgreementSharp_product_finiteStage_le stages.toFinset
    (fun stage ↦ stage.2.val) (fun stage ↦ jetTotalDegree stage.1) (fun _ ↦ H)
    δ n K k A ℓ ν h d (2 * K) hδ hδone hd hn hk hν hh hKn hgap hAn le_rfl
  · exact (List.toFinset_card_le stages).trans (hc.length_le.trans cert.jetTotalDegree_le)
  · intro stage _
    exact Fin.is_le stage.2
  · intro stage hs
    have hactive := (isHighestActiveJet_of_highestActiveJet_eq_some
      (hc.highestActiveJet_eq_of_mem (List.mem_toFinset.mp hs))).1
    exact hactive.trans_le (jetDegree_le_total stage.1 stage.2)
  · intro stage hs
    exact (hc.jetTotalDegree_le_of_mem (List.mem_toFinset.mp hs)).trans cert.jetTotalDegree_le
  · exact fun _ _ ↦ hH

end ReedSolomon
