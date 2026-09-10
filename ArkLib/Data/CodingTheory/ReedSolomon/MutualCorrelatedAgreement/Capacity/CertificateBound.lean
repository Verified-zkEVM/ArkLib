/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.Certificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.ProductCounting
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
/-!
# Exact curve agreement from a finite interpolation certificate

The certificate determines a single symbolic equation before the challenge or candidate.
Its actual separant stages give one finite exceptional set with full agreement-set
equality. Only after this construction do the incidence products and stage degrees
receive the scalar bound `ℓ * CE * n^(d+1)`.

The jet cap `ν` and per-unit-curve height `h` are independent inputs. In particular,
a variable interpolation margin can supply `h` without changing the geometric proof.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial PolynomialDifferential HiddenDerivative SymbolicReceivedInterpolation
open SymbolicSeparantChain
open scoped BigOperators

universe u

/-- A certified equation gives exact powers-batched agreement with the rate theorem's
scalar constant, including characteristic equal to the block length. -/
theorem exists_curveMCA_of_certificate {F E : Type u} [Field F] [Field E]
    [DecidableEq E] [IsAlgClosed E] {n k A K ℓ ν d height h : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (embedding : F →+* E)
    (certificate : SymbolicReceivedCurve.Certificate.{u, u} F A k ℓ ν d height domain
      (fun index ↦ powerBatchedCoordinate fun term ↦ values term index))
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hn : 0 < n) (hk : 0 < k)
    (hd : 0 < d) (hν : 0 < ν) (hh : 0 < h) (hℓ : 0 < ℓ)
    (hdK : d < K) (hkK : k ≤ K) (hKn : K ≤ n) (hνn : ν < n)
    (hkA : k ≤ A) (hAn : A ≤ n) (hgap : (k : ℝ) + δ * n ≤ A)
    (hheight : height ≤ ℓ * h) (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant δ ν h d *
        (n : ℝ) ^ (d + 1) ∧
      ∀ challenge ∉ exceptional, ∀ polynomial : E[X], polynomial.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain embedding)
          (powerBatchedWord (fun term index ↦ embedding (values term index)) challenge)
            polynomial).card →
        HasExactPowerAgreement domain values embedding k challenge polynomial := by
  classical
  let cutoff := correlatedProductCutoff d k A
  obtain ⟨stages, terminal, hchain, exceptional, hcard, hexact⟩ :=
    certificate.exists_exceptional_symbolicCurveMCA_sharp embedding K cutoff (2 * K - 3)
      (fun order _ ↦ taylorExponentSufficient_two_mul_sub_three order (by omega))
      (by omega) hdK hkK hk
      (correlatedProductCutoff_bounds d k A hkA).1
      (correlatedProductCutoff_bounds d k A hkA).2 hAn hℓ
      (hchar.imp_right (fun h ↦ hνn.trans_le h)) (by
        intro order _ index horder hindex
        exact binomial_pivots_of_characteristic
          (hchar.imp_right (fun h ↦ hKn.trans h)) order index horder hindex)
  refine ⟨exceptional, ?_, hexact⟩
  have hstages : stages.toFinset.card ≤ ν :=
    (List.toFinset_card_le stages).trans (hchain.length_le.trans certificate.jetWeight_le)
  have hweights : ∀ stage ∈ stages, 0 < jetWeight stage.1 ∧ jetWeight stage.1 ≤ ν := by
    intro stage hstage
    refine ⟨?_, (hchain.stage_contract stage hstage).2.2.1.trans certificate.jetWeight_le⟩
    exact (isHighestActiveJet_of_highestActiveJet_eq_some
      (hchain.stage_contract stage hstage).2.1).1.trans_le
      (jetDegree_le_jetWeight stage.1 stage.2)
  have hcardReal : (exceptional.card : ℝ) ≤ (height : ℝ) +
      ∑ stage ∈ stages.toFinset,
        (regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k cutoff A
          (jetWeight stage.1) height (τ := 2 * K - 3) : ℝ) := by
    exact_mod_cast hcard
  apply hcardReal.trans
  calc
    (height : ℝ) + ∑ stage ∈ stages.toFinset,
        (regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k cutoff A
          (jetWeight stage.1) height (τ := 2 * K - 3) : ℝ) ≤
      ((ℓ * h : ℕ) : ℝ) + ∑ stage ∈ stages.toFinset,
        (regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k cutoff A
          (jetWeight stage.1) height (τ := 2 * K - 3) : ℝ) := by
            exact add_le_add (Nat.cast_le.mpr hheight) le_rfl
    _ ≤ _ := regularSymbolicCurveMCASharp_product_finiteStage_le stages.toFinset
      (fun stage ↦ stage.2.val) (fun stage ↦ jetWeight stage.1) (fun _ ↦ height)
      δ n K k A ℓ ν h d (2 * K - 3) hδ hδone hd hn hk hν hh hKn hgap hAn
      (Nat.sub_le _ _) hstages (fun stage _ ↦ Fin.is_le stage.2)
      (fun stage hstage ↦ (hweights stage (List.mem_toFinset.mp hstage)).1)
      (fun stage hstage ↦ (hweights stage (List.mem_toFinset.mp hstage)).2)
      (fun _ _ ↦ hheight)

/-- A symbolic curve certificate gives the explicit scalar exceptional bound at any
positive agreement gap. The independent parameters are supplied by finite support estimates. -/
theorem exists_curveMCA_of_certificate_of_jetCharacteristic {F E : Type u} [Field F] [Field E]
    [DecidableEq E] [IsAlgClosed E]
    {n k A K d ν H h ℓ : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (cert : SymbolicReceivedCurve.Certificate.{u, u} F A k ℓ ν d H domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i))
    (hk : 0 < k) (hkK : k ≤ K) (hd : 0 < d) (hdK : d < K) (hKn : K ≤ n)
    (hkA : k ≤ A) (hAn : A ≤ n) (hν : 0 < ν) (hh : 0 < h)
    (hℓ : 0 < ℓ) (hH : H ≤ ℓ * h) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (K - 1) ν < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant δ ν h d *
        (n : ℝ) ^ (d + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  have hn : 0 < n := hk.trans_le (hkK.trans hKn)
  have hK : 0 < K := hk.trans_le hkK
  have hcharJet : ringChar F = 0 ∨ ν < ringChar F :=
    hchar.imp_right (fun hc ↦ (Nat.le_max_right _ _).trans_lt hc)
  have hcharK : ringChar F = 0 ∨ K ≤ ringChar F := by
    apply hchar.imp_right
    intro hc
    have := (Nat.le_max_left (K - 1) ν).trans_lt hc
    omega
  let L := correlatedProductCutoff d k A
  obtain ⟨stages, terminal, hc, exceptional, hcard, hexact⟩ :=
    cert.exists_exceptional_symbolicCurveMCA_sharp iota K L (2 * K)
      (fun r _ ↦ taylorExponentSufficient_two_mul r K) (by omega) hdK hkK hk
      (correlatedProductCutoff_bounds d k A hkA).1
      (correlatedProductCutoff_bounds d k A hkA).2 hAn hℓ hcharJet
      (fun r _ i hri hi ↦ binomial_pivots_of_characteristic hcharK r i hri hi)
  refine ⟨exceptional, ?_, hexact⟩
  have hcardR : (exceptional.card : ℝ) ≤ (H : ℝ) +
      ∑ stage ∈ stages.toFinset,
        (regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k L A
          (jetWeight stage.1) H (τ := 2 * K) : ℝ) := by exact_mod_cast hcard
  apply hcardR.trans
  apply le_trans (add_le_add (Nat.cast_le.mpr hH) le_rfl)
  apply regularSymbolicCurveMCASharp_product_finiteStage_le stages.toFinset
    (fun stage ↦ stage.2.val) (fun stage ↦ jetWeight stage.1) (fun _ ↦ H)
    δ n K k A ℓ ν h d (2 * K) hδ hδone hd hn hk hν hh hKn hgap hAn le_rfl
  · exact (List.toFinset_card_le stages).trans (hc.length_le.trans cert.jetWeight_le)
  · intro stage _
    exact Fin.is_le stage.2
  · intro stage hs
    have hactive := (isHighestActiveJet_of_highestActiveJet_eq_some
      (hc.stage_contract stage (List.mem_toFinset.mp hs)).2.1).1
    exact hactive.trans_le (jetDegree_le_jetWeight stage.1 stage.2)
  · intro stage hs
    exact (hc.stage_contract stage (List.mem_toFinset.mp hs)).2.2.1.trans cert.jetWeight_le
  · exact fun _ _ ↦ hH

end ReedSolomon
