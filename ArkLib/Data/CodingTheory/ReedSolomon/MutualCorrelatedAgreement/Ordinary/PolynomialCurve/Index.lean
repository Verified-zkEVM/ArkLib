/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.ExceptionalSet
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FullAgreement
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Recovery
/-!
# Polynomial-curve MCA over arbitrary finite coordinate types

The exact polynomial-curve recovery theorems are naturally indexed by `Fin n`.  This file
transfers their semantic conclusion to the public Reed--Solomon code interface on an arbitrary
finite coordinate type.  A projected-code candidate is first extended to one global
degree-bounded polynomial; the requested subset is then embedded into its full agreement set.
Exact power recovery supplies constituent polynomials, whose evaluations are finally restricted
back to the original subset.

The exceptional set is fixed before the challenge, subset, and candidate.  The arbitrary-field
semantic adapter and finite-field probability corollary are deliberately separate.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial CoreDefinitions LinearCode
open scoped BigOperators ProbabilityTheory ENNReal

open Classical in
/-- **Every-subset power-curve recovery on arbitrary finite coordinates.**

Any uniform exact-power certificate on the canonical `Fin` reindexing extends every constituent
received word to a Reed--Solomon codeword on every qualifying subset.  This semantic statement
works over arbitrary fields and in arbitrary characteristic; finite-field sampling is handled by
the separate `mcaError` theorem below. -/
theorem exists_exceptional_powerMCA_arbitrary_index
    {ι : Type} [Fintype ι]
    {F : Type} [Field F]
    (domain : ι ↪ F) (ℓ k agreement exceptionalCount : ℕ) (radius : ℝ)
    (hthreshold : agreement ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊)
    (U : Fin (ℓ + 1) → ι → F)
    (hpower : UniformExactPowerAgreement
      ((Fintype.equivFin ι).symm.toEmbedding.trans domain)
      (fun t i ↦ U t ((Fintype.equivFin ι).symm i))
      k agreement exceptionalCount) :
    ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ exceptionalCount ∧
      ∀ z, z ∉ exceptional → ∀ T : Finset ι,
        (T.card : ℝ) ≥ Fintype.card ι * (1 - radius) →
        projectedWord (fun i ↦ ∑ t, z ^ t.val • U t i) T ∈
          projectedCodeSubmod (code domain k) T →
        ∃ p : Fin (ℓ + 1) → code domain k,
          ∀ t i, i ∈ T → (p t).val i = U t i := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let domainFin : Fin n ↪ F := e.symm.toEmbedding.trans domain
  let valuesFin : Fin (ℓ + 1) → Fin n → F := fun t i ↦ U t (e.symm i)
  obtain ⟨exceptional, hcard, hgood⟩ := hpower
  refine ⟨exceptional, ?_, ?_⟩
  · exact_mod_cast hcard
  · intro z hz T hT hcombination
    have hcombination' :
        projectedWord (fun i ↦ ∑ t, z ^ t.val * U t i) T ∈
          projectedCodeSubmod (code domain k) T := by
      simpa only [smul_eq_mul] using hcombination
    obtain ⟨Q, hQdegree, hQOnT⟩ :=
      (projectedWord_mem_code_iff_exists_polynomial domain k _ T).mp hcombination'
    let TFin : Finset (Fin n) := T.image e
    have hTFinCard : TFin.card = T.card := by
      simpa only [TFin] using Finset.card_image_of_injective T e.injective
    have hAgreementT : agreement ≤ T.card := by
      apply hthreshold.trans
      apply Nat.ceil_le.mpr
      simpa only [n] using hT
    have hTFinSubset :
        TFin ⊆ polynomialAgreementSet domainFin (powerBatchedWord valuesFin z) Q := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [domainFin, valuesFin, powerBatchedWord,
        Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
        using hQOnT i hi
    have hAgreement : agreement ≤
        (polynomialAgreementSet domainFin (powerBatchedWord valuesFin z) Q).card :=
      (hAgreementT.trans_eq hTFinCard.symm).trans (Finset.card_le_card hTFinSubset)
    obtain ⟨P, hPdegree, _hPidentity, hfull⟩ :=
      hgood z hz Q hQdegree hAgreement
    let codeword (t : Fin (ℓ + 1)) : code domain k :=
      ⟨evalOnPoints domain (P t), evalOnPoints_mem_code_of_degree_lt (hPdegree t)⟩
    refine ⟨codeword, ?_⟩
    intro t i hi
    have hiFin : e i ∈ TFin := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hiCommon :
        e i ∈ commonCurveAgreementSet domainFin valuesFin P := by
      rw [← hfull]
      exact hTFinSubset hiFin
    have hiAll := (Finset.mem_filter.mp hiCommon).2
    change (P t).eval (domain i) = U t i
    simpa only [domainFin, valuesFin, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using hiAll t

open Classical in
/-- The arbitrary-index every-subset adapter applied to the all-samples recovery theorem.

This is an unconditional arbitrary-field semantic result.  Its retained-family factor
`n.choose k` is intentionally explicit; stronger ordinary incidence bounds can replace the
certificate consumed by `exists_exceptional_powerMCA_arbitrary_index` without changing that
adapter. -/
theorem exists_exceptional_powerMCA_all_samples_arbitrary_index
    {ι : Type} [Fintype ι]
    {F : Type} [Field F]
    (domain : ι ↪ F) (ℓ k agreement : ℕ) (radius : ℝ)
    (hkAgreement : k ≤ agreement)
    (hthreshold : agreement ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊)
    (U : Fin (ℓ + 1) → ι → F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        ((Fintype.card ι).choose k * (ℓ * (Fintype.card ι - k)) : ℕ) ∧
      ∀ z, z ∉ exceptional → ∀ T : Finset ι,
        (T.card : ℝ) ≥ Fintype.card ι * (1 - radius) →
        projectedWord (fun i ↦ ∑ t, z ^ t.val • U t i) T ∈
          projectedCodeSubmod (code domain k) T →
        ∃ p : Fin (ℓ + 1) → code domain k,
          ∀ t i, i ∈ T → (p t).val i = U t i := by
  apply exists_exceptional_powerMCA_arbitrary_index
    domain ℓ k agreement
      ((Fintype.card ι).choose k * (ℓ * (Fintype.card ι - k))) radius hthreshold U
  exact uniformExactPowerAgreement_of_all_samples _ _ hkAgreement

open Classical in
/-- **Canonical finite-field MCA bound for the univariate-powers generator.**

Uniform sampling turns any exact-power certificate on the canonical `Fin` reindexing into the
uncapped quotient `exceptionalCount / |F|`.  No characteristic hypothesis involving `ℓ` is
required. -/
theorem power_mcaError_le_arbitrary_index
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Fintype F]
    (domain : ι ↪ F) (ℓ k agreement exceptionalCount : ℕ) (radius : ℝ)
    (hthreshold : agreement ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊)
    (hpower : ∀ U : Fin (ℓ + 1) → ι → F,
      UniformExactPowerAgreement
        ((Fintype.equivFin ι).symm.toEmbedding.trans domain)
        (fun t i ↦ U t ((Fintype.equivFin ι).symm i))
        k agreement exceptionalCount) :
    mcaError (univariatePowersGenerator F ℓ) (code domain k) radius ≤
      ENNReal.ofReal (exceptionalCount / (Fintype.card F : ℝ)) := by
  apply CoreDefinitions.mcaError_le_of_exists_exceptional_set_codewords
  intro U
  exact exists_exceptional_powerMCA_arbitrary_index
    domain ℓ k agreement exceptionalCount radius hthreshold U (hpower U)

open Classical in
/-- The explicit all-samples specialization of the canonical finite-field power-MCA bound. -/
theorem power_mcaError_le_all_samples_arbitrary_index
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Fintype F]
    (domain : ι ↪ F) (ℓ k agreement : ℕ) (radius : ℝ)
    (hkAgreement : k ≤ agreement)
    (hthreshold : agreement ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊) :
    mcaError (univariatePowersGenerator F ℓ) (code domain k) radius ≤
      ENNReal.ofReal
        (((Fintype.card ι).choose k * (ℓ * (Fintype.card ι - k)) : ℕ) /
          (Fintype.card F : ℝ)) := by
  apply power_mcaError_le_arbitrary_index domain ℓ k agreement
    ((Fintype.card ι).choose k * (ℓ * (Fintype.card ι - k))) radius hthreshold
  intro U
  exact uniformExactPowerAgreement_of_all_samples _ _ hkAgreement

end ReedSolomon
