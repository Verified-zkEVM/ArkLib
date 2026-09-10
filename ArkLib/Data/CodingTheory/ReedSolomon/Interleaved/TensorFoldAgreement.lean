/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement

/-!
# Shared-level tensor-fold agreement for interleaved Reed--Solomon codes

This file lifts an exact scalar line certificate to a full-agreement level witness for every
finite family over a nonempty row-wise interleaving, without a factor depending on either width.
It then specializes the generic binary tensor-fold theorem at height three.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial Code CoreDefinitions LinearCode TensorMCA
open scoped BigOperators ProbabilityTheory ENNReal

/-- Failure of constituent projection at an integer agreement threshold. -/
private def lineProjectionBad {ι F A : Type} [Fintype ι] [Field F]
    [AddCommMonoid A] [Module F A]
    (C : ModuleCode ι F A) (agreement : ℕ) (r : F) (u₀ u₁ : ι → A) : Prop :=
  ∃ T : Finset ι,
    agreement ≤ T.card ∧
    projectedWord (binaryLineFold r u₀ u₁) T ∈ projectedCodeSubmod C T ∧
    (projectedWord u₀ T ∉ projectedCodeSubmod C T ∨
      projectedWord u₁ T ∉ projectedCodeSubmod C T)

open Classical in
private theorem scalar_lineProjectionBad_card_le
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k agreement exceptionalCount : ℕ}
    (domain : Fin n ↪ F)
    (hline : LineExactAgreementBound domain k agreement exceptionalCount)
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter fun r : F ↦
      lineProjectionBad (code domain k) agreement r u₀ u₁).card ≤ exceptionalCount := by
  classical
  obtain ⟨exceptional, hcard, hgood⟩ := hline u₀ (u₁ - u₀)
  apply (Finset.card_le_card ?_).trans
  · exact_mod_cast hcard
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    obtain ⟨T, hT, hroot, hchild⟩ := hr
    have hroot' :
        projectedWord (fun i ↦ u₀ i + r * (u₁ i - u₀ i)) T ∈
          projectedCodeSubmod (code domain k) T := by
      have heq : binaryLineFold r u₀ u₁ =
          fun i ↦ u₀ i + r * (u₁ i - u₀ i) := by
        funext i
        simp only [binaryLineFold, smul_eq_mul]
        ring
      rwa [← heq]
    obtain ⟨P, hPdegree, hPonT⟩ :=
      (projectedWord_mem_code_iff_exists_polynomial domain k _ T).mp hroot'
    have hsubset : T ⊆ polynomialAgreementSet domain
        (fun i ↦ u₀ i + r * (u₁ i - u₀ i)) P := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPonT i hi⟩
    have hagreement : agreement ≤ (polynomialAgreementSet domain
        (fun i ↦ u₀ i + r * (u₁ i - u₀ i)) P).card :=
      hT.trans (Finset.card_le_card hsubset)
    by_contra hrExceptional
    obtain ⟨P₀, D, hP₀, hD, -, hexact⟩ :=
      hgood r hrExceptional P hPdegree hagreement
    rcases hchild with hchild | hchild
    · apply hchild
      apply (projectedWord_mem_code_iff_exists_polynomial domain k u₀ T).mpr
      refine ⟨P₀, hP₀, fun i hi ↦ ?_⟩
      have hi' : i ∈ commonPolynomialAgreementSet domain u₀ (u₁ - u₀) P₀ D := by
        rw [← hexact]
        exact hsubset hi
      exact (Finset.mem_filter.mp hi').2.1
    · apply hchild
      apply (projectedWord_mem_code_iff_exists_polynomial domain k u₁ T).mpr
      refine ⟨P₀ + D, ?_, fun i hi ↦ ?_⟩
      · exact mem_degreeLT.mp <|
          (degreeLT F k).add_mem (mem_degreeLT.mpr hP₀) (mem_degreeLT.mpr hD)
      · have hi' : i ∈ commonPolynomialAgreementSet domain u₀ (u₁ - u₀) P₀ D := by
          rw [← hexact]
          exact hsubset hi
        have hi0 := (Finset.mem_filter.mp hi').2.1
        have hiD := (Finset.mem_filter.mp hi').2.2
        simp only [eval_add, Pi.sub_apply] at hiD ⊢
        rw [hi0, hiD]
        ring

open Classical in
private theorem interleaved_lineProjectionBad_card_le
    {ι F A τ : Type} [Fintype ι]
    [Field F] [Fintype F]
    [AddCommMonoid A] [Module F A] [Finite τ] [Nonempty τ]
    (C : ModuleCode ι F A) {agreement exceptionalCount : ℕ}
    (hscalar : ∀ v₀ v₁ : ι → A,
      (Finset.univ.filter fun r : F ↦ lineProjectionBad C agreement r v₀ v₁).card ≤
        exceptionalCount)
    (u₀ u₁ : ι → τ → A) :
    (Finset.univ.filter fun r : F ↦
      lineProjectionBad (C ^⋈ τ) agreement r u₀ u₁).card ≤ exceptionalCount := by
  classical
  let : Fintype τ := Fintype.ofFinite τ
  let isBad (r : F) := lineProjectionBad (C ^⋈ τ) agreement r u₀ u₁
  let bad := Finset.univ.filter isBad
  obtain ⟨T, hT⟩ : ∃ T : F → Finset ι, ∀ r, isBad r →
      agreement ≤ (T r).card ∧
      projectedWord (binaryLineFold r u₀ u₁) (T r) ∈
        projectedCodeSubmod (C ^⋈ τ) (T r) ∧
      (projectedWord u₀ (T r) ∉ projectedCodeSubmod (C ^⋈ τ) (T r) ∨
        projectedWord u₁ (T r) ∉ projectedCodeSubmod (C ^⋈ τ) (T r)) := by
    choose! T hT using fun r (hr : isBad r) => hr
    exact ⟨T, hT⟩
  let rowComb (l : τ → F) (b : Bool) : ι → A := fun i =>
    ∑ j, l j • (if b then u₁ i j else u₀ i j)
  let K (r : F) : Submodule F (τ → F) := {
    carrier := {l | ∀ b : Bool,
      projectedWord (rowComb l b) (T r) ∈ projectedCodeSubmod C (T r)}
    zero_mem' := by
      intro b
      have hz : projectedWord (rowComb 0 b) (T r) = 0 := by
        ext i
        simp [projectedWord, rowComb]
      rw [hz]
      exact (projectedCodeSubmod C (T r)).zero_mem
    add_mem' := by
      intro l l' hl hl' b
      have hadd : projectedWord (rowComb (l + l') b) (T r) =
          projectedWord (rowComb l b) (T r) + projectedWord (rowComb l' b) (T r) := by
        ext i
        cases b <;> simp [projectedWord, rowComb, add_smul, Finset.sum_add_distrib]
      rw [hadd]
      exact (projectedCodeSubmod C (T r)).add_mem (hl b) (hl' b)
    smul_mem' := by
      intro a l hl b
      have hsmul : projectedWord (rowComb (a • l) b) (T r) =
          a • projectedWord (rowComb l b) (T r) := by
        ext i
        simp [projectedWord, rowComb, Finset.smul_sum, mul_smul]
      rw [hsmul]
      exact (projectedCodeSubmod C (T r)).smul_mem a (hl b) }
  have hK (r : F) (hr : r ∈ bad) : K r ≠ ⊤ := by
    rcases (hT r (Finset.mem_filter.mp hr).2).2.2 with hbad | hbad
    · have hbad' : ∃ j : τ,
          projectedWord (fun i ↦ u₀ i j) (T r) ∉ projectedCodeSubmod C (T r) := by
        by_contra hall
        push Not at hall
        apply hbad
        exact (projectedCodeSubmod_moduleInterleavedCode_iff F A τ ι C u₀ (T r)).mpr hall
      obtain ⟨j, hj⟩ := hbad'
      intro htop
      have he : Pi.single j (1 : F) ∈ K r := by rw [htop]; exact Submodule.mem_top
      apply hj
      have hrow := he false
      simpa [K, rowComb] using hrow
    · have hbad' : ∃ j : τ,
          projectedWord (fun i ↦ u₁ i j) (T r) ∉ projectedCodeSubmod C (T r) := by
        by_contra hall
        push Not at hall
        apply hbad
        exact (projectedCodeSubmod_moduleInterleavedCode_iff F A τ ι C u₁ (T r)).mpr hall
      obtain ⟨j, hj⟩ := hbad'
      intro htop
      have he : Pi.single j (1 : F) ∈ K r := by rw [htop]; exact Submodule.mem_top
      apply hj
      have hrow := he true
      simpa [K, rowComb] using hrow
  have hbadcard : bad.card ≤ Fintype.card F := by
    simpa [bad] using Finset.card_filter_le Finset.univ isBad
  obtain ⟨l, hl⟩ := exists_vector_avoiding_submodules bad K hK hbadcard
  have himp : ∀ r : F, isBad r → lineProjectionBad C agreement r
      (rowComb l false) (rowComb l true) := by
    intro r hr
    have hrbad : r ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
    have hd := hT r hr
    refine ⟨T r, hd.1, ?_, ?_⟩
    · have hrows : ∀ j : τ,
          projectedWord (fun i => binaryLineFold r u₀ u₁ i j) (T r) ∈
            projectedCodeSubmod C (T r) :=
        (projectedCodeSubmod_moduleInterleavedCode_iff F A τ ι C
          (binaryLineFold r u₀ u₁) (T r)).mp hd.2.1
      rw [mem_projectedCodeSubmod_iff]
      convert projectedCode_linearCombination C (T r)
        (fun j i => binaryLineFold r u₀ u₁ i j) l
        (fun j => (mem_projectedCodeSubmod_iff C (T r) _).mp (hrows j)) using 1
      ext i
      change (1 - r) • (∑ j, l j • u₀ i j) + r • (∑ j, l j • u₁ i j) =
        ∑ j, l j • ((1 - r) • u₀ i j + r • u₁ i j)
      simp only [Finset.smul_sum, smul_add, smul_smul, Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> rw [mul_comm]
    · have hnot := hl r hrbad
      change ¬ ∀ b : Bool, projectedWord (rowComb l b) (T r) ∈
        projectedCodeSubmod C (T r) at hnot
      push Not at hnot
      rcases hnot with ⟨b, hb⟩
      cases b
      · exact Or.inl hb
      · exact Or.inr hb
  calc
    (Finset.univ.filter isBad).card ≤
        (Finset.univ.filter fun r : F ↦ lineProjectionBad C agreement r
          (rowComb l false) (rowComb l true)).card := by
      apply Finset.card_le_card
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact himp r hr
    _ ≤ exceptionalCount := hscalar _ _

/-- A scalar exact-line certificate gives one full-set binary-line witness over any finite
nonempty row index, at the same exceptional count. -/
private theorem exists_exceptional_fullSetLine_interleaved_of_exactAgreement
    {F τ : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype τ] [Nonempty τ]
    {n k agreement exceptionalCount : ℕ}
    (domain : Fin n ↪ F)
    (hline : LineExactAgreementBound domain k agreement exceptionalCount)
    (hkAgreement : k ≤ agreement) :
    ∀ u₀ u₁ : Fin n → τ → F, ∃ exceptional : Finset F,
      exceptional.card ≤ exceptionalCount ∧
      ∀ r ∉ exceptional, ∀ c : Fin n → τ → F,
        c ∈ ((code domain k) ^⋈ τ) →
        agreement ≤ (fullAgreementSet c (binaryLineFold r u₀ u₁)).card →
        ∃ c₀ c₁ : Fin n → τ → F,
          c₀ ∈ ((code domain k) ^⋈ τ) ∧ c₁ ∈ ((code domain k) ^⋈ τ) ∧
          c = binaryLineFold r c₀ c₁ ∧
          fullAgreementSet c (binaryLineFold r u₀ u₁) =
            fullAgreementSet c₀ u₀ ∩ fullAgreementSet c₁ u₁ := by
  intro u₀ u₁
  classical
  let exceptional := Finset.univ.filter fun r : F ↦
    lineProjectionBad ((code domain k) ^⋈ τ) agreement r u₀ u₁
  refine ⟨exceptional, ?_, ?_⟩
  · exact interleaved_lineProjectionBad_card_le (code domain k)
      (scalar_lineProjectionBad_card_le domain hline) u₀ u₁
  · intro r hr c hc hagreement
    have hgood : ¬ lineProjectionBad ((code domain k) ^⋈ τ)
        agreement r u₀ u₁ := by
      simpa [exceptional] using hr
    let S := fullAgreementSet c (binaryLineFold r u₀ u₁)
    have hroot : projectedWord (binaryLineFold r u₀ u₁) S ∈
        projectedCodeSubmod ((code domain k) ^⋈ τ) S := by
      rw [mem_projectedCodeSubmod_iff]
      refine ⟨c, hc, ?_⟩
      funext i
      exact (Finset.mem_filter.mp i.property).2.symm
    have hchildren :
        projectedWord u₀ S ∈ projectedCodeSubmod ((code domain k) ^⋈ τ) S ∧
        projectedWord u₁ S ∈ projectedCodeSubmod ((code domain k) ^⋈ τ) S := by
      by_contra h
      apply hgood
      exact ⟨S, hagreement, hroot, not_and_or.mp h⟩
    obtain ⟨c₀, hc₀, hc₀S⟩ :=
      (mem_projectedCodeSubmod_iff _ S _).mp hchildren.1
    obtain ⟨c₁, hc₁, hc₁S⟩ :=
      (mem_projectedCodeSubmod_iff _ S _).mp hchildren.2
    have hfoldmem : binaryLineFold r c₀ c₁ ∈
        ModuleCode.moduleInterleavedCode F F τ (Fin n) (code domain k) := by
      exact (ModuleCode.moduleInterleavedCode F F τ (Fin n) (code domain k)).add_mem
        ((ModuleCode.moduleInterleavedCode F F τ (Fin n)
          (code domain k)).smul_mem (1 - r) hc₀)
        ((ModuleCode.moduleInterleavedCode F F τ (Fin n)
          (code domain k)).smul_mem r hc₁)
    have hcEq : c = binaryLineFold r c₀ c₁ := by
      apply interleavedCodeword_eq_of_agree_on domain S (hkAgreement.trans hagreement) hc hfoldmem
      intro i hi
      have hci := (Finset.mem_filter.mp hi).2
      have h0 := congrFun hc₀S ⟨i, hi⟩
      have h1 := congrFun hc₁S ⟨i, hi⟩
      change u₀ i = c₀ i at h0
      change u₁ i = c₁ i at h1
      rw [hci, binaryLineFold, h0, h1]
      rfl
    refine ⟨c₀, c₁, hc₀, hc₁, hcEq, ?_⟩
    ext i
    simp only [Finset.mem_inter, fullAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      exact ⟨congrFun hc₀S ⟨i, hiS⟩ |>.symm, congrFun hc₁S ⟨i, hiS⟩ |>.symm⟩
    · rintro ⟨h0, h1⟩
      simp [hcEq, binaryLineFold, h0, h1]

/-- A scalar exact-line certificate controls every finite family of lines over a nonempty
row-wise interleaving.  The parent-family index and the original row index are combined into one
larger interleaving, so the exceptional count is independent of both widths. -/
theorem fullSetLevelWitness_interleaved_of_exactAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k agreement exceptionalCount width : ℕ}
    (domain : Fin n ↪ F)
    (hline : LineExactAgreementBound domain k agreement exceptionalCount)
    (hwidth : 0 < width) (hkAgreement : k ≤ agreement) :
    FullSetLevelWitness ((code domain k) ^⋈ (Fin width)) agreement exceptionalCount := by
  intro β _ _ u₀ u₁
  classical
  let pack (u : β → Fin n → Fin width → F) : Fin n → β × Fin width → F :=
    fun i p ↦ u p.1 i p.2
  let : Nonempty (Fin width) := Fin.pos_iff_nonempty.mp hwidth
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_fullSetLine_interleaved_of_exactAgreement
      (τ := β × Fin width) domain hline hkAgreement (pack u₀) (pack u₁)
  refine ⟨exceptional, hcard, ?_⟩
  intro r hr c hc hagreement
  have pack_mem (d : β → Fin n → Fin width → F)
      (hd : ∀ b, d b ∈ ((code domain k) ^⋈ (Fin width))) :
      pack d ∈ ((code domain k) ^⋈ (β × Fin width)) := by
    change ∀ p : β × Fin width, (fun i ↦ pack d i p) ∈ code domain k
    rintro ⟨b, j⟩
    have hdb := hd b
    change ∀ row, (fun i ↦ d b i row) ∈ code domain k at hdb
    exact hdb j
  have agreementSet_pack (d v : β → Fin n → Fin width → F) :
      familyAgreementSet d v = fullAgreementSet (pack d) (pack v) := by
    ext i
    simp only [familyAgreementSet, fullAgreementSet, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hi
      funext p
      exact congrFun (hi p.1) p.2
    · intro hi b
      funext j
      exact congrFun hi (b, j)
  have pack_fold (d₀ d₁ : β → Fin n → Fin width → F) :
      pack (fun b ↦ binaryLineFold r (d₀ b) (d₁ b)) =
        binaryLineFold r (pack d₀) (pack d₁) := by
    rfl
  have hagreement' : agreement ≤
      (fullAgreementSet (pack c) (binaryLineFold r (pack u₀) (pack u₁))).card := by
    rw [← pack_fold u₀ u₁]
    rw [← agreementSet_pack c (fun b ↦ binaryLineFold r (u₀ b) (u₁ b))]
    exact hagreement
  obtain ⟨d₀, d₁, hd₀, hd₁, hdEq, hset⟩ :=
    hgood r hr (pack c) (pack_mem c hc) hagreement'
  let c₀ : β → Fin n → Fin width → F := fun b i j ↦ d₀ i (b, j)
  let c₁ : β → Fin n → Fin width → F := fun b i j ↦ d₁ i (b, j)
  have hc₀ : ∀ b, c₀ b ∈ ((code domain k) ^⋈ (Fin width)) := by
    intro b
    change ∀ j, (fun i ↦ c₀ b i j) ∈ code domain k
    have hrows := hd₀
    change ∀ p, (fun i ↦ d₀ i p) ∈ code domain k at hrows
    exact fun j ↦ hrows (b, j)
  have hc₁ : ∀ b, c₁ b ∈ ((code domain k) ^⋈ (Fin width)) := by
    intro b
    change ∀ j, (fun i ↦ c₁ b i j) ∈ code domain k
    have hrows := hd₁
    change ∀ p, (fun i ↦ d₁ i p) ∈ code domain k at hrows
    exact fun j ↦ hrows (b, j)
  have hpack₀ : pack c₀ = d₀ := by rfl
  have hpack₁ : pack c₁ = d₁ := by rfl
  refine ⟨c₀, c₁, hc₀, hc₁, ?_, ?_⟩
  · intro b
    funext i j
    exact congrFun (congrFun hdEq i) (b, j)
  · rw [agreementSet_pack c (fun b ↦ binaryLineFold r (u₀ b) (u₁ b)),
      agreementSet_pack c₀ u₀, agreementSet_pack c₁ u₁,
      pack_fold, hpack₀, hpack₁]
    exact hset

/-- Height three has three shared-level exceptional events, independent of interleaving width. -/
theorem interleavedRS_tensorFoldBad_card_le_heightThree
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k agreement exceptionalCount width : ℕ}
    (domain : Fin n ↪ F)
    (hline : LineExactAgreementBound domain k agreement exceptionalCount)
    (hwidth : 0 < width) (hkAgreement : k ≤ agreement)
    (u : (Fin 3 → Bool) → Fin n → Fin width → F) :
    (tensorFoldBad
      (fullSetLevelWitness_interleaved_of_exactAgreement domain hline hwidth hkAgreement) u).card ≤
        3 * exceptionalCount * Fintype.card F ^ 2 := by
  simpa using tensorFoldBad_card_le
    (fullSetLevelWitness_interleaved_of_exactAgreement domain hline hwidth hkAgreement) u

end

end ReedSolomon
