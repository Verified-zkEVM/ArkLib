/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds

/-!
# Shared-level tensor-fold agreement for interleaved Reed--Solomon codes

This file lifts an exact scalar line certificate to a full-agreement line witness for every
nonempty row-wise interleaving, without a factor depending on the number of rows.  It then
specializes the generic binary tensor-fold theorem at height three.
-/

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

/-- At most `|K|` proper subspaces cannot cover a nontrivial finite `K`-vector space. -/
private theorem exists_forall_notMem_of_card_le
    {α K M : Type} [Field K] [Fintype K] [AddCommGroup M] [Module K M]
    [Finite M] [Nontrivial M]
    (s : Finset α) (p : α → Submodule K M)
    (hp : ∀ i ∈ s, p i ≠ ⊤) (hs : s.card ≤ Fintype.card K) :
    ∃ x : M, ∀ i ∈ s, x ∉ p i := by
  classical
  let := Fintype.ofFinite M
  let q := Fintype.card K
  let d := Module.finrank K M
  let nz (i : α) := Finset.univ.filter fun x : M => x ∈ p i ∧ x ≠ 0
  let covered := insert (0 : M) (s.biUnion nz)
  have hq : 1 < q := Fintype.one_lt_card
  have hd : 0 < d := Module.finrank_pos
  have hnz (i : α) (hi : i ∈ s) : (nz i).card ≤ q ^ (d - 1) - 1 := by
    let allp := Finset.univ.filter fun x : M => x ∈ p i
    have hzero : (0 : M) ∈ allp := by simp [allp]
    have hnz_eq : nz i = allp.erase 0 := by
      ext x
      simp [nz, allp, and_comm]
    rw [hnz_eq, Finset.card_erase_of_mem hzero]
    have hcard : allp.card = Fintype.card (p i) := by
      symm
      exact Fintype.card_ofFinset allp (by simp [allp])
    have hcardpow : Fintype.card (p i) = q ^ Module.finrank K (p i) := by
      simpa [q] using (Module.card_eq_pow_finrank (K := K) (V := p i))
    rw [hcard, hcardpow]
    exact Nat.sub_le_sub_right
      (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hq)
        (Nat.le_sub_one_of_lt (Submodule.finrank_lt (hp i hi)))) 1
  have hcovered : covered.card < Fintype.card M := by
    have hbi : (s.biUnion nz).card ≤ s.card * (q ^ (d - 1) - 1) := by
      calc
        (s.biUnion nz).card ≤ ∑ i ∈ s, (nz i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ s, (q ^ (d - 1) - 1) :=
          Finset.sum_le_sum fun i hi => hnz i hi
        _ = s.card * (q ^ (d - 1) - 1) := by simp
    have hmul : s.card * (q ^ (d - 1) - 1) ≤ q * (q ^ (d - 1) - 1) :=
      Nat.mul_le_mul_right _ hs
    have hpow : q ^ d = q * q ^ (d - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hd]
      simp [pow_succ, Nat.mul_comm]
    have hcardM : Fintype.card M = q ^ d := by
      simpa [q, d] using (Module.card_eq_pow_finrank (K := K) (V := M))
    rw [hcardM, hpow]
    calc
      covered.card ≤ (s.biUnion nz).card + 1 := Finset.card_insert_le _ _
      _ ≤ s.card * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hbi 1
      _ ≤ q * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hmul 1
      _ < q * q ^ (d - 1) := by
        have hpos : 0 < q ^ (d - 1) := pow_pos (Nat.zero_lt_of_lt hq) _
        have hqmul : q ≤ q * q ^ (d - 1) := by
          simpa using Nat.mul_le_mul_left q hpos
        rw [Nat.mul_sub_left_distrib]
        simp only [mul_one]
        omega
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := covered) (t := Finset.univ) (by simpa using hcovered)
  refine ⟨x, fun i hi hxi => hx ?_⟩
  by_cases hx0 : x = 0
  · simp [covered, hx0]
  · simp only [covered, Finset.mem_insert]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, by simp [nz, hxi, hx0]⟩)

open Classical in
private theorem interleaved_lineProjectionBad_card_le
    {ι F A : Type} [Fintype ι]
    [Field F] [Fintype F]
    [AddCommMonoid A] [Module F A]
    (C : ModuleCode ι F A) {agreement t exceptionalCount : ℕ}
    (ht : 0 < t)
    (hscalar : ∀ v₀ v₁ : ι → A,
      (Finset.univ.filter fun r : F ↦ lineProjectionBad C agreement r v₀ v₁).card ≤
        exceptionalCount)
    (u₀ u₁ : ι → Fin t → A) :
    (Finset.univ.filter fun r : F ↦
      lineProjectionBad (C ^⋈ (Fin t)) agreement r u₀ u₁).card ≤ exceptionalCount := by
  classical
  let : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  let isBad (r : F) := lineProjectionBad (C ^⋈ (Fin t)) agreement r u₀ u₁
  let bad := Finset.univ.filter isBad
  obtain ⟨T, hT⟩ : ∃ T : F → Finset ι, ∀ r, isBad r →
      agreement ≤ (T r).card ∧
      projectedWord (binaryLineFold r u₀ u₁) (T r) ∈
        projectedCodeSubmod (C ^⋈ (Fin t)) (T r) ∧
      (projectedWord u₀ (T r) ∉ projectedCodeSubmod (C ^⋈ (Fin t)) (T r) ∨
        projectedWord u₁ (T r) ∉ projectedCodeSubmod (C ^⋈ (Fin t)) (T r)) := by
    choose! T hT using fun r (hr : isBad r) => hr
    exact ⟨T, hT⟩
  let rowComb (l : Fin t → F) (b : Bool) : ι → A := fun i =>
    ∑ j, l j • (if b then u₁ i j else u₀ i j)
  let K (r : F) : Submodule F (Fin t → F) := {
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
    · have hbad' : ∃ j : Fin t,
          projectedWord (fun i ↦ u₀ i j) (T r) ∉ projectedCodeSubmod C (T r) := by
        by_contra hall
        push Not at hall
        apply hbad
        exact (projectedCodeSubmod_moduleInterleavedCode_iff F A (Fin t) ι C u₀ (T r)).mpr hall
      obtain ⟨j, hj⟩ := hbad'
      intro htop
      have he : Pi.single j (1 : F) ∈ K r := by rw [htop]; exact Submodule.mem_top
      apply hj
      have hrow := he false
      simpa [K, rowComb] using hrow
    · have hbad' : ∃ j : Fin t,
          projectedWord (fun i ↦ u₁ i j) (T r) ∉ projectedCodeSubmod C (T r) := by
        by_contra hall
        push Not at hall
        apply hbad
        exact (projectedCodeSubmod_moduleInterleavedCode_iff F A (Fin t) ι C u₁ (T r)).mpr hall
      obtain ⟨j, hj⟩ := hbad'
      intro htop
      have he : Pi.single j (1 : F) ∈ K r := by rw [htop]; exact Submodule.mem_top
      apply hj
      have hrow := he true
      simpa [K, rowComb] using hrow
  have hbadcard : bad.card ≤ Fintype.card F := by
    simpa [bad] using Finset.card_filter_le Finset.univ isBad
  obtain ⟨l, hl⟩ := exists_forall_notMem_of_card_le bad K hK hbadcard
  have himp : ∀ r : F, isBad r → lineProjectionBad C agreement r
      (rowComb l false) (rowComb l true) := by
    intro r hr
    have hrbad : r ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
    have hd := hT r hr
    refine ⟨T r, hd.1, ?_, ?_⟩
    · have hrows : ∀ j : Fin t,
          projectedWord (fun i => binaryLineFold r u₀ u₁ i j) (T r) ∈
            projectedCodeSubmod C (T r) :=
        (projectedCodeSubmod_moduleInterleavedCode_iff F A (Fin t) ι C
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

private theorem interleaved_eq_of_agree_on
    {F : Type} [Field F] {n k t : ℕ} (domain : Fin n ↪ F)
    (S : Finset (Fin n)) (hkS : k ≤ S.card)
    {c d : Fin n → Fin t → F}
    (hc : c ∈ ModuleCode.moduleInterleavedCode F F (Fin t) (Fin n) (code domain k))
    (hd : d ∈ ModuleCode.moduleInterleavedCode F F (Fin t) (Fin n) (code domain k))
    (hagree : ∀ i ∈ S, c i = d i) : c = d := by
  apply _root_.funext
  intro i
  apply _root_.funext
  intro j
  have hcj := (mem_moduleInterleavedCode_iff F F (Fin t) (Fin n) (code domain k) c).mp hc j
  have hdj := (mem_moduleInterleavedCode_iff F F (Fin t) (Fin n) (code domain k) d).mp hd j
  obtain ⟨P, hP, hPeval⟩ := mem_code_iff_eval.mp hcj
  obtain ⟨Q, hQ, hQeval⟩ := mem_code_iff_eval.mp hdj
  change ∀ x, P.eval (domain x) = c x j at hPeval
  change ∀ x, Q.eval (domain x) = d x j at hQeval
  have hPQ : P = Q := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := S) domain.injective.injOn
      (hP.trans_le (by exact_mod_cast hkS)) (hQ.trans_le (by exact_mod_cast hkS))
    intro x hx
    rw [hPeval x, hQeval x]
    exact congrFun (hagree x hx) j
  change c i j = d i j
  rw [← hPeval i, ← hQeval i, hPQ]

/-- A scalar exact-line certificate gives a full-set binary-line witness for every nonempty
row-wise interleaving, at the same exceptional count. -/
theorem fullSetLineWitness_interleaved_of_exactAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k agreement exceptionalCount width : ℕ}
    (domain : Fin n ↪ F)
    (hline : LineExactAgreementBound domain k agreement exceptionalCount)
    (hwidth : 0 < width) (hkAgreement : k ≤ agreement) :
    FullSetLineWitness ((code domain k) ^⋈ (Fin width)) agreement exceptionalCount := by
  intro u₀ u₁
  classical
  let exceptional := Finset.univ.filter fun r : F ↦
    lineProjectionBad ((code domain k) ^⋈ (Fin width)) agreement r u₀ u₁
  refine ⟨exceptional, ?_, ?_⟩
  · exact interleaved_lineProjectionBad_card_le (code domain k) hwidth
      (scalar_lineProjectionBad_card_le domain hline) u₀ u₁
  · intro r hr c hc hagreement
    have hgood : ¬ lineProjectionBad ((code domain k) ^⋈ (Fin width))
        agreement r u₀ u₁ := by
      simpa [exceptional] using hr
    let S := fullAgreementSet c (binaryLineFold r u₀ u₁)
    have hroot : projectedWord (binaryLineFold r u₀ u₁) S ∈
        projectedCodeSubmod ((code domain k) ^⋈ (Fin width)) S := by
      rw [mem_projectedCodeSubmod_iff]
      refine ⟨c, hc, ?_⟩
      funext i
      exact (Finset.mem_filter.mp i.property).2.symm
    have hchildren :
        projectedWord u₀ S ∈ projectedCodeSubmod ((code domain k) ^⋈ (Fin width)) S ∧
        projectedWord u₁ S ∈ projectedCodeSubmod ((code domain k) ^⋈ (Fin width)) S := by
      by_contra h
      apply hgood
      exact ⟨S, hagreement, hroot, not_and_or.mp h⟩
    obtain ⟨c₀, hc₀, hc₀S⟩ :=
      (mem_projectedCodeSubmod_iff _ S _).mp hchildren.1
    obtain ⟨c₁, hc₁, hc₁S⟩ :=
      (mem_projectedCodeSubmod_iff _ S _).mp hchildren.2
    have hfoldmem : binaryLineFold r c₀ c₁ ∈
        ModuleCode.moduleInterleavedCode F F (Fin width) (Fin n) (code domain k) := by
      exact (ModuleCode.moduleInterleavedCode F F (Fin width) (Fin n) (code domain k)).add_mem
        ((ModuleCode.moduleInterleavedCode F F (Fin width) (Fin n)
          (code domain k)).smul_mem (1 - r) hc₀)
        ((ModuleCode.moduleInterleavedCode F F (Fin width) (Fin n)
          (code domain k)).smul_mem r hc₁)
    have hcEq : c = binaryLineFold r c₀ c₁ := by
      apply interleaved_eq_of_agree_on domain S (hkAgreement.trans hagreement) hc hfoldmem
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

/-- Height three has the safe shared-level factor seven, independent of interleaving width. -/
theorem interleavedRS_tensorFoldBad_card_le_heightThree
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k agreement exceptionalCount width : ℕ}
    (domain : Fin n ↪ F)
    (hline : LineExactAgreementBound domain k agreement exceptionalCount)
    (hwidth : 0 < width) (hkAgreement : k ≤ agreement)
    (u : (Fin 3 → Bool) → Fin n → Fin width → F) :
    (tensorFoldBad
      (fullSetLineWitness_interleaved_of_exactAgreement domain hline hwidth hkAgreement) u).card ≤
        7 * exceptionalCount * Fintype.card F ^ 2 := by
  simpa using tensorFoldBad_card_le
    (fullSetLineWitness_interleaved_of_exactAgreement domain hline hwidth hkAgreement) u

end

end ReedSolomon
