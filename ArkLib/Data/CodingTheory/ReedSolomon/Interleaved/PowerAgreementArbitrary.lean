/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement
public import Mathlib.Algebra.Module.Submodule.Union

/-!
# Arbitrary-field interleaved power agreement

The scalar-to-interleaved transfer has the same exceptional count over every field.  The finite
case is the counting argument in `PowerAgreement`.  Over an infinite field, any hypothetical
finite family of bad challenges admits one scalar row projection detecting every member: a
finite union of proper row-dual subspaces cannot cover the row-dual space.  The scalar uniform
certificate then bounds that family, and hence the full set of bad challenges.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial Code CoreDefinitions LinearCode
open scoped BigOperators

variable {F : Type} [Field F]

/-- Failure of constituent projection at an integer agreement threshold. -/
private def powerProjectionBadArbitrary {ι A : Type*} [Fintype ι]
    [AddCommMonoid A] [Module F A]
    (C : ModuleCode ι F A) (agreement : ℕ) (z : F)
    {ℓ : ℕ} (values : Fin (ℓ + 1) → ι → A) : Prop :=
  ∃ T : Finset ι,
    agreement ≤ T.card ∧
    projectedWord (fun i ↦ ∑ t, z ^ t.val • values t i) T ∈ projectedCodeSubmod C T ∧
    ∃ t, projectedWord (values t) T ∉ projectedCodeSubmod C T

private theorem scalar_powerProjectionBadArbitrary_mem_exceptional
    [DecidableEq F] {n k agreement ℓ : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (exceptional : Finset F)
    (hgood : ∀ z ∉ exceptional, ∀ Q : F[X], Q.degree < k →
      agreement ≤ (polynomialAgreementSet domain (powerBatchedWord values z) Q).card →
      HasExactPowerAgreement domain values (RingHom.id F) k z Q)
    {z : F}
    (hz : powerProjectionBadArbitrary (code domain k) agreement z values) :
    z ∈ exceptional := by
  classical
  obtain ⟨T, hTcard, hroot, t, ht⟩ := hz
  have hroot' : projectedWord (powerBatchedWord values z) T ∈
      projectedCodeSubmod (code domain k) T := by
    convert hroot using 1
    ext i
    rfl
  obtain ⟨Q, hQdegree, hQonT⟩ :=
    (projectedWord_mem_code_iff_exists_polynomial domain k _ T).mp hroot'
  have hsubset : T ⊆ polynomialAgreementSet domain (powerBatchedWord values z) Q := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by
      simpa [powerBatchedWord, smul_eq_mul] using hQonT i hi⟩
  have hagreement : agreement ≤
      (polynomialAgreementSet domain (powerBatchedWord values z) Q).card :=
    hTcard.trans (Finset.card_le_card hsubset)
  by_contra hzExceptional
  obtain ⟨P, hPdegree, -, hset⟩ := hgood z hzExceptional Q hQdegree hagreement
  apply ht
  apply (projectedWord_mem_code_iff_exists_polynomial domain k (values t) T).mpr
  refine ⟨P t, hPdegree t, fun i hi ↦ ?_⟩
  have hmem := congrArg (fun s : Finset (Fin n) ↦ i ∈ s) hset
  have hi' := hmem.mp (hsubset hi)
  have hall : ∀ t, (P t).eval (domain i) = values t i := by
    simpa only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      using hi'
  exact hall t

private theorem interleaved_powerProjectionBadArbitrary_finset_card_le
    [Infinite F]
    {ι : Type} [Fintype ι] {agreement exceptionalCount width ℓ : ℕ}
    (C : ModuleCode ι F F) (hwidth : 0 < width)
    (hscalar : ∀ values : Fin (ℓ + 1) → ι → F,
      ∃ exceptional : Finset F, exceptional.card ≤ exceptionalCount ∧
        ∀ z, powerProjectionBadArbitrary C agreement z values → z ∈ exceptional)
    (values : Fin (ℓ + 1) → ι → Fin width → F)
    (s : Finset F)
    (hs : ∀ z ∈ s,
      powerProjectionBadArbitrary (C ^⋈ (Fin width)) agreement z values) :
    s.card ≤ exceptionalCount := by
  classical
  let : Nonempty (Fin width) := Fin.pos_iff_nonempty.mp hwidth
  obtain ⟨T, hT⟩ : ∃ T : F → Finset ι, ∀ z ∈ s,
      agreement ≤ (T z).card ∧
      projectedWord (fun i ↦ ∑ t, z ^ t.val • values t i) (T z) ∈
        projectedCodeSubmod (C ^⋈ (Fin width)) (T z) ∧
      ∃ t, projectedWord (values t) (T z) ∉
        projectedCodeSubmod (C ^⋈ (Fin width)) (T z) := by
    choose! T hT using fun z (hz : z ∈ s) => hs z hz
    exact ⟨T, hT⟩
  let rowComb (l : Fin width → F) (t : Fin (ℓ + 1)) : ι → F := fun i ↦
    ∑ j, l j * values t i j
  let K (z : F) : Submodule F (Fin width → F) := {
    carrier := {l | ∀ t,
      projectedWord (rowComb l t) (T z) ∈ projectedCodeSubmod C (T z)}
    zero_mem' := by
      intro t
      have hz : projectedWord (rowComb 0 t) (T z) = 0 := by
        ext i
        simp [projectedWord, rowComb]
      rw [hz]
      exact (projectedCodeSubmod C (T z)).zero_mem
    add_mem' := by
      intro l l' hl hl' t
      have hadd : projectedWord (rowComb (l + l') t) (T z) =
          projectedWord (rowComb l t) (T z) + projectedWord (rowComb l' t) (T z) := by
        ext i
        simp [projectedWord, rowComb, add_mul, Finset.sum_add_distrib]
      rw [hadd]
      exact (projectedCodeSubmod C (T z)).add_mem (hl t) (hl' t)
    smul_mem' := by
      intro a l hl t
      have hsmul : projectedWord (rowComb (a • l) t) (T z) =
          a • projectedWord (rowComb l t) (T z) := by
        ext i
        simp [projectedWord, rowComb, Finset.mul_sum, mul_assoc]
      rw [hsmul]
      exact (projectedCodeSubmod C (T z)).smul_mem a (hl t) }
  have hK (z : F) (hz : z ∈ s) : K z ≠ ⊤ := by
    obtain ⟨t, ht⟩ := (hT z hz).2.2
    have ht' : ∃ j : Fin width,
        projectedWord (fun i ↦ values t i j) (T z) ∉ projectedCodeSubmod C (T z) := by
      by_contra hall
      push Not at hall
      apply ht
      exact (projectedCodeSubmod_moduleInterleavedCode_iff F F (Fin width) ι
        C (values t) (T z)).mpr hall
    obtain ⟨j, hj⟩ := ht'
    intro htop
    let e : Fin width → F := fun j' ↦ if j' = j then 1 else 0
    have he : e ∈ K z := by rw [htop]; exact Submodule.mem_top
    apply hj
    have hrow := he t
    convert hrow using 1
    ext i
    change values t (i : ι) j = ∑ j', e j' * values t (i : ι) j'
    simp [e]
  let p : {z // z ∈ s} → Submodule F (Fin width → F) := fun z ↦ K z
  have hp : ∀ z, p z ≠ ⊤ := fun z ↦ hK z z.property
  obtain ⟨l, hl⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  have hl' : ∀ z ∈ s, l ∉ K z := fun z hz ↦ hl ⟨z, hz⟩
  have himp : ∀ z ∈ s,
      powerProjectionBadArbitrary C agreement z (rowComb l) := by
    intro z hz
    have hd := hT z hz
    refine ⟨T z, hd.1, ?_, ?_⟩
    · let batched : InterleavedWord F (Fin width) ι := fun i j ↦
        ∑ t, z ^ t.val * values t i j
      have hbatched : (fun i ↦ ∑ t, z ^ t.val • values t i) = batched := by
        funext i j
        simp [batched]
      have hroot : projectedWord batched (T z) ∈
          projectedCodeSubmod (C ^⋈ (Fin width)) (T z) := by
        rw [← hbatched]
        exact hd.2.1
      have hrows : ∀ j : Fin width,
          projectedWord (fun i ↦ ∑ t, z ^ t.val • values t i j) (T z) ∈
            projectedCodeSubmod C (T z) := by
        intro j
        have hj := (projectedCodeSubmod_moduleInterleavedCode_iff F F (Fin width) ι C
          batched (T z)).mp hroot j
        convert hj using 1
        ext i
        change (∑ t, z ^ t.val * values t (i : ι) j) = batched (i : ι) j
        rfl
      rw [mem_projectedCodeSubmod_iff]
      convert projectedCode_linearCombination C (T z)
        (fun j i ↦ ∑ t, z ^ t.val • values t i j) l
        (fun j ↦ (mem_projectedCodeSubmod_iff C (T z) _).mp (hrows j)) using 1
      ext i
      change ∑ t, z ^ t.val * (∑ j, l j * values t i j) =
        ∑ j, l j * (∑ t, z ^ t.val * values t i j)
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · have hnot := hl' z hz
      change ¬ ∀ t, projectedWord (rowComb l t) (T z) ∈
        projectedCodeSubmod C (T z) at hnot
      push Not at hnot
      exact hnot
  obtain ⟨exceptional, hcard, hexceptional⟩ := hscalar (rowComb l)
  exact (Finset.card_le_card fun z hz ↦ hexceptional z (himp z hz)).trans hcard

private theorem interleaved_powerProjectionBadArbitrary_exceptional
    [Infinite F] [DecidableEq F]
    {n k agreement exceptionalCount width ℓ : ℕ}
    (domain : Fin n ↪ F)
    (hscalar : ∀ values : Fin (ℓ + 1) → Fin n → F,
      UniformExactPowerAgreement domain values k agreement exceptionalCount)
    (hwidth : 0 < width)
    (values : Fin (ℓ + 1) → Fin n → Fin width → F) :
    ∃ exceptional : Finset F, exceptional.card ≤ exceptionalCount ∧
      ∀ z, powerProjectionBadArbitrary ((code domain k) ^⋈ (Fin width))
        agreement z values → z ∈ exceptional := by
  classical
  have hscalar' : ∀ scalarValues : Fin (ℓ + 1) → Fin n → F,
      ∃ exceptional : Finset F, exceptional.card ≤ exceptionalCount ∧
        ∀ z, powerProjectionBadArbitrary (code domain k) agreement z scalarValues →
          z ∈ exceptional := by
    intro scalarValues
    obtain ⟨exceptional, hcard, hgood⟩ := hscalar scalarValues
    exact ⟨exceptional, hcard, fun z hz ↦
      scalar_powerProjectionBadArbitrary_mem_exceptional domain scalarValues exceptional hgood hz⟩
  let isBad (z : F) := powerProjectionBadArbitrary ((code domain k) ^⋈ (Fin width))
    agreement z values
  have hfiniteFamily (s : Finset F) (hs : ∀ z ∈ s, isBad z) :
      s.card ≤ exceptionalCount :=
    interleaved_powerProjectionBadArbitrary_finset_card_le (code domain k) hwidth
      hscalar' values s hs
  let badSet : Set F := {z | isBad z}
  have hbadFinite : badSet.Finite := by
    by_contra hnot
    have hinfinite : badSet.Infinite := hnot
    obtain ⟨s, hs, hcard⟩ := hinfinite.exists_subset_card_eq (exceptionalCount + 1)
    have hle := hfiniteFamily s (fun z hz ↦ hs hz)
    omega
  let exceptional := hbadFinite.toFinset
  refine ⟨exceptional, ?_, ?_⟩
  · apply hfiniteFamily
    intro z hz
    simpa [exceptional, badSet] using hz
  · intro z hz
    simpa [exceptional, badSet] using hz

private theorem exactInterleavedPowerAgreement_of_not_projectionBad
    [DecidableEq F]
    {n k agreement width ℓ : ℕ}
    (domain : Fin n ↪ F) (hwidth : 0 < width) (hkAgreement : k ≤ agreement)
    (values : Fin (ℓ + 1) → Fin n → Fin width → F)
    (z : F)
    (hgood : ¬ powerProjectionBadArbitrary ((code domain k) ^⋈ (Fin width))
      agreement z values)
    (Q : Fin width → F[X]) (hQdegree : ∀ j, (Q j).degree < k)
    (hagreement : agreement ≤
      (interleavedPolynomialAgreementSet domain
        (interleavedPowerBatchedWord values z) Q).card) :
    HasExactInterleavedPowerAgreement domain values k z Q := by
  classical
  let : Nonempty (Fin width) := Fin.pos_iff_nonempty.mp hwidth
  let S := interleavedPolynomialAgreementSet domain
    (interleavedPowerBatchedWord values z) Q
  let c : Fin n → Fin width → F := fun i j ↦ (Q j).eval (domain i)
  have hc : c ∈ ModuleCode.moduleInterleavedCode F F (Fin width) (Fin n)
      (code domain k) := by
    apply (mem_moduleInterleavedCode_iff F F (Fin width) (Fin n)
      (code domain k) c).mpr
    intro j
    exact evalOnPoints_mem_code_of_degree_lt (hQdegree j)
  have hroot : projectedWord (interleavedPowerBatchedWord values z) S ∈
      projectedCodeSubmod ((code domain k) ^⋈ (Fin width)) S := by
    rw [mem_projectedCodeSubmod_iff]
    refine ⟨c, hc, ?_⟩
    funext i
    funext j
    exact ((Finset.mem_filter.mp i.property).2 j).symm
  have hconstituents : ∀ t,
      projectedWord (values t) S ∈
        projectedCodeSubmod ((code domain k) ^⋈ (Fin width)) S := by
    by_contra h
    push Not at h
    obtain ⟨t, ht⟩ := h
    apply hgood
    refine ⟨S, hagreement, ?_, t, ht⟩
    convert hroot using 1
    ext i j
    change (∑ t, z ^ t.val • values t (i : Fin n)) j =
      ∑ t, z ^ t.val * values t (i : Fin n) j
    simp
  choose cP hcP hcPS using fun t ↦
    (mem_projectedCodeSubmod_iff _ S _).mp (hconstituents t)
  let P : Fin (ℓ + 1) → Fin width → F[X] := fun t j ↦
    Classical.choose (mem_code_iff_eval.mp
      ((mem_moduleInterleavedCode_iff F F (Fin width) (Fin n)
        (code domain k) (cP t)).mp (hcP t) j))
  have hPdegree (t) (j) : (P t j).degree < k :=
    (Classical.choose_spec (mem_code_iff_eval.mp
      ((mem_moduleInterleavedCode_iff F F (Fin width) (Fin n)
        (code domain k) (cP t)).mp (hcP t) j))).1
  have hPeval (t) (j) (i) : (P t j).eval (domain i) = cP t i j :=
    (Classical.choose_spec (mem_code_iff_eval.mp
      ((mem_moduleInterleavedCode_iff F F (Fin width) (Fin n)
        (code domain k) (cP t)).mp (hcP t) j))).2 i
  let combined : Fin n → Fin width → F := fun i j ↦ ∑ t, z ^ t.val * cP t i j
  have hcombined : combined ∈ ModuleCode.moduleInterleavedCode F F (Fin width) (Fin n)
      (code domain k) := by
    rw [show combined = ∑ t, (z ^ t.val) • cP t by
      funext i j
      simp [combined]]
    apply Submodule.sum_mem
    intro t _
    exact (ModuleCode.moduleInterleavedCode F F (Fin width) (Fin n)
      (code domain k)).smul_mem (z ^ t.val) (hcP t)
  have hcEq : c = combined := by
    apply interleavedCodeword_eq_of_agree_on domain S
      (hkAgreement.trans hagreement) hc hcombined
    intro i hi
    apply _root_.funext
    intro j
    have hci := (Finset.mem_filter.mp hi).2 j
    change (Q j).eval (domain i) = ∑ t, z ^ t.val * cP t i j
    rw [hci]
    apply Finset.sum_congr rfl
    intro t _
    have hti := congrFun (hcPS t) ⟨i, hi⟩
    change values t i = cP t i at hti
    rw [congrFun hti j]
  have hQidentity (j) : Q j = powerBatchedPolynomial (fun t ↦ P t j) z := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := S) domain.injective.injOn
      (hQdegree j |>.trans_le (by exact_mod_cast hkAgreement.trans hagreement))
      ((powerBatchedPolynomial_degree_lt (fun t ↦ P t j) z k
        (fun t ↦ hPdegree t j)).trans_le (by exact_mod_cast hkAgreement.trans hagreement))
    intro i hi
    rw [powerBatchedPolynomial_eval]
    have hcEqAt := congrFun (congrFun hcEq i) j
    change (Q j).eval (domain i) = combined i j at hcEqAt
    rw [hcEqAt]
    apply Finset.sum_congr rfl
    intro t _
    rw [hPeval]
  refine ⟨P, hPdegree, hQidentity, ?_⟩
  ext i
  simp only [interleavedPolynomialAgreementSet, interleavedCommonPowerAgreementSet,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi t j
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    have ht := congrFun (hcPS t) ⟨i, hiS⟩
    change values t i = cP t i at ht
    rw [hPeval, ← congrFun ht j]
  · intro hi j
    rw [hQidentity]
    rw [powerBatchedPolynomial_eval]
    apply Finset.sum_congr rfl
    intro t _
    rw [hi t j]

/-- A scalar uniform exact-power certificate lifts, over an arbitrary field, to every nonempty
row-wise interleaving without increasing its exceptional count. -/
theorem uniformExactInterleavedPowerAgreement_of_scalar_arbitrary
    [DecidableEq F]
    {n k agreement exceptionalCount width ℓ : ℕ}
    (domain : Fin n ↪ F)
    (hscalar : ∀ values : Fin (ℓ + 1) → Fin n → F,
      UniformExactPowerAgreement domain values k agreement exceptionalCount)
    (hwidth : 0 < width) (hkAgreement : k ≤ agreement)
    (values : Fin (ℓ + 1) → Fin n → Fin width → F) :
    UniformExactInterleavedPowerAgreement domain values k agreement exceptionalCount := by
  classical
  obtain hfinite | hinfinite := finite_or_infinite F
  · let _ : Finite F := hfinite
    exact uniformExactInterleavedPowerAgreement_of_scalar domain hscalar hwidth hkAgreement values
  · let _ : Infinite F := hinfinite
    obtain ⟨exceptional, hcard, hexceptional⟩ :=
      interleaved_powerProjectionBadArbitrary_exceptional domain hscalar hwidth values
    refine ⟨exceptional, hcard, ?_⟩
    intro z hz Q hQdegree hagreement
    apply exactInterleavedPowerAgreement_of_not_projectionBad domain hwidth hkAgreement
      values z _ Q hQdegree hagreement
    intro hbad
    exact hz (hexceptional z hbad)

end ReedSolomon
