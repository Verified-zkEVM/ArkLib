/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.LargeAlphabet.Basic

/-!
# Large-alphabet barrier: separated subcodes, centres, and incidence counting

Greedy extraction of a large *separated* subcode
(`greedy_separated_extraction`), the construction of a Hamming centre from disjoint agreement
blocks (`hamming_center_from_disjoint_blocks`, `balanced_center_construction`,
`barrier_center_from_blocks`), the incidence double-counting lemmas that drive the moment bound, and
the core of the rounded-barrier codeword bound.

See `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean` for the family overview and the
references, and `Bounds/LargeAlphabet.lean` for the two theorems this development serves.
-/

-- All three are load-bearing, verified by removing them and rebuilding: the statements below carry
-- `[Fintype ι]` / `[DecidableEq F]` and section variables that their *proofs* do not use, which the
-- corresponding linters each report.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open Code

namespace LargeAlphabetBarrier

/-- **Greedy extraction of a separated subcode.** If every ball of radius `d` around a codeword
holds at most `B` codewords, then `C` has a `(d+1)`-separated subset `D` with `|C| ≤ B · |D|`. -/
theorem greedy_separated_extraction :
    ∀ {ι A : Type} [Fintype ι] [DecidableEq A]
      (C : Set (ι → A)) (d B : ℕ), C.Finite →
      (∀ c ∈ C,
        ({x : ι → A | x ∈ C ∧ hammingDist c x ≤ d} : Set (ι → A)).ncard ≤ B) →
      ∃ D : Set (ι → A), D ⊆ C ∧ D.Finite ∧ separated D (d + 1) ∧
        C.ncard ≤ B * D.ncard := by
  classical
  intro ι A _ _ C d B hC hlocal
  let s := hC.toFinset
  have hsC : (s : Set (ι → A)) = C := hC.coe_toFinset
  have aux : ∀ s : Finset (ι → A), (s : Set (ι → A)) ⊆ C →
      ∃ t : Finset (ι → A), t ⊆ s ∧ separated (t : Set (ι → A)) (d + 1) ∧
        s.card ≤ B * t.card := by
    apply Finset.strongInduction
    intro u ih huC
    by_cases hu : u = ∅
    · subst u
      refine ⟨∅, by simp, ?_, by simp⟩
      simp only [separated]
      intro x hx
      simp at hx
    · obtain ⟨c, hcu⟩ := Finset.nonempty_iff_ne_empty.mpr hu
      let N : Finset (ι → A) := u.filter fun x => hammingDist c x ≤ d
      let r : Finset (ι → A) := u \ N
      have hcN : c ∈ N := by
        simp only [N, Finset.mem_filter, hcu, true_and]
        simp only [hammingDist_self, zero_le]
      have hNsub : N ⊆ u := by
        intro x hx
        exact (Finset.mem_filter.mp hx).1
      have hrproper : r ⊂ u := by
        exact Finset.sdiff_ssubset hNsub ⟨c, hcN⟩
      have hrC : (r : Set (ι → A)) ⊆ C := by
        intro x hx
        exact huC (Finset.sdiff_subset hx)
      obtain ⟨t, htr, hsep, hcard⟩ := ih r hrproper hrC
      have hNset : (N : Set (ι → A)) ⊆
          {x : ι → A | x ∈ C ∧ hammingDist c x ≤ d} := by
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        exact ⟨huC hx'.1, hx'.2⟩
      have hbigfin :
          ({x : ι → A | x ∈ C ∧ hammingDist c x ≤ d} : Set (ι → A)).Finite :=
        hC.subset fun x hx => hx.1
      have hNcard : N.card ≤ B := by
        rw [← Set.ncard_coe_finset]
        exact (Set.ncard_le_ncard hNset hbigfin).trans (hlocal c (huC hcu))
      have hct : c ∉ t := by
        intro hct
        have hcr := htr hct
        exact (Finset.mem_sdiff.mp hcr).2 hcN
      refine ⟨insert c t, ?_, ?_, ?_⟩
      · exact Finset.insert_subset_iff.mpr
          ⟨hcu, htr.trans Finset.sdiff_subset⟩
      · intro x hx y hy hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
        rcases hx with hxc | hx
        · subst x
          rcases hy with hyc | hy
          · subst y
            exact (hxy rfl).elim
          · have hyr := htr hy
            have hyn := (Finset.mem_sdiff.mp hyr).2
            have hnot : ¬hammingDist c y ≤ d := by
              intro hle
              apply hyn
              simp only [N, Finset.mem_filter]
              exact ⟨Finset.sdiff_subset hyr, hle⟩
            omega
        · rcases hy with hyc | hy
          · subst y
            have hxr := htr hx
            have hxn := (Finset.mem_sdiff.mp hxr).2
            have hnot : ¬hammingDist c x ≤ d := by
              intro hle
              apply hxn
              simp only [N, Finset.mem_filter]
              exact ⟨Finset.sdiff_subset hxr, hle⟩
            rw [hammingDist_comm]
            omega
          · exact hsep hx hy hxy
      · have hpart := Finset.card_sdiff_add_card_eq_card hNsub
        have hins := Finset.card_insert_of_notMem hct
        change r.card + N.card = u.card at hpart
        rw [hins]
        calc
          u.card = r.card + N.card := hpart.symm
          _ ≤ B * t.card + B := Nat.add_le_add hcard hNcard
          _ = B * (t.card + 1) := by rw [Nat.mul_add, Nat.mul_one]
  obtain ⟨t, hts, hsep, hcard⟩ := aux s (by
    intro x hx
    rw [← hsC]
    exact hx)
  refine ⟨(t : Set (ι → A)), ?_, Set.toFinite _, hsep, ?_⟩
  · intro x hx
    rw [← hsC]
    exact hts hx
  · rw [← hsC, Set.ncard_coe_finset, Set.ncard_coe_finset]
    exact hcard

theorem hamming_center_from_disjoint_blocks
    (ℓ r r' t : ℕ)
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (c : ι → A) (v : Fin ℓ → ι → A) (S : Finset ι)
    (blocks : Fin ℓ → Finset ι)
    (hblocks_sub : ∀ j, blocks j ⊆ S)
    (hblocks_card : ∀ j, (blocks j).card = t)
    (hblocks_disjoint : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (hcommon : ∀ i ∈ S, ∀ j, c i ≠ v j i)
    (hdist : ∀ j, hammingDist c (v j) ≤ r')
    (hcenter : ℓ * t ≤ r) (hother : r' - t ≤ r) :
    ∃ y : ι → A,
      hammingDist c y ≤ r ∧ ∀ j, hammingDist (v j) y ≤ r := by
  classical
  let U : Finset ι := Finset.univ.biUnion blocks
  have hUexists : ∀ i ∈ U, ∃ j, i ∈ blocks j := by
    intro i hi
    simpa only [U, Finset.mem_biUnion, Finset.mem_univ, true_and] using hi
  let owner : {i : ι // i ∈ U} → Fin ℓ := fun i =>
    Classical.choose (hUexists i i.property)
  have howner_mem : ∀ i : {i : ι // i ∈ U}, i.1 ∈ blocks (owner i) := by
    intro i
    exact Classical.choose_spec (hUexists i i.property)
  have howner_eq : ∀ (i : {i : ι // i ∈ U}) (j : Fin ℓ),
      i.1 ∈ blocks j → owner i = j := by
    intro i j hij
    by_contra hne
    exact (Finset.disjoint_left.mp
      (hblocks_disjoint (owner i) j hne)) (howner_mem i) hij
  let y : ι → A := fun i =>
    if hi : i ∈ U then v (owner ⟨i, hi⟩) i else c i
  have hy_block : ∀ (j : Fin ℓ) {i : ι}, i ∈ blocks j → y i = v j i := by
    intro j i hij
    have hiU : i ∈ U := by
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hij⟩
    rw [show y i = v (owner ⟨i, hiU⟩) i by simp only [y, dif_pos hiU]]
    rw [howner_eq ⟨i, hiU⟩ j hij]
  have hpair :
      ((Finset.univ : Finset (Fin ℓ)) : Set (Fin ℓ)).PairwiseDisjoint blocks := by
    intro i hi j hj hij
    exact hblocks_disjoint i j hij
  have hUcard : U.card = ℓ * t := by
    dsimp only [U]
    rw [Finset.card_biUnion hpair]
    simp only [hblocks_card, Finset.sum_const_nat, Finset.card_univ,
      Fintype.card_fin]
  refine ⟨y, ?_, ?_⟩
  · unfold hammingDist
    have hsub : (Finset.univ.filter fun i => c i ≠ y i) ⊆ U := by
      intro i hi
      have hneq := (Finset.mem_filter.mp hi).2
      by_contra hiU
      have hyc : y i = c i := by simp only [y, dif_neg hiU]
      exact hneq hyc.symm
    exact (Finset.card_le_card hsub).trans (hUcard ▸ hcenter)
  · intro j
    let D : Finset ι := Finset.univ.filter fun i => v j i ≠ c i
    have hblockD : blocks j ⊆ D := by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hcommon i (hblocks_sub j hi) j).symm⟩
    have hsub : (Finset.univ.filter fun i => v j i ≠ y i) ⊆ D \ blocks j := by
      intro i hi
      have hneq := (Finset.mem_filter.mp hi).2
      apply Finset.mem_sdiff.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        by_cases hiU : i ∈ U
        · exact (hcommon i (hblocks_sub (owner ⟨i, hiU⟩)
            (howner_mem ⟨i, hiU⟩)) j).symm
        · have hyc : y i = c i := by simp only [y, dif_neg hiU]
          exact fun heq => hneq (heq.trans hyc.symm)
      · intro hij
        exact hneq (hy_block j hij).symm
    have hDle : D.card ≤ r' := by
      change hammingDist (v j) c ≤ r'
      rw [hammingDist_comm]
      exact hdist j
    unfold hammingDist
    calc
      (Finset.univ.filter fun i => v j i ≠ y i).card ≤
          (D \ blocks j).card := Finset.card_le_card hsub
      _ = D.card - (blocks j).card := Finset.card_sdiff_of_subset hblockD
      _ = D.card - t := by rw [hblocks_card]
      _ ≤ r' - t := Nat.sub_le_sub_right hDle t
      _ ≤ r := hother

/-- **Balanced centre from `ℓ` nearby codewords.** If `c` and `v 1, …, v ℓ` are pairwise within the
boosted radius and they disagree with `c` on a large common set, then some single word `y` is within
radius `p` of all of them — so the point list at `y` has `ℓ + 1` members. -/
theorem balanced_center_construction :
    ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (p : ℝ), 0 < p → p < 1 →
      ∀ {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
        (c : ι → A) (v : Fin ℓ → ι → A),
        (∀ j, hammingDist c (v j) ≤
          Nat.floor (boostedRadius ℓ p * Fintype.card ι)) →
        8 * (ℓ : ℝ) ≤ p ^ ℓ * Fintype.card ι →
        Nat.ceil ((3 * p ^ ℓ / 4) * Fintype.card ι) ≤
          ({i : ι | ∀ j, c i ≠ v j i} : Set ι).ncard →
        ∃ y : ι → A,
          hammingDist c y ≤ Nat.floor (p * Fintype.card ι) ∧
          ∀ j, hammingDist (v j) y ≤ Nat.floor (p * Fintype.card ι) := by
  classical
  intro ℓ hℓ p hp hp_lt ι A _ _ _ c v hdist hsize hcommonCard
  let n := Fintype.card ι
  let r := Nat.floor (p * n)
  let r' := Nat.floor (boostedRadius ℓ p * n)
  let t := r' - r
  have harith := balanced_center_arithmetic ℓ p n hℓ hp hp_lt (by
    simpa only [n] using hsize)
  rcases harith with ⟨hrle, hcancel, ht_center, ht_common⟩
  let S : Finset ι := Finset.univ.filter fun i => ∀ j, c i ≠ v j i
  have hScoe : (S : Set ι) = {i : ι | ∀ j, c i ≠ v j i} := by
    ext i
    simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  have hScard : S.card = ({i : ι | ∀ j, c i ≠ v j i} : Set ι).ncard := by
    rw [← Set.ncard_coe_finset, hScoe]
  have hblocksSize : ℓ * t ≤ S.card := by
    calc
      ℓ * t ≤ Nat.ceil ((3 * p ^ ℓ / 4) * n) := ht_common
      _ ≤ ({i : ι | ∀ j, c i ≠ v j i} : Set ι).ncard := by
        simpa only [n] using hcommonCard
      _ = S.card := hScard.symm
  obtain ⟨blocks, hblocks_sub, hblocks_card, hblocks_disjoint⟩ :=
    disjoint_equal_blocks S ℓ t hblocksSize
  obtain ⟨y, hyc, hyv⟩ := hamming_center_from_disjoint_blocks
    ℓ r r' t c v S blocks hblocks_sub hblocks_card hblocks_disjoint
    (by
      intro i hi j
      exact (Finset.mem_filter.mp hi).2 j)
    (by
      intro j
      simpa only [r', n] using hdist j)
    ht_center hcancel.le
  refine ⟨y, ?_, ?_⟩
  · simpa only [r, n] using hyc
  · intro j
    simpa only [r, n] using hyv j

theorem hamming_dist_le_card_compl_of_agree
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (u v : ι → A) (S : Finset ι)
    (hagree : ∀ i ∈ S, u i = v i) :
    hammingDist u v ≤ Fintype.card ι - S.card := by
  unfold hammingDist
  have hsub : (Finset.univ.filter fun i => u i ≠ v i) ⊆
      Finset.univ \ S := by
    intro i hi
    have hne := (Finset.mem_filter.mp hi).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hiS
    exact hne (hagree i hiS)
  calc
    (Finset.univ.filter fun i => u i ≠ v i).card ≤
        (Finset.univ \ S).card := Finset.card_le_card hsub
    _ = Finset.univ.card - S.card :=
      Finset.card_sdiff_of_subset (Finset.subset_univ S)
    _ = Fintype.card ι - S.card := by
      rw [Finset.card_univ]

theorem alternative_fiber_bound
    (W aFamily aUnion n boosted : ℕ)
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (C : Set (ι → A)) (hn : Fintype.card ι = n)
    (family : LargeUnionFamily ι W aFamily aUnion)
    (c₀ : ι → A) (hc₀ : c₀ ∈ C)
    (alt : Finset ι → ι → A)
    (haltC : ∀ S ∈ family.sets, alt S ∈ C)
    (haltNe : ∀ S ∈ family.sets, alt S ≠ c₀)
    (hagree : ∀ S ∈ family.sets, ∀ i ∈ S, alt S i = c₀ i)
    (hsep : separated C boosted)
    (hgap : n - aUnion < boosted) (hW : 0 < W) :
    ∀ z, (family.sets.filter fun S => alt S = z).card < W := by
  classical
  intro z
  by_contra hnot
  have hWle : W ≤ (family.sets.filter fun S => alt S = z).card :=
    Nat.le_of_not_gt hnot
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hWle
  have hTsets : T ⊆ family.sets := by
    intro S hST
    exact (Finset.mem_filter.mp (hTsub hST)).1
  have hlarge := family.large_union T hTsets hTcard
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hTempty
    rw [hTempty] at hTcard
    simp only [Finset.card_empty] at hTcard
    omega
  obtain ⟨S₀, hS₀T⟩ := hTne
  have hS₀filter := Finset.mem_filter.mp (hTsub hS₀T)
  have hzC : z ∈ C := by
    rw [← hS₀filter.2]
    exact haltC S₀ hS₀filter.1
  have hzne : z ≠ c₀ := by
    intro hzc
    exact (haltNe S₀ hS₀filter.1) (hS₀filter.2.trans hzc)
  have hagreeUnion : ∀ i ∈ T.biUnion id, c₀ i = z i := by
    intro i hi
    rcases Finset.mem_biUnion.mp hi with ⟨S, hST, hiS⟩
    have hSfilter := Finset.mem_filter.mp (hTsub hST)
    have heq := hagree S hSfilter.1 i hiS
    rw [hSfilter.2] at heq
    exact heq.symm
  have hdist := hamming_dist_le_card_compl_of_agree c₀ z
    (T.biUnion id) hagreeUnion
  have hcomp : Fintype.card ι - (T.biUnion id).card ≤ n - aUnion := by
    rw [hn]
    exact Nat.sub_le_sub_left hlarge n
  have hdistlt : hammingDist c₀ z < boosted :=
    (hdist.trans hcomp).trans_lt hgap
  have hdistge := hsep hc₀ hzC hzne.symm
  omega

theorem barrier_center_from_blocks
    (ℓ n dZero dOne aFamily : ℕ)
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (hn : Fintype.card ι = n)
    (blocks : CoordinateBlocks ι ℓ dZero dOne)
    (c₀ : ι → A) (chosen : Fin ℓ → Finset ι)
    (u : Fin ℓ → ι → A) (common : blocks.zero → A)
    (hcard : ∀ j, (chosen j).card = aFamily)
    (hdisjoint : ∀ j, Disjoint (chosen j) blocks.zero ∧
      ∀ k, Disjoint (chosen j) (blocks.other k))
    (hagree : ∀ j, ∀ i ∈ chosen j, u j i = c₀ i)
    (hzero : ∀ j, ∀ i, ∀ hi : i ∈ blocks.zero,
      u j i = common ⟨i, hi⟩) :
    ∃ y : ι → A,
      hammingDist c₀ y ≤ dZero + ℓ * dOne ∧
      ∀ j, hammingDist (u j) y ≤ n - dZero - dOne - aFamily := by
  classical
  let U : Finset ι := Finset.univ.biUnion blocks.other
  have hUexists : ∀ i ∈ U, ∃ j, i ∈ blocks.other j := by
    intro i hi
    simpa only [U, Finset.mem_biUnion, Finset.mem_univ, true_and] using hi
  let owner : {i : ι // i ∈ U} → Fin ℓ := fun i =>
    Classical.choose (hUexists i i.property)
  have howner_mem : ∀ i : {i : ι // i ∈ U},
      i.1 ∈ blocks.other (owner i) := by
    intro i
    exact Classical.choose_spec (hUexists i i.property)
  have howner_eq : ∀ (i : {i : ι // i ∈ U}) (j : Fin ℓ),
      i.1 ∈ blocks.other j → owner i = j := by
    intro i j hij
    by_contra hne
    exact (Finset.disjoint_left.mp
      (blocks.other_disjoint (owner i) j hne)) (howner_mem i) hij
  let y : ι → A := fun i =>
    if hi0 : i ∈ blocks.zero then common ⟨i, hi0⟩
    else if hiU : i ∈ U then u (owner ⟨i, hiU⟩) i else c₀ i
  have hyzero : ∀ (j : Fin ℓ) {i : ι}, i ∈ blocks.zero → y i = u j i := by
    intro j i hi
    rw [show y i = common ⟨i, hi⟩ by simp only [y, dif_pos hi]]
    exact (hzero j i hi).symm
  have hyother : ∀ (j : Fin ℓ) {i : ι},
      i ∈ blocks.other j → y i = u j i := by
    intro j i hi
    have hi0 : i ∉ blocks.zero := by
      intro hiz
      exact (Finset.disjoint_left.mp (blocks.zero_disjoint j)) hiz hi
    have hiU : i ∈ U :=
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩
    rw [show y i = u (owner ⟨i, hiU⟩) i by
      simp only [y, dif_neg hi0, dif_pos hiU]]
    rw [howner_eq ⟨i, hiU⟩ j hi]
  have hpair :
      ((Finset.univ : Finset (Fin ℓ)) : Set (Fin ℓ)).PairwiseDisjoint
        blocks.other := by
    intro i hi j hj hij
    exact blocks.other_disjoint i j hij
  have hzeroU : Disjoint blocks.zero U := by
    rw [Finset.disjoint_left]
    intro x hxzero hxU
    rcases Finset.mem_biUnion.mp hxU with ⟨j, hj, hxj⟩
    exact (Finset.disjoint_left.mp (blocks.zero_disjoint j)) hxzero hxj
  have hUcard : U.card = ℓ * dOne := by
    dsimp only [U]
    rw [Finset.card_biUnion hpair]
    simp only [blocks.card_other, Finset.sum_const_nat,
      Finset.card_univ, Fintype.card_fin]
  have husedCard : (blocks.zero ∪ U).card = dZero + ℓ * dOne := by
    rw [Finset.card_union_of_disjoint hzeroU, blocks.card_zero, hUcard]
  refine ⟨y, ?_, ?_⟩
  · unfold hammingDist
    have hsub : (Finset.univ.filter fun i => c₀ i ≠ y i) ⊆
        blocks.zero ∪ U := by
      intro i hi
      have hne := (Finset.mem_filter.mp hi).2
      by_contra hnot
      have hi0 : i ∉ blocks.zero := fun h =>
        hnot (Finset.mem_union_left U h)
      have hiU : i ∉ U := fun h =>
        hnot (Finset.mem_union_right blocks.zero h)
      have hy : y i = c₀ i := by simp only [y, dif_neg hi0, dif_neg hiU]
      exact hne hy.symm
    exact (Finset.card_le_card hsub).trans_eq husedCard
  · intro j
    let E : Finset ι := (blocks.zero ∪ blocks.other j) ∪ chosen j
    have hzo : Disjoint blocks.zero (blocks.other j) :=
      blocks.zero_disjoint j
    have hzoChosen : Disjoint (blocks.zero ∪ blocks.other j) (chosen j) := by
      rw [Finset.disjoint_left]
      intro x hx hxs
      rcases Finset.mem_union.mp hx with hx0 | hxj
      · exact (Finset.disjoint_left.mp (hdisjoint j).1) hxs hx0
      · exact (Finset.disjoint_left.mp ((hdisjoint j).2 j)) hxs hxj
    have hEcard : E.card = dZero + dOne + aFamily := by
      dsimp only [E]
      rw [Finset.card_union_of_disjoint hzoChosen,
        Finset.card_union_of_disjoint hzo, blocks.card_zero,
        blocks.card_other, hcard]
    have hagreeE : ∀ i ∈ E, u j i = y i := by
      intro i hi
      rcases Finset.mem_union.mp hi with hblock | hchosen
      · rcases Finset.mem_union.mp hblock with hzeroMem | hotherMem
        · exact (hyzero j hzeroMem).symm
        · exact (hyother j hotherMem).symm
      · have hi0 : i ∉ blocks.zero := by
          intro hi
          exact (Finset.disjoint_left.mp (hdisjoint j).1) hchosen hi
        have hiU : i ∉ U := by
          intro hi
          rcases Finset.mem_biUnion.mp hi with ⟨k, hk, hik⟩
          exact (Finset.disjoint_left.mp ((hdisjoint j).2 k)) hchosen hik
        have hy : y i = c₀ i := by simp only [y, dif_neg hi0, dif_neg hiU]
        exact (hagree j i hchosen).trans hy.symm
    have hd := hamming_dist_le_card_compl_of_agree (u j) y E hagreeE
    rw [hn, hEcard] at hd
    simpa only [Nat.sub_sub] using hd

/-- Double counting `ℓ`-subsets of set-indices against coordinates:
`∑ᵢ C(incidence i, ℓ) = ∑_{|J| = ℓ} |{i : i ∈ S j for all j ∈ J}|`. -/
theorem incidence_double_count :
    ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (ℓ : ℕ) (S : κ → Finset ι),
      let incidence : ι → ℕ := fun i => (Finset.univ.filter fun j => i ∈ S j).card
      let common : Finset κ → Finset ι := fun J =>
        Finset.univ.filter fun i => ∀ j ∈ J, i ∈ S j
      ∑ i, Nat.choose (incidence i) ℓ =
        ∑ J ∈ Finset.univ.powersetCard ℓ, (common J).card := by
  classical
  intro ι κ _ _ _ _ ℓ S
  dsimp
  calc
    (∑ i, Nat.choose ((Finset.univ.filter fun j => i ∈ S j).card) ℓ) =
        ∑ i, ((Finset.univ.filter fun j => i ∈ S j).powersetCard ℓ).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.card_powersetCard ℓ _).symm
    _ = ∑ i, ∑ J ∈ Finset.univ.powersetCard ℓ,
          if J ⊆ Finset.univ.filter (fun j => i ∈ S j) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.card_filter]
      congr 1
      ext J
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
        true_and]
      constructor
      · rintro ⟨hsub, hcard⟩
        exact ⟨hcard, hsub⟩
      · rintro ⟨hcard, hsub⟩
        exact ⟨hsub, hcard⟩
    _ = ∑ J ∈ Finset.univ.powersetCard ℓ, ∑ i,
          if J ⊆ Finset.univ.filter (fun j => i ∈ S j) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ J ∈ Finset.univ.powersetCard ℓ,
          (Finset.univ.filter fun i => ∀ j ∈ J, i ∈ S j).card := by
      apply Finset.sum_congr rfl
      intro J hJ
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      simp only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The numeric slack the moment bound needs: `(3p^ℓ/4) · M^ℓ ≤ (p·M − (ℓ−1))^ℓ` once
`M ≥ ⌈4ℓ²/p⌉`. -/
theorem incidence_power_gap :
    ∀ (ℓ M : ℕ) (p : ℝ), 2 ≤ ℓ → 0 < p →
      Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M →
      (3 * p ^ ℓ / 4) * (M : ℝ) ^ ℓ ≤
        (p * M - (ℓ - 1)) ^ ℓ := by
  intro ℓ M p hℓ hp hM
  have hℓR : (0 : ℝ) < ℓ := by
    exact_mod_cast (show 0 < ℓ by omega)
  have hℓtwo : (2 : ℝ) ≤ ℓ := by
    exact_mod_cast hℓ
  have hsize : 4 * (ℓ : ℝ) ^ 2 / p ≤ (M : ℝ) :=
    (Nat.ceil_le).mp hM
  have hpm : 4 * (ℓ : ℝ) ^ 2 ≤ p * M := by
    simpa only [mul_comm] using (div_le_iff₀ hp).mp hsize
  have hden : (0 : ℝ) < 4 * ℓ := by positivity
  have hratio : (ℓ : ℝ) - 1 ≤ p * M / (4 * ℓ) := by
    rw [le_div_iff₀ hden]
    have haux : 4 * (ℓ : ℝ) * ((ℓ : ℝ) - 1) ≤ 4 * (ℓ : ℝ) ^ 2 := by
      calc
        4 * (ℓ : ℝ) * ((ℓ : ℝ) - 1) ≤ 4 * (ℓ : ℝ) * ℓ :=
          mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one)
            (mul_nonneg (by norm_num) hℓR.le)
        _ = 4 * (ℓ : ℝ) ^ 2 := by ring
    exact (by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using haux.trans hpm)
  let q : ℝ := 1 - 1 / (4 * ℓ)
  have hone : 1 / (4 * (ℓ : ℝ)) ≤ 1 :=
    (div_le_one hden).2 (by nlinarith only [hℓtwo])
  have hq : 0 ≤ q := by simpa only [q] using sub_nonneg.mpr hone
  have hneg : (-2 : ℝ) ≤ -(1 / (4 * (ℓ : ℝ))) := by
    exact neg_le_neg (hone.trans (by norm_num))
  have hbern : (3 : ℝ) / 4 ≤ q ^ ℓ := by
    calc
      (3 : ℝ) / 4 =
          1 + (ℓ : ℝ) * (-(1 / (4 * (ℓ : ℝ)))) := by
        field_simp [ne_of_gt hℓR]
        ring
      _ ≤ (1 + -(1 / (4 * (ℓ : ℝ)))) ^ ℓ :=
        one_add_mul_le_pow hneg ℓ
      _ = q ^ ℓ := by congr 1
  have hpM : 0 ≤ p * (M : ℝ) := mul_nonneg hp.le (by positivity)
  have hbase : q * (p * M) ≤ p * M - ((ℓ : ℝ) - 1) := by
    calc
      q * (p * M) = p * M - p * M / (4 * ℓ) := by
        dsimp [q]
        ring
      _ ≤ p * M - ((ℓ : ℝ) - 1) :=
        sub_le_sub_left hratio _
  have hpow : (q * (p * M)) ^ ℓ ≤
      (p * M - ((ℓ : ℝ) - 1)) ^ ℓ :=
    pow_le_pow_left₀ (mul_nonneg hq hpM) hbase ℓ
  calc
    (3 * p ^ ℓ / 4) * (M : ℝ) ^ ℓ =
        ((3 : ℝ) / 4) * (p * M) ^ ℓ := by
      rw [mul_pow]
      ring
    _ ≤ q ^ ℓ * (p * M) ^ ℓ :=
      mul_le_mul_of_nonneg_right hbern (pow_nonneg hpM ℓ)
    _ = (q * (p * M)) ^ ℓ := by simp only [mul_pow]
    _ ≤ (p * M - ((ℓ : ℝ) - 1)) ^ ℓ := hpow

/-- Counting incidences two ways: `∑ᵢ #{j : i ∈ S j} = ∑_j |S j|`. -/
theorem incidence_sum_double_count :
    ∀ {ι κ : Type} [Fintype ι] [Fintype κ]
      [DecidableEq ι] [DecidableEq κ] (S : κ → Finset ι),
      ∑ i, (Finset.univ.filter fun j => i ∈ S j).card =
        ∑ j, (S j).card := by
  classical
  intro ι κ _ _ _ _ S
  calc
    (∑ i, (Finset.univ.filter fun j => i ∈ S j).card) =
        ∑ i, ∑ j, if i ∈ S j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.card_filter]
    _ = ∑ j, ∑ i, if i ∈ S j then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j, (S j).card := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.card_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem injective_family_of_ncard_diff
    {α : Type} [Fintype α] [DecidableEq α]
    (I B : Set α) (ℓ M : ℕ) (hIB : I ⊆ B)
    (hI : I.ncard ≤ ℓ) (hB : ℓ + M < B.ncard) :
    ∃ v : Fin M → α, Function.Injective v ∧ ∀ j, v j ∈ B \ I := by
  classical
  have hdiff : M ≤ (B \ I).ncard := by
    have hcard := Set.ncard_sdiff_add_ncard_of_subset hIB (Set.toFinite B)
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Set.exists_subset_card_eq hdiff
  have hTfin : T.Finite := Set.toFinite T
  let t : Finset α := hTfin.toFinset
  have htcoe : (t : Set α) = T := hTfin.coe_toFinset
  have htcard : t.card = M := by
    rw [← Set.ncard_coe_finset, htcoe, hTcard]
  let e : Fin M ≃ t := (Finset.equivFinOfCardEq htcard).symm
  let v : Fin M → α := fun j => (e j).1
  refine ⟨v, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    exact hij
  · intro j
    apply hTsub
    rw [← htcoe]
    exact (e j).2

open _root_.Code in
theorem lambda_contradiction_of_injective_center
    (ℓ : ℕ)
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (p : ℝ) (hp : 0 ≤ p)
    (c : ι → A) (hc : c ∈ C)
    (u : Fin ℓ → ι → A) (huinj : Function.Injective u)
    (huC : ∀ j, u j ∈ C) (huc : ∀ j, u j ≠ c)
    (y : ι → A)
    (hyc : hammingDist c y ≤ Nat.floor (p * Fintype.card ι))
    (huy : ∀ j, hammingDist (u j) y ≤ Nat.floor (p * Fintype.card ι))
    (hLambda : Lambda C p ≤ (ℓ : ℕ∞)) : False := by
  classical
  have hpoint := (Code.Lambda_le_iff_forall_ncard_le.mp hLambda) y
  rw [closeCodewordsRel_eq_setOf C p hp y] at hpoint
  let image : Finset (ι → A) := Finset.univ.image u
  have hcnot : c ∉ image := by
    intro hcimage
    rcases Finset.mem_image.mp hcimage with ⟨j, hj, hju⟩
    exact (huc j) hju
  let t : Finset (ι → A) := insert c image
  have himagecard : image.card = ℓ := by
    dsimp only [image]
    rw [Finset.card_image_of_injective _ huinj]
    simp only [Finset.card_univ, Fintype.card_fin]
  have htcard : t.card = ℓ + 1 := by
    dsimp only [t]
    rw [Finset.card_insert_of_notMem hcnot, himagecard]
  have hsub : (t : Set (ι → A)) ⊆
      {x : ι → A | x ∈ C ∧
        hammingDist x y ≤ Nat.floor (p * Fintype.card ι)} := by
    intro x hx
    change x ∈ insert c image at hx
    rcases Finset.mem_insert.mp hx with hxc | hximage
    · subst x
      exact ⟨hc, hyc⟩
    · rcases Finset.mem_image.mp hximage with ⟨j, hj, hju⟩
      subst x
      exact ⟨huC j, huy j⟩
  have hle : t.card ≤
      ({x : ι → A | x ∈ C ∧
        hammingDist x y ≤ Nat.floor (p * Fintype.card ι)} : Set (ι → A)).ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub hpoint.1
  rw [htcard] at hle
  omega

theorem large_fiber_of_image_bound
    {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (s : Finset X) (f : X → Y) (B k : ℕ)
    (hs : s.Nonempty) (himage : (s.image f).card ≤ B)
    (hlarge : B * k ≤ s.card) :
    ∃ y ∈ s.image f, k ≤ (s.filter fun x => f x = y).card := by
  have himul : (s.image f).card * k ≤ s.card := by
    exact (Nat.mul_le_mul_right k himage).trans hlarge
  apply Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := s) (t := s.image f) (f := f)
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · exact hs.image f
  · exact himul

/-- A large-union family can be reparametrised to nearby sizes `a₁ ≥ a₀`, `b₁ ≤ b₀`, at the cost
of a factor `W` in the number of sets. -/
theorem large_union_family_resize :
    ∀ (W a₀ b₀ a₁ b₁ : ℕ), 0 < W → a₀ ≤ a₁ → a₁ < b₀ → b₁ ≤ b₀ →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι], a₁ ≤ Fintype.card ι →
        ∀ source : LargeUnionFamily ι W a₀ b₀,
          ∃ target : LargeUnionFamily ι W a₁ b₁,
            source.sets.card ≤ W * target.sets.card := by
  classical
  intro W a₀ b₀ a₁ b₁ hW ha hlt hb ι _ _ ha₁ source
  have hext : ∀ A ∈ source.sets,
      ∃ E : Finset ι, A ⊆ E ∧ E.card = a₁ := by
    intro A hA
    apply Finset.exists_superset_card_eq
    · simpa only [source.card_each A hA] using ha
    · exact ha₁
  let extend : Finset ι → Finset ι := fun A =>
    if hA : A ∈ source.sets then Classical.choose (hext A hA) else ∅
  have hextend : ∀ A ∈ source.sets,
      A ⊆ extend A ∧ (extend A).card = a₁ := by
    intro A hA
    dsimp only [extend]
    rw [dif_pos hA]
    exact Classical.choose_spec (hext A hA)
  let targetSets : Finset (Finset ι) := source.sets.image extend
  have hcard_each : ∀ E ∈ targetSets, E.card = a₁ := by
    intro E hE
    rcases Finset.mem_image.mp hE with ⟨A, hA, rfl⟩
    exact (hextend A hA).2
  have hfiber : ∀ E ∈ targetSets,
      (source.sets.filter fun A => extend A = E).card ≤ W := by
    intro E hE
    by_contra hle
    have hWle : W ≤ (source.sets.filter fun A => extend A = E).card := by
      omega
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hWle
    have hTsource : T ⊆ source.sets := by
      intro A hA
      exact (Finset.mem_filter.mp (hTsub hA)).1
    have hlarge := source.large_union T hTsource hTcard
    have hUsub : T.biUnion id ⊆ E := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨A, hAT, hxA⟩
      have hAf := Finset.mem_filter.mp (hTsub hAT)
      have hAE := (hextend A hAf.1).1 hxA
      simpa only [hAf.2] using hAE
    have hUcard : (T.biUnion id).card ≤ E.card := Finset.card_le_card hUsub
    rcases Finset.mem_image.mp hE with ⟨A, hA, hAE⟩
    have hEcard : E.card = a₁ := by
      rw [← hAE]
      exact (hextend A hA).2
    rw [hEcard] at hUcard
    omega
  have htarget_large : ∀ T : Finset (Finset ι), T ⊆ targetSets → T.card = W →
      b₁ ≤ (T.biUnion id).card := by
    intro T hTsub hTcard
    have hpre : ∀ E ∈ T, ∃ A ∈ source.sets, extend A = E := by
      intro E hE
      rcases Finset.mem_image.mp (hTsub hE) with ⟨A, hA, hAE⟩
      exact ⟨A, hA, hAE⟩
    let pre : Finset ι → Finset ι := fun E =>
      if hE : E ∈ T then Classical.choose (hpre E hE) else ∅
    have hpre_spec : ∀ E ∈ T,
        pre E ∈ source.sets ∧ extend (pre E) = E := by
      intro E hE
      dsimp only [pre]
      rw [dif_pos hE]
      exact Classical.choose_spec (hpre E hE)
    let U : Finset (Finset ι) := T.image pre
    have hUsub : U ⊆ source.sets := by
      intro A hA
      rcases Finset.mem_image.mp hA with ⟨E, hE, rfl⟩
      exact (hpre_spec E hE).1
    have hpreinj : Set.InjOn pre (T : Set (Finset ι)) := by
      intro E hE E' hE' hEq
      have h1 := (hpre_spec E hE).2
      have h2 := (hpre_spec E' hE').2
      rw [← h1, ← h2, hEq]
    have hUcard : U.card = W := by
      rw [show U = T.image pre by rfl, Finset.card_image_of_injOn hpreinj, hTcard]
    have hlarge := source.large_union U hUsub hUcard
    have hUnionSub : U.biUnion id ⊆ T.biUnion id := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨A, hAU, hxA⟩
      rcases Finset.mem_image.mp hAU with ⟨E, hET, rfl⟩
      have hsub := (hextend (pre E) (hpre_spec E hET).1).1 hxA
      have hEq := (hpre_spec E hET).2
      apply Finset.mem_biUnion.mpr
      refine ⟨E, hET, ?_⟩
      change x ∈ E
      rw [← hEq]
      exact hsub
    exact hb.trans (hlarge.trans (Finset.card_le_card hUnionSub))
  let target : LargeUnionFamily ι W a₁ b₁ :=
    { sets := targetSets
      card_each := hcard_each
      large_union := htarget_large }
  refine ⟨target, ?_⟩
  change source.sets.card ≤ W * targetSets.card
  exact Finset.card_le_mul_card_image source.sets W hfiber

theorem nat_quotient_window
    (ℓ radius dZero n : ℕ) (hℓ : 0 < ℓ)
    (hdZero : dZero ≤ radius) (hradius : radius ≤ n) :
    let dOne := (radius - dZero) / ℓ
    let used := dZero + ℓ * dOne
    let m := n - used
    used ≤ radius ∧ radius < used + ℓ ∧
      n - radius ≤ m ∧ m ≤ n - radius + (ℓ - 1) := by
  dsimp only
  have hmod := Nat.mod_add_div (radius - dZero) ℓ
  have hrem := Nat.mod_lt (radius - dZero) hℓ
  omega

/-- The barrier's radius, `ℓ/(ℓ+1) · (1 − ρ − η)` — the generalized Singleton radius at rate `ρ`,
pulled back by `η`. -/
noncomputable def relRadius (ℓ : ℕ) (ρ η : ℝ) : ℝ :=
  (ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η)

/-- **Existence of a barrier package.** For a list size `ℓ`, a rate `R` and a neighbourhood cap `B`,
there are constants `ηCut, γ, K, Wmax` and a length threshold beyond which every small `η` admits
barrier parameters, a block structure and a large-union family fitting together. -/
def BarrierPackageExistence : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (R : ℝ), 0 < R → R < 1 →
    ∀ (B : ℕ), 0 < B →
    ∃ ηCut : ℝ, 0 < ηCut ∧
      ∃ γ : ℝ, 0 < γ ∧ ∃ K : ℝ, 0 < K ∧
        ∃ Wmax : ℕ, 0 < Wmax ∧ ∃ n₀ : ℕ,
          ∀ (η : ℝ), 0 < η → η < ηCut →
            ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι],
              n₀ ≤ Fintype.card ι →
              1 / η ≤ (Fintype.card ι : ℝ) →
              ∃ params : BarrierParameters ℓ (Fintype.card ι)
                  (Nat.floor (relRadius ℓ R η * Fintype.card ι))
                  (Nat.ceil (boostedRadius ℓ (relRadius ℓ R η) * Fintype.card ι)),
                0 < params.W ∧ params.W ≤ Wmax ∧
                params.aFamily + (B + 1) ≤ Nat.floor (R * Fintype.card ι) ∧
                params.dZero ≤ Nat.ceil (K * η * Fintype.card ι) ∧
                ∃ blocks : CoordinateBlocks ι ℓ params.dZero params.dOne,
                  ∃ family : LargeUnionFamily ι params.W
                      params.aFamily params.aUnion,
                    (∀ S ∈ family.sets, Disjoint S blocks.zero ∧
                      ∀ j, Disjoint S (blocks.other j)) ∧
                    (2 : ℝ) ^ (γ * Fintype.card ι) ≤ family.sets.card

/-- **The robust minimum-distance barrier.** A `boosted`-separated code over an alphabet of size at
least `2`, whose list size at the barrier radius is at most `ℓ`, cannot be large: its size is capped
by `|A|^(aFamily)`-type quantities, which forces `|A| ≥ 2^(α/η)`. This is the statement the
large-alphabet lower bound consumes. -/
def RobustMinimumDistanceBarrierStatement : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (R : ℝ), 0 < R → R < 1 →
    ∀ (B : ℕ), 0 < B →
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (η : ℝ), 0 < η →
        ∀ {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          [Fintype A] [DecidableEq A]
          (C : Set (ι → A)),
          2 ≤ Fintype.card A →
          n₀ ≤ Fintype.card ι →
          1 / η ≤ (Fintype.card ι : ℝ) →
          (Fintype.card A : ℝ) ^ (R * Fintype.card ι) ≤
            (B : ℝ) * (C.ncard : ℝ) →
          separated C
            (Nat.ceil (boostedRadius ℓ (relRadius ℓ R η) * Fintype.card ι)) →
          Lambda C (relRadius ℓ R η) ≤ (ℓ : ℕ∞) →
          (Fintype.card A : ℝ) ≥ (2 : ℝ) ^ (α / η)

theorem relRadius_balance
    (ℓ : ℕ) (hℓ : 0 < ℓ) (R η : ℝ) :
    R + relRadius ℓ R η + relRadius ℓ R η / ℓ = 1 - η := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  unfold relRadius
  field_simp [ne_of_gt hℓR]
  ring

theorem relRadius_pos (ℓ : ℕ) (hℓ_pos : 0 < ℓ)
    (ρ η : ℝ) (hη_lt : η < 1 - ρ) : 0 < relRadius ℓ ρ η := by
  unfold relRadius
  have hℓ_real : (0 : ℝ) < ℓ := by exact_mod_cast hℓ_pos
  have hden : (0 : ℝ) < ℓ + 1 := by positivity
  have hgap : 0 < 1 - ρ - η := by linarith
  exact mul_pos (div_pos hℓ_real hden) hgap

theorem rate_loss_to_cardinality
    (q B a n N : ℕ) (R : ℝ)
    (hq : 2 ≤ q) (hB : 0 < B) (hR : 0 ≤ R)
    (ha : a + (B + 1) ≤ Nat.floor (R * n))
    (hsize : (q : ℝ) ^ (R * n) ≤ (B : ℝ) * N) :
    2 * q ^ a ≤ N := by
  have hBpow : B ≤ 2 ^ B := by
    calc
      B = Nat.choose B 1 := (Nat.choose_one_right B).symm
      _ ≤ 2 ^ B := Nat.choose_le_two_pow B 1
  have htwoB : 2 * B ≤ q ^ (B + 1) := by
    calc
      2 * B ≤ 2 * 2 ^ B := Nat.mul_le_mul_left 2 hBpow
      _ = 2 ^ (B + 1) := by rw [pow_succ]; ring
      _ ≤ q ^ (B + 1) := pow_le_pow_left' hq (B + 1)
  have hnat : B * (2 * q ^ a) ≤ q ^ (a + (B + 1)) := by
    calc
      B * (2 * q ^ a) = (2 * B) * q ^ a := by ring
      _ ≤ q ^ (B + 1) * q ^ a :=
        Nat.mul_le_mul_right (q ^ a) htwoB
      _ = q ^ (a + (B + 1)) := by
        rw [← pow_add]
        congr 1
        omega
  have hRn : 0 ≤ R * (n : ℝ) := mul_nonneg hR (by positivity)
  have hexp : ((a + (B + 1) : ℕ) : ℝ) ≤ R * n := by
    calc
      ((a + (B + 1) : ℕ) : ℝ) ≤ Nat.floor (R * n) := by
        exact_mod_cast ha
      _ ≤ R * n := Nat.floor_le hRn
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hpow : ((q ^ (a + (B + 1)) : ℕ) : ℝ) ≤
      (q : ℝ) ^ (R * n) := by
    calc
      ((q ^ (a + (B + 1)) : ℕ) : ℝ) =
          (q : ℝ) ^ (a + (B + 1) : ℕ) := by norm_num
      _ = (q : ℝ) ^ ((a + (B + 1) : ℕ) : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ ≤ (q : ℝ) ^ (R * n) :=
        Real.rpow_le_rpow_of_exponent_le hqOne hexp
  have hreal : (B : ℝ) * (2 * q ^ a : ℕ) ≤ (B : ℝ) * N := by
    calc
      (B : ℝ) * (2 * q ^ a : ℕ) ≤
          (q ^ (a + (B + 1)) : ℕ) := by exact_mod_cast hnat
      _ ≤ (q : ℝ) ^ (R * n) := hpow
      _ ≤ (B : ℝ) * N := hsize
  have hcancel : ((2 * q ^ a : ℕ) : ℝ) ≤ (N : ℝ) :=
    le_of_mul_le_mul_left hreal (by exact_mod_cast hB)
  exact_mod_cast hcancel

/-- The length threshold `⌈(B+1)/R⌉` at which the barrier's basic bounds hold. -/
noncomputable def roundedBarrierBasicThreshold (R : ℝ) (B : ℕ) : ℕ :=
  Nat.ceil (((B + 1 : ℕ) : ℝ) / R)

/-- The barrier's parameters at a given length, all rounded to integers: radius and boosted radius,
the `dZero`/`dOne` block sizes, the used and unused coordinate counts, and the large-union family's
set and union sizes. Every later estimate is stated against this record. -/
noncomputable def roundedBarrierData
    (ℓ : ℕ) (R η K : ℝ) (B n : ℕ) : RoundedBarrierData :=
  let radius := Nat.floor (relRadius ℓ R η * n)
  let boosted := Nat.ceil (boostedRadius ℓ (relRadius ℓ R η) * n)
  let dZero := Nat.ceil (K * η * n)
  let dOne := (radius - dZero) / ℓ
  let used := dZero + ℓ * dOne
  { radius := radius
    boosted := boosted
    dZero := dZero
    dOne := dOne
    used := used
    unused := n - used
    aFamily := Nat.floor (R * n) - (B + 1)
    aUnion := n + 1 - boosted }

theorem rounded_barrier_other_codeword_bound_core
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R η : ℝ) (B n : ℕ)
    (hone : 1 ≤ η * n)
    (hrate : B + 1 ≤ Nat.floor (R * n))
    (hdZero : Nat.ceil (barrierK ℓ B * η * n) ≤
      Nat.floor (relRadius ℓ R η * n)) :
    let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
    n - d.dZero - d.dOne - d.aFamily ≤ d.radius := by
  dsimp only [roundedBarrierData]
  let p := relRadius ℓ R η
  let K := barrierK ℓ B
  let r := Nat.floor (p * n)
  let z := Nat.ceil (K * η * n)
  let o := (r - z) / ℓ
  let a := Nat.floor (R * n) - (B + 1)
  change n - z - o - a ≤ r
  change z ≤ r at hdZero
  have hℓpos : 0 < ℓ := by omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hcoefPos : (0 : ℝ) < 1 + 1 / (ℓ : ℝ) := by positivity
  have hcoefNonneg : (0 : ℝ) ≤ 1 - 1 / (ℓ : ℝ) := by
    have hℓTwo : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have honeDiv : 1 / (ℓ : ℝ) ≤ 1 := by
      apply (div_le_one hℓR).2
      linarith
    linarith
  have hrFloor : p * n < (r : ℝ) + 1 := by
    simpa only [r] using Nat.lt_floor_add_one (p * n)
  have hrLower : p * n - 1 < (r : ℝ) := by linarith
  have hrWeighted :
      (p * n - 1) * (1 + 1 / (ℓ : ℝ)) <
        (r : ℝ) * (1 + 1 / (ℓ : ℝ)) :=
    mul_lt_mul_of_pos_right hrLower hcoefPos
  have hzLower : K * η * n ≤ (z : ℝ) := by
    simpa only [z] using Nat.le_ceil (K * η * n)
  have hzWeighted :
      K * η * n * (1 - 1 / (ℓ : ℝ)) ≤
        (z : ℝ) * (1 - 1 / (ℓ : ℝ)) :=
    mul_le_mul_of_nonneg_right hzLower hcoefNonneg
  have hmod := Nat.mod_add_div (r - z) ℓ
  have hrem := Nat.mod_lt (r - z) hℓpos
  have hquotNat : r - z < ℓ * (o + 1) := by
    calc
      r - z = (r - z) % ℓ + ℓ * ((r - z) / ℓ) := hmod.symm
      _ < ℓ + ℓ * ((r - z) / ℓ) := Nat.add_lt_add_right hrem _
      _ = ℓ * (((r - z) / ℓ) + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ = ℓ * (o + 1) := by rfl
  have hquotReal :
      ((r - z : ℕ) : ℝ) < ((ℓ * (o + 1) : ℕ) : ℝ) := by
    exact_mod_cast hquotNat
  norm_num only [Nat.cast_sub hdZero, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one] at hquotReal
  have hquotDiv :
      ((r : ℝ) - z) / (ℓ : ℝ) < (o : ℝ) + 1 := by
    rw [div_lt_iff₀ hℓR]
    simpa only [mul_comm] using hquotReal
  have hoLower :
      (r : ℝ) / (ℓ : ℝ) - (z : ℝ) / (ℓ : ℝ) - 1 < o := by
    rw [← sub_div]
    linarith
  have hrateEq : Nat.floor (R * n) = a + (B + 1) := by
    dsimp only [a]
    exact (Nat.sub_add_cancel hrate).symm
  have hrateFloor : R * n < (Nat.floor (R * n) : ℝ) + 1 :=
    Nat.lt_floor_add_one (R * n)
  have haLower : R * n - ((B : ℝ) + 2) < (a : ℝ) := by
    rw [hrateEq] at hrateFloor
    norm_num only [Nat.cast_add, Nat.cast_one] at hrateFloor
    linarith
  have hbalance : R + p + p / (ℓ : ℝ) = 1 - η := by
    simpa only [p] using relRadius_balance ℓ hℓpos R η
  have hbalanceN :
      R * n + p * n + (p / (ℓ : ℝ)) * n =
        (n : ℝ) - η * n := by
    calc
      R * n + p * n + (p / (ℓ : ℝ)) * n =
          (R + p + p / (ℓ : ℝ)) * n := by ring
      _ = (1 - η) * n := by rw [hbalance]
      _ = (n : ℝ) - η * n := by ring
  have hslack := barrier_k_slack ℓ B hℓ
  change (B : ℝ) + 4 + 1 / (ℓ : ℝ) ≤
    K * (1 - 1 / (ℓ : ℝ)) - 1 at hslack
  have hconstNonneg :
      (0 : ℝ) ≤ (B : ℝ) + 4 + 1 / (ℓ : ℝ) := by positivity
  have hfactorNonneg :
      (0 : ℝ) ≤ K * (1 - 1 / (ℓ : ℝ)) - 1 :=
    hconstNonneg.trans hslack
  have hfactorGrow :
      K * (1 - 1 / (ℓ : ℝ)) - 1 ≤
        (K * (1 - 1 / (ℓ : ℝ)) - 1) * (η * n) := by
    calc
      K * (1 - 1 / (ℓ : ℝ)) - 1 =
          (K * (1 - 1 / (ℓ : ℝ)) - 1) * 1 := by ring
      _ ≤ (K * (1 - 1 / (ℓ : ℝ)) - 1) * (η * n) :=
        mul_le_mul_of_nonneg_left hone hfactorNonneg
  have hbudget :
      (B : ℝ) + 4 + 1 / (ℓ : ℝ) ≤
        (K * (1 - 1 / (ℓ : ℝ)) - 1) * (η * n) :=
    hslack.trans hfactorGrow
  let L : ℝ :=
    (R * n - ((B : ℝ) + 2)) +
      (p * n - 1) * (1 + 1 / (ℓ : ℝ)) +
      K * η * n * (1 - 1 / (ℓ : ℝ)) - 1
  have hLFormula : L =
      (n : ℝ) +
        (K * (1 - 1 / (ℓ : ℝ)) - 1) * (η * n) -
        ((B : ℝ) + 4 + 1 / (ℓ : ℝ)) := by
    dsimp only [L]
    calc
      (R * n - ((B : ℝ) + 2)) +
          (p * n - 1) * (1 + 1 / (ℓ : ℝ)) +
          K * η * n * (1 - 1 / (ℓ : ℝ)) - 1 =
        (R * n + p * n + (p / (ℓ : ℝ)) * n) +
          K * η * n * (1 - 1 / (ℓ : ℝ)) -
          ((B : ℝ) + 4 + 1 / (ℓ : ℝ)) := by ring
      _ = (n : ℝ) +
          (K * (1 - 1 / (ℓ : ℝ)) - 1) * (η * n) -
          ((B : ℝ) + 4 + 1 / (ℓ : ℝ)) := by
        rw [hbalanceN]
        ring
  have hLeL : (n : ℝ) ≤ L := by
    rw [hLFormula]
    linarith
  let U : ℝ :=
    (a : ℝ) + (r : ℝ) * (1 + 1 / (ℓ : ℝ)) +
      (z : ℝ) * (1 - 1 / (ℓ : ℝ)) - 1
  have hAR :
      (R * n - ((B : ℝ) + 2)) +
          (p * n - 1) * (1 + 1 / (ℓ : ℝ)) <
        (a : ℝ) + (r : ℝ) * (1 + 1 / (ℓ : ℝ)) :=
    add_lt_add haLower hrWeighted
  have hLltU : L < U := by
    dsimp only [L, U]
    exact sub_lt_sub_right
      (add_lt_add_of_lt_of_le hAR hzWeighted) 1
  have hsumDiff :
      ((r : ℝ) + z + o + a) - U =
        (o : ℝ) -
          ((r : ℝ) / (ℓ : ℝ) - (z : ℝ) / (ℓ : ℝ) - 1) := by
    dsimp only [U]
    ring
  have hUltSum : U < (r : ℝ) + z + o + a := by
    apply sub_pos.mp
    rw [hsumDiff]
    exact sub_pos.mpr hoLower
  have hsumReal : (n : ℝ) < (r : ℝ) + z + o + a :=
    hLeL.trans_lt (hLltU.trans hUltSum)
  have hsumNat : n < r + z + o + a := by
    exact_mod_cast hsumReal
  omega

/-- The mean of the shifted incidences `aᵢ + 1 − ℓ` is at least `p·M − (ℓ−1)`. -/
theorem shifted_incidence_mean_lower :
    ∀ (ℓ M n : ℕ) (p : ℝ), 2 ≤ ℓ → 0 < n →
      ∀ a : Fin n → ℕ,
        p * M * n ≤ ∑ i, (a i : ℝ) →
        p * M - (ℓ - 1) ≤
          (∑ i, ((a i + 1 - ℓ : ℕ) : ℝ)) / n := by
  intro ℓ M n p hℓ hn a hsum
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hpoint : ∀ i : Fin n,
      (a i : ℝ) ≤ ((a i + 1 - ℓ : ℕ) : ℝ) + (ℓ - 1 : ℕ) := by
    intro i
    exact_mod_cast (show a i ≤ a i + 1 - ℓ + (ℓ - 1) by omega)
  have hsum_le : (∑ i, (a i : ℝ)) ≤
      ∑ i, (((a i + 1 - ℓ : ℕ) : ℝ) + (ℓ - 1 : ℕ)) := by
    exact Finset.sum_le_sum fun i _ => hpoint i
  rw [Finset.sum_add_distrib] at hsum_le
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum_le
  have hcast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast] at hsum_le
  rw [le_div_iff₀ hnR]
  nlinarith

/-- From a bound on the *mean* incidence to a bound on its `ℓ`-th binomial moment:
`p·M·n ≤ ∑ᵢ aᵢ` implies `(3p^ℓ/4) · C(M, ℓ) · n ≤ ∑ᵢ C(aᵢ, ℓ)`, by convexity once `M ≥ ⌈4ℓ²/p⌉`. -/
theorem incidence_moment_lower :
    ∀ (ℓ M n : ℕ) (p : ℝ), 2 ≤ ℓ → 0 < n → 0 < p → p < 1 →
      Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M →
      ∀ a : Fin n → ℕ,
        p * M * n ≤ ∑ i, (a i : ℝ) →
        (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n ≤
          ∑ i, (Nat.choose (a i) ℓ : ℝ) := by
  intro ℓ M n p hℓ hn hp hp_lt hM a hsum
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast hn
  let b : Fin n → ℝ := fun i => (a i + 1 - ℓ : ℕ)
  have hmean : p * M - (ℓ - 1) ≤ (∑ i, b i) / n := by
    simpa only [b] using
      (shifted_incidence_mean_lower ℓ M n p hℓ hn a hsum)
  have hℓR : (0 : ℝ) < ℓ := by
    exact_mod_cast (show 0 < ℓ by omega)
  have hsize : 4 * (ℓ : ℝ) ^ 2 / p ≤ (M : ℝ) :=
    (Nat.ceil_le).mp hM
  have hpm : 4 * (ℓ : ℝ) ^ 2 ≤ p * M := by
    simpa only [mul_comm] using (div_le_iff₀ hp).mp hsize
  have hgap_nonneg : 0 ≤ p * M - ((ℓ : ℝ) - 1) := by
    have hℓtwo : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have hsmall : (ℓ : ℝ) - 1 ≤ 4 * (ℓ : ℝ) ^ 2 := by
      nlinarith only [hℓtwo, sq_nonneg (ℓ : ℝ)]
    apply sub_nonneg.mpr
    exact hsmall.trans hpm
  have hmeanpow :
      (p * M - ((ℓ : ℝ) - 1)) ^ ℓ ≤ ((∑ i, b i) / n) ^ ℓ :=
    pow_le_pow_left₀ hgap_nonneg hmean ℓ
  let w : Fin n → ℝ := fun _ => 1 / n
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w i := by
    intro i hi
    dsimp [w]
    positivity
  have hwsum : ∑ i ∈ (Finset.univ : Finset (Fin n)), w i = 1 := by
    dsimp [w]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [ne_of_gt hnR]
  have hb : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ b i := by
    intro i hi
    dsimp [b]
    positivity
  have hj := Real.pow_arith_mean_le_arith_mean_pow
    (Finset.univ : Finset (Fin n)) w b hw hwsum hb ℓ
  have hleft :
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i * b i) =
        (∑ i, b i) / n := by
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i * b i) =
          ∑ i ∈ (Finset.univ : Finset (Fin n)), b i / n := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [w]
        ring
      _ = (∑ i, b i) / n := by rw [Finset.sum_div]
  have hright :
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i * b i ^ ℓ) =
        (∑ i, b i ^ ℓ) / n := by
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i * b i ^ ℓ) =
          ∑ i ∈ (Finset.univ : Finset (Fin n)), b i ^ ℓ / n := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [w]
        ring
      _ = (∑ i, b i ^ ℓ) / n := by rw [Finset.sum_div]
  rw [hleft, hright] at hj
  have hfact : (0 : ℝ) < Nat.factorial ℓ := by positivity
  have hchooseM : (Nat.choose M ℓ : ℝ) ≤
      (M : ℝ) ^ ℓ / Nat.factorial ℓ := by
    exact Nat.choose_le_pow_div ℓ M
  have hcoeff : 0 ≤ 3 * p ^ ℓ / 4 := by positivity
  have hgap := incidence_power_gap ℓ M p hℓ hp hM
  have hfirst :
      (3 * p ^ ℓ / 4) * (Nat.choose M ℓ : ℝ) ≤
        (p * M - ((ℓ : ℝ) - 1)) ^ ℓ / Nat.factorial ℓ := by
    calc
      (3 * p ^ ℓ / 4) * (Nat.choose M ℓ : ℝ) ≤
          (3 * p ^ ℓ / 4) * ((M : ℝ) ^ ℓ / Nat.factorial ℓ) :=
        mul_le_mul_of_nonneg_left hchooseM hcoeff
      _ = ((3 * p ^ ℓ / 4) * (M : ℝ) ^ ℓ) /
          Nat.factorial ℓ := by ring
      _ ≤ (p * M - ((ℓ : ℝ) - 1)) ^ ℓ /
          Nat.factorial ℓ :=
        div_le_div_of_nonneg_right hgap hfact.le
  have hchoose : ∀ i : Fin n,
      b i ^ ℓ / Nat.factorial ℓ ≤ (Nat.choose (a i) ℓ : ℝ) := by
    intro i
    simpa only [b] using (Nat.pow_le_choose (α := ℝ) ℓ (a i))
  have hsumchoose :
      (∑ i, b i ^ ℓ) / Nat.factorial ℓ ≤
        ∑ i, (Nat.choose (a i) ℓ : ℝ) := by
    calc
      (∑ i, b i ^ ℓ) / Nat.factorial ℓ =
          ∑ i, b i ^ ℓ / Nat.factorial ℓ := by
        rw [Finset.sum_div]
      _ ≤ ∑ i, (Nat.choose (a i) ℓ : ℝ) :=
        Finset.sum_le_sum fun i hi => hchoose i
  have hcore :
      (3 * p ^ ℓ / 4) * (Nat.choose M ℓ : ℝ) ≤
        (∑ i, (Nat.choose (a i) ℓ : ℝ)) / n := by
    calc
      (3 * p ^ ℓ / 4) * (Nat.choose M ℓ : ℝ) ≤
          (p * M - ((ℓ : ℝ) - 1)) ^ ℓ / Nat.factorial ℓ := hfirst
      _ ≤ ((∑ i, b i) / n) ^ ℓ / Nat.factorial ℓ :=
        div_le_div_of_nonneg_right hmeanpow hfact.le
      _ ≤ ((∑ i, b i ^ ℓ) / n) / Nat.factorial ℓ :=
        div_le_div_of_nonneg_right hj hfact.le
      _ = ((∑ i, b i ^ ℓ) / Nat.factorial ℓ) / n := by ring
      _ ≤ (∑ i, (Nat.choose (a i) ℓ : ℝ)) / n :=
        div_le_div_of_nonneg_right hsumchoose hnR.le
  simpa only [mul_assoc] using (le_div_iff₀ hnR).mp hcore

end LargeAlphabetBarrier

end CodingTheory
