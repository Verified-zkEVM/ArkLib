/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# List-size bounds for interleaved codes

This file bounds the list size of row-wise interleavings in terms of the base code's list size.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
* [Gopalan, P., Guruswami, V., Raghavendra, P., *List Decoding Tensor Products and
  Interleaved Codes*][GGR11]
-/

namespace InterleavedCode

open Code

private inductive BranchColor
  | white
  | blue
  | red
  deriving DecidableEq

private def agreesBeforeNat {d : ℕ} {α : Type} (j : ℕ) (V W : Fin d → α) : Prop :=
  ∀ k, k.val < j → V k = W k

private def colorCountFrom {d : ℕ} {α : Type}
    (color : ℕ → (Fin d → α) → BranchColor)
    (j : ℕ) (V : Fin d → α) (c : BranchColor) : ℕ :=
  ((Finset.Ico j d).filter fun k => color k V = c).card

private def treeBound (L : ℕ∞) (b r : ℕ) : ℕ∞ :=
  ((b + r).choose r : ℕ∞) * L ^ r

private lemma colorCountFrom_eq_add {d : ℕ} {α : Type}
    (color : ℕ → (Fin d → α) → BranchColor)
    {j : ℕ} (hj : j < d) (V : Fin d → α) (c : BranchColor) :
    colorCountFrom color j V c =
      (if color j V = c then 1 else 0) + colorCountFrom color (j + 1) V c := by
  have hIco : Finset.Ico j d = insert j (Finset.Ico (j + 1) d) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [colorCountFrom, hIco, Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem]
    · simp [colorCountFrom, Nat.add_comm]
    · simp
  · simp [colorCountFrom]

private lemma one_le_treeBound {L : ℕ∞} (hL : 1 ≤ L) (b r : ℕ) :
    1 ≤ treeBound L b r := by
  have hchoose : 0 < (b + r).choose r := Nat.choose_pos (Nat.le_add_left r b)
  have hchoose' : (1 : ℕ∞) ≤ ((b + r).choose r : ℕ∞) := by exact_mod_cast hchoose
  have hpow : (1 : ℕ∞) ≤ L ^ r := one_le_pow₀ hL
  calc
    1 = 1 * 1 := by simp
    _ ≤ ((b + r).choose r : ℕ∞) * L ^ r := mul_le_mul hchoose' hpow zero_le zero_le

private lemma treeBound_succ_succ (L : ℕ∞) (b r : ℕ) :
    treeBound L (b + 1) (r + 1) =
      treeBound L b (r + 1) + L * treeBound L (b + 1) r := by
  simp only [treeBound, pow_succ]
  rw [show b + 1 + (r + 1) = (b + r + 1) + 1 by omega,
    Nat.choose_succ_succ, Nat.cast_add, add_mul]
  simp only [Nat.succ_eq_add_one]
  rw [show b + (r + 1) = b + r + 1 by omega,
    show b + 1 + r = b + r + 1 by omega]
  simp [mul_assoc, mul_comm, add_comm]

private lemma treeBound_zero_succ (L : ℕ∞) (r : ℕ) :
    treeBound L 0 (r + 1) = L * treeBound L 0 r := by
  simp [treeBound, pow_succ, mul_comm]

private theorem card_le_treeBound {d : ℕ} {α : Type} [DecidableEq α]
    (T : Finset (Fin d → α)) (color : ℕ → (Fin d → α) → BranchColor) (L : ℕ∞)
    (hL : 1 ≤ L)
    (hcolor : ∀ j (hj : j < d) V, V ∈ T → ∀ W, W ∈ T →
      agreesBeforeNat j V W → V ⟨j, hj⟩ = W ⟨j, hj⟩ → color j V = color j W)
    (hwhite : ∀ j (hj : j < d) V, V ∈ T → ∀ W, W ∈ T →
      agreesBeforeNat j V W → color j V = .white → V ⟨j, hj⟩ = W ⟨j, hj⟩)
    (hblue : ∀ j (hj : j < d) V, V ∈ T → ∀ W, W ∈ T →
      agreesBeforeNat j V W → color j V = .blue → color j W = .blue →
        V ⟨j, hj⟩ = W ⟨j, hj⟩)
    (hred : ∀ j (hj : j < d) (S : Finset (Fin d → α)), S ⊆ T →
      (∀ V ∈ S, ∀ W ∈ S, agreesBeforeNat j V W) →
      (((S.filter fun V => color j V = .red).image fun V => V ⟨j, hj⟩).card : ℕ∞) ≤ L) :
    ∀ b r, (∀ V ∈ T,
      colorCountFrom color 0 V .blue ≤ b ∧ colorCountFrom color 0 V .red ≤ r) →
      (T.card : ℕ∞) ≤ treeBound L b r := by
  -- The recursive statement applies to every prefix fiber of `T`.
  apply (Nat.decreasingInduction (n := d)
      (motive := fun j hj => ∀ (S : Finset (Fin d → α)), S ⊆ T →
        (∀ V ∈ S, ∀ W ∈ S, agreesBeforeNat j V W) →
        ∀ b r, (∀ V ∈ S, colorCountFrom color j V .blue ≤ b ∧
          colorCountFrom color j V .red ≤ r) →
        (S.card : ℕ∞) ≤ treeBound L b r) ?_ ?_ (Nat.zero_le d)) T (by simp) ?_
  · intro j hj ih S hST hpref b r hbudget
    have hjlt : j < d := hj
    by_cases hS : S = ∅
    · simp [hS]
    by_cases hw : ∃ V ∈ S, color j V = .white
    · obtain ⟨Vw, hVwS, hVwColor⟩ := hw
      have hnext : ∀ W ∈ S, Vw ⟨j, hjlt⟩ = W ⟨j, hjlt⟩ := by
        intro W hWS
        exact hwhite j hjlt Vw (hST hVwS) W (hST hWS)
          (hpref Vw hVwS W hWS) hVwColor
      refine ih S hST ?_ b r ?_
      · intro V hVS W hWS k hk
        by_cases hkj : k.val < j
        · exact hpref V hVS W hWS k hkj
        · have hkeq : k = ⟨j, hjlt⟩ := by apply Fin.ext; simp; omega
          subst k
          exact (hnext V hVS).symm.trans (hnext W hWS)
      · intro V hVS
        have hVwhite : color j V = .white := by
          exact (hcolor j hjlt V (hST hVS) Vw (hST hVwS) (hpref V hVS Vw hVwS)
            (hnext V hVS).symm).trans hVwColor
        constructor
        · have h := (hbudget V hVS).1
          rw [colorCountFrom_eq_add color hjlt, if_neg (by simp [hVwhite])] at h
          simpa using h
        · have h := (hbudget V hVS).2
          rw [colorCountFrom_eq_add color hjlt, if_neg (by simp [hVwhite])] at h
          simpa using h
    · let next : (Fin d → α) → α := fun V => V ⟨j, hjlt⟩
      let fiber (c : α) := S.filter fun V => next V = c
      let blueChoices := (S.filter fun V => color j V = .blue).image next
      let redChoices := (S.filter fun V => color j V = .red).image next
      have hcases (V : Fin d → α) (hVS : V ∈ S) :
          color j V = .blue ∨ color j V = .red := by
        cases hV : color j V with
        | white => exact (hw ⟨V, hVS, hV⟩).elim
        | blue => exact Or.inl rfl
        | red => exact Or.inr rfl
      have hmaps : Set.MapsTo next (S : Set (Fin d → α))
          ((blueChoices ∪ redChoices : Finset α) : Set α) := by
        intro V hVS
        rcases hcases V hVS with hV | hV
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨V, Finset.mem_filter.mpr ⟨hVS, hV⟩, rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨V, Finset.mem_filter.mpr ⟨hVS, hV⟩, rfl⟩)
      have hcard : S.card = ∑ c ∈ blueChoices ∪ redChoices, (fiber c).card := by
        simpa [fiber] using Finset.card_eq_sum_card_fiberwise hmaps
      have hdisj : Disjoint blueChoices redChoices := by
        rw [Finset.disjoint_left]
        intro c hcB hcR
        obtain ⟨V, hVB, hVc⟩ := Finset.mem_image.mp hcB
        obtain ⟨W, hWR, hWc⟩ := Finset.mem_image.mp hcR
        have hVB' := Finset.mem_filter.mp hVB
        have hWR' := Finset.mem_filter.mp hWR
        have hrow : V ⟨j, hjlt⟩ = W ⟨j, hjlt⟩ := by simpa [next] using hVc.trans hWc.symm
        have := hcolor j hjlt V (hST hVB'.1) W (hST hWR'.1)
          (hpref V hVB'.1 W hWR'.1) hrow
        rw [hVB'.2, hWR'.2] at this
        contradiction
      have hblueCard : blueChoices.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro c hc c' hc'
        obtain ⟨V, hVB, hVc⟩ := Finset.mem_image.mp hc
        obtain ⟨W, hWB, hWc⟩ := Finset.mem_image.mp hc'
        have hVB' := Finset.mem_filter.mp hVB
        have hWB' := Finset.mem_filter.mp hWB
        have hrow := hblue j hjlt V (hST hVB'.1) W (hST hWB'.1)
          (hpref V hVB'.1 W hWB'.1) hVB'.2 hWB'.2
        simpa [next] using hVc.symm.trans (hrow.trans hWc)
      have hblueCardE : (blueChoices.card : ℕ∞) ≤ 1 := by exact_mod_cast hblueCard
      have hredCard : (redChoices.card : ℕ∞) ≤ L := by
        simpa [redChoices, next] using hred j hjlt S hST hpref
      have hfiber_subset (c : α) : fiber c ⊆ T := by
        intro V hV
        exact hST (Finset.mem_filter.mp hV).1
      have hfiber_prefix (c : α) :
          ∀ V ∈ fiber c, ∀ W ∈ fiber c, agreesBeforeNat (j + 1) V W := by
        intro V hVF W hWF k hk
        have hVF' := Finset.mem_filter.mp hVF
        have hWF' := Finset.mem_filter.mp hWF
        by_cases hkj : k.val < j
        · exact hpref V hVF'.1 W hWF'.1 k hkj
        · have hkeq : k = ⟨j, hjlt⟩ := by apply Fin.ext; simp; omega
          subst k
          simpa [fiber, next] using hVF'.2.trans hWF'.2.symm
      have hcolor_fiber (c : α) (V : Fin d → α) (hVF : V ∈ fiber c)
          (W : Fin d → α) (hWF : W ∈ fiber c) : color j V = color j W := by
        have hVF' := Finset.mem_filter.mp hVF
        have hWF' := Finset.mem_filter.mp hWF
        apply hcolor j hjlt V (hST hVF'.1) W (hST hWF'.1)
          (hpref V hVF'.1 W hWF'.1)
        simpa [fiber, next] using hVF'.2.trans hWF'.2.symm
      have hblueFiber {b' : ℕ} (hb : b = b' + 1) (c : α) (hc : c ∈ blueChoices) :
          ((fiber c).card : ℕ∞) ≤ treeBound L b' r := by
        obtain ⟨V₀, hV₀B, hV₀c⟩ := Finset.mem_image.mp hc
        have hV₀B' := Finset.mem_filter.mp hV₀B
        apply ih (fiber c) (hfiber_subset c) (hfiber_prefix c) b' r
        intro V hVF
        have hVblue : color j V = .blue := by
          have hV₀F : V₀ ∈ fiber c := Finset.mem_filter.mpr ⟨hV₀B'.1, hV₀c⟩
          rw [hcolor_fiber c V hVF V₀ hV₀F, hV₀B'.2]
        constructor
        · have h := (hbudget V (Finset.mem_filter.mp hVF).1).1
          rw [colorCountFrom_eq_add color hjlt, if_pos hVblue, hb] at h
          omega
        · have h := (hbudget V (Finset.mem_filter.mp hVF).1).2
          rw [colorCountFrom_eq_add color hjlt, if_neg (by simp [hVblue])] at h
          simpa using h
      have hredFiber {r' : ℕ} (hr : r = r' + 1) (c : α) (hc : c ∈ redChoices) :
          ((fiber c).card : ℕ∞) ≤ treeBound L b r' := by
        obtain ⟨V₀, hV₀R, hV₀c⟩ := Finset.mem_image.mp hc
        have hV₀R' := Finset.mem_filter.mp hV₀R
        apply ih (fiber c) (hfiber_subset c) (hfiber_prefix c) b r'
        intro V hVF
        have hVred : color j V = .red := by
          have hV₀F : V₀ ∈ fiber c := Finset.mem_filter.mpr ⟨hV₀R'.1, hV₀c⟩
          rw [hcolor_fiber c V hVF V₀ hV₀F, hV₀R'.2]
        constructor
        · have h := (hbudget V (Finset.mem_filter.mp hVF).1).1
          rw [colorCountFrom_eq_add color hjlt, if_neg (by simp [hVred])] at h
          simpa using h
        · have h := (hbudget V (Finset.mem_filter.mp hVF).1).2
          rw [colorCountFrom_eq_add color hjlt, if_pos hVred, hr] at h
          omega
      have hcastCard : (S.card : ℕ∞) =
          ∑ c ∈ blueChoices ∪ redChoices, ((fiber c).card : ℕ∞) := by
        exact_mod_cast hcard
      rw [hcastCard, Finset.sum_union hdisj]
      rcases b with _ | b'
      · have hblueEmpty : blueChoices = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro c hc
          obtain ⟨V, hVB, _⟩ := Finset.mem_image.mp hc
          have hVB' := Finset.mem_filter.mp hVB
          have h := (hbudget V hVB'.1).1
          rw [colorCountFrom_eq_add color hjlt, if_pos hVB'.2] at h
          omega
        rw [hblueEmpty]
        simp only [Finset.sum_empty, zero_add]
        rcases r with _ | r'
        · have hredEmpty : redChoices = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro c hc
            obtain ⟨V, hVR, _⟩ := Finset.mem_image.mp hc
            have hVR' := Finset.mem_filter.mp hVR
            have h := (hbudget V hVR'.1).2
            rw [colorCountFrom_eq_add color hjlt, if_pos hVR'.2] at h
            omega
          simp [hredEmpty, treeBound]
        · calc
            ∑ c ∈ redChoices, ((fiber c).card : ℕ∞) ≤
                ∑ _c ∈ redChoices, treeBound L 0 r' :=
              Finset.sum_le_sum fun c hc => hredFiber rfl c hc
            _ = (redChoices.card : ℕ∞) * treeBound L 0 r' := by simp
            _ ≤ L * treeBound L 0 r' := by
              exact mul_le_mul_left hredCard (treeBound L 0 r')
            _ = treeBound L 0 (r' + 1) := (treeBound_zero_succ L r').symm
      · rcases r with _ | r'
        · have hredEmpty : redChoices = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro c hc
            obtain ⟨V, hVR, _⟩ := Finset.mem_image.mp hc
            have hVR' := Finset.mem_filter.mp hVR
            have h := (hbudget V hVR'.1).2
            rw [colorCountFrom_eq_add color hjlt, if_pos hVR'.2] at h
            omega
          rw [hredEmpty]
          simp only [Finset.sum_empty, add_zero]
          calc
            ∑ c ∈ blueChoices, ((fiber c).card : ℕ∞) ≤
                ∑ _c ∈ blueChoices, treeBound L b' 0 :=
              Finset.sum_le_sum fun c hc => hblueFiber rfl c hc
            _ = (blueChoices.card : ℕ∞) * treeBound L b' 0 := by simp
            _ ≤ 1 * treeBound L b' 0 := by
              exact mul_le_mul_left hblueCardE (treeBound L b' 0)
            _ = treeBound L (b' + 1) 0 := by simp [treeBound]
        · calc
            (∑ c ∈ blueChoices, ((fiber c).card : ℕ∞)) +
                ∑ c ∈ redChoices, ((fiber c).card : ℕ∞) ≤
              (∑ _c ∈ blueChoices, treeBound L b' (r' + 1)) +
                ∑ _c ∈ redChoices, treeBound L (b' + 1) r' := by
              exact add_le_add
                (Finset.sum_le_sum fun c hc => hblueFiber rfl c hc)
                (Finset.sum_le_sum fun c hc => hredFiber rfl c hc)
            _ = (blueChoices.card : ℕ∞) * treeBound L b' (r' + 1) +
                (redChoices.card : ℕ∞) * treeBound L (b' + 1) r' := by simp
            _ ≤ treeBound L b' (r' + 1) + L * treeBound L (b' + 1) r' :=
              add_le_add
                (by simpa only [one_mul] using
                  mul_le_mul_left hblueCardE (treeBound L b' (r' + 1)))
                (mul_le_mul_left hredCard (treeBound L (b' + 1) r'))
            _ = treeBound L (b' + 1) (r' + 1) := (treeBound_succ_succ L b' r').symm
  · intro S hST hpref b r hbudget
    have hcard : S.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro V hVS W hWS
      funext k
      exact hpref V hVS W hWS k k.isLt
    exact (by exact_mod_cast hcard : (S.card : ℕ∞) ≤ 1) |>.trans (one_le_treeBound hL b r)
  · intro V hVT W hWT k hk
    omega

private def prefixErrors {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    {d : ℕ} (R V : Fin d → ι → A) (j : ℕ) : Finset ι :=
  Finset.univ.filter fun i => ∃ k : Fin d, k.val < j ∧ R k i ≠ V k i

private def newErrors {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    {d : ℕ} (R V : Fin d → ι → A) (j : ℕ) : Finset ι :=
  prefixErrors R V (j + 1) \ prefixErrors R V j

private lemma prefixErrors_mono {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    {d : ℕ} (R V : Fin d → ι → A) {j k : ℕ} (hjk : j ≤ k) :
    prefixErrors R V j ⊆ prefixErrors R V k := by
  classical
  intro i hi
  simp only [prefixErrors, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  obtain ⟨l, hlj, hl⟩ := hi
  exact ⟨l, hlj.trans_le hjk, hl⟩

private lemma prefixErrors_succ_eq_union {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    {d : ℕ} (R V : Fin d → ι → A) (j : ℕ) :
    prefixErrors R V (j + 1) = prefixErrors R V j ∪ newErrors R V j := by
  classical
  unfold newErrors
  simpa [Nat.succ_eq_add_one] using
    (Finset.union_sdiff_of_subset (prefixErrors_mono R V (Nat.le_succ j))).symm

private lemma disjoint_prefixErrors_newErrors
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    {d : ℕ} (R V : Fin d → ι → A) (j : ℕ) :
    Disjoint (prefixErrors R V j) (newErrors R V j) := by
  classical
  rw [Finset.disjoint_left]
  intro i hi hi'
  exact (Finset.mem_sdiff.mp hi').2 hi

private lemma card_prefixErrors_succ {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    {d : ℕ} (R V : Fin d → ι → A) (j : ℕ) :
    (prefixErrors R V (j + 1)).card =
      (prefixErrors R V j).card + (newErrors R V j).card := by
  rw [prefixErrors_succ_eq_union, Finset.card_union_of_disjoint
    (disjoint_prefixErrors_newErrors R V j)]

private lemma prefixErrors_eq_of_agreesBefore {ι A : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq A]
    {d : ℕ} (R : Fin d → ι → A) {V W : Fin d → ι → A} {j : ℕ}
    (h : agreesBeforeNat j V W) : prefixErrors R V j = prefixErrors R W j := by
  classical
  ext i
  simp only [prefixErrors, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, hne⟩
    exact ⟨k, hk, fun heq => hne (heq.trans (congrFun (h k hk) i).symm)⟩
  · rintro ⟨k, hk, hne⟩
    exact ⟨k, hk, fun heq => hne (heq.trans (congrFun (h k hk) i))⟩

private lemma newErrors_eq_of_agreesBefore_of_row_eq
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A] {d : ℕ}
    (R : Fin d → ι → A) {V W : Fin d → ι → A} {j : ℕ} (hj : j < d)
    (hpref : agreesBeforeNat j V W) (hrow : V ⟨j, hj⟩ = W ⟨j, hj⟩) :
    newErrors R V j = newErrors R W j := by
  unfold newErrors
  rw [prefixErrors_eq_of_agreesBefore R hpref]
  congr 1
  apply prefixErrors_eq_of_agreesBefore R
  · intro k hk
    by_cases hkj : k.val < j
    · exact hpref k hkj
    · have hkeq : k = ⟨j, hj⟩ := by apply Fin.ext; simp; omega
      simpa [hkeq] using hrow

private def ggrColor {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    {d : ℕ} (D e : ℕ) (R : Fin d → ι → A) (j : ℕ)
    (V : Fin d → ι → A) : BranchColor :=
  if (newErrors R V j).card < D - e then .white
  else if 2 * (newErrors R V j).card < D - (prefixErrors R V j).card then .blue
  else .red

private def colorCountBefore {d : ℕ} {α : Type}
    (color : ℕ → (Fin d → α) → BranchColor)
    (j : ℕ) (V : Fin d → α) (c : BranchColor) : ℕ :=
  ((Finset.range j).filter fun k => color k V = c).card

private lemma colorCountBefore_succ {d : ℕ} {α : Type}
    (color : ℕ → (Fin d → α) → BranchColor)
    (j : ℕ) (V : Fin d → α) (c : BranchColor) :
  colorCountBefore color (j + 1) V c =
      colorCountBefore color j V c + if color j V = c then 1 else 0 := by
  rw [colorCountBefore, colorCountBefore, Finset.range_add_one, Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem]
    · simp
  · simp

private lemma colorCountFrom_zero_eq_before {d : ℕ} {α : Type}
    (color : ℕ → (Fin d → α) → BranchColor) (V : Fin d → α) (c : BranchColor) :
    colorCountFrom color 0 V c = colorCountBefore color d V c := by
  simp [colorCountFrom, colorCountBefore]

private lemma ggrColor_count_bounds {ι A : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq A] {d : ℕ} (D e : ℕ) (hde : e < D) (R V : Fin d → ι → A)
    (hglobal : (prefixErrors R V d).card ≤ e) :
    colorCountFrom (ggrColor D e R) 0 V .blue * (D - e) ≤ e ∧
      2 ^ colorCountFrom (ggrColor D e R) 0 V .red * (D - e) ≤ D := by
  have hprefix (j : ℕ) (hj : j ≤ d) : (prefixErrors R V j).card ≤ e :=
    (Finset.card_le_card (prefixErrors_mono R V hj)).trans hglobal
  have hinv (j : ℕ) (hj : j ≤ d) :
      colorCountBefore (ggrColor D e R) j V .blue * (D - e) ≤
          (prefixErrors R V j).card ∧
        2 ^ colorCountBefore (ggrColor D e R) j V .red *
            (D - (prefixErrors R V j).card) ≤ D := by
    induction j with
    | zero => simp [colorCountBefore, prefixErrors]
    | succ j ih =>
      have hjlt : j < d := by omega
      have ih' := ih (by omega)
      let s := (prefixErrors R V j).card
      let w := (newErrors R V j).card
      have hsucc : (prefixErrors R V (j + 1)).card = s + w :=
        card_prefixErrors_succ R V j
      have hsw : s + w ≤ e := by rw [← hsucc]; exact hprefix (j + 1) hj
      have hswD : s + w < D := hsw.trans_lt hde
      by_cases hwhite : w < D - e
      · have hcol : ggrColor D e R j V = .white := by simp [ggrColor, w, hwhite]
        rw [colorCountBefore_succ, colorCountBefore_succ, hcol]
        simp only [reduceCtorEq, ↓reduceIte, add_zero]
        rw [hsucc]
        constructor
        · exact ih'.1.trans (Nat.le_add_right _ _)
        · apply ih'.2.trans'
          apply Nat.mul_le_mul_left
          omega
      · by_cases hblue : 2 * w < D - s
        · have hcol : ggrColor D e R j V = .blue := by
            simp [ggrColor, s, w, hwhite, hblue]
          rw [colorCountBefore_succ, colorCountBefore_succ, hcol]
          simp only [reduceCtorEq, ↓reduceIte, add_zero]
          rw [hsucc]
          constructor
          · calc
              (colorCountBefore (ggrColor D e R) j V .blue + 1) * (D - e) =
                  colorCountBefore (ggrColor D e R) j V .blue * (D - e) + (D - e) := by
                simp [Nat.add_mul]
              _ ≤ s + w := Nat.add_le_add ih'.1 (le_of_not_gt hwhite)
          · apply ih'.2.trans'
            apply Nat.mul_le_mul_left
            omega
        · have hcol : ggrColor D e R j V = .red := by
            simp [ggrColor, s, w, hwhite, hblue]
          have hhalf : 2 * (D - (s + w)) ≤ D - s := by omega
          rw [colorCountBefore_succ, colorCountBefore_succ, hcol]
          simp only [reduceCtorEq, ↓reduceIte, add_zero]
          rw [hsucc]
          constructor
          · exact ih'.1.trans (Nat.le_add_right _ _)
          · calc
              2 ^ (colorCountBefore (ggrColor D e R) j V .red + 1) *
                    (D - (s + w)) =
                  2 ^ colorCountBefore (ggrColor D e R) j V .red *
                    (2 * (D - (s + w))) := by
                rw [pow_succ]
                simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              _ ≤ 2 ^ colorCountBefore (ggrColor D e R) j V .red * (D - s) :=
                Nat.mul_le_mul_left _ hhalf
              _ ≤ D := ih'.2
  have hfin := hinv d le_rfl
  rw [colorCountFrom_zero_eq_before, colorCountFrom_zero_eq_before]
  constructor
  · exact hfin.1.trans hglobal
  · calc
      2 ^ colorCountBefore (ggrColor D e R) d V .red * (D - e) ≤
          2 ^ colorCountBefore (ggrColor D e R) d V .red *
            (D - (prefixErrors R V d).card) := by
        exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hglobal D)
      _ ≤ D := hfin.2

private lemma blue_count_le_ceil {n D e q : ℕ} {δ : ℝ}
    (hn : 0 < n) (hδD : δ < (D : ℝ) / n)
    (he : (e : ℝ) ≤ δ * n) (hq : q * (D - e) ≤ e) :
    q ≤ ⌈δ / ((D : ℝ) / n - δ)⌉₊ := by
  let η : ℝ := (D : ℝ) / n - δ
  have hη : 0 < η := sub_pos.mpr hδD
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heD : e ≤ D := by
    exact_mod_cast (he.trans_lt ((lt_div_iff₀ hnR).mp hδD)).le
  have hgap : (n : ℝ) * η ≤ D - e := by
    dsimp [η]
    have : (n : ℝ) * ((D : ℝ) / n) = D := by field_simp
    rw [mul_sub, this]
    simpa [mul_comm] using sub_le_sub_left he (D : ℝ)
  have hqR : (q : ℝ) * ((D : ℝ) - e) ≤ e := by
    calc
      (q : ℝ) * ((D : ℝ) - e) = ((q * (D - e) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub heD]
        rfl
      _ ≤ e := by exact_mod_cast hq
  have hqη : (q : ℝ) * η ≤ δ := by
    have hq_nonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith [mul_le_mul_of_nonneg_left hgap hq_nonneg]
  have hqdiv : (q : ℝ) ≤ δ / η := (le_div_iff₀ hη).mpr hqη
  change q ≤ ⌈δ / η⌉₊
  exact_mod_cast hqdiv.trans (Nat.le_ceil (δ / η))

private lemma red_count_le_ceil {n D e q : ℕ} {δ : ℝ}
    (hn : 0 < n) (hδD : δ < (D : ℝ) / n)
    (he : (e : ℝ) ≤ δ * n) (hq : 2 ^ q * (D - e) ≤ D) :
    q ≤ ⌈Real.log (((D : ℝ) / n) / ((D : ℝ) / n - δ)) / Real.log 2⌉₊ := by
  let δC : ℝ := (D : ℝ) / n
  let η : ℝ := δC - δ
  have hη : 0 < η := sub_pos.mpr hδD
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heD : e ≤ D := by
    exact_mod_cast (he.trans_lt ((lt_div_iff₀ hnR).mp hδD)).le
  have hgap : (n : ℝ) * η ≤ D - e := by
    dsimp [η, δC]
    have : (n : ℝ) * ((D : ℝ) / n) = D := by field_simp
    rw [mul_sub, this]
    simpa [mul_comm] using sub_le_sub_left he (D : ℝ)
  have hqR : ((2 : ℝ) ^ q) * ((D : ℝ) - e) ≤ D := by
    calc
      ((2 : ℝ) ^ q) * ((D : ℝ) - e) = ((2 ^ q * (D - e) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub heD]
        rfl
      _ ≤ D := by exact_mod_cast hq
  have hp : (2 : ℝ) ^ q ≤ δC / η := by
    apply (le_div_iff₀ hη).mpr
    have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ q := by positivity
    have hmul := mul_le_mul_of_nonneg_left hgap hpow
    dsimp [δC]
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ q) hp
  rw [Real.log_pow] at hlog
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hqlog : (q : ℝ) ≤ Real.log (δC / η) / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr hlog
  change q ≤ ⌈Real.log (δC / η) / Real.log 2⌉₊
  exact_mod_cast hqlog.trans (Nat.le_ceil (Real.log (δC / η) / Real.log 2))

private lemma prefixErrors_transpose_all {ι A : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq A]
    {d : ℕ} (U V : ι → Fin d → A) :
    prefixErrors (Matrix.transpose U) (Matrix.transpose V) d = disagreementCols U V := by
  classical
  ext i
  simp only [prefixErrors, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_disagreementCols]
  constructor
  · rintro ⟨k, _, hk⟩
    intro h
    exact hk (congrFun h k)
  · intro h
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact ⟨k, k.isLt, hk⟩

private lemma row_disagreement_subset_prefix_union_new {ι A : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq A] {d : ℕ} (R V W : Fin d → ι → A)
    {j : ℕ} (hj : j < d) (hpref : agreesBeforeNat j V W) :
    disagreementCols (V ⟨j, hj⟩) (W ⟨j, hj⟩) ⊆
      prefixErrors R V j ∪ newErrors R V j ∪ newErrors R W j := by
  intro i hi
  simp only [Finset.mem_union]
  by_cases hiS : i ∈ prefixErrors R V j
  · exact Or.inl (Or.inl hiS)
  by_cases hiV : i ∈ newErrors R V j
  · exact Or.inl (Or.inr hiV)
  by_cases hiW : i ∈ newErrors R W j
  · exact Or.inr hiW
  exfalso
  have hRV : R ⟨j, hj⟩ i = V ⟨j, hj⟩ i := by
    by_contra hne
    apply hiV
    rw [newErrors, Finset.mem_sdiff]
    refine ⟨?_, hiS⟩
    simp only [prefixErrors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨j, hj⟩, by simp, hne⟩
  have hiSW : i ∉ prefixErrors R W j := by
    intro hi
    apply hiS
    rw [prefixErrors_eq_of_agreesBefore R hpref]
    exact hi
  have hRW : R ⟨j, hj⟩ i = W ⟨j, hj⟩ i := by
    by_contra hne
    apply hiW
    rw [newErrors, Finset.mem_sdiff]
    refine ⟨?_, hiSW⟩
    simp only [prefixErrors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨j, hj⟩, by simp, hne⟩
  exact (mem_disagreementCols.mp hi) (hRV.symm.trans hRW)

private lemma row_disagreement_subset_all_errors {ι A : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq A] {d : ℕ} (R V : Fin d → ι → A)
    {j : ℕ} (hj : j < d) :
    disagreementCols (R ⟨j, hj⟩) (V ⟨j, hj⟩) ⊆ prefixErrors R V d := by
  intro i hi
  simp only [prefixErrors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨j, hj⟩, hj, mem_disagreementCols.mp hi⟩

/-- Let `C` have relative minimum distance `δ_C := minDist C / |ι|`, and let
`δ ∈ [0, δ_C)`. With

* `η := δ_C - δ`,
* `b := ⌈δ / η⌉`, and
* `r := ⌈log₂(δ_C / η)⌉`,

the list size of every nonempty row-wise interleaving is at most
`choose (b + r) r * Lambda(C, δ)^r`. -/
theorem lambda_interleaved_le_choose_mul_pow {ι A : Type} [Fintype ι] [Finite A]
    [DecidableEq A]
    (C : Set (ι → A)) (δ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hδ_lb : 0 ≤ δ)
    (hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι) :
    let δC : ℝ := (Code.minDist C : ℝ) / Fintype.card ι
    let η : ℝ := δC - δ
    let b : ℕ := ⌈δ / η⌉₊
    let r : ℕ := ⌈Real.log (δC / η) / Real.log 2⌉₊
    Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤
      ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  let n := Fintype.card ι
  let D := Code.minDist C
  let e := Nat.floor (δ * n)
  let b := ⌈δ / ((D : ℝ) / n - δ)⌉₊
  let r := ⌈Real.log (((D : ℝ) / n) / ((D : ℝ) / n - δ)) / Real.log 2⌉₊
  change Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤
    ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    simp [n, hn0] at hδ_ub hδ_lb
    linarith
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by simpa [n] using hn)
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
  have heR : (e : ℝ) ≤ δ * n := by
    exact_mod_cast Nat.floor_le (mul_nonneg hδ_lb (Nat.cast_nonneg n))
  have hde : e < D := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hδn : δ * n < D := (lt_div_iff₀ hnR).mp (by simpa [D, n] using hδ_ub)
    exact_mod_cast heR.trans_lt hδn
  by_cases hC : C.Nonempty
  · obtain ⟨c₀, hc₀⟩ := hC
    have hL : (1 : ℕ∞) ≤ Lambda C δ := by
      have hcclose : c₀ ∈ closeCodewordsRel C c₀ δ := by
        rw [mem_closeCodewordsRel_iff]
        refine ⟨hc₀, ?_⟩
        simp [Code.relHammingDist, hδ_lb]
      exact (Set.one_le_encard_iff_nonempty.mpr ⟨c₀, hcclose⟩).trans
        (encard_closeCodewordsRel_le_Lambda C δ c₀)
    rw [Lambda_le_iff_forall_encard_le]
    intro U
    have hcloseFinite : (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) U δ).Finite :=
      Set.toFinite _
    rw [← hcloseFinite.cast_ncard_eq]
    let Q := hcloseFinite.toFinset
    let stack : (ι → Fin m → A) → (Fin m → ι → A) := Matrix.transpose
    let T := Q.image stack
    have hTcard : T.card = Q.card := Finset.card_image_of_injective Q fun _ _ h =>
      Matrix.transpose_injective h
    have hQcard : Q.card =
        (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) U δ).ncard := by
      exact Set.ncard_eq_toFinset_card _ hcloseFinite |>.symm
    rw [← hQcard, ← hTcard]
    let R : Fin m → ι → A := Matrix.transpose U
    let color : ℕ → (Fin m → ι → A) → BranchColor := ggrColor D e R
    have hrowMem (V : Fin m → ι → A) (hVT : V ∈ T) (j : Fin m) : V j ∈ C := by
      obtain ⟨X, hXQ, rfl⟩ := Finset.mem_image.mp hVT
      have hXclose := hcloseFinite.mem_toFinset.mp hXQ
      exact (mem_closeCodewordsRel_iff.mp hXclose).1 j
    have hglobal (V : Fin m → ι → A) (hVT : V ∈ T) :
        (prefixErrors R V m).card ≤ e := by
      obtain ⟨X, hXQ, rfl⟩ := Finset.mem_image.mp hVT
      have hXclose := hcloseFinite.mem_toFinset.mp hXQ
      have hrelR : (δᵣ(U, X) : ℝ) ≤ δ := (mem_closeCodewordsRel_iff.mp hXclose).2
      let δnn : NNReal := ⟨δ, hδ_lb⟩
      have hδnn : (δnn : ℝ) = δ := rfl
      have hrel : δᵣ(U, X) ≤ δnn := by exact_mod_cast hrelR
      have hdist : Δ₀(U, X) ≤ e := by
        rw [pairRelDist_le_iff_pairDist_le] at hrel
        change Δ₀(U, X) ≤ Nat.floor ((δnn : ℝ) * Fintype.card ι) at hrel
        rw [hδnn] at hrel
        simpa [δnn, e, n] using hrel
      rw [show R = Matrix.transpose U from rfl, prefixErrors_transpose_all]
      simpa [hammingDist_eq_disagreementCols_card] using hdist
    apply card_le_treeBound T color (Lambda C δ) hL
    · intro j hj V hVT W hWT hpref hrow
      have hp := prefixErrors_eq_of_agreesBefore R hpref
      have hnw := newErrors_eq_of_agreesBefore_of_row_eq R hj hpref hrow
      simp only [color, ggrColor, hp, hnw]
    · intro j hj V hVT W hWT hpref hVwhite
      let S₀ := prefixErrors R V j
      let EV := newErrors R V j
      let EW := newErrors R W j
      have hp := prefixErrors_eq_of_agreesBefore R hpref
      have hEV : EV.card < D - e := by
        change ggrColor D e R j V = BranchColor.white at hVwhite
        simp only [ggrColor] at hVwhite
        split at hVwhite
        next h => simpa [EV] using h
        next _ => split at hVwhite <;> contradiction
      have hWsucc : S₀.card + EW.card ≤ e := by
        have hbound := (Finset.card_le_card
          (prefixErrors_mono R W (j := j + 1) (k := m) (by omega))).trans (hglobal W hWT)
        rw [card_prefixErrors_succ] at hbound
        simpa [S₀, EW, hp] using hbound
      apply eq_of_disagreementCols_subset_of_card_lt_minDist (hrowMem V hVT ⟨j, hj⟩)
        (hrowMem W hWT ⟨j, hj⟩) (S₀ ∪ EV ∪ EW)
      · exact row_disagreement_subset_prefix_union_new R V W hj hpref
      · calc
          (S₀ ∪ EV ∪ EW).card ≤ S₀.card + EV.card + EW.card := by
            exact (Finset.card_union_le (S₀ ∪ EV) EW).trans
              (Nat.add_le_add_right (Finset.card_union_le S₀ EV) _)
          _ < D := by omega
    · intro j hj V hVT W hWT hpref hVblue hWblue
      let S₀ := prefixErrors R V j
      let EV := newErrors R V j
      let EW := newErrors R W j
      have hp := prefixErrors_eq_of_agreesBefore R hpref
      have hEV : 2 * EV.card < D - S₀.card := by
        change ggrColor D e R j V = BranchColor.blue at hVblue
        simp only [ggrColor] at hVblue
        split at hVblue
        next _ => contradiction
        next _ =>
          split at hVblue
          next h => simpa [EV, S₀] using h
          next _ => contradiction
      have hEW : 2 * EW.card < D - S₀.card := by
        have : prefixErrors R W j = S₀ := hp.symm
        change ggrColor D e R j W = BranchColor.blue at hWblue
        simp only [ggrColor] at hWblue
        split at hWblue
        next _ => contradiction
        next _ =>
          split at hWblue
          next h => simpa [EW, this] using h
          next _ => contradiction
      apply eq_of_disagreementCols_subset_of_card_lt_minDist (hrowMem V hVT ⟨j, hj⟩)
        (hrowMem W hWT ⟨j, hj⟩) (S₀ ∪ EV ∪ EW)
      · exact row_disagreement_subset_prefix_union_new R V W hj hpref
      · calc
          (S₀ ∪ EV ∪ EW).card ≤ S₀.card + EV.card + EW.card := by
            exact (Finset.card_union_le (S₀ ∪ EV) EW).trans
              (Nat.add_le_add_right (Finset.card_union_le S₀ EV) _)
          _ < D := by omega
    · intro j hj S hST hpref
      let rows := (S.filter fun V => color j V = .red).image fun V => V ⟨j, hj⟩
      have hrows : (rows : Set (ι → A)) ⊆ closeCodewordsRel C (R ⟨j, hj⟩) δ := by
        intro c hc
        obtain ⟨V, hVR, rfl⟩ := Finset.mem_image.mp hc
        have hVS := (Finset.mem_filter.mp hVR).1
        rw [mem_closeCodewordsRel_iff]
        refine ⟨hrowMem V (hST hVS) ⟨j, hj⟩, ?_⟩
        let δnn : NNReal := ⟨δ, hδ_lb⟩
        have hδnn : (δnn : ℝ) = δ := rfl
        have hdist : Δ₀(R ⟨j, hj⟩, V ⟨j, hj⟩) ≤ e := by
          rw [hammingDist_eq_disagreementCols_card]
          exact (Finset.card_le_card (row_disagreement_subset_all_errors R V hj)).trans
            (hglobal V (hST hVS))
        have hrel : δᵣ(R ⟨j, hj⟩, V ⟨j, hj⟩) ≤ δnn := by
          rw [pairRelDist_le_iff_pairDist_le]
          change Δ₀(R ⟨j, hj⟩, V ⟨j, hj⟩) ≤
            Nat.floor ((δnn : ℝ) * Fintype.card ι)
          rw [hδnn]
          simpa [e, n] using hdist
        exact_mod_cast hrel
      change (rows.card : ℕ∞) ≤ Lambda C δ
      calc
        (rows.card : ℕ∞) = (rows : Set (ι → A)).encard := by simp
        _ ≤ (closeCodewordsRel C (R ⟨j, hj⟩) δ).encard := Set.encard_mono hrows
        _ ≤ Lambda C δ := encard_closeCodewordsRel_le_Lambda C δ _
    · intro V hVT
      have hnat := ggrColor_count_bounds D e hde R V (hglobal V hVT)
      rw [show color = ggrColor D e R from rfl]
      constructor
      · exact blue_count_le_ceil hn (by simpa [D, n] using hδ_ub) heR hnat.1
      · exact red_count_le_ceil hn (by simpa [D, n] using hδ_ub) heR hnat.2
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
    subst C
    rw [Lambda_le_iff_forall_encard_le]
    intro U
    have hpoint : closeCodewordsRel
        (interleavedCodeSet (κ := Fin m) (∅ : Set (ι → A))) U δ = ∅ := by
      ext c
      constructor
      · intro hc
        exact (hc.1 ⟨0, by omega⟩).elim
      · simp
    rw [hpoint]
    simp only [Set.encard_empty]
    exact (zero_le : (0 : ℕ∞) ≤ _)

end InterleavedCode
