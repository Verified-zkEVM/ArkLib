/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.TensorGenerator
import ArkLib.Data.CodingTheory.ProximityGenerator.PolynomialGenerator

/-!
# Full agreement through shared-level binary tensor folds

This file strengthens binary line MCA with witnesses that preserve the complete agreement set,
then iterates those witnesses through the shared-level binary fold.
-/

namespace TensorMCA

open CoreDefinitions LinearCode
open scoped BigOperators

variable {ι F A : Type} [Fintype ι] [DecidableEq ι] [Field F]
  [AddCommMonoid A] [Module F A]

/-- Positions on which two words agree. -/
def fullAgreementSet [DecidableEq A] (c u : ι → A) : Finset ι :=
  Finset.univ.filter fun i ↦ c i = u i

/-- The equality-weight binary line fold. -/
def binaryLineFold (r : F) (u₀ u₁ : ι → A) : ι → A :=
  fun i ↦ (1 - r) • u₀ i + r • u₁ i

/-- The shared-level binary fold, recursively from the root challenge. -/
def binaryTensorFold : ∀ {h : ℕ}, (Fin h → F) → ((Fin h → Bool) → ι → A) → ι → A
  | 0, _, u => u default
  | _ + 1, r, u => binaryLineFold (r 0)
      (binaryTensorFold (Fin.tail r) (fun leaf ↦ u (Fin.cons false leaf)))
      (binaryTensorFold (Fin.tail r) (fun leaf ↦ u (Fin.cons true leaf)))

/-- A line certificate supplies a bounded exceptional set and, outside it, constituent
codewords whose common agreement set is exactly the folded codeword's full agreement set. -/
def FullSetLineWitness [DecidableEq A]
    (C : ModuleCode ι F A) (agreement exceptionalCount : ℕ) : Prop :=
  ∀ u₀ u₁ : ι → A, ∃ exceptional : Finset F,
    exceptional.card ≤ exceptionalCount ∧
    ∀ r ∉ exceptional, ∀ c : ι → A, c ∈ C →
      agreement ≤ (fullAgreementSet c (binaryLineFold r u₀ u₁)).card →
      ∃ c₀ c₁ : ι → A, c₀ ∈ C ∧ c₁ ∈ C ∧
        c = binaryLineFold r c₀ c₁ ∧
        fullAgreementSet c (binaryLineFold r u₀ u₁) =
          fullAgreementSet c₀ u₀ ∩ fullAgreementSet c₁ u₁

/-- Leaf codewords reconstruct the root codeword and their common agreement set equals the
root's complete agreement set. -/
def HasFullTensorDecomposition [DecidableEq A]
    (C : ModuleCode ι F A) (agreement : ℕ) {h : ℕ}
    (r : Fin h → F) (u : (Fin h → Bool) → ι → A) : Prop :=
  ∀ c : ι → A, c ∈ C → agreement ≤ (fullAgreementSet c (binaryTensorFold r u)).card →
    ∃ leafCode : (Fin h → Bool) → ι → A,
      (∀ leaf, leafCode leaf ∈ C) ∧
      c = binaryTensorFold r leafCode ∧
      fullAgreementSet c (binaryTensorFold r u) =
        Finset.univ.filter (fun i ↦ ∀ leaf, leafCode leaf i = u leaf i)

noncomputable def lineExceptional [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hline : FullSetLineWitness C agreement exceptionalCount)
    (u₀ u₁ : ι → A) : Finset F :=
  Classical.choose (hline u₀ u₁)

theorem lineExceptional_card_le [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hline : FullSetLineWitness C agreement exceptionalCount) (u₀ u₁ : ι → A) :
    (lineExceptional hline u₀ u₁).card ≤ exceptionalCount :=
  (Classical.choose_spec (hline u₀ u₁)).1

theorem lineExceptional_good [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hline : FullSetLineWitness C agreement exceptionalCount) (u₀ u₁ : ι → A)
    {r : F} (hr : r ∉ lineExceptional hline u₀ u₁)
    {c : ι → A} (hc : c ∈ C)
    (hagree : agreement ≤ (fullAgreementSet c (binaryLineFold r u₀ u₁)).card) :
    ∃ c₀ c₁ : ι → A, c₀ ∈ C ∧ c₁ ∈ C ∧
      c = binaryLineFold r c₀ c₁ ∧
      fullAgreementSet c (binaryLineFold r u₀ u₁) =
        fullAgreementSet c₀ u₀ ∩ fullAgreementSet c₁ u₁ :=
  (Classical.choose_spec (hline u₀ u₁)).2 r hr c hc hagree

/-- Recursive complement of all node exceptional events. Child folds depend only on later
challenges, matching the shared-level sampling order. -/
def TensorFoldGood [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hline : FullSetLineWitness C agreement exceptionalCount) :
    ∀ {h : ℕ}, (Fin h → F) → ((Fin h → Bool) → ι → A) → Prop
  | 0, _, _ => True
  | _ + 1, r, u =>
      let u₀ := fun leaf ↦ u (Fin.cons false leaf)
      let u₁ := fun leaf ↦ u (Fin.cons true leaf)
      let w₀ := binaryTensorFold (Fin.tail r) u₀
      let w₁ := binaryTensorFold (Fin.tail r) u₁
      r 0 ∉ lineExceptional hline w₀ w₁ ∧
        TensorFoldGood hline (Fin.tail r) u₀ ∧
        TensorFoldGood hline (Fin.tail r) u₁

private theorem card_le_of_eq_inter_left [DecidableEq A]
    {c c₀ c₁ u₀ u₁ : ι → A} {r : F}
    (h : fullAgreementSet c (binaryLineFold r u₀ u₁) =
      fullAgreementSet c₀ u₀ ∩ fullAgreementSet c₁ u₁) :
    (fullAgreementSet c (binaryLineFold r u₀ u₁)).card ≤
      (fullAgreementSet c₀ u₀).card := by
  rw [h]
  exact Finset.card_le_card Finset.inter_subset_left

private theorem card_le_of_eq_inter_right [DecidableEq A]
    {c c₀ c₁ u₀ u₁ : ι → A} {r : F}
    (h : fullAgreementSet c (binaryLineFold r u₀ u₁) =
      fullAgreementSet c₀ u₀ ∩ fullAgreementSet c₁ u₁) :
    (fullAgreementSet c (binaryLineFold r u₀ u₁)).card ≤
      (fullAgreementSet c₁ u₁).card := by
  rw [h]
  exact Finset.card_le_card Finset.inter_subset_right

set_option maxHeartbeats 800000 in
/-- Avoiding every node's line exceptional set gives a complete leaf decomposition. -/
theorem hasFullTensorDecomposition_of_good [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hline : FullSetLineWitness C agreement exceptionalCount)
    (r : Fin h → F) (u : (Fin h → Bool) → ι → A)
    (hgood : TensorFoldGood hline r u) :
    HasFullTensorDecomposition C agreement r u := by
  induction h with
  | zero =>
      intro c hc hagree
      refine ⟨fun _ ↦ c, fun _ ↦ hc, ?_, ?_⟩
      · simp only [binaryTensorFold]
      · ext i
        simp only [fullAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
        change (c i = u default i) ↔ ∀ leaf, c i = u leaf i
        constructor
        · intro hi leaf
          rw [Subsingleton.elim leaf default]
          exact hi
        · intro hi
          exact hi default
  | succ h ih =>
      intro c hc hagree
      simp only [TensorFoldGood] at hgood
      let u₀ : (Fin h → Bool) → ι → A := fun leaf ↦ u (Fin.cons false leaf)
      let u₁ : (Fin h → Bool) → ι → A := fun leaf ↦ u (Fin.cons true leaf)
      let w₀ := binaryTensorFold (Fin.tail r) u₀
      let w₁ := binaryTensorFold (Fin.tail r) u₁
      have hroot := lineExceptional_good hline w₀ w₁ hgood.1 hc hagree
      obtain ⟨c₀, c₁, hc₀, hc₁, hcroot, hagreeRoot⟩ := hroot
      have hagree₀ : agreement ≤ (fullAgreementSet c₀ w₀).card :=
        hagree.trans (card_le_of_eq_inter_left hagreeRoot)
      have hagree₁ : agreement ≤ (fullAgreementSet c₁ w₁).card :=
        hagree.trans (card_le_of_eq_inter_right hagreeRoot)
      obtain ⟨leaf₀, hleaf₀, hc₀eq, hagree₀eq⟩ :=
        ih (Fin.tail r) u₀ hgood.2.1 c₀ hc₀ hagree₀
      obtain ⟨leaf₁, hleaf₁, hc₁eq, hagree₁eq⟩ :=
        ih (Fin.tail r) u₁ hgood.2.2 c₁ hc₁ hagree₁
      let leafCode : (Fin (h + 1) → Bool) → ι → A := fun leaf ↦
        if leaf 0 then leaf₁ (Fin.tail leaf) else leaf₀ (Fin.tail leaf)
      refine ⟨leafCode, ?_, ?_, ?_⟩
      · intro leaf
        by_cases hb : leaf 0 <;> simp only [leafCode, hb, ↓reduceIte]
        · exact hleaf₁ _
        · exact hleaf₀ _
      · rw [hcroot]
        simp only [binaryTensorFold]
        apply congrArg₂ (binaryLineFold (r 0))
        · rw [hc₀eq]
          apply congrArg (binaryTensorFold (Fin.tail r))
          funext leaf
          simp [leafCode]
        · rw [hc₁eq]
          apply congrArg (binaryTensorFold (Fin.tail r))
          funext leaf
          simp [leafCode]
      · change fullAgreementSet c (binaryLineFold (r 0) w₀ w₁) = _
        rw [hagreeRoot, hagree₀eq, hagree₁eq]
        ext i
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h₀, h₁⟩ leaf
          by_cases hb : leaf 0
          · calc
              leafCode leaf i = leaf₁ (Fin.tail leaf) i := by simp [leafCode, hb]
              _ = u (Fin.cons true (Fin.tail leaf)) i := h₁ _
              _ = u leaf i := by rw [← hb, Fin.cons_self_tail]
          · have hbfalse : leaf 0 = false := Bool.eq_false_of_not_eq_true hb
            calc
              leafCode leaf i = leaf₀ (Fin.tail leaf) i := by simp [leafCode, hb]
              _ = u (Fin.cons false (Fin.tail leaf)) i := h₀ _
              _ = u leaf i := by rw [← hbfalse, Fin.cons_self_tail]
        · intro hall
          constructor
          · intro leaf
            simpa [leafCode] using hall (Fin.cons false leaf)
          · intro leaf
            simpa [leafCode] using hall (Fin.cons true leaf)

omit [Field F] in
private theorem card_filter_fin_cons [Fintype F]
    (n : ℕ) (P : (Fin (n + 1) → F) → Prop)
    [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ tail : Fin n → F, (Finset.univ.filter fun x : F ↦ P (Fin.cons x tail)).card := by
  rw [Finset.card_filter]
  rw [show (∑ r : Fin (n + 1) → F, if P r then 1 else 0) =
      ∑ p : F × (Fin n → F), if P (Fin.cons p.1 p.2) then 1 else 0 by
    exact (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) ↦ F))
      (fun r : Fin (n + 1) → F ↦ if P r then 1 else 0)).symm]
  rw [Fintype.sum_prod_type]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

omit [Field F] in
private theorem sum_card_filter_const [Fintype F] {T : Type} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    (∑ t : T, (Finset.univ.filter fun _ : F ↦ P t).card) =
      Fintype.card F * (Finset.univ.filter P).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change Fintype.card F * (∑ x, if P x then 1 else 0) = _
  rfl

private theorem tensorFoldBound_succ (q exceptionalCount h : ℕ) :
    q ^ h * exceptionalCount +
        q * (2 * ((2 ^ h - 1) * exceptionalCount * q ^ (h - 1))) ≤
      (2 ^ (h + 1) - 1) * exceptionalCount * q ^ h := by
  cases h with
  | zero => simp
  | succ h =>
      simp only [Nat.succ_sub_one, Nat.pow_succ]
      have hp0 : 0 < 2 ^ h := pow_pos (by omega) h
      have hp : 1 ≤ 2 ^ h * 2 := by omega
      have hp2 : 1 ≤ 2 ^ h * 2 * 2 := by omega
      exact_mod_cast (show
        (q ^ h : ℤ) * q * exceptionalCount +
            q * (2 * (((2 ^ h : ℤ) * 2 - 1) * exceptionalCount * q ^ h)) ≤
          ((2 ^ h : ℤ) * 2 * 2 - 1) * exceptionalCount * (q ^ h * q) by
        ring_nf
        exact le_rfl)

/-- The set of shared-level challenge vectors at which some node is exceptional. -/
noncomputable def tensorFoldBad [Fintype F] [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hline : FullSetLineWitness C agreement exceptionalCount)
    (u : (Fin h → Bool) → ι → A) : Finset (Fin h → F) :=
  by
    classical
    exact Finset.univ.filter fun r ↦ ¬ TensorFoldGood hline r u

set_option maxHeartbeats 800000 in
/-- A binary height-`h` shared-level fold has at most `2^h - 1` line events.  Each event fixes
one field challenge to one of at most `exceptionalCount` values and leaves the other `h - 1`
levels free. -/
theorem tensorFoldBad_card_le [Fintype F] [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hline : FullSetLineWitness C agreement exceptionalCount)
    (u : (Fin h → Bool) → ι → A) :
    (tensorFoldBad hline u).card ≤
      (2 ^ h - 1) * exceptionalCount * Fintype.card F ^ (h - 1) := by
  classical
  induction h with
  | zero => simp [tensorFoldBad, TensorFoldGood]
  | succ h ih =>
      let u₀ : (Fin h → Bool) → ι → A := fun leaf ↦ u (Fin.cons false leaf)
      let u₁ : (Fin h → Bool) → ι → A := fun leaf ↦ u (Fin.cons true leaf)
      let childBad : (Fin h → F) → Prop := fun tail ↦
        ¬ TensorFoldGood hline tail u₀ ∨ ¬ TensorFoldGood hline tail u₁
      rw [tensorFoldBad, card_filter_fin_cons]
      have hpoint : ∀ tail : Fin h → F,
          (Finset.univ.filter fun x : F ↦
              ¬ TensorFoldGood hline (Fin.cons x tail) u).card ≤
            exceptionalCount +
              (Finset.univ.filter fun _ : F ↦ childBad tail).card := by
        intro tail
        let w₀ := binaryTensorFold tail u₀
        let w₁ := binaryTensorFold tail u₁
        let rootBad : F → Prop := fun x ↦ x ∈ lineExceptional hline w₀ w₁
        have hsubset :
            (Finset.univ.filter fun x : F ↦
                ¬ TensorFoldGood hline (Fin.cons x tail) u) ⊆
              (Finset.univ.filter rootBad) ∪
                (Finset.univ.filter fun _ : F ↦ childBad tail) := by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          rw [Finset.mem_union]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, rootBad, childBad]
          simp only [TensorFoldGood, Fin.tail_cons, Fin.cons_zero] at hx
          rcases not_and_or.mp hx with hx | hx
          · exact Or.inl (not_not.mp hx)
          · exact Or.inr (not_and_or.mp hx)
        calc
          _ ≤ ((Finset.univ.filter rootBad) ∪
                (Finset.univ.filter fun _ : F ↦ childBad tail)).card :=
            Finset.card_le_card hsubset
          _ ≤ (Finset.univ.filter rootBad).card +
                (Finset.univ.filter fun _ : F ↦ childBad tail).card :=
            Finset.card_union_le _ _
          _ ≤ exceptionalCount +
                (Finset.univ.filter fun _ : F ↦ childBad tail).card := by
            apply Nat.add_le_add_right
            simpa [rootBad] using lineExceptional_card_le hline w₀ w₁
      calc
        (∑ tail : Fin h → F, (Finset.univ.filter fun x : F ↦
              ¬ TensorFoldGood hline (Fin.cons x tail) u).card)
            ≤ ∑ tail : Fin h → F, (exceptionalCount +
                (Finset.univ.filter fun _ : F ↦ childBad tail).card) :=
          Finset.sum_le_sum fun tail _ ↦ hpoint tail
        _ = Fintype.card F ^ h * exceptionalCount +
              Fintype.card F * (Finset.univ.filter childBad).card := by
          rw [Finset.sum_add_distrib, sum_card_filter_const]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, nsmul_eq_mul]
          change Fintype.card F ^ h * exceptionalCount +
            Fintype.card F * (Finset.univ.filter childBad).card = _
          rfl
        _ ≤ Fintype.card F ^ h * exceptionalCount +
              Fintype.card F *
                (2 * ((2 ^ h - 1) * exceptionalCount *
                  Fintype.card F ^ (h - 1))) := by
          apply Nat.add_le_add_left
          apply Nat.mul_le_mul_left
          calc
            (Finset.univ.filter childBad).card
                ≤ (Finset.univ.filter fun tail ↦ ¬ TensorFoldGood hline tail u₀).card +
                    (Finset.univ.filter fun tail ↦ ¬ TensorFoldGood hline tail u₁).card := by
              rw [show (Finset.univ.filter childBad) =
                  (Finset.univ.filter fun tail ↦ ¬ TensorFoldGood hline tail u₀) ∪
                    (Finset.univ.filter fun tail ↦ ¬ TensorFoldGood hline tail u₁) by
                ext tail
                simp [childBad]]
              exact Finset.card_union_le _ _
            _ ≤ 2 * ((2 ^ h - 1) * exceptionalCount *
                  Fintype.card F ^ (h - 1)) := by
              have h₀ := ih u₀
              have h₁ := ih u₁
              simp only [tensorFoldBad] at h₀ h₁
              omega
        _ ≤ (2 ^ (h + 1) - 1) * exceptionalCount * Fintype.card F ^ h :=
          tensorFoldBound_succ (Fintype.card F) exceptionalCount h

/-- Outside the explicitly counted bad set, the complete tensor decomposition is available. -/
theorem hasFullTensorDecomposition_of_not_mem_bad [Fintype F] [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hline : FullSetLineWitness C agreement exceptionalCount)
    (r : Fin h → F) (u : (Fin h → Bool) → ι → A)
    (hr : r ∉ tensorFoldBad hline u) :
    HasFullTensorDecomposition C agreement r u := by
  apply hasFullTensorDecomposition_of_good hline r u
  simpa [tensorFoldBad] using hr

end TensorMCA
