/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.TensorGenerator
public import ArkLib.Data.CodingTheory.ProximityGenerator.PolynomialGenerator

/-!
# Full agreement through shared-level binary tensor folds

This file gives a levelwise binary-fold interface whose exceptional set controls every parent at
one shared challenge level.  The induction preserves the complete common agreement set while it
opens all parents simultaneously, yielding one exceptional event per level.
-/

@[expose] public section

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

/-- Equality weights, indexed by the two children of a binary fold. -/
def binaryEqualityGenerator : Generator F Bool F :=
  fun r b ↦ if b then r else 1 - r

/-- The shared-level binary fold, recursively from the root challenge. -/
def binaryTensorFold : ∀ {h : ℕ}, (Fin h → F) → ((Fin h → Bool) → ι → A) → ι → A
  | 0, _, u => u default
  | _ + 1, r, u => binaryLineFold (r 0)
      (binaryTensorFold (Fin.tail r) (fun leaf ↦ u (Fin.cons false leaf)))
      (binaryTensorFold (Fin.tail r) (fun leaf ↦ u (Fin.cons true leaf)))

omit [Fintype ι] [DecidableEq ι] in
/-- The recursive binary fold is exactly the existing iterated tensor generator specialized to
the equality weights `1-r` and `r`. -/
theorem binaryTensorFold_eq_tensorGeneratorPi : ∀ {h : ℕ}
    (r : Fin h → F) (u : (Fin h → Bool) → ι → A),
    binaryTensorFold r u = fun i ↦
      ∑ leaf, PolynomialGenIsMCA.tensorGeneratorPi
        (fun _ ↦ binaryEqualityGenerator) r leaf • u leaf i := by
  intro h
  induction h with
  | zero =>
      intro r u
      funext i
      change u default i = ∑ leaf : Fin 0 → Bool,
        (∏ j : Fin 0, binaryEqualityGenerator (r j) (leaf j)) • u leaf i
      rw [Finset.univ_unique, Finset.sum_singleton, Finset.univ_eq_empty,
        Finset.prod_empty, one_smul]
      exact congrArg (fun leaf : Fin 0 → Bool ↦ u leaf i) (Subsingleton.elim _ _)
  | succ h ih =>
      intro r u
      funext i
      rw [binaryTensorFold]
      simp only [binaryLineFold, ih]
      rw [Finset.smul_sum, Finset.smul_sum]
      let e := Fin.consEquiv (fun _ : Fin (h + 1) ↦ Bool)
      have he (b : Bool) (tail : Fin h → Bool) : e (b, tail) = Fin.cons b tail := rfl
      rw [← e.sum_comp (fun leaf ↦
        PolynomialGenIsMCA.tensorGeneratorPi
          (fun _ ↦ binaryEqualityGenerator) r leaf • u leaf i)]
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [PolynomialGenIsMCA.tensorGeneratorPi, binaryEqualityGenerator, Fin.tail,
        Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, ↓reduceIte, Fin.cons_succ,
        he, mul_smul, Bool.false_eq_true, e]
      rw [add_comm]

/-- Positions on which every member of one finite family agrees with the corresponding member
of another family.  This is the common column set retained while a whole fold level is opened. -/
def familyAgreementSet {β : Type} [Fintype β] [DecidableEq A]
    (c u : β → ι → A) : Finset ι :=
  Finset.univ.filter fun i ↦ ∀ b, c b i = u b i

/-- A level certificate supplies one bounded exceptional set for every finite nonempty family of
binary lines.  Outside that set it opens all parent codewords simultaneously and preserves the
family's complete common agreement set.  Uniformity in the family type is what permits one shared
challenge to be charged once per tensor level, independently of that level's width. -/
def FullSetLevelWitness [DecidableEq A]
    (C : ModuleCode ι F A) (agreement exceptionalCount : ℕ) : Prop :=
  ∀ (β : Type) [Fintype β] [Nonempty β] (u₀ u₁ : β → ι → A),
    ∃ exceptional : Finset F,
      exceptional.card ≤ exceptionalCount ∧
      ∀ r ∉ exceptional, ∀ c : β → ι → A, (∀ b, c b ∈ C) →
        agreement ≤ (familyAgreementSet c
          (fun b ↦ binaryLineFold r (u₀ b) (u₁ b))).card →
        ∃ c₀ c₁ : β → ι → A,
          (∀ b, c₀ b ∈ C) ∧ (∀ b, c₁ b ∈ C) ∧
          (∀ b, c b = binaryLineFold r (c₀ b) (c₁ b)) ∧
          familyAgreementSet c (fun b ↦ binaryLineFold r (u₀ b) (u₁ b)) =
            familyAgreementSet c₀ u₀ ∩ familyAgreementSet c₁ u₁

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

noncomputable def levelExceptional [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    {β : Type} [Fintype β] [Nonempty β] (u₀ u₁ : β → ι → A) : Finset F :=
  Classical.choose (hlevel β u₀ u₁)

theorem levelExceptional_card_le [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    {β : Type} [Fintype β] [Nonempty β] (u₀ u₁ : β → ι → A) :
    (levelExceptional hlevel u₀ u₁).card ≤ exceptionalCount :=
  (Classical.choose_spec (hlevel β u₀ u₁)).1

theorem levelExceptional_good [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    {β : Type} [Fintype β] [Nonempty β] (u₀ u₁ : β → ι → A)
    {r : F} (hr : r ∉ levelExceptional hlevel u₀ u₁)
    {c : β → ι → A} (hc : ∀ b, c b ∈ C)
    (hagree : agreement ≤
      (familyAgreementSet c (fun b ↦ binaryLineFold r (u₀ b) (u₁ b))).card) :
    ∃ c₀ c₁ : β → ι → A,
      (∀ b, c₀ b ∈ C) ∧ (∀ b, c₁ b ∈ C) ∧
      (∀ b, c b = binaryLineFold r (c₀ b) (c₁ b)) ∧
      familyAgreementSet c (fun b ↦ binaryLineFold r (u₀ b) (u₁ b)) =
        familyAgreementSet c₀ u₀ ∩ familyAgreementSet c₁ u₁ :=
  (Classical.choose_spec (hlevel β u₀ u₁)).2 r hr c hc hagree

/-- Recursive complement of the one exceptional event charged at each remaining level.  The
current arrays depend only on later challenges, so the head challenge is tested only after those
arrays are fixed. -/
def TensorFoldFamilyGood [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount) :
    {β : Type} → [Fintype β] → [Nonempty β] →
      ∀ {h : ℕ}, (Fin h → F) → (β → (Fin h → Bool) → ι → A) → Prop
  | _, _, _, 0, _, _ => True
  | β, _, _, _ + 1, r, u =>
      let u₀ := fun b leaf ↦ u b (Fin.cons false leaf)
      let u₁ := fun b leaf ↦ u b (Fin.cons true leaf)
      let w₀ := fun b ↦ binaryTensorFold (Fin.tail r) (u₀ b)
      let w₁ := fun b ↦ binaryTensorFold (Fin.tail r) (u₁ b)
      r 0 ∉ levelExceptional hlevel w₀ w₁ ∧
        TensorFoldFamilyGood hlevel (β := β × Bool) (Fin.tail r)
          (fun p leaf ↦ if p.2 then u₁ p.1 leaf else u₀ p.1 leaf)

/-- The public good event starts the levelwise recursion from the singleton root family. -/
def TensorFoldGood [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (r : Fin h → F) (u : (Fin h → Bool) → ι → A) : Prop :=
  TensorFoldFamilyGood hlevel (β := Unit) r (fun _ ↦ u)

/-- Family form of the leaf decomposition invariant used by the levelwise induction. -/
private def HasFullTensorFamilyDecomposition [DecidableEq A]
    (C : ModuleCode ι F A) (agreement : ℕ) {β : Type} [Fintype β]
    {h : ℕ} (r : Fin h → F) (u : β → (Fin h → Bool) → ι → A) : Prop :=
  ∀ c : β → ι → A, (∀ b, c b ∈ C) →
    agreement ≤ (familyAgreementSet c
      (fun b ↦ binaryTensorFold r (u b))).card →
    ∃ leafCode : β → (Fin h → Bool) → ι → A,
      (∀ b leaf, leafCode b leaf ∈ C) ∧
      (∀ b, c b = binaryTensorFold r (leafCode b)) ∧
      familyAgreementSet c (fun b ↦ binaryTensorFold r (u b)) =
        Finset.univ.filter (fun i ↦ ∀ b leaf, leafCode b leaf i = u b leaf i)

set_option maxHeartbeats 800000 in
-- Witness assembly expands dependent function equalities at every level.
private theorem hasFullTensorFamilyDecomposition_of_good [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    {β : Type} [Fintype β] [Nonempty β]
    (r : Fin h → F) (u : β → (Fin h → Bool) → ι → A)
    (hgood : TensorFoldFamilyGood hlevel r u) :
    HasFullTensorFamilyDecomposition C agreement r u := by
  induction h generalizing β with
  | zero =>
      intro c hc hagree
      refine ⟨fun b _ ↦ c b, fun b _ ↦ hc b, fun _ ↦ ?_, ?_⟩
      · simp only [binaryTensorFold]
      · ext i
        change (i ∈ Finset.univ.filter (fun i ↦ ∀ b, c b i = u b default i)) ↔
          i ∈ Finset.univ.filter (fun i ↦ ∀ b leaf, c b i = u b leaf i)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi b leaf
          rw [Subsingleton.elim leaf default]
          exact hi b
        · intro hi b
          exact hi b default
  | succ h ih =>
      intro c hc hagree
      simp only [TensorFoldFamilyGood] at hgood
      let u₀ : β → (Fin h → Bool) → ι → A :=
        fun b leaf ↦ u b (Fin.cons false leaf)
      let u₁ : β → (Fin h → Bool) → ι → A :=
        fun b leaf ↦ u b (Fin.cons true leaf)
      let w₀ : β → ι → A := fun b ↦ binaryTensorFold (Fin.tail r) (u₀ b)
      let w₁ : β → ι → A := fun b ↦ binaryTensorFold (Fin.tail r) (u₁ b)
      have hroot := levelExceptional_good hlevel w₀ w₁ hgood.1 hc hagree
      obtain ⟨c₀, c₁, hc₀, hc₁, hcroot, hagreeRoot⟩ := hroot
      let c' : β × Bool → ι → A := fun p ↦ if p.2 then c₁ p.1 else c₀ p.1
      let u' : β × Bool → (Fin h → Bool) → ι → A := fun p leaf ↦
        if p.2 then u₁ p.1 leaf else u₀ p.1 leaf
      have hagreeExpanded : familyAgreementSet c' (fun p ↦
          binaryTensorFold (Fin.tail r) (u' p)) =
          familyAgreementSet c₀ w₀ ∩ familyAgreementSet c₁ w₁ := by
        ext i
        simp only [familyAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_inter]
        constructor
        · intro hi
          exact ⟨fun b ↦ by simpa [c', u', w₀] using hi (b, false),
            fun b ↦ by simpa [c', u', w₁] using hi (b, true)⟩
        · rintro ⟨h₀, h₁⟩ ⟨b, flag⟩
          cases flag <;> simp [c', u', w₀, w₁, h₀ b, h₁ b]
      have hagree' : agreement ≤
          (familyAgreementSet c' (fun p ↦ binaryTensorFold (Fin.tail r) (u' p))).card := by
        rw [hagreeExpanded, ← hagreeRoot]
        exact hagree
      have hc' : ∀ p, c' p ∈ C := by
        rintro ⟨b, flag⟩
        cases flag <;> simp [c', hc₀ b, hc₁ b]
      obtain ⟨leaf', hleaf', hc'eq, hagree'eq⟩ :=
        ih (Fin.tail r) u' hgood.2 c' hc' hagree'
      let leafCode : β → (Fin (h + 1) → Bool) → ι → A := fun b leaf ↦
        if leaf 0 then leaf' (b, true) (Fin.tail leaf)
        else leaf' (b, false) (Fin.tail leaf)
      refine ⟨leafCode, ?_, ?_, ?_⟩
      · intro b leaf
        by_cases hb : leaf 0 <;> simp only [leafCode, hb, ↓reduceIte]
        · exact hleaf' _ _
        · exact hleaf' _ _
      · intro b
        rw [hcroot b]
        simp only [binaryTensorFold]
        apply congrArg₂ (binaryLineFold (r 0))
        · have hfalse := hc'eq (b, false)
          simp only [c', Bool.false_eq_true, ↓reduceIte] at hfalse
          rw [hfalse]
          apply congrArg (binaryTensorFold (Fin.tail r))
          funext leaf
          simp [leafCode]
        · have htrue := hc'eq (b, true)
          simp only [c', ↓reduceIte] at htrue
          rw [htrue]
          apply congrArg (binaryTensorFold (Fin.tail r))
          funext leaf
          simp [leafCode]
      · change familyAgreementSet c
          (fun b ↦ binaryLineFold (r 0) (w₀ b) (w₁ b)) = _
        rw [hagreeRoot, ← hagreeExpanded, hagree'eq]
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hall b leaf
          by_cases hb : leaf 0
          · calc
              leafCode b leaf i = leaf' (b, true) (Fin.tail leaf) i := by
                simp [leafCode, hb]
              _ = u' (b, true) (Fin.tail leaf) i := hall (b, true) (Fin.tail leaf)
              _ = u b (Fin.cons true (Fin.tail leaf)) i := by rfl
              _ = u b leaf i := by rw [← hb, Fin.cons_self_tail]
          · have hbfalse : leaf 0 = false := Bool.eq_false_of_not_eq_true hb
            calc
              leafCode b leaf i = leaf' (b, false) (Fin.tail leaf) i := by
                simp [leafCode, hb]
              _ = u' (b, false) (Fin.tail leaf) i := hall (b, false) (Fin.tail leaf)
              _ = u b (Fin.cons false (Fin.tail leaf)) i := by rfl
              _ = u b leaf i := by rw [← hbfalse, Fin.cons_self_tail]
        · intro hall ⟨b, flag⟩ leaf
          cases flag
          · simpa [leafCode, u'] using hall b (Fin.cons false leaf)
          · simpa [leafCode, u'] using hall b (Fin.cons true leaf)

/-- Avoiding the single exceptional set at every level gives a complete leaf decomposition. -/
theorem hasFullTensorDecomposition_of_good [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (r : Fin h → F) (u : (Fin h → Bool) → ι → A)
    (hgood : TensorFoldGood hlevel r u) :
    HasFullTensorDecomposition C agreement r u := by
  have hfamily := hasFullTensorFamilyDecomposition_of_good hlevel r (fun _ : Unit ↦ u) hgood
  intro c hc hagree
  let cFamily : Unit → ι → A := fun _ ↦ c
  have hagreeFamily : agreement ≤
      (familyAgreementSet cFamily (fun _ ↦ binaryTensorFold r u)).card := by
    simpa [cFamily, familyAgreementSet, fullAgreementSet] using hagree
  obtain ⟨leafFamily, hleaf, hcEq, hagreeEq⟩ :=
    hfamily cFamily (fun _ ↦ hc) hagreeFamily
  refine ⟨leafFamily (), hleaf (), ?_, ?_⟩
  · exact hcEq ()
  · calc
      fullAgreementSet c (binaryTensorFold r u) =
          familyAgreementSet cFamily (fun _ ↦ binaryTensorFold r u) := by
        simp [cFamily, familyAgreementSet, fullAgreementSet]
      _ = Finset.univ.filter
          (fun i ↦ ∀ b leaf, leafFamily b leaf i = u leaf i) := hagreeEq
      _ = Finset.univ.filter
          (fun i ↦ ∀ leaf, leafFamily () leaf i = u leaf i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi leaf
          exact hi () leaf
        · intro hi _ leaf
          exact hi leaf

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

private theorem levelFoldBound_succ (q exceptionalCount h : ℕ) :
    q ^ h * exceptionalCount + q * (h * exceptionalCount * q ^ (h - 1)) ≤
      (h + 1) * exceptionalCount * q ^ h := by
  cases h with
  | zero => simp
  | succ h =>
      simp only [Nat.succ_sub_one, Nat.pow_succ]
      ring_nf
      exact le_rfl

/-- Bad challenge vectors for an arbitrary current family. -/
noncomputable def tensorFoldFamilyBad [Fintype F] [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    {β : Type} [Fintype β] [Nonempty β]
    (u : β → (Fin h → Bool) → ι → A) : Finset (Fin h → F) := by
  classical
  exact Finset.univ.filter fun r ↦ ¬ TensorFoldFamilyGood hlevel r u

/-- The set of shared-level challenge vectors at which some level is exceptional. -/
noncomputable def tensorFoldBad [Fintype F] [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (u : (Fin h → Bool) → ι → A) : Finset (Fin h → F) :=
  tensorFoldFamilyBad hlevel (fun _ : Unit ↦ u)

set_option maxHeartbeats 800000 in
-- The recurrence conditions on the later challenges before counting the current level.
private theorem tensorFoldFamilyBad_card_le [Fintype F] [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    {β : Type} [Fintype β] [Nonempty β]
    (u : β → (Fin h → Bool) → ι → A) :
    (tensorFoldFamilyBad hlevel u).card ≤
      h * exceptionalCount * Fintype.card F ^ (h - 1) := by
  classical
  induction h generalizing β with
  | zero => simp [tensorFoldFamilyBad, TensorFoldFamilyGood]
  | succ h ih =>
      let u₀ : β → (Fin h → Bool) → ι → A :=
        fun b leaf ↦ u b (Fin.cons false leaf)
      let u₁ : β → (Fin h → Bool) → ι → A :=
        fun b leaf ↦ u b (Fin.cons true leaf)
      let u' : β × Bool → (Fin h → Bool) → ι → A := fun p leaf ↦
        if p.2 then u₁ p.1 leaf else u₀ p.1 leaf
      let childBad : (Fin h → F) → Prop := fun tail ↦
        ¬ TensorFoldFamilyGood hlevel tail u'
      rw [tensorFoldFamilyBad, card_filter_fin_cons]
      have hpoint : ∀ tail : Fin h → F,
          (Finset.univ.filter fun x : F ↦
              ¬ TensorFoldFamilyGood hlevel (Fin.cons x tail) u).card ≤
            exceptionalCount +
              (Finset.univ.filter fun _ : F ↦ childBad tail).card := by
        intro tail
        let w₀ : β → ι → A := fun b ↦ binaryTensorFold tail (u₀ b)
        let w₁ : β → ι → A := fun b ↦ binaryTensorFold tail (u₁ b)
        let rootBad : F → Prop := fun x ↦ x ∈ levelExceptional hlevel w₀ w₁
        have hsubset :
            (Finset.univ.filter fun x : F ↦
                ¬ TensorFoldFamilyGood hlevel (Fin.cons x tail) u) ⊆
              (Finset.univ.filter rootBad) ∪
                (Finset.univ.filter fun _ : F ↦ childBad tail) := by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          rw [Finset.mem_union]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, rootBad, childBad]
          simp only [TensorFoldFamilyGood, Fin.tail_cons, Fin.cons_zero] at hx
          rcases not_and_or.mp hx with hx | hx
          · exact Or.inl (not_not.mp hx)
          · exact Or.inr hx
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
            simpa [rootBad] using levelExceptional_card_le hlevel w₀ w₁
      calc
        (∑ tail : Fin h → F, (Finset.univ.filter fun x : F ↦
              ¬ TensorFoldFamilyGood hlevel (Fin.cons x tail) u).card)
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
                (h * exceptionalCount * Fintype.card F ^ (h - 1)) := by
          apply Nat.add_le_add_left
          apply Nat.mul_le_mul_left
          simpa [childBad, tensorFoldFamilyBad] using ih u'
        _ ≤ (h + 1) * exceptionalCount * Fintype.card F ^ h :=
          levelFoldBound_succ (Fintype.card F) exceptionalCount h

/-- A height-`h` shared-level fold has one event per level.  Each event fixes one challenge to
one of at most `exceptionalCount` values and leaves the other `h - 1` levels free. -/
theorem tensorFoldBad_card_le [Fintype F] [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (u : (Fin h → Bool) → ι → A) :
    (tensorFoldBad hlevel u).card ≤
      h * exceptionalCount * Fintype.card F ^ (h - 1) := by
  simpa [tensorFoldBad] using
    tensorFoldFamilyBad_card_le hlevel (fun _ : Unit ↦ u)

/-- A height-zero fold has no exceptional challenge tuple. -/
theorem tensorFoldBad_eq_empty_height_zero [Fintype F] [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (u : (Fin 0 → Bool) → ι → A) : tensorFoldBad hlevel u = ∅ := by
  apply Finset.card_eq_zero.mp
  have hcard := tensorFoldBad_card_le hlevel u
  simpa using hcard

/-- Outside the explicitly counted bad set, the complete tensor decomposition is available. -/
theorem hasFullTensorDecomposition_of_not_mem_bad [Fintype F] [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount h : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (r : Fin h → F) (u : (Fin h → Bool) → ι → A)
    (hr : r ∉ tensorFoldBad hlevel u) :
    HasFullTensorDecomposition C agreement r u := by
  apply hasFullTensorDecomposition_of_good hlevel r u
  simpa [tensorFoldBad, tensorFoldFamilyBad, TensorFoldGood] using hr

end TensorMCA
