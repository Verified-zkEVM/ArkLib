/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.BlockStructure
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.LayoutVecTree

/-!
# Blocks, layouts and the structure with layouts: concrete tests

A challenge with two coordinates, the first over `ZMod 5` and the second over `ZMod 3`, with
thresholds `(3, 2)`. As one block it is a star with `1 + 2 + 1 = 4` members. As two blocks of one
coordinate each it is a nested tree with `3 * 2 = 6` leaves. Both have the error
`2/5 + 1/3 = 11/15`, below one.
-/

open CoordinateWise ProtocolSpec

namespace CoordinateWiseLayoutTest

/-- The alphabet of coordinate `0` is `ZMod 5`, that of coordinate `1` is `ZMod 3`. -/
def alph : Fin 2 → Type
  | 0 => ZMod 5
  | 1 => ZMod 3

instance : ∀ u, DecidableEq (alph u)
  | 0 => inferInstanceAs (DecidableEq (ZMod 5))
  | 1 => inferInstanceAs (DecidableEq (ZMod 3))

instance : ∀ u, Fintype (alph u)
  | 0 => inferInstanceAs (Fintype (ZMod 5))
  | 1 => inferInstanceAs (Fintype (ZMod 3))

/-- The coordinate vector with the given entries. -/
def vec (a : ZMod 5) (b : ZMod 3) : (u : Fin 2) → alph u
  | 0 => a
  | 1 => b

/-- Thresholds `(3, 2)`. -/
def k : Fin 2 → ℕ := ![3, 2]

/-! ## Stars on dependent coordinates -/

/-- A star: center `(0, 0)`, two siblings in coordinate `0` and one in coordinate `1`. -/
def star : Fin 4 → ((u : Fin 2) → alph u) := ![vec 0 0, vec 1 0, vec 2 0, vec 0 1]

example : IsBlockSpecialSoundFamily k star := by decide

/-- The star is as small as a star can be: `∑ u, (k u - 1) + 1 = 4`. -/
example : ∑ u, (k u - 1) + 1 = 4 := by decide

example : ∑ u, (k u - 1) + 1 ≤ 4 := (show IsBlockSpecialSoundFamily k star by decide).card_ge

/-- Distinct vectors do not make a star: no two of them differ in one coordinate only. -/
def diagonal : Fin 3 → ((u : Fin 2) → alph u) := ![vec 0 0, vec 1 1, vec 2 2]

example : Function.Injective diagonal ∧ ¬ IsBlockSpecialSoundFamily ![2, 2] diagonal := by
  decide

/-- A family with a sibling in coordinate `1` but a repeated vector is not a star either. -/
example : ¬ IsBlockSpecialSoundFamily k ![vec 0 0, vec 1 0, vec 1 0, vec 0 1] := by decide

/-- Over one alphabet and one threshold the notion is `IsSpecialSoundFamily`. -/
example : IsSpecialSoundFamily 2 3
    (![![0, 0], ![1, 0], ![2, 0], ![0, 1], ![0, 2]] : Fin 5 → (Fin 2 → ZMod 5)) :=
  (isSpecialSoundFamily_iff_isBlockSpecialSoundFamily _).2 (by decide)

/-- `CoordEq` keeps its call sites: it applies to vectors over one alphabet. -/
example : CoordEq (0 : Fin 2) (![0, 0] : Fin 2 → ZMod 5) ![1, 0] := by decide

/-- A threshold above the size of the alphabet cannot be met. This is why admissible thresholds are
at most `|X u|`. -/
example (c : Fin 3 → (Fin 1 → Fin 2)) :
    ¬ IsBlockSpecialSoundFamily (S := fun _ : Fin 1 => Fin 2) (fun _ => 3) c := fun h => by
  have := Fintype.card_le_of_injective c h.1
  simp at this

/-! ## Blocks and layouts -/

/-- The block with both coordinates. -/
abbrev block : Block := ⟨2, alph, k⟩

example : block.arity = 4 := by decide

example : block.IsStar star := (by decide : IsBlockSpecialSoundFamily k star)

theorem block_admissible : block.Admissible := by
  intro u
  fin_cases u <;> exact ⟨by decide, by decide⟩

/-- Flat and nested layouts of the same coordinates. -/
abbrev flatLayout : Layout := Layout.flat block

abbrev nestedLayout : Layout := Layout.nested 2 alph k

example : flatLayout.arity = 4 := by decide

example : nestedLayout.arity = 6 := by decide

example : nestedLayout.arity = ∏ u, k u := Layout.arity_nested 2 alph k (by decide)

#eval flatLayout.error

#eval nestedLayout.error

example : flatLayout.error = 11 / 15 := by
  simp only [Layout.error, Block.error, Finset.univ_unique, Finset.sum_singleton, Fin.sum_univ_two]
  have h5 : Fintype.card (alph 0) = 5 := by decide
  have h3 : Fintype.card (alph 1) = 3 := by decide
  simp only [k, h5, h3]
  norm_num

example : nestedLayout.error = flatLayout.error := Layout.error_nested_eq_error_flat 2 alph k

/-! ## Trees of a layout -/

/-- The label of the leaf at position `q` of the nested layout: block `0` shows the first child
index `p₀ = q % 3`, block `1` shows `p₀ + p₁`, where `p₁ = q / 3`. Below a prefix, the children of
block `0` carry the distinct labels `0, 1, 2`, and the children of block `1` carry two distinct
labels. -/
def nestedTree (q : Fin 6) : nestedLayout.Point
  | 0 => fun _ => ((q.val % 3 : ℕ) : ZMod 5)
  | 1 => fun _ => ((q.val % 3 + q.val / 3 : ℕ) : ZMod 3)

example : nestedLayout.IsTree nestedTree := by
  unfold Layout.IsTree
  decide +kernel

/-- A tree whose block-`1` label ignores the second child index repeats a label below a prefix. -/
def collapsedTree (q : Fin 6) : nestedLayout.Point
  | 0 => fun _ => ((q.val % 3 : ℕ) : ZMod 5)
  | 1 => fun _ => ((q.val % 3 : ℕ) : ZMod 3)

example : ¬ nestedLayout.IsTree collapsedTree := by
  unfold Layout.IsTree
  decide +kernel

/-- A tree whose block-`0` label reads the second child index depends on a later branch. -/
def acausalTree (q : Fin 6) : nestedLayout.Point
  | 0 => fun _ => ((q.val / 3 : ℕ) : ZMod 5)
  | 1 => fun _ => ((q.val % 3 + q.val / 3 : ℕ) : ZMod 3)

example : ¬ nestedLayout.IsTree acausalTree := by
  unfold Layout.IsTree
  decide +kernel

/-- A tree of a layout is a structured vector tree over its blocks. -/
example : ∃ t : Rewinding.VecTree
    (fun b => (nestedLayout.block b).Point) (fun b => (nestedLayout.block b).arity),
      t.IsStructured (fun b => (nestedLayout.block b).IsStar) ∧
        ∀ p, nestedTree (nestedLayout.pathEquiv p) = t.leaf p :=
  (Layout.isTree_iff_vecTree (L := nestedLayout) nestedTree).1
    (by unfold Layout.IsTree; decide +kernel)

/-- The tree of a flat layout is a star of its block. -/
example : (Layout.flat block).IsTree (fun j _ => star (Fin.cast (by decide) j)) := by
  rw [Layout.isTree_flat_iff]
  unfold Block.IsStar
  exact (by decide)

/-! ## The structure with layouts -/

/-- A one-round protocol whose challenge is a vector over the alphabets `alph`. -/
abbrev pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], fun _ => (u : Fin 2) → alph u⟩

instance : Unique pSpec.ChallengeIdx where
  default := ⟨0, rfl⟩
  uniq _ := Subtype.ext (Subsingleton.elim _ _)

/-- The flat structure: one block with both coordinates. -/
abbrev Dflat : BlockCWSSStructure pSpec where
  layout := fun _ => flatLayout
  decompose := fun _ => (Equiv.funUnique (Fin 1) _).symm

/-- The nested structure: one coordinate per block. -/
abbrev Dnested : BlockCWSSStructure pSpec where
  layout := fun _ => nestedLayout
  decompose := fun _ => (Layout.nestedEquiv 2 alph k).symm.symm

example : Dflat.treeSize = 4 := by decide

example : Dnested.treeSize = 6 := by decide

example : Dflat.toShape.arity = fun _ => 4 := rfl

#eval Dflat.knowledgeError

#eval Dnested.knowledgeError

example : Dnested.knowledgeError = Dflat.knowledgeError := by
  unfold BlockCWSSStructure.knowledgeError
  simp only [Fintype.sum_unique]
  exact Layout.error_nested_eq_error_flat 2 alph k

example : Dnested.knowledgeError < 1 := by
  have h : Dnested.knowledgeError = 11 / 15 := by decide +kernel
  rw [h]
  norm_num

example : Dflat.Admissible := fun _ b => by
  fin_cases b
  exact block_admissible

/-- The blocks of the nested structure, in order: the sizes of their stars multiply to the tree
size. -/
example : Dnested.treeSize = ∏ β : Dnested.BlockIdx, (Dnested.blockOf β).arity :=
  Dnested.treeSize_eq_prod_blocks

/-- Plain `3`-special soundness of a one-round protocol with a `Bool` challenge, as a structure with
a layout, has the same shape and the same tree size as the homogeneous structure. -/
abbrev boolSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Bool]⟩

example (hk : ∀ i : boolSpec.ChallengeIdx, 2 ≤ (fun _ => 3) i) :
    (CWSSStructure.ofSpecialSound (fun _ => 3) hk).toBlock.toShape =
      (CWSSStructure.ofSpecialSound (fun _ => 3) hk).toShape :=
  CWSSStructure.toBlock_toShape _

example (hk : ∀ i : boolSpec.ChallengeIdx, 2 ≤ (fun _ => 3) i) :
    (CWSSStructure.ofSpecialSound (fun _ => 3) hk).toBlock.treeSize = 3 := by
  rw [CWSSStructure.toBlock_treeSize, Fintype.prod_unique]
  rfl

example : (BlockCWSSStructure.ofSpecialSound (pSpec := boolSpec) (fun _ => 3)).treeSize = 3 := by
  decide

end CoordinateWiseLayoutTest

/--
info: 'CoordinateWise.IsBlockSpecialSoundFamily.card_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CoordinateWise.IsBlockSpecialSoundFamily.card_ge

/--
info: 'CoordinateWise.isBlockSpecialSoundFamily_comp_equiv_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CoordinateWise.isBlockSpecialSoundFamily_comp_equiv_iff

/--
info: 'CoordinateWise.Layout.isTree_flat_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CoordinateWise.Layout.isTree_flat_iff

/--
info: 'CoordinateWise.Layout.isTree_iff_vecTree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CoordinateWise.Layout.isTree_iff_vecTree

/--
info: 'BlockCWSSStructure.treeSize_eq_prod_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BlockCWSSStructure.treeSize_eq_prod_blocks

/--
info: 'BlockCWSSStructure.knowledgeError_eq_sum_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BlockCWSSStructure.knowledgeError_eq_sum_blocks

/--
info: 'CWSSStructure.toBlock_toShape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CWSSStructure.toBlock_toShape

/--
info: 'CWSSStructure.toBlock_knowledgeError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CWSSStructure.toBlock_knowledgeError

/--
info: 'Verifier.treeSpecialSound_toBlock_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.treeSpecialSound_toBlock_iff
