/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn, Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.NNRat.Defs

/-!
  # Blocks and layouts of one vector challenge

  A vector challenge is extracted in two ways at once. Inside a **block**, the extractor needs a
  star of siblings: a center and, for every coordinate, `k u - 1` siblings that differ from the
  center in that coordinate alone. Across the blocks of a **layout**, it branches as a nested tree:
  below every prefix of choices, the children of block `b` form a star of block `b`.

  Flat extraction is one block. Nested interpolation is one coordinate per block, and plain
  `k`-special soundness is one block with one coordinate. This file defines the data and the
  tree condition, with no protocol and no rewinding. The protocol-level structure is in
  `CoordinateWiseSpecialSoundness.BlockStructure`.

  ## Main definitions

  - `CoordinateWise.Block`: the width, alphabets and thresholds of one block. `Block.arity` is
    `1 + ∑ u, (k u - 1)`, `Block.IsStar` the star condition, and `Block.error` the sum
    `∑ u, (k u - 1) / |X u|`.
  - `CoordinateWise.Layout`: a sequence of blocks. `Layout.arity` is the product of the block
    arities, `Layout.pathEquiv` indexes the leaves of a tree by one child per block, and
    `Layout.IsTree` is the tree condition on a family of points indexed by the leaves.
  - `Layout.flat`, `Layout.nested`, `Layout.single`, `Layout.homogeneous`, `Layout.append`: the
    special layouts, with their arities.

  ## Computability

  Everything here is a proposition or computable data. The errors take values in `ℚ≥0` so that they
  can be evaluated.

  ## References

  * [Dao, Q., Bodaghi, O., Khajehpour, A., Vitto, G., Badakhshan, M., Georghiades, M., Liu, F.,
      Zhang, J., and Thaler, J., *Akita: A High-Performance Lattice-Based Polynomial Commitment
      Scheme*][DBKVBGLZT26]
-/

@[expose] public section

open scoped NNRat

namespace CoordinateWise

/-- One block of a vector challenge: `width` coordinates, each with an alphabet and a threshold.
Inside a block, the extractor needs a star family. -/
structure Block where
  /-- The number of coordinates of the block. -/
  width : ℕ
  /-- The alphabet of each coordinate. -/
  Alphabet : Fin width → Type
  /-- The number of distinct values needed at each coordinate. -/
  threshold : Fin width → ℕ

namespace Block

variable (B : Block)

/-- The points of a block: one value per coordinate. -/
abbrev Point : Type := (u : Fin B.width) → B.Alphabet u

/-- The number of children of a block node, `1 + ∑ u, (k u - 1)`. -/
def arity : ℕ := ∑ u, (B.threshold u - 1) + 1

/-- A family of points indexed by the children of a block node is a star. -/
def IsStar (c : Fin B.arity → B.Point) : Prop := IsBlockSpecialSoundFamily B.threshold c

instance [∀ u, DecidableEq (B.Alphabet u)] (c : Fin B.arity → B.Point) : Decidable (B.IsStar c) :=
  inferInstanceAs (Decidable (IsBlockSpecialSoundFamily B.threshold c))

/-- The sum `∑ u, (k u - 1) / |X u|` over the coordinates of a block. The block finder gives this
sum its meaning: it samples a uniform center and draws the siblings of each coordinate `u` without
replacement from the values of `X u` other than the center's, so no two children collide, and
`OracleComp.isFinder_blockFinder` (VCVio) proves its bound `ε ≤ κ + (1 - κ) p` at `κ` equal to this
sum. This file only defines it. -/
def error [∀ u, Fintype (B.Alphabet u)] : ℚ≥0 :=
  ∑ u, ((B.threshold u - 1 : ℕ) : ℚ≥0) / Fintype.card (B.Alphabet u)

theorem arity_pos : 0 < B.arity := Nat.succ_pos _

/-- Admissible thresholds: `1 ≤ k u ≤ |X u|` on finite alphabets. A threshold of `0` gives the same
arity as `1`, and a threshold above `|X u|` asks for more distinct values than exist. -/
def Admissible [∀ u, Fintype (B.Alphabet u)] : Prop :=
  ∀ u, 1 ≤ B.threshold u ∧ B.threshold u ≤ Fintype.card (B.Alphabet u)

theorem Admissible.nonempty [∀ u, Fintype (B.Alphabet u)] (h : B.Admissible) (u : Fin B.width) :
    Nonempty (B.Alphabet u) :=
  Fintype.card_pos_iff.mp ((h u).1.trans (h u).2)

end Block

/-- The layout of one vector challenge: a sequence of blocks. The extractor branches as a nested
tree across blocks and as a star inside each block. -/
structure Layout where
  /-- The number of blocks. -/
  depth : ℕ
  /-- The blocks, in the order of extraction. -/
  block : Fin depth → Block

namespace Layout

variable (L : Layout)

/-- The points of a layout: one point per block. -/
abbrev Point : Type := (b : Fin L.depth) → (L.block b).Point

/-- A leaf of a tree of the layout: one child index per block. -/
abbrev Path : Type := (b : Fin L.depth) → Fin (L.block b).arity

/-- The number of leaves of a tree of the layout, `∏ b, (1 + ∑ u ∈ b, (k u - 1))`. -/
def arity : ℕ := ∏ b, (L.block b).arity

/-- The leaves of a tree of the layout, as paths and as positions. -/
def pathEquiv : L.Path ≃ Fin L.arity := finPiFinEquiv

/-- The sum of the errors of the blocks. -/
def error [∀ b u, Fintype ((L.block b).Alphabet u)] : ℚ≥0 := ∑ b, (L.block b).error

/-- Every block is admissible. -/
def Admissible [∀ b u, Fintype ((L.block b).Alphabet u)] : Prop := ∀ b, (L.block b).Admissible

theorem arity_pos : 0 < L.arity :=
  Finset.prod_pos fun b _ => (L.block b).arity_pos

/-- A family `c` of points indexed by the leaves is a **tree** of the layout: the part of a leaf at
block `b` depends only on the path up to `b`, and below every prefix the children at block `b` form
a star of block `b`. -/
def IsTree (c : Fin L.arity → L.Point) : Prop :=
  (∀ (p p' : L.Path) (b : Fin L.depth), (∀ b', b' ≤ b → p b' = p' b') →
      c (L.pathEquiv p) b = c (L.pathEquiv p') b) ∧
  ∀ (p : L.Path) (b : Fin L.depth),
    (L.block b).IsStar (fun j => c (L.pathEquiv (Function.update p b j)) b)

/-! ### Special layouts -/

/-- Flat: one block. -/
abbrev flat (B : Block) : Layout := ⟨1, fun _ => B⟩

/-- Nested: one coordinate per block, with its own alphabet and threshold. -/
abbrev nested (m : ℕ) (A : Fin m → Type) (k : Fin m → ℕ) : Layout :=
  ⟨m, fun u => ⟨1, fun _ => A u, fun _ => k u⟩⟩

/-- One coordinate with threshold `k`: plain `k`-special soundness. -/
abbrev single (A : Type) (k : ℕ) : Layout := flat ⟨1, fun _ => A, fun _ => k⟩

/-- `ℓ` coordinates over one alphabet with one threshold. -/
abbrev homogeneous (ℓ : ℕ) (A : Type) (k : ℕ) : Layout := flat ⟨ℓ, fun _ => A, fun _ => k⟩

/-- The blocks of `L₁` followed by the blocks of `L₂`, for several vector challenges returned in
one answer. -/
def append (L₁ L₂ : Layout) : Layout := ⟨L₁.depth + L₂.depth, Fin.append L₁.block L₂.block⟩

theorem arity_flat (B : Block) : (flat B).arity = B.arity := by
  simp [arity]

theorem arity_homogeneous (ℓ : ℕ) (A : Type) (k : ℕ) :
    (homogeneous ℓ A k).arity = ℓ * (k - 1) + 1 := by
  simp [arity, Block.arity]

theorem arity_nested (m : ℕ) (A : Fin m → Type) (k : Fin m → ℕ) (hk : ∀ u, 1 ≤ k u) :
    (nested m A k).arity = ∏ u, k u := by
  simp only [arity, Block.arity, Finset.univ_unique, Finset.sum_singleton]
  exact Finset.prod_congr rfl fun u _ => Nat.sub_add_cancel (hk u)

theorem arity_append (L₁ L₂ : Layout) : (append L₁ L₂).arity = L₁.arity * L₂.arity := by
  unfold arity append
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- The flat and nested errors are the same sum. This only evaluates two sums. -/
theorem error_nested_eq_error_flat (m : ℕ) (A : Fin m → Type) (k : Fin m → ℕ)
    [∀ u, Fintype (A u)] : (nested m A k).error = (flat ⟨m, A, k⟩).error := by
  simp [error, Block.error]

/-- The position of a path of a flat layout is its only child index. -/
theorem pathEquiv_flat_apply (B : Block) (p : (flat B).Path) :
    (flat B).pathEquiv p = Fin.cast (arity_flat B).symm (p 0) := by
  refine Fin.ext ?_
  change (finPiFinEquiv p : ℕ) = _
  rw [finPiFinEquiv_apply]
  simp

/-- A tree of a flat layout is a star of its block. -/
theorem isTree_flat_iff (B : Block) (c : Fin (flat B).arity → (flat B).Point) :
    (flat B).IsTree c ↔ B.IsStar (fun j => c (Fin.cast (arity_flat B).symm j) 0) := by
  have hpath : ∀ (p : (flat B).Path) (j : Fin B.arity),
      (flat B).pathEquiv (Function.update p 0 j) = Fin.cast (arity_flat B).symm j := fun p j => by
    rw [pathEquiv_flat_apply]
    simp
  constructor
  · rintro ⟨-, h⟩
    have := h (fun _ => ⟨0, B.arity_pos⟩) 0
    simpa only [hpath] using this
  · intro h
    refine ⟨fun p p' b hb => ?_, fun p b => ?_⟩
    · have hp : p = p' := funext fun b' => by
        rw [Subsingleton.elim b' b]
        exact hb b le_rfl
      rw [hp]
    · rw [Subsingleton.elim b 0]
      simpa only [hpath] using h

/-- The points of a homogeneous layout are the vectors over its alphabet. -/
def homogeneousEquiv (ℓ : ℕ) (A : Type) (k : ℕ) : (Fin ℓ → A) ≃ (homogeneous ℓ A k).Point :=
  (Equiv.funUnique (Fin 1) (Fin ℓ → A)).symm

/-- The points of a single-coordinate layout are the elements of its alphabet. -/
def singleEquiv (A : Type) (k : ℕ) : A ≃ (single A k).Point :=
  (Equiv.funUnique (Fin 1) A).symm.trans (Equiv.funUnique (Fin 1) (Fin 1 → A)).symm

/-- The points of a nested layout are the families with one value per round. -/
def nestedEquiv (m : ℕ) (A : Fin m → Type) (k : Fin m → ℕ) :
    ((u : Fin m) → A u) ≃ (nested m A k).Point :=
  Equiv.piCongrRight fun u => (Equiv.funUnique (Fin 1) (A u)).symm

end Layout

end CoordinateWise
