/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn, Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Layout
public import VCVio.CryptoFoundations.Rewinding.Finder

/-!
  # Trees of a layout as challenge trees of a rewinding finder

  A finder of the VCVio rewinding framework returns a `Rewinding.VecTree`: a challenge vector for
  every branch path, where the challenge of a round depends only on the branches up to that round.
  A tree of a layout (`CoordinateWise.Layout.IsTree`) is such a tree over the blocks of the layout,
  read through `Layout.pathEquiv`, whose nodes satisfy the star condition of their block.

  This file and `LayoutBlockFinder.lean`, which relates a block to VCVio's block finder, are the
  only places where the layouts meet the rewinding framework. The files that define layouts and
  structures import neither, so the protocol layer does not depend on the finder.

  ## Main results

  - `CoordinateWise.Layout.IsTree.toVecTree`: a tree of a layout as a `VecTree` over its blocks.
  - `CoordinateWise.Layout.IsTree.isStructured`: the star condition at every node of that tree.
  - `CoordinateWise.Layout.isTree_iff_vecTree`: a family indexed by the leaves is a tree of the
    layout exactly when it is the leaf function of a structured `VecTree`.

  ## References

  * [Dao, Q., Bodaghi, O., Khajehpour, A., Vitto, G., Badakhshan, M., Georghiades, M., Liu, F.,
      Zhang, J., and Thaler, J., *Akita: A High-Performance Lattice-Based Polynomial Commitment
      Scheme*][DBKVBGLZT26]
-/

@[expose] public section

namespace CoordinateWise.Layout

variable {L : Layout}

/-- A tree of a layout is a vector tree over its blocks: the leaf at a path is the family at that
position. -/
def IsTree.toVecTree {c : Fin L.arity → L.Point} (h : L.IsTree c) :
    Rewinding.VecTree (fun b => (L.block b).Point) (fun b => (L.block b).arity) where
  leaf p := c (L.pathEquiv p)
  causal := h.1

/-- Every node of the vector tree of a layout tree is a star of its block. -/
theorem IsTree.isStructured {c : Fin L.arity → L.Point} (h : L.IsTree c) :
    h.toVecTree.IsStructured (fun b => (L.block b).IsStar) :=
  fun p b => h.2 p b

/-- A family indexed by the leaves is a tree of the layout exactly when it is the leaf function of
a structured vector tree over the blocks. -/
theorem isTree_iff_vecTree (c : Fin L.arity → L.Point) :
    L.IsTree c ↔
      ∃ t : Rewinding.VecTree (fun b => (L.block b).Point) (fun b => (L.block b).arity),
        t.IsStructured (fun b => (L.block b).IsStar) ∧ ∀ p, c (L.pathEquiv p) = t.leaf p := by
  constructor
  · intro h
    exact ⟨h.toVecTree, h.isStructured, fun _ => rfl⟩
  · rintro ⟨t, ht, hc⟩
    refine ⟨fun p p' b hpp' => ?_, fun p b => ?_⟩
    · rw [hc, hc]
      exact t.causal p p' b hpp'
    · simp only [hc]
      exact ht p b

end CoordinateWise.Layout
