/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.LayoutBlockFinder
import ArkLibTest.OracleReduction.Security.CoordinateWiseSpecialSoundness.BlockStructure

/-!
# A block and VCVio's block finder: concrete tests

The fixtures are those of the structure test: a block with a first coordinate over `ZMod 5`, a
second over `ZMod 3` and thresholds `(3, 2)`, so `1 + 2 + 1 = 4` children.

* The star of the fixtures has a block star as its image. The diagonal family, which has no pair of
  vectors differing in one coordinate only, does not, and neither does a family with a repeated
  vector, whose image has three members instead of four. A block star enumerates back to a star.
* `Block.error` and `Block.arity` read in `ℝ≥0∞` are `2/5 + 1/3` and `4`, and VCVio's block finder
  meets its contract at these values. Over an empty alphabet the cast of the error is not the
  finder's error, so the nonemptiness hypothesis of `Block.coe_error` is needed.
* `CoordEq` unfolds to `Function.DiffersOnlyAt`.
-/

open CoordinateWise CoordinateWiseLayoutTest

open scoped ENNReal NNReal

namespace CoordinateWiseBlockFinderTest

/-- The star of the fixtures, indexed by the children of `k`. -/
def star' : Fin (∑ u, (k u - 1) + 1) → ((u : Fin 2) → alph u) :=
  star ∘ Fin.cast (by decide)

/-- The image of the star is a block star. -/
example : IsBlockSpecialSound k (Finset.univ.image star') :=
  (isBlockSpecialSoundFamily_iff_isBlockSpecialSound k star').mp (by unfold star'; decide)

/-- The diagonal family, indexed by the children of thresholds `(2, 2)`. -/
def diagonal' : Fin (∑ u, ((![2, 2] : Fin 2 → ℕ) u - 1) + 1) → ((u : Fin 2) → alph u) :=
  diagonal ∘ Fin.cast (by decide)

/-- The image of the diagonal family is not a block star. -/
example : ¬ IsBlockSpecialSound ![2, 2] (Finset.univ.image diagonal') := fun h =>
  absurd ((isBlockSpecialSoundFamily_iff_isBlockSpecialSound _ diagonal').mpr h)
    (by unfold diagonal'; decide)

/-- A family with a repeated vector is not a star, and its image is not a block star. -/
def repeated' : Fin (∑ u, (k u - 1) + 1) → ((u : Fin 2) → alph u) :=
  ![vec 0 0, vec 1 0, vec 1 0, vec 0 1] ∘ Fin.cast (by decide)

example : ¬ IsBlockSpecialSound k (Finset.univ.image repeated') := fun h =>
  absurd ((isBlockSpecialSoundFamily_iff_isBlockSpecialSound _ repeated').mpr h)
    (by unfold repeated'; decide)

/-- The image of the star enumerates back to a star family with the same image. -/
example : ∃ c : Fin (∑ u, (k u - 1) + 1) → ((u : Fin 2) → alph u),
    IsBlockSpecialSoundFamily k c ∧ Finset.univ.image c = Finset.univ.image star' :=
  exists_isBlockSpecialSoundFamily_of_isBlockSpecialSound
    ((isBlockSpecialSoundFamily_iff_isBlockSpecialSound k star').mp (by unfold star'; decide))

/-- `CoordEq` is `Function.DiffersOnlyAt`. -/
example : Function.DiffersOnlyAt (0 : Fin 2) (vec 0 0) (vec 1 0) :=
  (by decide : CoordEq (0 : Fin 2) (vec 0 0) (vec 1 0))

instance (u : Fin 2) : Nonempty (alph u) := Block.Admissible.nonempty block block_admissible u

noncomputable instance : SampleableType block.Point := SampleableType.piOfFintype alph

/-- The error of the block is `2/5 + 1/3 = 11/15`. -/
theorem error_block : block.error = 11 / 15 := by
  simp only [Block.error, Fin.sum_univ_two]
  have h5 : Fintype.card (alph 0) = 5 := by decide
  have h3 : Fintype.card (alph 1) = 3 := by decide
  simp only [k, h5, h3]
  norm_num

/-- The error of the block, read in `ℝ≥0∞`, is `2/5 + 1/3`. -/
example : ((block.error : ℝ≥0) : ℝ≥0∞) = 2 / 5 + 1 / 3 := by
  rw [Block.coe_error block (Block.Admissible.nonempty block block_admissible), Fin.sum_univ_two]
  have h5 : Fintype.card (alph 0) = 5 := by decide
  have h3 : Fintype.card (alph 1) = 3 := by decide
  simp only [k, h5, h3, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The arity of the block, read in `ℝ≥0∞`, is `1 + 2 + 1 = 4`. -/
example : ((block.arity : ℕ) : ℝ≥0∞) = 1 + (2 + 1) := by
  rw [Block.coe_arity, Fin.sum_univ_two]
  simp [k]

/-- VCVio's block finder of the block meets the finder contract at error `11/15` and cost `4`,
through the two casts. -/
example : Rewinding.IsFinder
    (fun ρ X => IsBlockSpecialSound block.threshold X ∧ ∀ c ∈ X, ρ c = true)
    (OracleComp.blockFinder (S := block.Alphabet) block.threshold)
    (((11 / 15 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) 4 := by
  have h := OracleComp.isFinder_blockFinder (S := block.Alphabet) block.threshold
  rw [← Block.coe_error block (Block.Admissible.nonempty block block_admissible),
    ← Block.coe_arity, error_block, show block.arity = 4 by decide] at h
  exact_mod_cast h

/-- A block with one coordinate over the empty alphabet and threshold `2`. -/
abbrev emptyBlock : Block := ⟨1, fun _ => Fin 0, fun _ => 2⟩

/-- Over an empty alphabet the cast of `Block.error` is `0` and the finder's error is `⊤`. -/
example : ((emptyBlock.error : ℝ≥0) : ℝ≥0∞) ≠
    ∑ u, ((emptyBlock.threshold u - 1 : ℕ) : ℝ≥0∞) /
      (Fintype.card (emptyBlock.Alphabet u) : ℝ≥0∞) := by
  simp [Block.error]

end CoordinateWiseBlockFinderTest
