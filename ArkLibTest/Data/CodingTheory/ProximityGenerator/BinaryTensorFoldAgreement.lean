/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement
import Mathlib.Algebra.Field.ZMod

/-!
# Binary tensor-fold clients

These clients compute folds at `0/1` challenges and at a fractional challenge, build a full-set
level witness with no exceptional challenge for the full code at threshold equal to the block
length through `fullSetLevelWitness_of_uniformExactAgreement`, and use it to show that the bad
set of a height-three fold over `ZMod 3` is empty. They also check the interleaving and
parametrization lemmas at an empty row type and on a concrete line.
-/

open Code LinearCode TensorMCA CoreDefinitions

namespace BinaryTensorFoldAgreementTest

-- At challenges `0` and `1` the fold selects a leaf: bit `false` at `0`, bit `true` at `1`.
example (u : (Fin 2 → Bool) → Fin 3 → ℚ) :
    binaryTensorFold ![(0 : ℚ), 1] u = u ![false, true] := by
  funext i
  simp only [binaryTensorFold, binaryLineFold, Fin.tail]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, sub_zero, sub_self, one_smul, zero_smul,
    add_zero, zero_add]
  congr 1
  funext j
  fin_cases j <;> rfl

-- At `r = 1/2` the line fold is the average.
example : binaryLineFold (1 / 2 : ℚ) ![(2 : ℚ), 4] ![6, 0] = ![4, 2] := by
  funext i
  fin_cases i <;> norm_num [binaryLineFold]

-- The fold agrees with the tensor generator of the equality weights, here at height two.
example (r : Fin 2 → ℚ) (u : (Fin 2 → Bool) → Fin 3 → ℚ) :
    binaryTensorFold r u = fun i ↦
      ∑ leaf, PolynomialGenIsMCA.tensorGeneratorPi (fun _ ↦ binaryEqualityGenerator) r leaf •
        u leaf i :=
  binaryTensorFold_eq_tensorGeneratorPi r u

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The full code on two coordinates over `ZMod 3`. -/
abbrev fullCode : ModuleCode (Fin 2) (ZMod 3) (ZMod 3) := ⊤

-- Codewords of the full code agreeing on two coordinates of `Fin 2` agree everywhere.
theorem fullCode_determined : DeterminedByAgreement fullCode 2 := by
  intro c _ c' _ T hT hcc'
  have hT' : T = Finset.univ := Finset.eq_univ_of_card T (le_antisymm (card_finset_fin_le T) hT)
  subst hT'
  exact funext fun i ↦ hcc' i (Finset.mem_univ i)

-- No challenge is projection-bad for the full code: every word projects into it.
theorem fullCode_line (V : Bool → Fin 2 → ZMod 3) :
    UniformExactAgreement binaryEqualityGenerator fullCode 2 0 V := by
  refine uniformExactAgreement_of_encard_le fullCode_determined ?_
  have : {r | IsProjectionBad binaryEqualityGenerator fullCode 2 r V} = ∅ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨T, -, -, j, hj⟩
    exact hj ((mem_projectedCodeSubmod_iff _ T _).mpr ⟨V j, Submodule.mem_top, rfl⟩)
  simp [this]

/-- The full code at threshold `2` has a level witness with no exceptional challenge. -/
theorem fullCode_level : FullSetLevelWitness fullCode 2 0 :=
  fullSetLevelWitness_of_uniformExactAgreement fullCode_determined fullCode_line

-- The level witness is equivalent to the line guarantee.
example : FullSetLevelWitness fullCode 2 0 ↔ ∀ V, UniformExactAgreement binaryEqualityGenerator
    fullCode 2 0 V :=
  fullSetLevelWitness_iff fullCode_determined

-- With count `0`, every height-three fold has no bad challenge triple.
theorem fullCode_bad_empty (u : (Fin 3 → Bool) → Fin 2 → ZMod 3) :
    tensorFoldBad fullCode_level u = ∅ :=
  Finset.card_eq_zero.mp (Nat.le_zero.mp (by simpa using tensorFoldBad_card_le fullCode_level u))

-- So every challenge triple decomposes every close root codeword into codeword leaves.
example (r : Fin 3 → ZMod 3) (u : (Fin 3 → Bool) → Fin 2 → ZMod 3) :
    HasFullTensorDecomposition fullCode 2 r u :=
  hasFullTensorDecomposition_of_not_mem_bad fullCode_level r u (by
    rw [fullCode_bad_empty]
    exact Finset.notMem_empty r)

-- The height-zero fold has no bad challenge, for any level witness.
example {C : ModuleCode (Fin 2) (ZMod 3) (ZMod 3)} {a e : ℕ} (h : FullSetLevelWitness C a e)
    (u : (Fin 0 → Bool) → Fin 2 → ZMod 3) : tensorFoldBad h u = ∅ :=
  tensorFoldBad_eq_empty_height_zero h u

-- A level witness passes to interleavings with the same count, including an empty row type.
example : FullSetLevelWitness (fullCode^⋈(Fin 0)) 2 0 := fullCode_level.moduleInterleavedCode

example : FullSetLevelWitness (fullCode^⋈(Fin 5)) 2 0 := fullCode_level.moduleInterleavedCode

-- The general height-`h` count for the interleaved witness.
example {h : ℕ} (u : (Fin h → Bool) → Fin 2 → Fin 5 → ZMod 3) :
    (tensorFoldBad (fullCode_level.moduleInterleavedCode (κ := Fin 5)) u).card ≤
      h * 0 * Fintype.card (ZMod 3) ^ (h - 1) :=
  tensorFoldBad_card_le _ u

-- The binary line `(1 - r) • u₀ + r • u₁` is the affine line `u₀ + r • (u₁ - u₀)`: both
-- parametrizations have the same projection-bad challenges.
example {C : ModuleCode (Fin 2) ℚ ℚ} {a : ℕ} {r : ℚ} (u₀ u₁ : Fin 2 → ℚ) :
    IsProjectionBad binaryEqualityGenerator C a r (fun b ↦ if b then u₁ else u₀) ↔
      IsProjectionBad (AffineLineGenerator ℚ) C a r ![u₀, u₁ - u₀] :=
  isProjectionBad_binaryEqualityGenerator_iff _

end BinaryTensorFoldAgreementTest
