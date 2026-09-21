/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement

/-!
# Scalar exact power agreement clients

These clients check that `k ≤ a` cannot be dropped from `determinedByAgreement_code`, compute
the uniform guarantee for a single received word with no exceptional challenge, and transport it
to the code-level predicate.
-/

open Polynomial ReedSolomon CoreDefinitions

namespace PowerAgreementTest

/-- The evaluation points `0, 1, 2` in `ℚ`. -/
def domain3 : Fin 3 ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

@[simp] theorem domain3_apply (i : Fin 3) : domain3 i = ((i : ℕ) : ℚ) := rfl

-- `k ≤ a` is needed: the codewords of `X` and `0` agree at the point `0` but differ.
example : ¬ Code.DeterminedByAgreement (code domain3 2) 1 := fun h ↦ by
  have hX : evalOnPoints domain3 X ∈ code domain3 2 :=
    evalOnPoints_mem_code_of_degree_lt (by rw [degree_X]; decide)
  have := congrFun (h _ hX 0 (Submodule.zero_mem _) {0} (by simp)
    (by simp [evalOnPoints])) 1
  simp [evalOnPoints] at this

-- With `k ≤ a` it holds.
example : Code.DeterminedByAgreement (code domain3 2) 2 := determinedByAgreement_code domain3 le_rfl

-- A single received word needs no challenge: the guarantee holds with no exceptional value, for
-- every degree bound and threshold, including `k` larger than the block length.
theorem uniformExactPowerAgreement_single {F ι : Type} [Field F] [Fintype ι] [DecidableEq F]
    (domain : ι ↪ F) (w : Fin 1 → ι → F) (k L : ℕ) :
    UniformExactPowerAgreement domain w k L 0 := by
  refine ⟨∅, by simp, fun z _ Q hQ _ ↦ ?_⟩
  refine (hasExactPowerAgreement_id_iff _ _ _ _ _).mpr ⟨fun _ ↦ Q, fun _ ↦ hQ, ?_, ?_⟩
  · simp [powerBatchedPolynomial]
  · ext i
    simp [powerBatchedWord]

-- The same statement at the code level, for `univariatePowersGenerator F 0`.
example {F ι : Type} [Field F] [Fintype ι] [DecidableEq F] (domain : ι ↪ F)
    (w : Fin 1 → ι → F) (k L : ℕ) :
    Code.UniformExactAgreement (univariatePowersGenerator F 0) (code domain k) L 0 w :=
  (uniformExactPowerAgreement_iff_uniformExactAgreement domain w).mp
    (uniformExactPowerAgreement_single domain w k L)

-- Batching preserves degree bounds, and evaluation commutes with it, on a concrete pair.
example : (powerBatchedPolynomial ![(1 : ℚ[X]), X] 2).eval 3 = 7 := by
  simp [powerBatchedPolynomial_eval, Fin.sum_univ_two]
  norm_num

end PowerAgreementTest
