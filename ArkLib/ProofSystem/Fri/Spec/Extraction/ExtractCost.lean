/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.LoopCost
public import ArkLib.ProofSystem.Fri.Spec.Extraction.GeneratorCost

/-!
# Complete extractor resource bounds

All bounds apply to the measured program defining the named extractor, including rejected
histories. The word-read bound counts the scan's actual local checks and bounded sample cache.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- Initialization performs no retained-word accesses on any input. -/
@[simp]
theorem profile_prepareInputs_word (d : ℕ+) :
    (profile s o α (prepareInputs s o α d)).2 (.inr .wordRead) = 0 := by
  by_cases hd : (finalPolynomial s o).natDegree < d.val <;>
    simp [prepareInputs, profile_bind, accessAnswer, hd, copyCoefficients,
      profile_arrayProgram_apply, profile_initGenerator, initRoundGenerator,
      embedArithmeticCost, instructionCost, AccessOp.costKind]

/-- Final interpolation accesses only cached arrays and candidate-polynomial degree metadata. -/
@[simp]
theorem profile_interpolateSelection_word (d : ℕ+)
    (state : Selection s o (foldingDegree s d 0)) :
    (profile s o α (interpolateSelection s d o α state)).2 (.inr .wordRead) = 0 := by
  by_cases hc : foldingDegree s d 0 ≤ state.count
  · simp [interpolateSelection, hc, profile_bind, embedArithmeticCost,
      instructionCost, AccessOp.costKind]
    split_ifs <;> simp
  · simp [interpolateSelection, hc]

/-- Extraction reads each checked block, each non-final successor, and at most one sample per
cached position. -/
theorem profile_extractProgram_word_le (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n) :
    (profile s o α (extractProgram s d hs o α)).2 (.inr .wordRead) ≤
      2 ^ n * ((∑ i, 2 ^ (s i).val) + k) + foldingDegree s d 0 := by
  have hprep := profile_prepareInputs_word s o α d
  unfold extractProgram
  rw [profile_bind]
  cases hi : (profile s o α (prepareInputs s o α d)).1 with
  | none => simp [hi, hprep]
  | some input =>
    have hscan := profile_scan_word_le s o α hs input.generator
      (checkPosition s o α hs input) ((∑ i, 2 ^ (s i).val) + k)
      (profile_checkPosition_word_le s o α hs input) (foldingDegree s d 0)
    simpa [hi, profile_bind, hprep] using hscan

end Fri.Spec.Extractor
