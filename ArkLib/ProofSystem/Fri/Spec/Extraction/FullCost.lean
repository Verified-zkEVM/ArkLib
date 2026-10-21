/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.DriverCost
public import ArkLib.ProofSystem.Fri.Spec.Extraction.SetupCost
public import ArkLib.ProofSystem.Fri.Spec.Extraction.ExtractCost

/-!
# Full extractor profiles

The bounds refer to the exact instruction program defining retained-history extraction and cover
all histories, including final polynomials rejected before coefficient traversal. Counts concern
algebraic primitives and designated accesses or control ticks, rather than machine runtime.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- Final interpolation pays its coefficient-interpolation envelope and degree metadata check. -/
def finalInterpolationProfileBound (D : ℕ) (kind : CostKind) : ℕ :=
  embedArithmeticCost (Arithmetic.interpolationProfileBound D) kind +
    if kind = .inl .metadata then 1 else 0

/-- Every final interpolation branch stays within the interpolation-and-degree envelope. -/
theorem profile_interpolateSelection_apply_le (d : ℕ+)
    (state : Selection s o (foldingDegree s d 0)) (kind : CostKind) :
    (profile s o α (interpolateSelection s d o α state)).2 kind ≤
      finalInterpolationProfileBound (foldingDegree s d 0) kind := by
  unfold interpolateSelection finalInterpolationProfileBound
  by_cases hc : foldingDegree s d 0 ≤ state.count
  · simp only [hc, dite_true]
    refine profile_bind_apply_le s o α _ _ kind _ _ ?_ ?_
    · exact profile_liftComp_apply_le s o α _ _
        (Arithmetic.profileArithmetic_interpolate_le state.nodes state.values
          (foldingDegree s d 0)) kind
    intro p
    refine profile_bind_apply_le s o α _ _ kind
      (if kind = .inl .metadata then 1 else 0) 0 ?_ ?_
    · cases kind with
      | inl kind => cases kind <;> simp [instructionCost, AccessOp.costKind]
      | inr kind => simp [instructionCost, AccessOp.costKind]
    intro degree
    split_ifs <;> simp
  · simp [hc]

/-- The explicit whole-program envelope includes initialization, the complete scan, and recovery. -/
def extractorProfileBound (n : ℕ) {r : ℕ} (s : Fin (r + 1) → ℕ+) (d : ℕ+)
    (kind : CostKind) : ℕ :=
  initializationBound n s d.val kind +
    2 ^ n * scanCellProfileBound n (positionProfileBound s d.val) kind +
    (if kind = .inl .metadata then 1 else 0) +
    finalInterpolationProfileBound (foldingDegree s d 0) kind

/-- The named extractor's measured program satisfies every primitive-coordinate envelope. -/
theorem profile_extractProgram_apply_le (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n)
    (kind : CostKind) :
    (profile s o α (extractProgram s d hs o α)).2 kind ≤ extractorProfileBound n s d kind := by
  have hprep := profile_prepareInputs_apply_le s o α d kind
  unfold extractProgram
  rw [profile_bind]
  cases hi : (profile s o α (prepareInputs s o α d)).1 with
  | none =>
    simp only [hi, profile_pure, Pi.add_apply, Pi.zero_apply, add_zero]
    exact hprep.trans (by unfold extractorProfileBound; omega)
  | some input =>
    have hscan := profile_scan_apply_le s o α hs input.generator
      (checkPosition s o α hs input) (positionProfileBound s d.val)
      (profile_checkPosition_apply_le s o α hs input) (foldingDegree s d 0) kind
    let state := (profile s o α (scan s o α hs input.generator
      (checkPosition s o α hs input) (foldingDegree s d 0))).1
    have hfinal := profile_interpolateSelection_apply_le s o α d state.val kind
    simp only [hi, profile_bind, Pi.add_apply]
    dsimp only [state] at hfinal
    unfold extractorProfileBound
    omega

/-- Inversion counts include setup and the pairwise divisors of each interpolation. -/
theorem profile_extractProgram_inv_le (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n) :
    (profile s o α (extractProgram s d hs o α)).2 (.inl .inv) ≤
      1 + 2 ^ n * (∑ i, 2 ^ (s i).val * (2 ^ (s i).val - 1)) +
        foldingDegree s d 0 * (foldingDegree s d 0 - 1) := by
  simpa [extractorProfileBound, initializationBound, scanCellProfileBound,
    initialPointProfileBound, positionProfileBound, roundProfileBound,
    blockNodesProfileBound, blockValuesProfileBound,
    nextValueProfileBound,
    finalInterpolationProfileBound, Arithmetic.interpolationProfileBound,
    Arithmetic.evaluationProfileBound, embedArithmeticCost] using
      profile_extractProgram_apply_le s o α d hs (.inl .inv)

/-- Extraction uses at most two original-domain accesses, both during initialization. -/
theorem profile_extractProgram_domainRead_le (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n) :
    (profile s o α (extractProgram s d hs o α)).2 (.inr .domainRead) ≤ 2 := by
  simpa [extractorProfileBound, initializationBound, scanCellProfileBound,
    initialPointProfileBound, positionProfileBound, roundProfileBound,
    blockNodesProfileBound, blockValuesProfileBound,
    nextValueProfileBound,
    finalInterpolationProfileBound, embedArithmeticCost] using
      profile_extractProgram_apply_le s o α d hs (.inr .domainRead)

/-- Each folding challenge is read at most once during initialization. -/
theorem profile_extractProgram_challengeRead_le (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n) :
    (profile s o α (extractProgram s d hs o α)).2 (.inr .challengeRead) ≤ k + 1 := by
  simpa [extractorProfileBound, initializationBound, scanCellProfileBound,
    initialPointProfileBound, positionProfileBound, roundProfileBound,
    blockNodesProfileBound, blockValuesProfileBound,
    nextValueProfileBound,
    finalInterpolationProfileBound, embedArithmeticCost] using
      profile_extractProgram_apply_le s o α d hs (.inr .challengeRead)

/-- The final polynomial token contributes at most one immutable-input access. -/
theorem profile_extractProgram_finalPolynomialRead_le (d : ℕ+)
    (hs : (∑ j, (s j).val) ≤ n) :
    (profile s o α (extractProgram s d hs o α)).2 (.inr .finalPolynomialRead) ≤ 1 := by
  simpa [extractorProfileBound, initializationBound, scanCellProfileBound,
    initialPointProfileBound, positionProfileBound, roundProfileBound,
    blockNodesProfileBound, blockValuesProfileBound,
    nextValueProfileBound,
    finalInterpolationProfileBound, embedArithmeticCost] using
      profile_extractProgram_apply_le s o α d hs (.inr .finalPolynomialRead)

/-- Exactly one final-polynomial token is retrieved on every input, including early rejection. -/
theorem profile_extractProgram_finalPolynomialRead (d : ℕ+)
    (hs : (∑ j, (s j).val) ≤ n) :
    (profile s o α (extractProgram s d hs o α)).2 (.inr .finalPolynomialRead) = 1 := by
  apply Nat.le_antisymm (profile_extractProgram_finalPolynomialRead_le s o α d hs)
  have hprep : 1 ≤ (profile s o α (prepareInputs s o α d)).2
      (.inr .finalPolynomialRead) := by
    unfold prepareInputs
    rw [profile_bind, profile_readFinalPolynomial]
    change 1 ≤ 1 + _
    omega
  have hfirst : (profile s o α (prepareInputs s o α d)).2 (.inr .finalPolynomialRead) ≤
      (profile s o α (extractProgram s d hs o α)).2 (.inr .finalPolynomialRead) := by
    unfold extractProgram
    rw [profile_bind]
    exact Nat.le_add_right _ _
  exact hprep.trans hfirst

end Fri.Spec.Extractor
