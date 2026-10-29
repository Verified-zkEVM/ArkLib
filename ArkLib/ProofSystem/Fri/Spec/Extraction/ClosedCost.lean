/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.FullCost
public import ArkLib.ProofSystem.Fri.Spec.Extraction.GeneratorBudget

/-!
# Closed field-operation bounds for extraction

The bounds combine the complete measured-program envelopes with cubic interpolation and quadratic
power-sum evaluation budgets. Addition and subtraction share one interpolation budget, and the
final polynomial contributes one evaluation per position, only in the final folding round.
-/

@[expose] public section

namespace Fri.Spec.Extractor

open CompPoly

/-- A cubic budget for one interpolation's combined additions/subtractions, multiplications,
or equality tests. -/
def interpolationBudget (m : ℕ) : ℕ := 100 * (m + 1) ^ 3

/-- A quadratic budget for one power-sum evaluation's additions or multiplications. -/
def evaluationBudget (m : ℕ) : ℕ := (m + 1) ^ 2

/-- The multiplication budget for initializing the domain ratio and all folding-block roots. -/
def initializationFieldBudget (n : ℕ) {k : ℕ} (s : Fin (k + 1) → ℕ+) : ℕ :=
  1 + ∑ i, (n - (s i).val)

/-- A common bound for combined additions/subtractions, multiplications, or equality tests. -/
def fieldBudget (n : ℕ) {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+) : ℕ :=
  2 ^ n * (generationBudget n s +
    (∑ i, (interpolationBudget (2 ^ (s i).val) +
      evaluationBudget (2 ^ (s i).val) + 1)) + evaluationBudget d.val) +
    interpolationBudget (foldingDegree s d 0) + initializationFieldBudget n s

private theorem sum_final_value (k a : ℕ) :
    (∑ i : Fin (k + 1), if i.val < k then 0 else a) = a := by
  rw [Fin.sum_univ_castSucc]
  simp

private theorem extractorProfileBound_eq (n : ℕ) {k : ℕ} (s : Fin (k + 1) → ℕ+)
    (d : ℕ+) :
    extractorProfileBound n s d (.inl .eq) =
      2 ^ n * (∑ i, (Arithmetic.interpolationProfileBound (2 ^ (s i).val) .eq + 1)) +
        Arithmetic.interpolationProfileBound (foldingDegree s d 0) .eq := by
  simp [extractorProfileBound, initializationBound, scanCellProfileBound,
    initialPointProfileBound, positionProfileBound, roundProfileBound, blockNodesProfileBound,
    blockValuesProfileBound, nextValueProfileBound, finalInterpolationProfileBound,
    Arithmetic.evaluationProfileBound, embedArithmeticCost]

private theorem extractorProfileBound_add_sub (n : ℕ) {k : ℕ}
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) :
    extractorProfileBound n s d (.inl .add) + extractorProfileBound n s d (.inl .sub) =
      2 ^ n * ((∑ i, (Arithmetic.interpolationProfileBound (2 ^ (s i).val) .add +
        Arithmetic.interpolationProfileBound (2 ^ (s i).val) .sub + 2 ^ (s i).val)) + d.val) +
      (Arithmetic.interpolationProfileBound (foldingDegree s d 0) .add +
        Arithmetic.interpolationProfileBound (foldingDegree s d 0) .sub) := by
  simp [extractorProfileBound, initializationBound, scanCellProfileBound,
    initialPointProfileBound, positionProfileBound, roundProfileBound, blockNodesProfileBound,
    blockValuesProfileBound, nextValueProfileBound, finalInterpolationProfileBound,
    Arithmetic.evaluationProfileBound, embedArithmeticCost, Finset.sum_add_distrib,
    sum_final_value, Nat.mul_add]
  ring

private theorem extractorProfileBound_mul (n : ℕ) {k : ℕ} (s : Fin (k + 1) → ℕ+)
    (d : ℕ+) :
    extractorProfileBound n s d (.inl .mul) = initializationFieldBudget n s +
      2 ^ n * ((2 * n + 1 + (∑ i, (foldingPrefix s i.castSucc +
        2 ^ (s i).val * (2 * (s i).val + 1) + (s i).val))) +
        (∑ i, (Arithmetic.interpolationProfileBound (2 ^ (s i).val) .mul +
          (2 ^ (s i).val) ^ 2)) + d.val ^ 2) +
      Arithmetic.interpolationProfileBound (foldingDegree s d 0) .mul := by
  simp [extractorProfileBound, initializationBound, initializationFieldBudget,
    scanCellProfileBound, initialPointProfileBound, positionProfileBound, roundProfileBound,
    blockNodesProfileBound, blockValuesProfileBound, nextValueProfileBound,
    finalInterpolationProfileBound, Arithmetic.evaluationProfileBound, embedArithmeticCost,
    Finset.sum_add_distrib, sum_final_value, Nat.mul_add]
  ring

private theorem le_evaluationBudget (m : ℕ) : m ≤ evaluationBudget m := by
  unfold evaluationBudget
  nlinarith

private theorem sq_le_evaluationBudget (m : ℕ) : m ^ 2 ≤ evaluationBudget m :=
  Nat.pow_le_pow_left (Nat.le_succ m) 2

/-- Combined addition and subtraction envelopes share one cubic interpolation budget. -/
theorem extractorProfileBound_add_sub_le (n : ℕ) {k : ℕ}
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) :
    extractorProfileBound n s d (.inl .add) + extractorProfileBound n s d (.inl .sub) ≤
      fieldBudget n s d := by
  have hsum : (∑ i, (Arithmetic.interpolationProfileBound (2 ^ (s i).val) .add +
        Arithmetic.interpolationProfileBound (2 ^ (s i).val) .sub + 2 ^ (s i).val)) ≤
      ∑ i, (interpolationBudget (2 ^ (s i).val) +
        evaluationBudget (2 ^ (s i).val) + 1) := by
    apply Finset.sum_le_sum
    intro i _
    have hI := Arithmetic.interpolationProfileBound_add_sub_le (2 ^ (s i).val)
    have hE := le_evaluationBudget (2 ^ (s i).val)
    change _ ≤ interpolationBudget _ at hI
    omega
  have hfinal := Arithmetic.interpolationProfileBound_add_sub_le (foldingDegree s d 0)
  have heval := le_evaluationBudget d.val
  change _ ≤ interpolationBudget _ at hfinal
  rw [extractorProfileBound_add_sub]
  calc
    _ ≤ 2 ^ n * (generationBudget n s +
        (∑ i, (interpolationBudget (2 ^ (s i).val) +
          evaluationBudget (2 ^ (s i).val) + 1)) + evaluationBudget d.val) +
        interpolationBudget (foldingDegree s d 0) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) hfinal
    _ ≤ fieldBudget n s d := Nat.le_add_right _ _

/-- Multiplication envelopes include one final-polynomial evaluation per initial position. -/
theorem extractorProfileBound_mul_le (n : ℕ) {k : ℕ}
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (hs : (∑ i, (s i).val) ≤ n) :
    extractorProfileBound n s d (.inl .mul) ≤ fieldBudget n s d := by
  have hsum : (∑ i, (Arithmetic.interpolationProfileBound (2 ^ (s i).val) .mul +
        (2 ^ (s i).val) ^ 2)) ≤
      ∑ i, (interpolationBudget (2 ^ (s i).val) +
        evaluationBudget (2 ^ (s i).val) + 1) := by
    apply Finset.sum_le_sum
    intro i _
    have hI := Arithmetic.interpolationProfileBound_le (2 ^ (s i).val) .mul
    have hE := sq_le_evaluationBudget (2 ^ (s i).val)
    change _ ≤ interpolationBudget _ at hI
    omega
  have hgen := generation_mul_le s hs
  have heval := sq_le_evaluationBudget d.val
  have hfinal := Arithmetic.interpolationProfileBound_le (foldingDegree s d 0) .mul
  change _ ≤ interpolationBudget _ at hfinal
  have hper : (2 * n + 1 + (∑ i, (foldingPrefix s i.castSucc +
        2 ^ (s i).val * (2 * (s i).val + 1) + (s i).val))) +
        (∑ i, (Arithmetic.interpolationProfileBound (2 ^ (s i).val) .mul +
          (2 ^ (s i).val) ^ 2)) + d.val ^ 2 ≤
      generationBudget n s +
        (∑ i, (interpolationBudget (2 ^ (s i).val) +
          evaluationBudget (2 ^ (s i).val) + 1)) + evaluationBudget d.val := by omega
  rw [extractorProfileBound_mul]
  calc
    _ ≤ initializationFieldBudget n s +
        2 ^ n * (generationBudget n s +
          (∑ i, (interpolationBudget (2 ^ (s i).val) +
            evaluationBudget (2 ^ (s i).val) + 1)) + evaluationBudget d.val) +
          interpolationBudget (foldingDegree s d 0) :=
      Nat.add_le_add
        (Nat.add_le_add_left (Nat.mul_le_mul_left (2 ^ n) hper) _) hfinal
    _ = fieldBudget n s d := by
      unfold fieldBudget
      omega

/-- Equality-test envelopes fit the common cubic field-operation budget. -/
theorem extractorProfileBound_eq_le (n : ℕ) {k : ℕ}
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) :
    extractorProfileBound n s d (.inl .eq) ≤ fieldBudget n s d := by
  have hsum : (∑ i, (Arithmetic.interpolationProfileBound (2 ^ (s i).val) .eq + 1)) ≤
      ∑ i, (interpolationBudget (2 ^ (s i).val) +
        evaluationBudget (2 ^ (s i).val) + 1) := by
    apply Finset.sum_le_sum
    intro i _
    have hI := Arithmetic.interpolationProfileBound_le (2 ^ (s i).val) .eq
    change _ ≤ interpolationBudget _ at hI
    omega
  have hfinal := Arithmetic.interpolationProfileBound_le (foldingDegree s d 0) .eq
  change _ ≤ interpolationBudget _ at hfinal
  rw [extractorProfileBound_eq]
  calc
    _ ≤ 2 ^ n * (generationBudget n s +
        (∑ i, (interpolationBudget (2 ^ (s i).val) +
          evaluationBudget (2 ^ (s i).val) + 1)) + evaluationBudget d.val) +
        interpolationBudget (foldingDegree s d 0) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) hfinal
    _ ≤ fieldBudget n s d := Nat.le_add_right _ _

section MeasuredProgram

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : Domain.SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, Fri.Spec.FinalOracleStatement s ω j)
variable (α : Fri.Spec.FinalStatement F k)

/-- Combined additions and subtractions of the actual extraction program obey one closed budget. -/
theorem profile_extractProgram_add_sub_le (d : ℕ+) (hs : (∑ i, (s i).val) ≤ n) :
    (profile s o α (extractProgram s d hs o α)).2 (.inl .add) +
      (profile s o α (extractProgram s d hs o α)).2 (.inl .sub) ≤ fieldBudget n s d :=
  (Nat.add_le_add (profile_extractProgram_apply_le s o α d hs (.inl .add))
    (profile_extractProgram_apply_le s o α d hs (.inl .sub))).trans
    (extractorProfileBound_add_sub_le n s d)

/-- Multiplications of the actual extraction program obey the closed field-operation budget. -/
theorem profile_extractProgram_mul_le (d : ℕ+) (hs : (∑ i, (s i).val) ≤ n) :
    (profile s o α (extractProgram s d hs o α)).2 (.inl .mul) ≤ fieldBudget n s d :=
  (profile_extractProgram_apply_le s o α d hs (.inl .mul)).trans
    (extractorProfileBound_mul_le n s d hs)

/-- Field equality tests of the actual extraction program obey the closed budget. -/
theorem profile_extractProgram_eq_le (d : ℕ+) (hs : (∑ i, (s i).val) ≤ n) :
    (profile s o α (extractProgram s d hs o α)).2 (.inl .eq) ≤ fieldBudget n s d :=
  (profile_extractProgram_apply_le s o α d hs (.inl .eq)).trans
    (extractorProfileBound_eq_le n s d)

end MeasuredProgram
end Fri.Spec.Extractor
