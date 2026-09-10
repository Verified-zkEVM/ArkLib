/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageInputBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CanonicalGuardBounds
/-!
# Canonical-guard budgets from coefficient width and equation mass

These bounds replace the visited-equation sums by polynomial expressions in coefficient width,
derivative order, exponent mass, sample count and prefix length. They bound the existing guard
program's budgets, not a new oracle. Concrete base-field lowering remains a separate refinement.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CanonicalGuardMachine

open StageRootsMachine

/-- Uniform fuel per previous equation or terminal witness, including local dispatch. -/
def inputScanFuel (w d M n : ℕ) : ℕ := batchFuelBound w d M n + n + 7

/-- Uniform work per previous equation or terminal witness, including nested dispatch. -/
def inputScanWork (w d M n : ℕ) : ℕ :=
  batchWorkBound w d M n + 6 * batchFuelBound w d M n + 9 * n + 46

/-- Prefix length bounds the complete guard's fuel without inspecting equation values. -/
def inputFuel (w d M n p : ℕ) : ℕ := (p + 1) * inputScanFuel w d M n + 1

/-- Prefix length bounds the same guard's primitive charge. -/
def inputWork (w d M n p : ℕ) : ℕ := (p + 1) * inputScanWork w d M n + 4

variable {F : Type*} [Field F]

/-- The actual batch budgets used by a guard are bounded from numerical input sizes. -/
theorem residual_bounds (input : Input F) (q : Equation F) (w d M : ℕ)
    (hw : input.coefficients.length ≤ w) (hd : input.order ≤ d)
    (hm : MvPolynomial.PartialDerivativeMachine.inputMass q ≤ M) :
    ResidualBatchMachine.fuel (residualInput input q) input.samples.length ≤
        batchFuelBound w d M input.samples.length ∧
      (ResidualBatchMachine.cost (residualInput input q) input.samples.length).total ≤
        batchWorkBound w d M input.samples.length :=
  batch_bounds (residualInput input q) w d M input.samples.length
    (hw.trans (Nat.le_succ w)) hd hm

/-- Initial size bounds majorize each visited zero test and the terminal witness test. -/
theorem scan_input_bounds (input : Input F) (ps : List (Equation F)) (w d M : ℕ)
    (hw : input.coefficients.length ≤ w) (hd : input.order ≤ d)
    (hs : MvPolynomial.PartialDerivativeMachine.inputMass input.separant ≤ M)
    (hp : ∀ q ∈ ps, MvPolynomial.PartialDerivativeMachine.inputMass q ≤ M) :
    scanFuel input ps ≤ (ps.length + 1) * inputScanFuel w d M input.samples.length ∧
      scanWork input ps ≤ (ps.length + 1) * inputScanWork w d M input.samples.length := by
  obtain ⟨hsf, hsw⟩ := residual_bounds input input.separant w d M hw hd hs
  induction ps with
  | nil =>
      simp only [scanFuel, scanWork, List.length_nil, Nat.zero_add, one_mul]
      unfold witnessFuel witnessWork ResidualWitnessMachine.fuel
        ResidualWitnessMachine.workBound inputScanFuel inputScanWork
      constructor <;> omega
  | cons q ps ih =>
      obtain ⟨ht, hb⟩ := ih (fun r hr ↦ hp r (by simp [hr]))
      obtain ⟨hqf, hqw⟩ := residual_bounds input q w d M hw hd (hp q (by simp))
      simp only [scanFuel, scanWork, List.length_cons]
      unfold zeroWork ResidualZeroMachine.fuel
      dsimp only
      unfold inputScanFuel inputScanWork at *
      constructor <;> nlinarith

/-- Both complete existing guard budgets are polynomial in numerical sizes and a prefix cap. -/
theorem input_bounds (input : Input F) (ps : List (Equation F)) (w d M p : ℕ)
    (hw : input.coefficients.length ≤ w) (hd : input.order ≤ d)
    (hs : MvPolynomial.PartialDerivativeMachine.inputMass input.separant ≤ M)
    (hp : ∀ q ∈ ps, MvPolynomial.PartialDerivativeMachine.inputMass q ≤ M)
    (hlen : ps.length ≤ p) :
    fuel input ps ≤ inputFuel w d M input.samples.length p ∧
      workBound input ps ≤ inputWork w d M input.samples.length p := by
  obtain ⟨hf, hb⟩ := scan_input_bounds input ps w d M hw hd hs hp
  constructor
  · exact Nat.add_le_add_right (hf.trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right hlen 1))) 1
  · exact Nat.add_le_add_right (hb.trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right hlen 1))) 4

end ReedSolomon.HiddenDerivative.CanonicalGuardMachine
