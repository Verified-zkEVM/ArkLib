/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageRootsSemantics
/-!
# A single alphabet exponent for all active stages

Each stage contributes its existing polynomial per-jet budget. The maximum original derivative
order bounds all alphabet exponents, and summing the stage polynomials introduces no new exponent.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.StageRootsMachine

open PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Per-stage polynomial step factor, with every alphabet exponent removed. -/
def fuelPolynomial (input : Input F) (D L n : ℕ) (stage : Stage F) : ℕ :=
  match stage.selected with
  | none => 2
  | some (i, _) =>
      JetRootsMachine.itemFuel (CenterRootsMachine.centerInput
        (centerInput input stage (i - 1)) 0) D L n + 32 * (i - 1 + 2) + 20

/-- Per-stage polynomial work factor, including child wrappers and output conversion. -/
def workPolynomial (input : Input F) (D L n : ℕ) (stage : Stage F) : ℕ :=
  match stage.selected with
  | none => 13
  | some (i, _) =>
      let ji := CenterRootsMachine.centerInput (centerInput input stage (i - 1)) 0
      JetRootsMachine.itemWork ji D L n + 6 * JetRootsMachine.itemFuel ji D L n +
        704 * (i - 1 + 2) + 200

/-- Every actual selected order is at most the original maximum derivative order. -/
theorem chain_orders {d : ℕ} {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages) :
    ∀ stage ∈ stages, ∀ i e, stage.selected = some (i, e) → i - 1 ≤ d := by
  induction hchain with
  | terminal layout rep nonzero last =>
      intro stage hm i e hs
      have he := List.mem_singleton.mp hm
      subst stage
      cases hs
  | active j layout rep nonzero highest next ih =>
      intro stage hm i e hs
      rcases List.mem_cons.mp hm with rfl | hm
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs
        rw [← hs.1, Nat.add_sub_cancel]
        exact Nat.le_of_lt_succ j.isLt
      · exact ih stage hm i e hs

omit [Field F] [DecidableEq F] in
/-- A stage's count is bounded by the single original-order alphabet factor. -/
theorem stageCount_le (input : Input F) (d : ℕ) (hq : 0 < input.alphabet.length)
    (stage : Stage F) (ho : ∀ i e, stage.selected = some (i, e) → i - 1 ≤ d) :
    stageCount input stage ≤ input.alphabet.length ^ (d + 2) := by
  cases hs : stage.selected with
  | none => simp [stageCount, hs]
  | some pair =>
      rcases pair with ⟨i, e⟩
      have hi := ho i e hs
      simpa only [stageCount, hs] using
        Nat.pow_le_pow_right (show 0 < input.alphabet.length from hq) (show i - 1 + 2 ≤ d + 2 by
          omega)

omit [DecidableEq F] in
/-- Stage fuel has one original-order alphabet factor times an explicit polynomial. -/
theorem stageFuel_le (input : Input F) (D L n d : ℕ) (hq : 0 < input.alphabet.length)
    (stage : Stage F) (ho : ∀ i e, stage.selected = some (i, e) → i - 1 ≤ d) :
    stageFuel input D L n stage ≤
      input.alphabet.length ^ (d + 2) * fuelPolynomial input D L n stage := by
  have hpos : 1 ≤ input.alphabet.length ^ (d + 2) := Nat.one_le_pow _ _ (by omega)
  cases hs : stage.selected with
  | none => simp only [stageFuel, fuelPolynomial, hs]; omega
  | some pair =>
      rcases pair with ⟨i, e⟩
      have hb := CenterRootsMachine.fuel_single_exponent
        (centerInput input stage (i - 1)) D L n hq
      have hp : 1 ≤ input.alphabet.length ^ (i - 1 + 2) := Nat.one_le_pow _ _ (by omega)
      have hm := stageCount_le input d hq stage ho
      simp only [stageCount, hs] at hm
      have hm' := Nat.mul_le_mul_right (fuelPolynomial input D L n stage) hm
      dsimp only [centerInput] at hb
      simp only [stageFuel, fuelPolynomial, hs] at hm' ⊢
      dsimp only [centerInput] at hm' ⊢
      nlinarith

omit [DecidableEq F] in
/-- Stage work has the same single alphabet factor, including all copied record cells. -/
theorem stageWork_le (input : Input F) (D L n d : ℕ) (hq : 0 < input.alphabet.length)
    (stage : Stage F) (ho : ∀ i e, stage.selected = some (i, e) → i - 1 ≤ d) :
    stageWork input D L n stage ≤
      input.alphabet.length ^ (d + 2) * workPolynomial input D L n stage := by
  have hpos : 1 ≤ input.alphabet.length ^ (d + 2) := Nat.one_le_pow _ _ (by omega)
  cases hs : stage.selected with
  | none => simp only [stageWork, workPolynomial, hs]; omega
  | some pair =>
      rcases pair with ⟨i, e⟩
      have hf := CenterRootsMachine.fuel_single_exponent
        (centerInput input stage (i - 1)) D L n hq
      have hw := CenterRootsMachine.work_single_exponent
        (centerInput input stage (i - 1)) D L n hq
      have hp : 1 ≤ input.alphabet.length ^ (i - 1 + 2) := Nat.one_le_pow _ _ (by omega)
      have hm := stageCount_le input d hq stage ho
      simp only [stageCount, hs] at hm
      have hm' := Nat.mul_le_mul_right (workPolynomial input D L n stage) hm
      dsimp only [centerInput] at hf hw
      simp only [stageWork, workPolynomial, hs] at hm' ⊢
      dsimp only [centerInput] at hm' ⊢
      nlinarith

omit [Field F] [DecidableEq F] in
private theorem sum_le_factor (stages : List (Stage F)) (f g : Stage F → ℕ) (q : ℕ)
    (h : ∀ stage ∈ stages, f stage ≤ q * g stage) :
    (stages.map f).sum ≤ q * (stages.map g).sum := by
  induction stages with
  | nil => simp
  | cons stage stages ih =>
      have hh := h stage (by simp)
      have ht := ih (fun s hs ↦ h s (by simp [hs]))
      simp only [List.map_cons, List.sum_cons]
      nlinarith

/-- The full visited-stage work uses one alphabet exponent and a sum of polynomial factors. -/
theorem work_single_exponent {d : ℕ} (input : Input F) (D L n B : ℕ)
    (hq : 0 < input.alphabet.length) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages) :
    workForStages input D L n B stages ≤ 4 * B + input.alphabet.length ^ (d + 2) *
      (stages.map (workPolynomial input D L n)).sum + 20 := by
  have h := sum_le_factor stages _ _ _ (fun s hs ↦
    stageWork_le input D L n d hq s (chain_orders hchain s hs))
  dsimp only [workForStages]
  omega

/-- The full visited-stage fuel uses the same original-order exponent. -/
theorem fuel_single_exponent {d : ℕ} (input : Input F) (D L n B : ℕ)
    (hq : 0 < input.alphabet.length) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages) :
    fuelForStages input D L n B stages ≤ B + input.alphabet.length ^ (d + 2) *
      (stages.map (fuelPolynomial input D L n)).sum + 5 := by
  have h := sum_le_factor stages _ _ _ (fun s hs ↦
    stageFuel_le input D L n d hq s (chain_orders hchain s hs))
  dsimp only [fuelForStages]
  omega

/-- The total raw record count is at most the stage count times the original-order jet factor. -/
theorem count_single_exponent {d : ℕ} (input : Input F) (hq : 0 < input.alphabet.length)
    {ts : List (Term F)} {Q : DifferentialPolynomial F d} {stages : List (Stage F)}
    (hchain : SeparantChainRefinement.OrderedChain ts Q stages) :
    (stages.map (stageCount input)).sum ≤ stages.length * input.alphabet.length ^ (d + 2) := by
  have h := sum_le_factor stages (stageCount input) (fun _ ↦ 1)
    (input.alphabet.length ^ (d + 2)) (fun s hs ↦ by
      simpa using stageCount_le input d hq s (chain_orders hchain s hs))
  simpa [List.map_const, Nat.mul_comm] using h

end ReedSolomon.HiddenDerivative.StageRootsMachine
