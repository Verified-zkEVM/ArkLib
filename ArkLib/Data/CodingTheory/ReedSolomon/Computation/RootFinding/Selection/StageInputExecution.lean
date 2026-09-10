/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageInputBounds
/-!
# Initial-input fuel for the actual stage-root machine

The caller supplies only initial instance sizes. Every visited equation is bounded by the
ordered-chain invariant; summing its uniform stage polynomial adds the initial degree budget
as a factor. Surplus fuel preserves the identical completed execution and primitive ledger.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.StageRootsMachine

open MvPolynomial PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Original-input chain budget; no emitted stage list occurs in this expression. -/
def inputChainBudget (input : Input F) (Δ : ℕ) : ℕ :=
  SeparantChainRefinement.budget Δ input.terms.length (input.order + 2)
    (PartialDerivativeMachine.inputMass input.terms)

/-- Host fuel is a single original-order alphabet power times a fixed-degree polynomial. -/
def inputFuel (input : Input F) (D L n Δ : ℕ) : ℕ := inputChainBudget input Δ +
  input.alphabet.length ^ (input.order + 2) * (Δ + 1) *
    uniformFuel D input.order (PartialDerivativeMachine.inputMass input.terms) L n + 5

/-- Full primitive work has the same alphabet exponent and only initial numeric sizes. -/
def inputWork (input : Input F) (D L n Δ : ℕ) : ℕ := 4 * inputChainBudget input Δ +
  input.alphabet.length ^ (input.order + 2) * (Δ + 1) *
    uniformWork D input.order (PartialDerivativeMachine.inputMass input.terms) L n + 20

omit [Field F] [DecidableEq F] in
private theorem sum_uniform {α : Type*} (xs : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ x ∈ xs, f x ≤ B) : (xs.map f).sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x (by simp)
    have ht := ih (fun y hy ↦ h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- Visited fuel and work are bounded simultaneously by the original instance's budgets. -/
theorem visited_bounds (input : Input F) (D L n Δ : ℕ) (hq : 0 < input.alphabet.length)
    {Q : DifferentialPolynomial F input.order} {stages : List (Stage F)}
    (hchain : SeparantChainRefinement.OrderedChain input.terms Q stages)
    (hlen : stages.length ≤ Δ + 1) :
    fuelForStages input D L n (inputChainBudget input Δ) stages ≤ inputFuel input D L n Δ ∧
      workForStages input D L n (inputChainBudget input Δ) stages ≤ inputWork input D L n Δ := by
  have hf := sum_uniform stages (fuelPolynomial input D L n) _ (fun stage hs ↦
    (stage_polynomials input D L n hchain stage hs).1)
  have hw := sum_uniform stages (workPolynomial input D L n) _ (fun stage hs ↦
    (stage_polynomials input D L n hchain stage hs).2)
  have hf' := hf.trans (Nat.mul_le_mul_right _ hlen)
  have hw' := hw.trans (Nat.mul_le_mul_right _ hlen)
  constructor
  · refine (fuel_single_exponent input D L n (inputChainBudget input Δ) hq hchain).trans ?_
    have h := Nat.mul_le_mul_left (input.alphabet.length ^ (input.order + 2)) hf'
    unfold inputFuel
    nlinarith only [h]
  · refine (work_single_exponent input D L n (inputChainBudget input Δ) hq hchain).trans ?_
    have h := Nat.mul_le_mul_left (input.alphabet.length ^ (input.order + 2)) hw'
    unfold inputWork
    nlinarith only [h]

/-- Replaying an already completed run with more fuel preserves its result and exact charges. -/
theorem runFuel_surplus (input : Input F) (D L fuel larger : ℕ) (s : Configuration F)
    (out : Option (List (Record F))) (c : Cost)
    (hr : runFuel input D L fuel s = (.done out, c)) (hle : fuel ≤ larger) :
    runFuel input D L larger s = (.done out, c) := by
  obtain ⟨steps, hs, ht⟩ := runFuel_refines input D L fuel s
  rw [hr] at ht
  have he := ht.runFuel_done (larger - steps)
  rwa [Nat.add_sub_of_le (hs.trans hle)] at he

/-- Actual execution terminates at caller-computable initial-input fuel with identical costs.
The old visited-stage run is retained in the conclusion to make surplus-fuel equality explicit;
it is not a premise or part of the caller's chosen fuel. -/
theorem execution_input_budget {D L : ℕ} (input : Input F) (points : Fin L ↪ F)
    (samples : List F) (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hq : 0 < input.alphabet.length) (hdepth : input.order ≤ D) (Δ : ℕ)
    (Q : DifferentialPolynomial F input.order)
    (hl : DenseNormalizeMachine.DenseLayout (List.range (input.order + 2)) input.terms)
    (hQ : EvaluationMachine.sparsePolynomial input.terms =
      rename HighestJetTransport.encodeJet Q) (hne : Q ≠ 0)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hdeg : jetTotalDegree Q ≤ Δ)
    (hweight : differentialWeightedDegree D Q < L) :
    ∃ stages out c, SeparantChainRefinement.OrderedChain input.terms Q stages ∧
      stages.length ≤ Δ + 1 ∧
      runFuel input D L (inputFuel input D L samples.length Δ) (.start samples) =
        (.done (some out), c) ∧
      runFuel input D L
        (fuelForStages input D L samples.length (inputChainBudget input Δ) stages)
        (.start samples) = (.done (some out), c) ∧
      Specification input D L samples stages [] out ∧
      (∀ record ∈ out, record.coefficients.length = D + 1) ∧
      out.length ≤ (Δ + 1) * input.alphabet.length ^ (input.order + 2) ∧
      totalCost c ≤ inputWork input D L samples.length Δ := by
  obtain ⟨stages, out, c, hchain, hlen, hr, hspec, hwidth, hcount, hc⟩ :=
    execution_correct input points samples hsamples hq hdepth Δ Q hl hQ hne hchar hdeg hweight
  obtain ⟨hf, hw⟩ := visited_bounds input D L samples.length Δ hq hchain hlen
  have hr' := runFuel_surplus input D L _ _ (.start samples) (some out) c hr hf
  have hcount' := (count_single_exponent input hq hchain).trans (Nat.mul_le_mul_right _ hlen)
  exact ⟨stages, out, c, hchain, hlen, hr', hr, hspec, hwidth, hcount.trans hcount', hc.trans hw⟩

/-- A single initial size dominates every numeric parameter and chain-size measure. -/
def instanceSize (input : Input F) (D L n Δ : ℕ) : ℕ :=
  D + input.order + PartialDerivativeMachine.inputMass input.terms + L + n + Δ +
    input.terms.length

/-- A degree-five polynomial includes the chain and every visited stage's degree-four work. -/
def instancePolynomial (S : ℕ) : ℕ :=
  55978 * S ^ 5 + 190160 * S ^ 4 + 239307 * S ^ 3 + 148071 * S ^ 2 + 59151 * S + 16245

/-- The displayed polynomial is the exact expansion of the uniform numerical majorant. -/
theorem instancePolynomial_eq (S : ℕ) :
    4 * SeparantChainRefinement.budget S S (S + 2) S +
      (S + 1) * sizePolynomial S + 20 = instancePolynomial S := by
  unfold SeparantChainRefinement.budget SeparantChainMachine.stageBudget
    HighestJetMachine.budget DenseNormalizeMachine.budget sizePolynomial instancePolynomial
  ring

/-- Caller-computable fuel and work, with the sole alphabet exponent fixed by original order. -/
def polynomialBudget (input : Input F) (D L n Δ : ℕ) : ℕ :=
  input.alphabet.length ^ (input.order + 2) * instancePolynomial (instanceSize input D L n Δ)

omit [Field F] [DecidableEq F] in
/-- Both initial budgets fit the same degree-five polynomial and original-order alphabet power. -/
theorem input_bounds_polynomial (input : Input F) (D L n Δ : ℕ)
    (hq : 0 < input.alphabet.length) :
    inputFuel input D L n Δ ≤ polynomialBudget input D L n Δ ∧
      inputWork input D L n Δ ≤ polynomialBudget input D L n Δ := by
  let S := instanceSize input D L n Δ
  have hD : D ≤ S := by dsimp [S, instanceSize]; omega
  have hd : input.order ≤ S := by dsimp [S, instanceSize]; omega
  have hM : PartialDerivativeMachine.inputMass input.terms ≤ S := by
    dsimp [S, instanceSize]; omega
  have hL : L ≤ S := by dsimp [S, instanceSize]; omega
  have hn : n ≤ S := by dsimp [S, instanceSize]; omega
  have hΔ : Δ ≤ S := by dsimp [S, instanceSize]; omega
  have ht : input.terms.length ≤ S := by dsimp [S, instanceSize]; omega
  have hb : inputChainBudget input Δ ≤ SeparantChainRefinement.budget S S (S + 2) S := by
    unfold inputChainBudget SeparantChainRefinement.budget SeparantChainMachine.stageBudget
      HighestJetMachine.budget DenseNormalizeMachine.budget
    gcongr
  have hp := uniform_sum_le D input.order (PartialDerivativeMachine.inputMass input.terms)
    L n S hD hd hM hL hn
  have hf : (Δ + 1) * uniformFuel D input.order
      (PartialDerivativeMachine.inputMass input.terms) L n ≤ (S + 1) * sizePolynomial S :=
    Nat.mul_le_mul (by omega) (by omega)
  have hw : (Δ + 1) * uniformWork D input.order
      (PartialDerivativeMachine.inputMass input.terms) L n ≤ (S + 1) * sizePolynomial S :=
    Nat.mul_le_mul (by omega) (by omega)
  have hq' : 1 ≤ input.alphabet.length ^ (input.order + 2) := Nat.one_le_pow _ _ hq
  have hbf := Nat.mul_le_mul_left (input.alphabet.length ^ (input.order + 2)) hf
  have hbw := Nat.mul_le_mul_left (input.alphabet.length ^ (input.order + 2)) hw
  have hbc := Nat.mul_le_mul_left (4 * SeparantChainRefinement.budget S S (S + 2) S + 20) hq'
  unfold polynomialBudget
  rw [← instancePolynomial_eq]
  change _ ≤ _ * (4 * SeparantChainRefinement.budget S S (S + 2) S +
    (S + 1) * sizePolynomial S + 20) ∧ _ ≤ _
  unfold inputFuel inputWork
  constructor <;> nlinarith only [hb, hbf, hbw, hbc]

/-- The actual machine terminates using only the initial alphabet power and degree-five fuel.
All semantic outputs and primitive costs are inherited from the same completed execution. -/
theorem execution_polynomial_budget {D L : ℕ} (input : Input F) (points : Fin L ↪ F)
    (samples : List F) (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hq : 0 < input.alphabet.length) (hdepth : input.order ≤ D) (Δ : ℕ)
    (Q : DifferentialPolynomial F input.order)
    (hl : DenseNormalizeMachine.DenseLayout (List.range (input.order + 2)) input.terms)
    (hQ : EvaluationMachine.sparsePolynomial input.terms =
      rename HighestJetTransport.encodeJet Q) (hne : Q ≠ 0)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hdeg : jetTotalDegree Q ≤ Δ)
    (hweight : differentialWeightedDegree D Q < L) :
    ∃ stages out c, SeparantChainRefinement.OrderedChain input.terms Q stages ∧
      stages.length ≤ Δ + 1 ∧
      runFuel input D L (polynomialBudget input D L samples.length Δ) (.start samples) =
        (.done (some out), c) ∧
      runFuel input D L (inputFuel input D L samples.length Δ) (.start samples) =
        (.done (some out), c) ∧
      Specification input D L samples stages [] out ∧
      (∀ record ∈ out, record.coefficients.length = D + 1) ∧
      out.length ≤ (Δ + 1) * input.alphabet.length ^ (input.order + 2) ∧
      totalCost c ≤ polynomialBudget input D L samples.length Δ := by
  obtain ⟨stages, out, c, hchain, hlen, hr, _, hspec, hwidth, hcount, hc⟩ :=
    execution_input_budget input points samples hsamples hq hdepth Δ Q hl hQ hne hchar hdeg hweight
  obtain ⟨hf, hw⟩ := input_bounds_polynomial input D L samples.length Δ hq
  exact ⟨stages, out, c, hchain, hlen,
    runFuel_surplus input D L _ _ (.start samples) (some out) c hr hf,
    hr, hspec, hwidth, hcount, hc.trans hw⟩

end ReedSolomon.HiddenDerivative.StageRootsMachine
