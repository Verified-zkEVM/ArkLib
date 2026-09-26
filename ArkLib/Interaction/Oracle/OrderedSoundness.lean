/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Composition
public import VCVio.EvalDist.Monad.Measure

/-!
# Soundness of optional ordered execution

`OrderedExecution.run_soundness_measure` accumulates soundness errors across the actual dependent
stages of `OrderedExecution.run`. Truth is declared separately at every execution boundary. A
stage bound applies only to a false input and counts accepted true outputs; rejected outputs
have no truth claim and contribute no error. From a false initial state, the probability of an
accepted true final state is at most the sum of the stage errors.

The probability interpretation is the chosen native measure semantics of the ambient oracles.
Boundary state spaces are discrete measurable spaces; they may contain function-valued oracle
behaviors and need not be countable. There is no uniform-sampling or probability-compatibility
assumption. This theorem concerns the optional execution combinator only: it does not establish
persistent-world admissibility, a fault model, or soundness of a flattened protocol strategy.
-/

@[expose] public section

universe u

open scoped ENNReal BigOperators

namespace Interaction.Oracle.OrderedExecution

variable {ι : Type u} {ambient : OracleSpec.{u, u} ι}

/-- Soundness errors add along an ordered execution of actual reductions. Each stage must bound
the mass of accepted true outputs by `ε i` whenever its input is false. No preservation premise
is needed for true inputs: their entire continuation mass is charged to the first false-to-true
transition. Rejection short-circuits execution and is excluded from the final event.

The conclusion uses native measure semantics and requires no countability of boundary states,
which include the closed oracle behavior and private prover state. -/
theorem run_soundness_measure
    [∀ q, MeasurableSpace (ambient q)] [∀ q, DiscreteMeasurableSpace (ambient q)]
    [ambient.IsMeasureSpec]
    (n : Nat) (I : Fin (n + 1) → ExecutionInterface.{u})
    [∀ i, MeasurableSpace (I i).State] [∀ i, DiscreteMeasurableSpace (I i).State]
    (stages : (i : Fin n) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (Rel : (i : Fin (n + 1)) → (I i).State → Prop)
    (ε : Fin n → ℝ≥0∞)
    (sound : ∀ (i : Fin n) (input : (I i.castSucc).State), ¬ Rel i.castSucc input →
      𝒟[(stages i).run input]
        {result | ∃ output, result = some output ∧ Rel i.succ output} ≤ ε i)
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State)
    (hinput : ¬ Rel ⟨0, Nat.zero_lt_succ _⟩ input) :
    𝒟[run n I stages input]
      {result | ∃ output, result = some output ∧ Rel (Fin.last n) output} ≤
        ∑ i, ε i := by
  induction n with
  | zero =>
    have hnot : some input ∉
        {result | ∃ output, result = some output ∧ Rel (Fin.last 0) output} := by
      rintro ⟨output, houtput, hrel⟩
      have hout : input = output := Option.some.inj houtput
      subst output
      exact hinput hrel
    rw [run_zero, evalDist_pure, MeasureTheory.Measure.dirac_apply,
      Set.indicator_of_notMem hnot]
    exact bot_le
  | succ n ih =>
    -- Charge all accepted true intermediate states to the first stage's soundness error.
    rw [run_succ, Fin.sum_univ_succ]
    refine evalDist_bind_apply_le_add_of_bad _ _ Measurable.of_discrete
      MeasurableSet.of_discrete MeasurableSet.of_discrete
      (sound ⟨0, Nat.zero_lt_succ _⟩ input hinput) ?_
    intro mid hmid
    cases mid with
    | none =>
      -- A rejected intermediate state never runs the suffix and cannot satisfy its final event.
      simp [evalDist_pure]
    | some value =>
      -- Every remaining accepted input is false, so the suffix induction hypothesis applies.
      exact ih (fun i => I i.succ) (fun i => stages i.succ) (fun i => Rel i.succ)
        (fun i => ε i.succ) (fun i => sound i.succ) value
        (fun hvalue => hmid ⟨value, rfl, hvalue⟩)

end Interaction.Oracle.OrderedExecution
