/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Probability bounds for sequential computations

Average the next computation's error over the actual first computation's output distribution.
Exceptional outputs are charged separately. These bounds use the existing distribution semantics;
missing mass is retained and no independence or losslessness assumption is needed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe v

/-- Bound success after a common draw by its exceptional probability and the average error on
nonexceptional outputs. The local bound need only hold almost everywhere under the actual draw.
The integral is not normalized: neither computation has to return with probability one. -/
theorem prEvent_bind_le_prEvent_add_lintegral_ae
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type}
    (mx : m α) (suffix : α → m β) (Exceptional : α → Prop) (Success : β → Prop)
    (error : α → ENNReal)
    (hsuffix : letI : MeasurableSpace α := ⊤
      ∀ᵐ b ∂𝒟[mx], ¬ Exceptional b → Pr{let value ← suffix b}[Success value] ≤ error b) :
    let : MeasurableSpace α := ⊤
    Pr{let b ← mx; let value ← suffix b}[Success value] ≤
      Pr{let b ← mx}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[mx] := by
  classical
  let : MeasurableSpace α := ⊤
  have h := prEvent_bind_le_sum_add_lintegral_ae mx suffix Success
    (fun _ : Unit => predInd Exceptional) Measurable.of_discrete
    (fun _ => Measurable.of_discrete) ({b | ¬ Exceptional b}.indicator error) (by
      apply hsuffix.mono
      intro b hb
      by_cases he : Exceptional b
      · simp [he]
      · simpa [he] using hb he)
  simpa only [Fintype.sum_unique, lintegral_indicator MeasurableSet.of_discrete] using h
