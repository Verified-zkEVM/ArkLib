/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Terminal
import VCVio.EvalDist.WithFailure

/-!
# Terminal observations with explicit runtime faults

The VCVio completion keeps an outer `none` for execution missing mass. `observe` collapses that
case only after the caller names a fault. Acceptance and rejection retain exactly their original
mass; the new fault may coincide with a returned model fault, in which case their masses combine.
-/

universe u v

namespace Interaction.Oracle.Terminal

open MeasureTheory

variable {Claim Fault : Type u} {m : Type u → Type v} [EvalDistSemantics m]
    [MeasurableSpace (Terminal Claim Fault)] [DiscreteMeasurableSpace (Terminal Claim Fault)]

/-- Observe terminal outcomes after explicitly assigning execution missing mass a named fault. -/
noncomputable def observe (missingFault : Fault) (program : m (Terminal Claim Fault)) :
    Measure (Terminal Claim Fault) :=
  (evalDistWithFailure program).map (decodeRuntime missingFault)

/-- Explicit runtime-fault materialization cannot create or remove an accepting result. -/
theorem observe_accept (missingFault : Fault) (program : m (Terminal Claim Fault)) (claim : Claim) :
    observe missingFault program {accept claim} = evalDist program {accept claim} := by
  rw [observe, Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  have preimage : decodeRuntime missingFault ⁻¹' {accept claim} = {some (accept claim)} := by
    ext outcome
    simp
  rw [preimage, evalDistWithFailure_some]

/-- Verifier rejection remains a returned protocol result, with no missing mass added to it. -/
theorem observe_reject (missingFault : Fault) (program : m (Terminal Claim Fault)) :
    observe missingFault program {reject} = evalDist program {reject} := by
  rw [observe, Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  have preimage : decodeRuntime (Claim := Claim) missingFault ⁻¹' {reject} = {some reject} := by
    ext outcome
    simp
  rw [preimage, evalDistWithFailure_some]

/-- The named runtime fault receives exactly its returned mass plus execution missing mass. -/
theorem observe_namedFault (missingFault : Fault) (program : m (Terminal Claim Fault)) :
    observe missingFault program {fault missingFault} =
      evalDist program {fault missingFault} + (1 - evalDist program Set.univ) := by
  rw [observe, Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  have preimage : decodeRuntime (Claim := Claim) missingFault ⁻¹' {fault missingFault} =
      {some (fault missingFault)} ∪ {none} := by
    ext outcome
    cases outcome <;> simp [decodeRuntime]
  rw [preimage, measure_union (by simp) (measurableSet_singleton _),
    evalDistWithFailure_some, evalDistWithFailure_none]

/-- The named-fault observation has total mass one. -/
theorem observe_isProbabilityMeasure (missingFault : Fault) (program : m (Terminal Claim Fault)) :
    IsProbabilityMeasure (observe missingFault program) := by
  let _ := evalDistWithFailure_isProbabilityMeasure program
  exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

end Interaction.Oracle.Terminal
