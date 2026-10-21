/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
import ArkLib.OracleReduction.LiftContext.Purity

/-!
# Guarded composition certificates and empty-oracle boundary cases

These checks audit the composition declarations and show that a guarded fallback can preserve an
arbitrary oracle family from input without assuming it is inhabited.
-/

open OracleSpec ProtocolSpec

namespace CompositionRetirementRegression

/-- The fallback preserves an arbitrary oracle value supplied in the input. -/
def preserveArbitraryFamily {α : Type}
    (V : Verifier []ₒ (Unit × α) (Bool × α) !p[]) : V.GuardedForm :=
  Verifier.GuardedForm.ofEmpty V (fun input => (false, input.2))

/-- A rejecting verifier with empty output does not admit a total guarded verdict function. -/
theorem no_guarded_form_for_empty_output :
    ¬ Nonempty (Verifier.GuardedForm
      (show Verifier []ₒ Unit Empty !p[] from ⟨fun _ _ => failure⟩)) := by
  rintro ⟨G⟩
  exact (G.out () default).elim

end CompositionRetirementRegression

/--
info: 'OracleComp.runEmpty' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleComp.runEmpty

/--
info: 'OracleComp.eq_pure_runEmpty' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleComp.eq_pure_runEmpty

/--
info: 'Prover.instOutputIsPureEmpty' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Prover.instOutputIsPureEmpty

/--
info: 'Verifier.GuardedForm.ofEmpty' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.ofEmpty

/--
info: 'Prover.instOutputIsPureLiftContext' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Prover.instOutputIsPureLiftContext

/--
info: 'Verifier.GuardedForm.liftContext' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.liftContext

/--
info: 'Verifier.GuardedForm.seqCompose' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.GuardedForm.seqCompose

/--
info: 'Reduction.seqCompose_completeness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.seqCompose_completeness_of_guarded_verifiers

/--
info: 'Reduction.seqCompose_perfectCompleteness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.seqCompose_perfectCompleteness_of_guarded_verifiers

/--
info: 'OracleReduction.append_completeness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleReduction.append_completeness_of_guarded_verifiers

/--
info: 'OracleReduction.append_perfectCompleteness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleReduction.append_perfectCompleteness_of_guarded_verifiers

/--
info: 'OracleReduction.seqCompose_completeness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleReduction.seqCompose_completeness_of_guarded_verifiers

/--
info: 'OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers

/--
info: 'CompositionRetirementRegression.preserveArbitraryFamily' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompositionRetirementRegression.preserveArbitraryFamily

/--
info: 'CompositionRetirementRegression.no_guarded_form_for_empty_output' depends on axioms:
[Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompositionRetirementRegression.no_guarded_form_for_empty_output
