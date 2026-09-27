/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Interaction.Legacy
import Mathlib.Data.ZMod.Basic

/-!
# Legacy single-round target regression

Over F₅, with degree bound zero and domain `{0}`, take input polynomial `p = 0`, claimed sum
`s = 1`, and round message `q = 1`. The input relation is false, but the message passes the sum
check. Executing either legacy verifier must return target `q(r) = 1` with output oracle `p = 0`,
so the output relation stays false at every challenge. Returning `p(r) = 0` would make it true.

These tests reduce the actual legacy verifier programs, including oracle simulation. They do not
use the admitted legacy soundness theorems or assert a full correspondence with native Sumcheck.
-/

namespace Sumcheck.LegacyVerifierTest

open Polynomial OracleComp OracleSpec
open Spec.SingleRound
open Interaction.SingleRound (legacyTranscript)

noncomputable section

private abbrev F := ZMod 5

private def domain : Fin 1 ↪ F :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private def inputPoly : F⦃≤ 0⦄[X] := ⟨0, by simp⟩

private def sentPoly : F⦃≤ 0⦄[X] := ⟨1, by simp [Polynomial.mem_degreeLE]⟩

/-- The original zero polynomial does not satisfy the claimed sum one. -/
theorem input_relation_false :
    ¬ ((1, fun _ : Unit ↦ inputPoly), ()) ∈ Simple.inputRelation F 0 domain := by
  change ¬ (∑ x ∈ Finset.univ.map domain, (0 : F[X]).eval x) = (1 : F)
  simpa using (show (0 : F) ≠ 1 by decide)

/-- The dishonest constant message nevertheless satisfies the verifier's sum guard. -/
theorem message_sum_passes :
    ∑ x ∈ Finset.univ.map domain, sentPoly.val.eval x = (1 : F) := by
  simp [sentPoly, domain]

/-- Direct execution returns the sent evaluation and preserves the zero input oracle. -/
theorem verifier_returns_sent_target (r : F) :
    ((Simple.verifier F 0 domain []ₒ).verify
      (1, fun _ ↦ inputPoly) (legacyTranscript F 0 sentPoly r)).run =
      pure (some ((1, r), fun _ : Unit ↦ inputPoly)) := by
  simp [Simple.verifier, sentPoly]

/-- Oracle execution gives the same result for every field challenge. -/
theorem oracleVerifier_returns_sent_target (r : F) :
    ((Simple.oracleVerifier F 0 domain []ₒ).toVerifier.verify
      (1, fun _ ↦ inputPoly) (legacyTranscript F 0 sentPoly r)).run =
      pure (some ((1, r), fun _ : Unit ↦ inputPoly)) := by
  rw [Simple.oracleVerifier_eq_verifier]
  exact verifier_returns_sent_target r

/-- The returned claim is false at every challenge, despite passing the round sum check. -/
theorem actual_execution_output_relation_false (r : F) :
    (Option.map (fun out ↦ (out, ()) ∈ Simple.outputRelation F 0)) <$>
      ((Simple.oracleVerifier F 0 domain []ₒ).toVerifier.verify
        (1, fun _ ↦ inputPoly) (legacyTranscript F 0 sentPoly r)).run =
      pure (some False) := by
  rw [oracleVerifier_returns_sent_target]
  simp [Simple.outputRelation, inputPoly, show (0 : F) ≠ 1 by decide]

/-- A failed message sum still causes rejection. -/
theorem inconsistent_sum_rejected (r : F) :
    ((Simple.oracleVerifier F 0 domain []ₒ).toVerifier.verify
      (0, fun _ ↦ inputPoly) (legacyTranscript F 0 sentPoly r)).run = pure none := by
  rw [Simple.oracleVerifier_eq_verifier]
  simp [Simple.verifier, sentPoly, domain, show (1 : F) ≠ 0 by decide]

/-- The honest zero input and message still return the valid zero target. -/
theorem honest_zero_accepted (r : F) :
    ((Simple.oracleVerifier F 0 domain []ₒ).toVerifier.verify
      (0, fun _ ↦ inputPoly) (legacyTranscript F 0 inputPoly r)).run =
      pure (some ((0, r), fun _ : Unit ↦ inputPoly)) := by
  rw [Simple.oracleVerifier_eq_verifier]
  simp [Simple.verifier, inputPoly]

/--
info: 'Sumcheck.LegacyVerifierTest.actual_execution_output_relation_false' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms actual_execution_output_relation_false

end

end Sumcheck.LegacyVerifierTest
