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

A degree-one case uses `q = X + 1` with the same domain and claimed sum. Its next target must
be `r + 1` at each challenge `r`, so evaluation at a different point is observable.

Over `ZMod 4`, `p = 0`, target `2`, and `q = 2X + 2` demonstrate why the soundness API needs
stronger algebraic assumptions: the actual output relation holds at two of four challenges.
This is an operational regression, not a formal negation of the existential RBR security game.

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

private def linearInputPoly : F⦃≤ 1⦄[X] := ⟨0, by simp⟩

private def linearSentPoly : F⦃≤ 1⦄[X] :=
  ⟨X + 1, by
    apply Polynomial.mem_degreeLE.mpr
    exact Polynomial.degree_add_le_of_degree_le Polynomial.degree_X_le
      (Polynomial.degree_one_le.trans (by decide))⟩

/-- A nonconstant message must be evaluated at the supplied challenge. -/
theorem verifier_returns_linear_sent_target (r : F) :
    ((Simple.verifier F 1 domain []ₒ).verify
      (1, fun _ ↦ linearInputPoly) (legacyTranscript F 1 linearSentPoly r)).run =
      pure (some ((r + 1, r), fun _ : Unit ↦ linearInputPoly)) := by
  have hdomain (i : Fin 1) : domain i = 0 := rfl
  simp [Simple.verifier, linearSentPoly, hdomain]

/-- Oracle routing preserves both the nonconstant message and its evaluation point. -/
theorem oracleVerifier_returns_linear_sent_target (r : F) :
    ((Simple.oracleVerifier F 1 domain []ₒ).toVerifier.verify
      (1, fun _ ↦ linearInputPoly) (legacyTranscript F 1 linearSentPoly r)).run =
      pure (some ((r + 1, r), fun _ : Unit ↦ linearInputPoly)) := by
  rw [Simple.oracleVerifier_eq_verifier]
  exact verifier_returns_linear_sent_target r

/--
info: 'Sumcheck.LegacyVerifierTest.oracleVerifier_returns_linear_sent_target' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms oracleVerifier_returns_linear_sent_target

/--
info: 'Sumcheck.LegacyVerifierTest.actual_execution_output_relation_false' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms actual_execution_output_relation_false

namespace ZeroDivisors

private abbrev R := ZMod 4

private def domain : Fin 1 ↪ R :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private def inputPoly : R⦃≤ 1⦄[X] := ⟨0, by simp⟩

private def sentPoly : R⦃≤ 1⦄[X] :=
  ⟨C 2 * X + C 2, Polynomial.mem_degreeLE.mpr
    (Polynomial.degree_add_le_of_degree_le (Polynomial.degree_C_mul_X_le 2)
      (Polynomial.degree_C_le.trans (by decide)))⟩

/-- The fixed input polynomial does not have the claimed sum two. -/
theorem input_relation_false :
    ¬ ((2, fun _ : Unit ↦ inputPoly), ()) ∈ Simple.inputRelation R 1 domain := by
  change ¬ (∑ x ∈ Finset.univ.map domain, (0 : R[X]).eval x) = (2 : R)
  simpa using (show (0 : R) ≠ 2 by decide)

/-- The degree-one message passes the sum guard over the ring with zero divisors. -/
theorem message_sum_passes :
    ∑ x ∈ Finset.univ.map domain, sentPoly.val.eval x = (2 : R) := by
  have hdomain (i : Fin 1) : domain i = 0 := rfl
  simp [sentPoly, hdomain]

/-- Direct execution remains available over this commutative ring and retains the input oracle. -/
theorem verifier_returns_sent_target (r : R) :
    ((Simple.verifier R 1 domain []ₒ).verify
      (2, fun _ ↦ inputPoly) (legacyTranscript R 1 sentPoly r)).run =
      pure (some ((2 * r + 2, r), fun _ : Unit ↦ inputPoly)) := by
  have hdomain (i : Fin 1) : domain i = 0 := rfl
  simp [Simple.verifier, sentPoly, hdomain]

/-- Oracle execution also preserves the zero input and evaluates the sent polynomial. -/
theorem oracleVerifier_returns_sent_target (r : R) :
    ((Simple.oracleVerifier R 1 domain []ₒ).toVerifier.verify
      (2, fun _ ↦ inputPoly) (legacyTranscript R 1 sentPoly r)).run =
      pure (some ((2 * r + 2, r), fun _ : Unit ↦ inputPoly)) := by
  rw [Simple.oracleVerifier_eq_verifier]
  exact verifier_returns_sent_target r

/-- The actual verifier's output relation holds exactly at challenges one and three. -/
theorem actual_execution_output_relation (r : R) :
    (Option.map (fun out ↦ (out, ()) ∈ Simple.outputRelation R 1)) <$>
      ((Simple.oracleVerifier R 1 domain []ₒ).toVerifier.verify
        (2, fun _ ↦ inputPoly) (legacyTranscript R 1 sentPoly r)).run =
      pure (some (r = 1 ∨ r = 3)) := by
  rw [oracleVerifier_returns_sent_target]
  have heq : ∀ r : R, (0 : R) = 2 * r + 2 ↔ r = 1 ∨ r = 3 := by decide
  simp [Simple.outputRelation, inputPoly, heq]

/-- Exactly two uniform challenges make the actual output relation true. -/
theorem true_output_challenge_count :
    (Finset.univ.filter (fun r : R ↦ r = 1 ∨ r = 3)).card = 2 := by
  decide

open scoped NNReal in
/-- The true-output fraction is one half, strictly exceeding the degree-one bound one quarter. -/
theorem true_output_fraction_exceeds_degree_bound :
    ((Finset.univ.filter (fun r : R ↦ r = 1 ∨ r = 3)).card : ℝ≥0) / Fintype.card R = 1 / 2 ∧
      (1 : ℝ≥0) / Fintype.card R <
        (Finset.univ.filter (fun r : R ↦ r = 1 ∨ r = 3)).card / Fintype.card R := by
  norm_num [true_output_challenge_count, R]

/--
info: 'Sumcheck.LegacyVerifierTest.ZeroDivisors.actual_execution_output_relation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms actual_execution_output_relation

/--
info: 'Sumcheck.LegacyVerifierTest.ZeroDivisors.true_output_fraction_exceeds_degree_bound'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms true_output_fraction_exceeds_degree_bound

end ZeroDivisors

end

end Sumcheck.LegacyVerifierTest
