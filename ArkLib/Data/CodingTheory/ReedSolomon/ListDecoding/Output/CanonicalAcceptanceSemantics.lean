/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalAcceptanceMachine
/-!
# Exact output of canonical base-field acceptance

The same terminating program enforces the canonical guard, base-coordinate descent, strict
message degree and the integer agreement threshold. An accepted output represents the original
extension polynomial under the base embedding. The guard's equation-chain interpretation and
whole-list uniqueness are supplied by the root-stage consumer, not assumed by execution.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CanonicalAcceptanceMachine

open Polynomial JetHornerMachine

variable {F : Type*} [CommSemiring F] [DecidableEq F] {a b : F}

/-- Emission requires both the canonical guard and the exact base-field acceptance result. -/
theorem result_eq_some_iff (input : Guard.Input (QuadraticAlgebra F a b))
    (previous : List (Guard.Equation (QuadraticAlgebra F a b))) (w k A : ℕ)
    (rows : List (F × F)) (out : List F) :
    result input previous w k A rows = some out ↔
      Guard.result input previous = true ∧
        Candidate.result w k A input.coefficients rows = some out := by
  cases hg : Guard.result input previous <;> simp [result, hg]

/-- A nonempty acceptance result is exactly the guard and the requested base-message conditions. -/
theorem result_ne_none_iff (input : Guard.Input (QuadraticAlgebra F a b))
    (previous : List (Guard.Equation (QuadraticAlgebra F a b))) (w k A : ℕ)
    (hwidth : input.coefficients.length = w) (hk : k ≤ w) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) :
    result input previous w k A (List.ofFn fun i ↦ (domain i, received i)) ≠ none ↔
      Guard.result input previous = true ∧
      ∃ cs : List F, input.coefficients = cs.map (algebraMap F (QuadraticAlgebra F a b)) ∧
        (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received := by
  cases hg : Guard.result input previous with
  | false => simp [result, hg]
  | true =>
      simpa only [result, hg, ↓reduceIte, true_and] using
        QuadraticCandidateMachine.result_ne_none_iff w k A input.coefficients hwidth hk
          domain received

/-- Every emitted base vector satisfies the message conditions and embeds to the original root. -/
theorem result_sound (input : Guard.Input (QuadraticAlgebra F a b))
    (previous : List (Guard.Equation (QuadraticAlgebra F a b))) (w k A : ℕ)
    (hwidth : input.coefficients.length = w) (hk : k ≤ w) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (out : List F)
    (hout : result input previous w k A (List.ofFn fun i ↦ (domain i, received i)) = some out) :
    Guard.result input previous = true ∧ out.length = k ∧
      (coefficientPolynomial out).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial out)) received ∧
      (coefficientPolynomial out).map (algebraMap F (QuadraticAlgebra F a b)) =
        coefficientPolynomial input.coefficients := by
  obtain ⟨hg, hc⟩ := (result_eq_some_iff _ _ _ _ _ _ _).mp hout
  exact ⟨hg, QuadraticCandidateMachine.result_sound w k A input.coefficients hwidth hk
    domain received out hc⟩

/-- Output semantics and the full composed work bound refer to the same actual execution. -/
theorem evaluation_runFuel_correct (input : Guard.Input (QuadraticAlgebra F a b))
    (previous : List (Guard.Equation (QuadraticAlgebra F a b))) (w k A : ℕ)
    (hwidth : input.coefficients.length = w) (hk : k ≤ w) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) :
    ∃ out c, runFuel input w k A (List.ofFn fun i ↦ (domain i, received i))
        (fuel input previous w k n) (.start previous) = (.done out, c) ∧
      (out ≠ none ↔ Guard.result input previous = true ∧
        ∃ cs : List F, input.coefficients = cs.map (algebraMap F (QuadraticAlgebra F a b)) ∧
          (coefficientPolynomial cs).degree < k ∧
          A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received) ∧
      (∀ ys, out = some ys → Guard.result input previous = true ∧ ys.length = k ∧
        (coefficientPolynomial ys).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial ys)) received ∧
        (coefficientPolynomial ys).map (algebraMap F (QuadraticAlgebra F a b)) =
          coefficientPolynomial input.coefficients) ∧
      c ≤ workBound input previous w k n := by
  obtain ⟨c, hr, hc⟩ := evaluation_runFuel input previous w k A
    (List.ofFn fun i ↦ (domain i, received i)) hwidth
  refine ⟨_, c, ?_, result_ne_none_iff input previous w k A hwidth hk domain received,
    result_sound input previous w k A hwidth hk domain received, ?_⟩
  · simpa only [List.length_ofFn] using hr
  · simpa only [List.length_ofFn] using hc

end ReedSolomon.ListDecoding.CanonicalAcceptanceMachine
