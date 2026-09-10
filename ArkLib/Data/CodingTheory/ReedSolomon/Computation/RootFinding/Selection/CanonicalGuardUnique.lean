/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CanonicalGuardSemantics
/-!+# Exclusivity of canonical residual witnesses

For fixed global coefficients and a fixed sampling order, an accepted guard determines a unique
center and certifies that its separant fails the zero test. Consequently, any later stage whose
current equation or earlier prefix contains that separant cannot accept the same candidate.
The current-equation case uses the root solver's zero certificate; it must not be inferred from
the strictly earlier prefix. These results are independent of interpolation degree hypotheses.
The stage driver supplies adjacency and the common coefficient representation.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CanonicalGuardMachine

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- A successful canonical guard certifies that its separant does not pass the zero test. -/
theorem separant_zero_test_false (input : Input F) (previous : List (Equation F))
    (h : result input previous = true) :
    ResidualZeroMachine.result (residualInput input input.separant) input.samples = false := by
  have hw := ((result_eq_true_iff input previous).mp h).2
  have hn : ResidualZeroMachine.result (residualInput input input.separant)
      input.samples ≠ true := by
    intro hz
    have he := (ResidualWitnessMachine.result_eq_none_iff
      (residualInput input input.separant) input.samples).mpr
        ((ResidualZeroMachine.result_eq_true_iff _ _).mp hz)
    rw [hw] at he
    contradiction
  cases hb : ResidualZeroMachine.result (residualInput input input.separant) input.samples
  · rfl
  · exact False.elim (hn hb)

/-- All accepted centers at a fixed stage coincide, even if supplied samples repeat. -/
theorem accepted_center_unique (cs samples : List F) (order : ℕ) (separant : Equation F)
    (previous previous' : List (Equation F)) (a b : F)
    (ha : result ⟨cs, samples, order, a, separant⟩ previous = true)
    (hb : result ⟨cs, samples, order, b, separant⟩ previous' = true) : a = b := by
  have hwa := ((result_eq_true_iff _ _).mp ha).2
  have hwb := ((result_eq_true_iff _ _).mp hb).2
  exact Option.some.inj (hwa.symm.trans hwb)

/-- A stage is rejected if its own separant is known to vanish on every sample. -/
theorem result_false_of_separant_zero (input : Input F) (previous : List (Equation F))
    (hz : ResidualZeroMachine.result (residualInput input input.separant)
      input.samples = true) : result input previous = false := by
  cases hr : result input previous
  · rfl
  · have hf := separant_zero_test_false input previous hr
    rw [hz] at hf
    contradiction

/-- A guard that accepts cannot also check its separant among the earlier zero equations. -/
theorem result_false_of_separant_mem (input : Input F) (previous : List (Equation F))
    (hm : input.separant ∈ previous) : result input previous = false := by
  cases hr : result input previous
  · rfl
  · have hz := ((result_eq_true_iff input previous).mp hr).1 input.separant hm
    have hf := result_false_of_separant_zero input previous hz
    rw [hr] at hf
    contradiction

/-- A later guard rejects if its earlier prefix contains an already accepted stage's separant.
The immediately adjacent stage instead uses its current-equation root certificate. -/
theorem later_result_false (cs samples : List F) (order : ℕ) (a b : F)
    (separant laterSeparant : Equation F) (previous laterPrevious : List (Equation F))
    (ha : result ⟨cs, samples, order, a, separant⟩ previous = true)
    (hm : separant ∈ laterPrevious) :
    result ⟨cs, samples, order, b, laterSeparant⟩ laterPrevious = false := by
  cases hb : result ⟨cs, samples, order, b, laterSeparant⟩ laterPrevious
  · rfl
  · have hz := ((result_eq_true_iff _ _).mp hb).1 separant hm
    have hf := separant_zero_test_false ⟨cs, samples, order, a, separant⟩ previous ha
    change ResidualZeroMachine.result ⟨cs, separant, 0, order⟩ samples = true at hz
    change ResidualZeroMachine.result ⟨cs, separant, 0, order⟩ samples = false at hf
    rw [hz] at hf
    contradiction

end ReedSolomon.HiddenDerivative.CanonicalGuardMachine
