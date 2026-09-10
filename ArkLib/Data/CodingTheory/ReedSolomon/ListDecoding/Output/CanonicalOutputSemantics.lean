/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalOutputMachine
/-!
# Exact accepted subsequences and linear collection overhead

The actual collection program returns exactly the accepted subsequence of its materialized
stage records. Each emitted base polynomial satisfies the message degree/agreement conditions
and embeds to its originating candidate. Work is linear in the number of input records times
the proved per-record acceptance budget, not quadratic in candidate count. Completeness and
duplicate freedom for all solutions require the generated stage records' additional contracts.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CanonicalOutputMachine

open Polynomial JetHornerMachine

variable {F : Type*} [CommSemiring F] [DecidableEq F] {a b : F}

/-- Output membership records its exact originating input and actual acceptance result. -/
theorem mem_result_iff (order w k A : ℕ) (samples : List (QuadraticAlgebra F a b))
    (rows : List (F × F)) (records : List (Record (QuadraticAlgebra F a b))) (cs : List F) :
    cs ∈ result order samples w k A rows records ↔
      ∃ r ∈ records, Accept.result (guardInput order samples r) r.context.previous w k A rows =
        some cs := List.mem_filterMap

/-- Filtering emits at most one output for each supplied stage record. -/
theorem result_length_le (order w k A : ℕ) (samples : List (QuadraticAlgebra F a b))
    (rows : List (F × F)) (records : List (Record (QuadraticAlgebra F a b))) :
    (result order samples w k A rows records).length ≤ records.length :=
  List.length_filterMap_le _ _

/-- Any emitted polynomial satisfies the required base-field message conditions. -/
theorem result_sound (order w k A : ℕ) (samples : List (QuadraticAlgebra F a b))
    (records : List (Record (QuadraticAlgebra F a b)))
    (hwidth : ∀ r ∈ records, r.coefficients.length = w) (hk : k ≤ w) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (cs : List F)
    (hcs : cs ∈ result order samples w k A (List.ofFn fun i ↦ (domain i, received i)) records) :
    cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received ∧
      ∃ r ∈ records, HiddenDerivative.CanonicalGuardMachine.result
        (guardInput order samples r) r.context.previous = true ∧
        (coefficientPolynomial cs).map (algebraMap F (QuadraticAlgebra F a b)) =
          coefficientPolynomial r.coefficients := by
  obtain ⟨r, hr, haccept⟩ := (mem_result_iff _ _ _ _ _ _ _ _).mp hcs
  obtain ⟨hg, hlen, hdegree, hagree, hpoly⟩ := CanonicalAcceptanceMachine.result_sound
    (guardInput order samples r) r.context.previous w k A (hwidth r hr) hk domain received cs
      haccept
  exact ⟨hlen, hdegree, hagree, r, hr, hg, hpoly⟩

omit [DecidableEq F] in
/-- Uniform bounds on the concrete child budgets give linear total collection overhead. -/
theorem scan_bounds (order w k n T B : ℕ) (samples : List (QuadraticAlgebra F a b))
    (records : List (Record (QuadraticAlgebra F a b)))
    (hT : ∀ r ∈ records, itemFuel order samples w k n r ≤ T)
    (hB : ∀ r ∈ records, itemWork order samples w k n r ≤ B) :
    scanFuel order samples w k n records ≤ (T + 4) * records.length + 3 ∧
      scanWork order samples w k n records ≤ (B + 3 * T + 30) * records.length + 12 := by
  induction records with
  | nil => simp [scanFuel, scanWork]
  | cons r rs ih =>
      obtain ⟨ht, hb⟩ := ih (fun r hr ↦ hT r (by simp [hr])) (fun r hr ↦ hB r (by simp [hr]))
      have ht' := hT r (by simp)
      have hb' := hB r (by simp)
      simp only [scanFuel, scanWork, List.length_cons]
      constructor <;> nlinarith

/-- The same closed run returns the exact accepted subsequence and all message guarantees. -/
theorem evaluation_runFuel_correct (order w k A : ℕ) (samples : List (QuadraticAlgebra F a b))
    (records : List (Record (QuadraticAlgebra F a b)))
    (hwidth : ∀ r ∈ records, r.coefficients.length = w) (hk : k ≤ w) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) :
    ∃ out c, runFuel order samples w k A (List.ofFn fun i ↦ (domain i, received i))
        (fuel order samples w k n records) (.start records) = (.done out, c) ∧
      out = result order samples w k A (List.ofFn fun i ↦ (domain i, received i)) records ∧
      out.length ≤ records.length ∧
      (∀ cs ∈ out, cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received ∧
        ∃ r ∈ records, HiddenDerivative.CanonicalGuardMachine.result
          (guardInput order samples r) r.context.previous = true ∧
          (coefficientPolynomial cs).map (algebraMap F (QuadraticAlgebra F a b)) =
            coefficientPolynomial r.coefficients) ∧
      c ≤ workBound order samples w k n records := by
  obtain ⟨c, hr, hc⟩ := evaluation_runFuel order w k A samples
    (List.ofFn fun i ↦ (domain i, received i)) records hwidth
  refine ⟨_, c, ?_, rfl, result_length_le _ _ _ _ _ _ _,
    result_sound order w k A samples records hwidth hk domain received, ?_⟩
  · simpa only [List.length_ofFn] using hr
  · simpa only [List.length_ofFn] using hc

end ReedSolomon.ListDecoding.CanonicalOutputMachine
