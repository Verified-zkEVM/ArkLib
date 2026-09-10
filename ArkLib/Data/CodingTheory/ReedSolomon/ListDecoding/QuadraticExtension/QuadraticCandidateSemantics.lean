/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticCandidateMachine
/-!
# Exactness of base-field candidate acceptance

An extension candidate passes precisely when its physical coefficient vector descends to a
base-field vector satisfying both the degree and agreement conditions. The output retains the
same polynomial under the base embedding. These statements and the work bound concern the
same closed execution; coefficient preparation and enumeration remain separate.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticCandidateMachine

open Polynomial JetHornerMachine
open QuadraticAlgebra.CoefficientDescentMachine (result_eq_some_iff result_represents)

variable {F : Type*} [CommSemiring F] [DecidableEq F] {a b : F}

/-- Acceptance requires actual base coordinates and both paper-level message conditions. -/
theorem result_ne_none_iff (w k A : ℕ) (xs : List (QuadraticAlgebra F a b))
    (hwidth : xs.length = w) (hk : k ≤ w) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) :
    result w k A xs (List.ofFn fun i => (domain i, received i)) ≠ none ↔
      ∃ cs : List F, xs = cs.map (algebraMap F (QuadraticAlgebra F a b)) ∧
        (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received := by
  cases hd : Descent.result xs with
  | none =>
      constructor
      · simp [result, hd]
      · rintro ⟨cs, hcs, _, _⟩
        have h := (result_eq_some_iff xs cs).mpr hcs
        rw [hd] at h
        contradiction
  | some cs =>
      have hcs : xs = cs.map (algebraMap F (QuadraticAlgebra F a b)) :=
        (result_eq_some_iff xs cs).mp hd
      have hcwidth := (Descent.result_length hd).trans hwidth
      simp only [result, hd, Option.bind_some]
      rw [CandidateFilterMachine.result_ne_none_iff w k A cs hcwidth hk domain received]
      constructor
      · intro hc
        exact ⟨cs, hcs, hc⟩
      · rintro ⟨other, ho, hc⟩
        have he := (result_eq_some_iff xs other).mpr ho
        rw [hd] at he
        cases he
        exact hc

/-- An emitted base vector has the requested width, satisfies the message conditions, and
embeds to the original candidate polynomial rather than an unchecked projection of it. -/
theorem result_sound (w k A : ℕ) (xs : List (QuadraticAlgebra F a b))
    (hwidth : xs.length = w) (hk : k ≤ w) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (out : List F)
    (hout : result w k A xs (List.ofFn fun i => (domain i, received i)) = some out) :
    out.length = k ∧ (coefficientPolynomial out).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial out)) received ∧
      (coefficientPolynomial out).map (algebraMap F (QuadraticAlgebra F a b)) =
        coefficientPolynomial xs := by
  cases hd : Descent.result xs with
  | none => simp [result, hd] at hout
  | some cs =>
      have hcwidth := (Descent.result_length hd).trans hwidth
      have hf : CandidateFilterMachine.result w k A cs
          (List.ofFn fun i => (domain i, received i)) = some out := by
        simpa only [result, hd, Option.bind_some] using hout
      obtain ⟨hlen, hpoly⟩ := CandidateFilterMachine.result_represents hcwidth hk hf
      have hgood := (CandidateFilterMachine.result_ne_none_iff w k A cs hcwidth hk
        domain received).mp (by simp only [hf, ne_eq, reduceCtorEq, not_false_eq_true])
      refine ⟨hlen, by rw [hpoly]; exact hgood.1, by rw [hpoly]; exact hgood.2, ?_⟩
      rw [hpoly, map_coefficientPolynomial, result_represents xs cs hd]
      rfl

/-- All acceptance, output and work guarantees are attached to the same closed driver run. -/
theorem evaluation_runFuel_correct (w k A : ℕ) (xs : List (QuadraticAlgebra F a b))
    (hwidth : xs.length = w) (hk : k ≤ w) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) :
    ∃ out c, runFuel w k A (List.ofFn fun i => (domain i, received i)) (fuel w k n)
        (.start xs) = (.done out, c) ∧
      (out ≠ none ↔ ∃ cs : List F,
        xs = cs.map (algebraMap F (QuadraticAlgebra F a b)) ∧
          (coefficientPolynomial cs).degree < k ∧
          A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received) ∧
      (∀ ys, out = some ys → ys.length = k ∧ (coefficientPolynomial ys).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial ys)) received ∧
        (coefficientPolynomial ys).map (algebraMap F (QuadraticAlgebra F a b)) =
          coefficientPolynomial xs) ∧
      c ≤ workBound w n := by
  obtain ⟨c, hr, hc⟩ := evaluation_runFuel w k A xs
    (List.ofFn fun i => (domain i, received i)) hwidth
  refine ⟨_, c, ?_, result_ne_none_iff w k A xs hwidth hk domain received, ?_, ?_⟩
  · simpa only [List.length_ofFn] using hr
  · exact result_sound w k A xs hwidth hk domain received
  · simpa only [List.length_ofFn] using hc

end ReedSolomon.ListDecoding.QuadraticCandidateMachine
