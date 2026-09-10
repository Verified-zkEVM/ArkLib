/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CandidateFilterMachine
/-!
# Exact polynomial acceptance by the executable candidate filter

Materialized descending coefficient vectors may contain leading zeros. The closed filter
accepts exactly the polynomials of degree below the message dimension with the requested
number of agreements. Its accepted output represents the same polynomial in the requested
width. Input preparation, base-field descent and duplicate removal are not part of this filter.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementMachine

open Polynomial JetHornerMachine

variable {F : Type*} [CommSemiring F] [DecidableEq F]

omit [DecidableEq F] in
private theorem eval_foldl (cs : List F) (p : F[X]) (x : F) :
    (cs.foldl (fun q a => q * X + C a) p).eval x =
      cs.foldl (fun v a => v * x + a) (p.eval x) := by
  induction cs generalizing p with
  | nil => rfl
  | cons a cs ih =>
      rw [List.foldl_cons, List.foldl_cons, ih, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C]

omit [DecidableEq F] in
/-- Horner evaluation agrees with the represented polynomial, including padded leading zeros. -/
theorem valueAt_eq_coefficientPolynomial (cs : List F) (x : F) :
    valueAt cs x = (coefficientPolynomial cs).eval x := by
  simpa only [valueAt, coefficientPolynomial, eval_zero] using (eval_foldl cs 0 x).symm

/-- Counting uses every indexed position once, without requiring normalized coefficients. -/
theorem agreementCount_eq_coefficientPolynomial_agree (cs : List F)
    {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) :
    agreementCount cs (List.ofFn fun i => (domain i, received i)) =
      Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received := by
  have hsum (rows : List (F × F)) : agreementCount cs rows =
      (rows.map fun row => if valueAt cs row.1 = row.2 then 1 else 0).sum := by
    induction rows with
    | nil => rfl
    | cons row rows ih => cases row; simp [agreementCount, ih]
  rw [hsum]
  simp [List.map_ofFn, List.sum_ofFn, valueAt_eq_coefficientPolynomial, Code.agree, evalOnPoints]
  rfl

end ReedSolomon.ListDecoding.AgreementMachine

namespace ReedSolomon.ListDecoding.CandidateFilterMachine

open Polynomial JetHornerMachine

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Successful filtering preserves the polynomial and emits exactly the requested width. -/
theorem result_represents {w k A : ℕ} {cs tail : List F} {rows : List (F × F)}
    (hwidth : cs.length = w) (hk : k ≤ w) (hout : result w k A cs rows = some tail) :
    tail.length = k ∧ coefficientPolynomial tail = coefficientPolynomial cs := by
  unfold result at hout
  split at hout
  next h => simp at hout
  next out h =>
    split at hout
    next ht =>
      cases hout
      have hs := (DegreeTruncationMachine.result_eq_some_iff (w - k) cs tail).mp h
      constructor
      · have hh := congrArg List.length hs
        simp only [List.length_append, List.length_replicate] at hh
        omega
      · rw [hs, coefficientPolynomial_zero_prefix]
    next ht => simp at hout

/-- Acceptance is equivalent to both paper-level conditions on the original polynomial. -/
theorem result_ne_none_iff (w k A : ℕ) (cs : List F) (hwidth : cs.length = w) (hk : k ≤ w)
    {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) :
    result w k A cs (List.ofFn fun i => (domain i, received i)) ≠ none ↔
      (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received := by
  have hdegree := DegreeTruncationMachine.exists_result_iff_degree_lt (w - k) k cs
    (show cs.length = w - k + k by omega)
  cases hd : DegreeTruncationMachine.result (w - k) cs with
  | none => simp [result, hd, ← hdegree]
  | some tail =>
      have hp : coefficientPolynomial tail = coefficientPolynomial cs := by
        have hs := (DegreeTruncationMachine.result_eq_some_iff (w - k) cs tail).mp hd
        rw [hs, coefficientPolynomial_zero_prefix]
      have hdeg := hdegree.mp ⟨tail, hd⟩
      simp [result, hd, AgreementMachine.agreementCount_eq_coefficientPolynomial_agree,
        hp, hdeg]

/-- The exact acceptance predicate, output representation and primitive-work bound hold of
one and the same execution. All input cells are supplied, not implicitly constructed. -/
theorem evaluation_runFuel_correct (w k A : ℕ) (cs : List F)
    (hwidth : cs.length = w) (hk : k ≤ w) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) :
    ∃ out c, runFuel w k A (List.ofFn fun i => (domain i, received i)) (fuel w k n)
        (.start cs) = (.done out, c) ∧
      (out ≠ none ↔ (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received) ∧
      (∀ tail, out = some tail → tail.length = k ∧
        coefficientPolynomial tail = coefficientPolynomial cs) ∧
      c ≤ workBound w n := by
  obtain ⟨c, hr, hc⟩ := evaluation_runFuel w k A cs
    (List.ofFn fun i => (domain i, received i)) hwidth.le
  refine ⟨_, c, ?_, result_ne_none_iff w k A cs hwidth hk domain received, ?_, ?_⟩
  · simpa only [List.length_ofFn] using hr
  · intro tail ht
    exact result_represents hwidth hk ht
  · simpa only [List.length_ofFn] using hc

end ReedSolomon.ListDecoding.CandidateFilterMachine
