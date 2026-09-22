/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import ArkLib.Data.CodingTheory.GuruswamiSudan.Correctness

/-!
# Executable Guruswami-Sudan decoder tests

Acceptance tests for bounded parameter search and a concrete end-to-end decoding path.
-/

namespace GuruswamiSudan

open Polynomial CompPoly CompPoly.GuruswamiSudan

noncomputable section

example : searchParamsUpTo 1 3 2 5 1 =
    some (execParamsOfMultiplicityAndDegree 2 1 1 2) := by
  decide

example : (boundedSearchParamSelector 1 3).CompleteAt 2 5 1 := by
  apply boundedSearchParamSelector_complete_at
  exact ⟨1, 2, by decide, by decide, by decide, by decide⟩

private abbrev F := KoalaBear.Field

private def evaluationPoints : Fin 2 ↪ F where
  toFun i := i.val
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

private def messagePolynomial : F[X] :=
  Polynomial.C (1 : F) + Polynomial.monomial 1 (2 : F)

private def receivedValues (i : Fin 2) : F :=
  messagePolynomial.eval (evaluationPoints i)

private def receivedWord : GSReceivedWord F :=
  { points := Array.ofFn fun i : Fin 2 => (evaluationPoints i, receivedValues i) }

example : ∃ cp,
    cp ∈ (decode koalaBearDenseRothContext
      (boundedSearchParamSelector 2 4).toCompPolySelector 2 0 receivedWord).toList ∧
      cp.toPoly = messagePolynomial := by
  apply decode_complete (ωs := evaluationPoints) (f := receivedValues)
    (ctx := koalaBearDenseRothContext) (selector := boundedSearchParamSelector 2 4)
  · rfl
  · apply boundedSearchParamSelector_complete_at
    exact ⟨1, 1, by decide, by decide, by decide, by decide⟩
  · rw [GSSpecSet]
    constructor
    · rw [degree_lt_iff_coeff_zero]
      intro m hm
      have hm0 : m ≠ 0 := by omega
      have h1m : 1 ≠ m := by omega
      rw [messagePolynomial, coeff_add, coeff_C, coeff_monomial]
      simp [hm0, h1m]
    · rw [Nat.le_zero, hammingDist_eq_zero]
      rfl

end

end GuruswamiSudan
