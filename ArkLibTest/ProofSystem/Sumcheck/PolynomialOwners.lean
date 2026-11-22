/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Structured.RoundLemmas

/-! # Shared sumcheck polynomial constructors

The same product API accepts nonuniform bounds and the identity combinator. Prefix fixing
preserves arbitrary uniform bounds, and the round wrapper accepts heterogeneous domains.
-/

open MvPolynomial Sumcheck Sumcheck.Structured

noncomputable section

example {R : Type} [CommSemiring R] {n : ℕ} {Context : Type} {b : Fin n → ℕ}
    (param : SumcheckMultiplierParam R n Context b) (ctx : Context)
    (t : MultilinearPoly R n) (j : Fin n) :
    (computeRoundPoly n param ctx t).val.degreeOf j ≤ param.degCombinator + b j :=
  (mem_restrictDegreeVar_iff_degreeOf_le _).mp (computeRoundPoly n param ctx t).property j

example {R : Type} [CommSemiring R] {n : ℕ} (t m : MultilinearPoly R n)
    (x : Fin n → R) :
    (computeInitialSumcheckPoly n t m).val.eval x = m.val.eval x * t.val.eval x := by
  simp only [coe_computeInitialSumcheckPoly, map_mul]

example {R : Type} [CommSemiring R] {n d : ℕ} (p : R⦃≤ d⦄[X Fin n])
    (i : Fin (n + 1)) (c : Fin i → R) (x : Fin (n - i) → R) :
    (fixPrefix n i p c).val.eval x = p.val.eval (Fin.append c x ∘ Fin.cast (by omega)) :=
  eval_fixFirstVariablesOfMQP_append i p.val c x

example {R : Type} [CommRing R] {n d : ℕ} [NeZero n]
    (D : SumcheckDomain R n) (i : Fin n) (p : R⦃≤ d⦄[X Fin (n - i)]) (r : R) :
    (getSumcheckRoundPoly n D i p).val.eval r =
      ∑ x ∈ (D.drop (i + 1)).cube,
        p.val.eval (Fin.cons r x ∘ Fin.cast (by have := i.isLt; omega)) := by
  simp only [getSumcheckRoundPoly, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun x _ => eval_evalExcept_first _ x p.val r
