/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.DegreeTruncationSemantics
/-!
# Exact output specification for Reed--Solomon decoders

This module owns the backend-independent contract for executable list decoders. Outputs use the
repository's fixed-width descending coefficient convention. Exactness includes duplicate freedom
both before and after interpreting those vectors as polynomials.
-/

namespace ReedSolomon.ListDecoding

open Polynomial JetHornerMachine

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- Exact fixed-width coefficient vectors and their polynomial interpretations, with no duplicates
in either representation. Membership means degree below `k` and at least `A` indexed agreements.

The degree comparison uses `Polynomial.degree`, so the zero polynomial satisfies every natural
degree bound, including `k = 0`. In that case its canonical coefficient vector is empty. -/
def ExactOutput (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (out : List (List F)) : Prop :=
  (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
    (∀ f : F[X], f ∈ out.map coefficientPolynomial ↔
      f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received) ∧
    (∀ cs : List F, cs ∈ out ↔ cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received)

omit [DecidableEq F] in
/-- Equal-width descending coefficient vectors are equal when they represent the same polynomial. -/
theorem coefficientVectors_eq {xs ys : List F} (hlen : xs.length = ys.length)
    (hpoly : coefficientPolynomial xs = coefficientPolynomial ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using hlen.symm
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons b ys =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hcoeff := congrArg (fun p : F[X] ↦ p.coeff xs.length) hpoly
          rw [coeff_coefficientPolynomial_cons_length, htail,
            coeff_coefficientPolynomial_cons_length] at hcoeff
          subst b
          rw [coefficientPolynomial_cons, coefficientPolynomial_cons, htail] at hpoly
          exact congrArg (a :: ·) (ih htail (add_left_cancel hpoly))

end ReedSolomon.ListDecoding
