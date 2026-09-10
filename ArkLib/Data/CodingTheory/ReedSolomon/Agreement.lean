/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Finset.Filter

/-!
# Polynomial agreement sets

The full coordinate sets on which one polynomial, or a pair of polynomials,
agrees with received words. No decoding-radius or correlated-agreement theorem is required.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

/-- The full set of positions where `P` agrees with a received word. -/
def polynomialAgreementSet {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (P : F[X]) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ P.eval (domain i) = received i

/-- The positions where two message polynomials simultaneously agree with two received words. -/
def commonPolynomialAgreementSet {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (F₀ G₀ : F[X]) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i

end
end ReedSolomon
