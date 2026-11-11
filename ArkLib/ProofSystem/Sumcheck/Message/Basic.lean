/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Data.MvPolynomial.Notation

/-!
# Neutral Sumcheck message contracts

Runtime operations are separate from their proof-only polynomial interpretation. Decoding may
use the running claim, allowing compressed messages without requiring an injective encoding.
-/

@[expose] public section

namespace Sumcheck

open Polynomial

/-- Executable evaluation and acceptance of a message at a running claim. -/
structure MessageOps (R M : Type) where
  evaluate : R → M → R → R
  accept : R → M → Bool

/-- A degree-bounded meaning for messages, with the exact runtime evaluation and sum check. -/
structure MessageModel {R M : Type} [CommRing R]
    (D : Finset R) (ops : MessageOps R M) (d : ℕ) where
  interpret : R → M → R⦃≤ d⦄[X]
  evaluate_eq : ∀ c m x, ops.evaluate c m x = (interpret c m).val.eval x
  accept_iff : ∀ c m, ops.accept c m = true ↔ ∑ x ∈ D, (interpret c m).val.eval x = c

variable {R M : Type} [CommRing R] {d : ℕ}

/-- Uncompressed messages use a claim-independent evaluator and an explicit finite sum check. -/
def plainOps [DecidableEq R] (D : Finset R) (ev : M → R → R) : MessageOps R M where
  evaluate _ := ev
  accept c m := decide (∑ x ∈ D, ev m x = c)

/-- The finite-domain check performed by uncompressed messages. -/
@[simp] theorem plainOps_accept_iff [DecidableEq R] (D : Finset R) (ev : M → R → R)
    (c : R) (m : M) :
    (plainOps D ev).accept c m = true ↔ ∑ x ∈ D, ev m x = c := by
  simp [plainOps]

/-- The identity interpretation on Mathlib polynomials is a proof-only reference model. -/
noncomputable def identityModel [DecidableEq R] (D : Finset R) :
    MessageModel D (plainOps D (fun p : R⦃≤ d⦄[X] => p.val.eval)) d where
  interpret _ p := p
  evaluate_eq _ _ _ := rfl
  accept_iff _ _ := by simp [plainOps]

end Sumcheck
