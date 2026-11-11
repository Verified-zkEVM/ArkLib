/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Message.Basic

/-!
# Neutral Sumcheck prover contracts

A prover stores an executable state indexed by its remaining arity. Its separate proof model
relates that state to residual polynomials and claims over a supplied family of finite cubes.
The one-step invariant states only honest acceptance and preservation of the residual claim.
-/

@[expose] public section

namespace Sumcheck

open Polynomial MvPolynomial

/-- Executable message generation and folding by a verifier challenge. -/
structure ProverOps (R M : Type) (State : ℕ → Type) where
  message : {n : ℕ} → State (n + 1) → M
  fold : {n : ℕ} → State (n + 1) → R → State n

/-- Proof-only residual semantics and the honest prover's local completeness obligations. -/
structure ProverModel {R M : Type} [CommRing R] (ops : MessageOps R M)
    (State : ℕ → Type) (prv : ProverOps R M State)
    (cube : (n : ℕ) → Finset (Fin n → R)) (d : ℕ) where
  polynomial : {n : ℕ} → State n → R⦃≤ d⦄[X Fin n]
  claim : {n : ℕ} → State n → R
  claim_eq : ∀ {n} (s : State n), claim s = ∑ b ∈ cube n, (polynomial s).val.eval b
  fold_eq : ∀ {n} (s : State (n + 1)) r x,
    (polynomial (prv.fold s r)).val.eval x = (polynomial s).val.eval (Fin.cons r x)
  message_eq : ∀ {n} (s : State (n + 1)) r,
    ops.evaluate (claim s) (prv.message s) r = claim (prv.fold s r)
  message_accept : ∀ {n} (s : State (n + 1)), ops.accept (claim s) (prv.message s) = true

/-- Check a message and, on acceptance, evaluate the next claim. -/
def step {R M : Type} (ops : MessageOps R M) (c : R) (m : M) (r : R) : Option R :=
  if ops.accept c m then some (ops.evaluate c m r) else none

/-- An honest step accepts and preserves equality with the prover's residual claim. -/
theorem honest_step {R M : Type} [CommRing R] {d : ℕ}
    (ops : MessageOps R M) (State : ℕ → Type) (prv : ProverOps R M State)
    (cube : (n : ℕ) → Finset (Fin n → R)) (model : ProverModel ops State prv cube d)
    {n : ℕ} (s : State (n + 1)) (r : R) :
    step ops (model.claim s) (prv.message s) r = some (model.claim (prv.fold s r)) := by
  simp [step, model.message_accept, model.message_eq]

end Sumcheck
