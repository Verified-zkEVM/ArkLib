/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.Basic

/-!
  # Simple Random Oracle based commitment scheme

  We define a simple commitment scheme based on random oracles:

  - The core commitment map is `commit v r := RO(v, r) : γ`.
  - The randomized helper `commitRandomized` samples `r : β` from the randomness oracle and then
    computes `commit v r`.
  - To open the commitment `cm`, the prover reveals `(v, r)` and the verifier checks that
    `RO(v, r) = cm`.

  We show that this is a commitment scheme satisfying completeness, extractability, and hiding.
-/

universe u

namespace SimpleRO

open OracleSpec OracleComp

@[reducible]
def randSpec (β : Type) : OracleSpec Unit := Unit →ₒ β

@[reducible]
def ROspec (α β γ : Type) : OracleSpec (α × β) := (α × β) →ₒ γ

@[reducible]
def oSpec (α β γ : Type) : OracleSpec (Unit ⊕ (α × β)) := randSpec β + ROspec α β γ

variable {α β γ : Type}

def sampleRandomness : OracleComp (oSpec α β γ) β :=
  query (spec := oSpec α β γ) (Sum.inl ())

def commit (v : α) (r : β) : OracleComp (oSpec α β γ) γ :=
  query (spec := oSpec α β γ) (Sum.inr (v, r))

def commitRandomized (v : α) : OracleComp (oSpec α β γ) γ := do
  let r ← sampleRandomness (α := α) (β := β) (γ := γ)
  commit v r

def verify [DecidableEq γ] (cm : γ) (v : α) (r : β) :
    OptionT (OracleComp (oSpec α β γ)) Unit := do
  let cm' ← liftM (commit v r)
  guard (cm' = cm)

@[reducible, simp]
def openingPSpec (β : Type) : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[β]⟩

-- The trivial `OracleInterface` instance for `α`
local instance : OracleInterface α where
  Query := Unit
  toOC.spec := fun () => α
  toOC.impl := fun () => read

abbrev OpeningStatement (α γ : Type) [OracleInterface α] :=
  γ × (q : OracleInterface.Query α) × OracleInterface.Response q

def openingProver : Prover (oSpec α β γ)
    (OpeningStatement α γ) (α × β) Bool Unit (openingPSpec β) where
  PrvState
  | 0 => OpeningStatement α γ × (α × β)
  | 1 => OpeningStatement α γ × (α × β)
  input := fun x => x
  sendMessage
  | ⟨0, _⟩ => fun state => pure (state.2.2, state)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun _ => pure (true, ())

def openingVerifier [DecidableEq γ] : Verifier (oSpec α β γ)
    (OpeningStatement α γ) Bool (openingPSpec β) where
  verify := fun ⟨cm, _, v⟩ transcript => do
    verify cm v (transcript 0)
    return true

def commitmentScheme [DecidableEq γ] :
    Commitment.Scheme (oSpec α β γ) α β γ (openingPSpec β) where
  commit := commit
  opening :=
    { prover := openingProver
      verifier := openingVerifier }

end SimpleRO
