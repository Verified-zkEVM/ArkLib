/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.Basic

/-!
  # Simple Random Oracle based commitment scheme

  We define a simple commitment scheme based on random oracles:

  - To commit to a value `v : α`, the prover samples a random `r : β` and computes
    `commit r v := RO(v, r) : γ`.
  - To open the commitment `cm`, the prover reveals `(v, r)` and the verifier checks that
    `RO(v, r) = cm`.

  We show that this is a commitment scheme satisfying completeness, extractability, and hiding.
-/

universe u

namespace SimpleRO

open OracleSpec OracleComp

@[reducible]
def randSpec (β : Type) : OracleSpec Unit := fun _ => (Unit, β)

@[reducible]
def ROspec (α β γ : Type) : OracleSpec Unit := fun _ => (α × β, γ)

@[reducible]
def oSpec (α β γ : Type) : OracleSpec (Unit ⊕ Unit) := randSpec β ++ₒ ROspec α β γ

variable {α β γ : Type}

-- TODO: figure out why we need so much explicit annotation

def commit (v : α) : OracleComp (oSpec α β γ) γ := do
  let r : β ← liftComp
    (query (spec := randSpec β) () () : OracleComp (randSpec β) β) _
  let cm : γ ← liftComp
    (query (spec := ROspec α β γ) () (v, r) : OracleComp (ROspec α β γ) γ) _
  return cm

def verify [BEq γ] (cm : γ) (v : α) (r : β) : OracleComp (ROspec α β γ) Unit := do
  let cm' ← (query (spec := ROspec α β γ) () (v, r) : OracleComp (ROspec α β γ) γ)
  guard (cm' == cm)

-- The trivial `OracleInterface` instance for `α`
local instance : OracleInterface α where
  Query := Unit
  Response := α
  oracle := fun x _ => x

def commitmentScheme : Commitment.Scheme (oSpec α β γ) α β γ !p[] where
  commit := fun v r => commit v
  opening := .mk (sorry) (.mk (sorry))

end SimpleRO
