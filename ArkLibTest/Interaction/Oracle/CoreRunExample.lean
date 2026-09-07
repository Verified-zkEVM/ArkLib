/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.CoreRun

/-! # Closing the verifier's actual output with the same execution's sources -/

namespace Interaction.Oracle.CoreRunExample

open OracleComp

/-- Observable ambient events. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Unit

/-- Arbitrary pure input behavior is separate from prover data. -/
abbrev input : OracleSpec Unit := Unit →ₒ Nat

/-- Only the first coordinate of each sent message is observable. -/
@[reducible]
def interface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := do return (← read).1

/-- The last sent message must remain available at the terminal leaf. -/
abbrev protocol : Oracle.Protocol := .oracleWith (Nat × Nat) interface .done

/-- Final source signature. -/
abbrev finalSpec := OracleSpec.ofPFunctor (Access.extend input.toPFunctor interface)

/-- One observable scalar output oracle. -/
@[reducible]
def output : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => OracleInterface.instDefault⟩

/-- A derived output query adds an input answer to the sent message's answer. -/
def plan : VirtualOracle finalSpec output := ⟨fun _ => do
  let old : Nat ← liftM (finalSpec.query (.inl ()))
  let sent : Nat ← liftM (finalSpec.query (.inr ()))
  return old + sent⟩

/-- Terminal computations produce the statement while leaving the output oracle as a plan. -/
def terminal (accept : Bool) :
    OracleComp (ambient + finalSpec) (Option (OracleClaim finalSpec Nat output)) := do
  let _ ← liftM ((ambient + finalSpec).query (.inl 2))
  let sent : Nat ← liftM ((ambient + finalSpec).query (.inr (.inr ())))
  return if accept then some ⟨sent, plan⟩ else none

/-- The verifier can query after receipt without obtaining the concrete pair. -/
def verifier (accept : Bool) : Verifier.Strategy ambient protocol.tree protocol.roles
    protocol.oracles input.toPFunctor
    (TerminalClaim protocol input.toPFunctor (fun _ => Nat) (fun _ => output)) := by
  change OracleComp (ambient + finalSpec)
    (OracleComp (ambient + finalSpec) (Option (OracleClaim finalSpec Nat output)))
  exact do
    let _ ← liftM ((ambient + finalSpec).query (.inl 1))
    return terminal accept

/-- The prover retains the hidden coordinate as private output. -/
def prover (message hidden : Nat) : Prover.Strategy ambient protocol.tree protocol.roles
    (fun _ => Nat) := do
  let _ ← liftM (ambient.query 0)
  return ⟨(message, hidden), hidden⟩

/-- Package the actual strategies for the core executor. -/
def reduction (accept : Bool) : Reduction ambient protocol input.toPFunctor Unit (Nat × Nat)
    (fun _ => Nat) (TerminalClaim protocol input.toPFunctor (fun _ => Nat) (fun _ => output)) where
  prover := fun _ witness => pure (prover witness.1 witness.2)
  verifier := fun _ => verifier accept

/-- Log each ambient event without assuming effect commutativity. -/
def logger : QueryImpl ambient (StateM (List Nat)) := fun tag => do
  modify (· ++ [tag])

/-- Observe the exported core executor. -/
def observed (accept : Bool) (message hidden : Nat) :=
  (simulateQ logger (executeCore (reduction accept) (fun _ => 7) () (message, hidden))).run []

example (hidden : Nat) : (observed true 11 hidden).2 = [0, 1, 2] := rfl

example (hidden : Nat) : (observed true 11 hidden).1.proverOut = hidden := rfl

example (hidden : Nat) : (observed true 11 hidden).1.closed.map (·.stmt) = some 11 := rfl

example (hidden : Nat) :
    (observed true 11 hidden).1.closed.map (fun claim => claim.oracles ⟨(), ()⟩) =
      some (18 : Nat) := rfl

/-- A different run closes with its own message, not the previous run's handler. -/
example (hidden : Nat) :
    (observed true 19 hidden).1.closed.map (fun claim => claim.oracles ⟨(), ()⟩) =
      some (26 : Nat) := rfl

example (message hidden : Nat) : (observed false message hidden).1.closed = none := rfl

end Interaction.Oracle.CoreRunExample
