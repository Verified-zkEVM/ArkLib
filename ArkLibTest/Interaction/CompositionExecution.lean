/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.CompositionSoundness

/-!
# Native dependent composition with noncommutative effects

A public challenge selects the suffix tree. Only the true branch has a verifier preamble.
The whole prover retains private memory and performs effects after both public challenges.
The ordinary paired runner executes both branch shapes with an observable ordered state trace.
-/

namespace Interaction.TwoParty.CompositionExecutionTest

open StrategyOver.TwoParty

def prefixTree : TypeTree := .node Bool (fun _ => .done)

def prefixRoles : RoleDecoration prefixTree := ⟨.receiver, fun _ => ⟨⟩⟩

def messageTree : TypeTree := .node Nat (fun _ => .node Bool (fun _ => .done))

def messageRoles : RoleDecoration messageTree :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => ⟨⟩⟩⟩

/-- The extra preamble is part of the selected protocol tree, not a local conditional effect. -/
def suffixTree : TypeTree.Path prefixTree → TypeTree
  | ⟨false, ⟨⟩⟩ => messageTree
  | ⟨true, ⟨⟩⟩ => .node Unit (fun _ => messageTree)

def suffixRoles : (t : TypeTree.Path prefixTree) → RoleDecoration (suffixTree t)
  | ⟨false, ⟨⟩⟩ => messageRoles
  | ⟨true, ⟨⟩⟩ => ⟨.receiver, fun _ => messageRoles⟩

def note (event : String) : StateM (List String) Unit := modify (· ++ [event])

/-- A private value survives in the response to the final public challenge. -/
def messageProver (memory : Nat) :
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (StateM (List String))) Participant.focal
      messageTree messageRoles (fun _ => Nat) := do
  note "second message"
  return ⟨memory, fun challenge => do
    note "after second challenge"
    return if challenge then memory + 1 else memory⟩

/-- This is one ordinary strategy on the full appended tree, not a prefix/suffix state model. -/
def wholeProver :
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (StateM (List String))) Participant.focal
      (prefixTree.append suffixTree) (prefixRoles.append suffixRoles) (fun _ => Nat) := by
  intro challenge
  cases challenge with
  | false => exact do
      note "after first challenge"
      return messageProver 7
  | true => exact do
      note "after first challenge"
      return fun _ => do
        note "after preamble"
        return messageProver 11

def firstVerifier (challenge : Bool) :
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (StateM (List String)))
      Participant.counterpart prefixTree prefixRoles (fun _ => Unit) := do
  note "first challenge"
  return ⟨challenge, ()⟩

def messageVerifier :
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (StateM (List String)))
      Participant.counterpart messageTree messageRoles (fun _ => Nat) := fun message => do
  note "message received"
  return do
    note "second challenge"
    return ⟨true, message⟩

def suffixVerifier : (t : TypeTree.Path prefixTree) → Unit →
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (StateM (List String)))
      Participant.counterpart (suffixTree t) (suffixRoles t) (fun _ => Nat)
  | ⟨false, ⟨⟩⟩, _ => messageVerifier
  | ⟨true, ⟨⟩⟩, _ => do
      note "suffix preamble"
      return ⟨(), messageVerifier⟩

/-- Select final participant outputs from the actual ordinary run. -/
def outputs (challenge : Bool) : StateM (List String) (Nat × Nat) := do
  let result ← run (prefixTree.append suffixTree) (prefixRoles.append suffixRoles)
    wholeProver (Counterpart.appendFlat (Output₂ := fun _ => Nat)
      (firstVerifier challenge) suffixVerifier)
  return (result.2.1, result.2.2)

/-- The short branch retains postchallenge and terminal effects and returns private memory. -/
example : (outputs false).run [] = ((8, 7),
    ["first challenge", "after first challenge", "second message", "message received",
      "second challenge", "after second challenge"]) := by
  unfold outputs
  rw [run_appendFlat_splitPrefix]
  rfl

/-- The selected preamble occurs after the first response and before the second message. -/
example : (outputs true).run [] = ((12, 11),
    ["first challenge", "after first challenge", "suffix preamble", "after preamble",
      "second message", "message received", "second challenge", "after second challenge"]) := by
  unfold outputs
  rw [run_appendFlat_splitPrefix]
  rfl

end Interaction.TwoParty.CompositionExecutionTest
