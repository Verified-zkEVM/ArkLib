/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Execution

/-! Acceptance examples for shape independence, recorded challenges and terminal effects. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.TwoParty.Lens

namespace Interaction.Core.Tests

def done : Protocol := .pure ⟨⟩
def coin : Protocol := .liftBind (.challenge Bool) (fun _ => done)

example : projectPathAlong plainSig coin ⟨true, ⟨⟩⟩ =
    projectPathAlong plainSig coin ⟨false, ⟨⟩⟩ := rfl

def branching : Protocol :=
  .liftBind (.message Bool) (fun (b : Bool) => if b = true then coin else done)

example : projectPathAlong plainSig branching ⟨false, ⟨⟩⟩ ≠
    projectPathAlong plainSig branching ⟨true, ⟨true, ⟨⟩⟩⟩ := by
  intro h
  have := congrArg Sigma.fst h
  exact Bool.false_ne_true this

def echo : Focal plainSig Id coin (fun _ => Bool) := fun b => b

def trueCoin : Counterpart plainSig Id coin (fun _ => PUnit) := ⟨true, ⟨⟩⟩
def falseCoin : Counterpart plainSig Id coin (fun _ => PUnit) := ⟨false, ⟨⟩⟩

example : (Interaction.TwoParty.Lens.run (OutC := fun _ => PUnit) coin echo trueCoin).2.1 =
    true := by
  rfl

example : (Interaction.TwoParty.Lens.run (OutC := fun _ => PUnit) coin echo falseCoin).2.1 =
    false := by
  rfl

/-- A stored challenge draw that always fails. -/
def failingDraw : (c : ChallengeNode plainSig coin) → Option (challengeSpec plainSig coin c) :=
  fun _ => none

def optionEcho : Focal plainSig Option coin (fun _ => Bool) := some fun b => some b

/-- Executing the converted sampler runs the failing draw. -/
example : Interaction.TwoParty.Lens.run (OutC := fun _ => PUnit) coin optionEcho
    (publicCoinSampler plainSig coin failingDraw).toCounterpart = none := rfl

/-- Replay follows the recorded challenge without executing the failing draw. -/
example : (publicCoinSampler plainSig coin failingDraw).replay ⟨true, ⟨⟩⟩ = some ⟨⟩ :=
  replay_publicCoinSampler coin failingDraw ⟨true, ⟨⟩⟩

run_cmd do
  unless ((publicCoinSampler plainSig coin failingDraw).replay ⟨false, ⟨⟩⟩).isSome do
    throwError "replay executed the stored draw"
  unless (Interaction.TwoParty.Lens.run (OutC := fun _ => PUnit) coin optionEcho
      (sampler plainSig coin failingDraw)).isNone do
    throwError "the runner's sampler did not execute its draw"

def leaf : Focal plainSig (StateM Nat) done (fun _ => Nat) := do
  modify (· + 1)
  get

def leafSampler : Counterpart plainSig (StateM Nat) done (fun _ => PUnit) := pure ⟨⟩

example : (Interaction.TwoParty.Lens.run (OutC := fun _ => PUnit) done leaf leafSampler).run 0 =
    (⟨⟨⟩, 1, ⟨⟩⟩, 1) := by
  rfl

run_cmd do
  unless ((Interaction.TwoParty.Lens.run (OutC := fun _ => PUnit)
    done leaf leafSampler).run 0).2 == 1 do
    throwError "the zero-round leaf must execute exactly once"

/-- The second challenge of two appended coins is the suffix coin's only challenge. -/
def secondChallenge : ChallengeNode plainSig (coin.append fun _ => coin) :=
  ⟨.inr ⟨⟨⟩, .inl ⟨⟩⟩, rfl⟩

example : ChallengeNode.appendEquiv plainSig coin (fun _ => coin) ⟨.inl ⟨⟩, rfl⟩ =
    .inl ⟨.inl ⟨⟩, rfl⟩ := rfl

example : ChallengeNode.appendEquiv plainSig coin (fun _ => coin) secondChallenge =
    .inr ⟨⟨⟨⟩, ⟨⟩⟩, ⟨.inl ⟨⟩, rfl⟩⟩ := rfl

example : (ChallengeNode.appendEquiv plainSig coin (fun _ => coin)).symm
    (.inr ⟨⟨⟨⟩, ⟨⟩⟩, ⟨.inl ⟨⟩, rfl⟩⟩) = secondChallenge := rfl

run_cmd do
  unless (ChallengeNode.appendEquiv plainSig coin (fun _ => coin) secondChallenge).isRight do
    throwError "the second challenge of two coins must belong to the suffix"

end Interaction.Core.Tests

run_cmd do
  for decl in [``Interaction.Core.toCounterpart_publicCoinSampler,
      ``Interaction.Core.toCounterpart_publicCoinOracleSampler,
      ``Interaction.Core.replay_publicCoinSampler,
      ``Interaction.Core.replay_publicCoinOracleSampler,
      ``Interaction.Core.Node.appendJoin_appendSplit,
      ``Interaction.Core.Node.appendSplit_appendJoin,
      ``Interaction.Core.Node.position_appendEquiv,
      ``Interaction.Core.ChallengeNode.appendEquiv] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
