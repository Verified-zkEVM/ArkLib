/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.LoggedExecution
import ArkLib.Interaction.Core.Oracle.Routing
import VCVio.OracleComp.Runtime

/-! # The hidden-bit runtime fixture

The runtime samples a hidden bit once at setup and counts ambient queries. The ambient request
`false` answers a dummy `false`; the request `true` reveals the hidden bit. The prefix receives a
`Unit` challenge and its decision makes the dummy request; it exports the input, which holds
`false`. The suffix receives a public guess; its decision reads the export as a pad, reveals the
hidden bit and claims `hidden ^^ pad`, and its output data is `guess ^^ pad`. A request `true`
costs 3 and a request `false` costs 1. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec

namespace Interaction.Core.HiddenBitFixture

/-- `false` requests a dummy answer; `true` reveals the hidden bit. -/
abbrev bitAmbient : OracleSpec Bool := Bool →ₒ Bool

/-- One bit-valued oracle slot, used for the input and the exports. -/
@[instance_reducible] def bits : OracleFamily.{0, 0, 0} Unit (fun _ => Bool) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The input slot holds `false`. -/
def falseData : ∀ _ : Unit, Bool := fun _ => false

/-- The verifier sends a `Unit` challenge. -/
@[instance_reducible] def bitFirst : OracleProtocol :=
  .liftBind (.challenge Unit) (fun _ => .pure ⟨⟩)

/-- The prover sends a public guess. -/
@[instance_reducible] def bitSecond : OracleProtocol :=
  .liftBind (.message Bool) (fun _ => .pure ⟨⟩)

/-- The challenge, then the guess. -/
abbrev bitCombined : OracleProtocol := bitFirst.append (fun _ => bitSecond)

/-- The prefix decision resources. -/
abbrev firstResources := sumFamily bits (pathFamily bitFirst ⟨⟨⟩, ⟨⟩⟩)

/-- The prefix decision makes the dummy request; the prefix exports its input. -/
def bitPrefix : OracleVerifier bitAmbient bitFirst Unit (fun _ => Unit) bits (fun _ => bits) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let _ ← liftM ((bitAmbient + firstResources.spec).query (.inl false))
      pure ()
  outputMap _ p _ := OracleMap.embedding (sumFamily bits (pathFamily bitFirst p)) .inl

/-- The suffix decision resources after `guess`. -/
abbrev secondResources (guess : Bool) := sumFamily bits (pathFamily bitSecond ⟨guess, ⟨⟩⟩)

/-- Export `guess ^^ pad`, reading the pad from the exported input. -/
def xorMap (guess : Bool) : OracleMap (secondResources guess) bits where
  f x _ := guess ^^ (show Bool from x (.inl ()))
  impl _ := do
    let pad : Bool ← liftM ((secondResources guess).spec.query ⟨.inl (), ()⟩)
    pure (guess ^^ pad)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- The suffix decision reads the pad, reveals the hidden bit and claims `hidden ^^ pad`. -/
def bitSuffix : OracleVerifier bitAmbient bitSecond Unit (fun _ => Bool) bits (fun _ => bits) where
  decide _ p _ := by
    rcases p with ⟨guess, ⟨⟩⟩
    exact do
      let pad : Bool ← liftM ((bitAmbient + (secondResources guess).spec).query
        (.inr ⟨.inl (), ()⟩))
      let hidden : Bool ← liftM ((bitAmbient + (secondResources guess).spec).query (.inl true))
      pure (hidden ^^ pad)
  outputMap _ p _ := by
    rcases p with ⟨guess, ⟨⟩⟩
    exact xorMap guess

/-- The composite output map is the suffix output map after `suffixRoute`. -/
def bitCompatible : OracleVerifier.OutputCompatibility bitPrefix (fun _ => bitSuffix) where
  outputMap stmt p v :=
    (bitSuffix.outputMap () (Path.split bitFirst (fun _ => bitSecond) p).2
      (View.split bitFirst (fun _ => bitSecond) p v).2).comp
        (OracleVerifier.suffixRoute bitPrefix stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- The composed hidden-bit verifier. -/
def bitVerifier := bitPrefix.append (fun _ => bitSuffix) bitCompatible

/-- A prover that commits to `guess` without querying, keeping `secret` as private output. -/
def guessProver (guess : Bool) (secret : Nat) :
    Prover oracleSig bitAmbient bitCombined (fun _ => Nat) :=
  Prover.append (s₂ := fun _ => bitSecond) (pure fun _ => pure secret)
    (fun _ memory => pure (pure ⟨guess, pure memory⟩))

/-- A prover that reveals the hidden bit in the seam slot, between the challenge and its guess,
and sends it. -/
def informedProver (secret : Nat) : Prover oracleSig bitAmbient bitCombined (fun _ => Nat) :=
  Prover.append (s₂ := fun _ => bitSecond) (pure fun _ => pure secret)
    (fun _ memory => do
      let hidden : Bool ← liftM (bitAmbient.query true)
      pure (pure ⟨hidden, pure memory⟩))

/-- The challenge is `()`. -/
def bitChallenges : QueryImpl (challengeSpec oracleSig bitCombined) Id
  | ⟨.inl _, _⟩ => pure ()
  | ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- Setup samples the hidden bit; each ambient request increments the count. Challenges leave
the state alone. -/
abbrev bitRuntime :
    OracleRuntime coinSpec (bitAmbient + challengeSpec oracleSig bitCombined) where
  State := Bool × Nat
  setup := do
    let hidden : Bool ← liftM (coinSpec.query ())
    pure (hidden, 0)
  handler
    | .inl request => fun state =>
      pure (if request then state.1 else false, (state.1, state.2 + 1))
    | .inr c => fun state => pure (bitChallenges c, state)

/-- Charge an ambient history: 3 for a reveal, 1 for a dummy request. -/
def bitCharge (history : QueryLog bitAmbient) : Nat :=
  (history.map fun entry => if entry.1 then 3 else 1).sum

/-- The full query and challenge surface of the hidden-bit runtime. -/
abbrev bitFull := bitAmbient + challengeSpec oracleSig bitCombined

/-- The challenge query in the surface trace. -/
def challengeEntry : bitFull.Domain := .inr ⟨.inl ⟨⟩, rfl⟩

end Interaction.Core.HiddenBitFixture
