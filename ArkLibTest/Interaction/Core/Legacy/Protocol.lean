/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Legacy.Protocol

/-! Acceptance examples for the legacy protocol tree and the transcript equivalence. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.TwoParty.Lens ProtocolSpec

namespace Interaction.Core.Legacy.Tests

/-- Two prover messages, two challenges, then one more message: every direction, with
consecutive rounds of the same owner. -/
def mixed : ProtocolSpec 5 := ⟨!v[.P_to_V, .P_to_V, .V_to_P, .V_to_P, .P_to_V],
  !v[Nat, Bool, Bool, Nat, Unit]⟩

example : protocol mixed =
    .liftBind (.message Nat) fun _ => .liftBind (.message Bool) fun _ =>
      .liftBind (.challenge Bool) fun _ => .liftBind (.challenge Nat) fun _ =>
        .liftBind (.message Unit) fun _ => .pure ⟨⟩ := rfl

/-- The empty protocol is a single leaf, and its only path is the empty transcript. -/
example : protocol (n := 0) !p[] = .pure ⟨⟩ := rfl

example (tr : FullTranscript (n := 0) !p[]) : (transcriptEquiv !p[]).symm tr = ⟨⟩ := rfl

/-- A runtime path through the mixed tree. -/
def mixedPath : PathAlong plainSig (protocol mixed) :=
  ⟨(3 : Nat), ⟨true, ⟨false, ⟨(7 : Nat), ⟨(), ⟨⟩⟩⟩⟩⟩⟩

example : decode mixed mixedPath 0 = (3 : Nat) := rfl
example : decode mixed mixedPath 1 = true := rfl
example : decode mixed mixedPath 2 = false := rfl
example : decode mixed mixedPath 3 = (7 : Nat) := rfl

example : (transcriptEquiv mixed).symm (decode mixed mixedPath) = mixedPath := rfl

/-- Challenge values are recorded in the transcript without changing the shape path. -/
example : projectPathAlong plainSig (protocol mixed) mixedPath =
    projectPathAlong plainSig (protocol mixed)
      ⟨(3 : Nat), ⟨true, ⟨true, ⟨(0 : Nat), ⟨(), ⟨⟩⟩⟩⟩⟩⟩ := rfl

/-- Only challenge rounds are receiver nodes. -/
example : owner plainSig (plainRound mixed 1) = .sender := rfl
example : owner plainSig (plainRound mixed 2) = .receiver := rfl

/-- A legacy message oracle interface for the oracle tree. -/
instance mixedOracles : ∀ i, OracleInterface.{0, 0} (mixed.Message i) := fun _ =>
  { Query := Unit, toOC := { spec := Unit →ₒ Unit, impl := fun _ => pure () } }

example : oracleProtocol mixed =
    .liftBind (.oracle Nat (mixedOracles ⟨0, rfl⟩)) fun _ =>
      .liftBind (.oracle Bool (mixedOracles ⟨1, rfl⟩))
        fun _ => .liftBind (.challenge Bool) fun _ => .liftBind (.challenge Nat) fun _ =>
          .liftBind (.oracle Unit (mixedOracles ⟨4, rfl⟩))
            fun _ => .pure ⟨⟩ := rfl

example : oracleDecode mixed ⟨(3 : Nat), ⟨true, ⟨false, ⟨(7 : Nat), ⟨(), ⟨⟩⟩⟩⟩⟩⟩ =
    decode mixed mixedPath := rfl

end Interaction.Core.Legacy.Tests
