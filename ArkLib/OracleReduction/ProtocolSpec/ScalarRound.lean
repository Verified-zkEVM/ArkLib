/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.OracleReduction.ProtocolSpec.Basic

/-!
# One-message protocol specifications

The prover sends one message, optionally followed by a scalar verifier challenge.
This module defines the wires and their interfaces independently of any execution
or security definitions.
-/

@[expose] public section

namespace RingSwitching

/-- One-round wire format: the prover sends a single message `Msg`, the verifier sends no
challenge. The one-message sibling of `CoordinateWise.ScalarRound.pSpecScalar`. -/
@[reducible] def pSpecMessage (Msg : Type) : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Msg]⟩

/-- The canonical oracle interface of the one-message wire: the message is sent in the clear,
so it is read through the default interface. -/
instance {Msg : Type} : ∀ i, OracleInterface ((pSpecMessage Msg).Message i)
  | ⟨0, _⟩ => OracleInterface.instDefault

/-- The one-message wire sends no challenge, so its `Challenge` family is empty and this
`SampleableType` obligation is discharged vacuously. -/
instance {Msg : Type} : ∀ i, SampleableType ((pSpecMessage Msg).Challenge i)
  | ⟨0, h⟩ => nomatch h

end RingSwitching

namespace CoordinateWise.ScalarRound

/-- The two-round scalar-challenge protocol: the prover sends a message `Msg` (round 0,
`P_to_V`), the verifier replies with a single scalar challenge `C` (round 1, `V_to_P`). -/
@[reducible] def pSpecScalar (Msg C : Type) : ProtocolSpec 2 :=
  ⟨!v[.P_to_V, .V_to_P], !v[Msg, C]⟩

section Instances

variable {Msg C : Type} [SampleableType C] [OracleInterface Msg]

/-- Hand-written 2-round instances (not auto-derived for `ProtocolSpec 2`). -/
instance : ∀ i, SampleableType ((pSpecScalar Msg C).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => (inferInstance : SampleableType C)

/-- `OracleInterface` for each message index: round 0 carries the prover message `Msg`;
round 1 is a challenge, so it has no message. -/
instance : ∀ i, OracleInterface ((pSpecScalar Msg C).Message i)
  | ⟨0, _⟩ => (inferInstance : OracleInterface Msg)
  | ⟨1, h⟩ => nomatch h

end Instances

end CoordinateWise.ScalarRound
