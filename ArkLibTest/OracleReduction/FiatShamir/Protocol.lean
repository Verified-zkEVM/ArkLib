/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

import ArkLib.OracleReduction.FiatShamir.Protocol.Canonical
import ArkLib.OracleReduction.FiatShamir.Protocol.DuplexSponge

/-!
# Fiat–Shamir protocol interface regressions

The protocol has no reduction output algorithm. Its NARG string consists of salt metadata
and prover messages, and its verifier decides acceptance. A response depending on the verifier
message exercises both execution paths.
-/

open OracleComp OracleSpec ProtocolSpec

namespace FiatShamirProtocolRegression

instance : VCVCompatible Bool where
  default := false

abbrev ambient : OracleSpec Unit := fun _ => Bool

abbrev verifierMessageResponse : ProtocolSpec 2 :=
  ⟨fun i => if i.val = 0 then .V_to_P else .P_to_V, fun _ => Bool⟩

/-- The witness masks the response to the public verifier message. -/
def prover : InteractiveProver ambient Bool Bool verifierMessageResponse where
  PrvState := fun _ => Bool
  input := Prod.snd
  sendMessage := fun _ state => pure (state, state)
  receiveChallenge := fun _ witness => pure (fun verifierMessage => xor witness verifierMessage)

/-- Accept precisely when the response equals the reconstructed verifier message. -/
def verifier : InteractiveVerifier ambient Bool verifierMessageResponse where
  verify := fun _ transcript => pure (transcript 0 == transcript 1)

def protocol : InteractiveProtocol ambient Bool Bool verifierMessageResponse :=
  ⟨prover, verifier⟩

def compiled := protocol.fiatShamirTyped (U := Bool) 0 (pure #v[])

/-- The statement selects the deterministic verifier message for this test oracle. -/
def verifierMessageImpl : QueryImpl (canonicalFSOracle Bool verifierMessageResponse Bool 0) Id :=
  fun query => pure query.2.1.1

def testImpl : QueryImpl (ambient + canonicalFSOracle Bool verifierMessageResponse Bool 0) Id :=
  ((fun _ => pure false) : QueryImpl ambient Id) + verifierMessageImpl

def run {α : Type}
    (comp : OracleComp (ambient + canonicalFSOracle Bool verifierMessageResponse Bool 0) α) : α :=
  Id.run (simulateQ testImpl comp)

/-- Honest responses are accepted for either oracle verifier message. -/
example : run (compiled.run false false) = true := by decide

example : run (compiled.run true false) = true := by decide

/-- Flipping the witness flips the response and is rejected. -/
example : run (compiled.run true true) = false := by decide

/-- A forged response is checked against the verifier message reconstructed from the statement. -/
example : run (compiled.verifier true (#v[], fun _ => false)) = false := by decide

/-- The sole prover message is the response, which depends on the verifier message. -/
example : run (do
    let nargString ← compiled.prover true false
    return nargString.2 ⟨1, rfl⟩) = true := by decide

/-- An old reduction prover whose terminal output performs an ambient query. -/
def reductionProver : Prover ambient Bool Bool Bool Bool verifierMessageResponse where
  toProverRound := prover.toProverRound
  input := prover.input
  output := fun state => do return (← query (spec := ambient) (), state)

/-- Forgetting terminal output leaves exactly the protocol's original NARG-string computation.
This is equality before simulation, so the discarded query cannot be hidden by an oracle reply. -/
example (stmt witness : Bool) :
    reductionProver.toInteractiveProver.fiatShamirTyped (U := Bool) 0 (pure #v[]) stmt witness =
      prover.fiatShamirTyped (U := Bool) 0 (pure #v[]) stmt witness := rfl

/-- A reduction verifier may abort instead of returning a Boolean value. -/
def abortingVerifier : Verifier ambient Bool Bool verifierMessageResponse :=
  ⟨fun _ _ => failure⟩

def acceptingVerifier : Verifier ambient Bool Bool verifierMessageResponse :=
  ⟨fun _ _ => pure true⟩

def rejectingVerifier : Verifier ambient Bool Bool verifierMessageResponse :=
  ⟨fun _ _ => pure false⟩

/-- The adapter turns abort into an ordinary rejection bit. -/
example (stmt : Bool) (transcript : verifierMessageResponse.FullTranscript) :
    abortingVerifier.toInteractiveVerifier.verify stmt transcript = pure false := by
  rfl

/-- Successful decisions preserve both acceptance and rejection. -/
example (stmt : Bool) (transcript : verifierMessageResponse.FullTranscript) :
    acceptingVerifier.toInteractiveVerifier.verify stmt transcript = pure true := by
  rfl

example (stmt : Bool) (transcript : verifierMessageResponse.FullTranscript) :
    rejectingVerifier.toInteractiveVerifier.verify stmt transcript = pure false := by
  rfl


end FiatShamirProtocolRegression
