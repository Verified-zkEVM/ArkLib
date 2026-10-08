/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.PublicMessage
public import ArkLib.Interaction.Oracle.Security.StateRestorationStopped
public import ArkLib.Interaction.Oracle.Execution

/-!
# Public native stopped verifier for full-prefix Fiat–Shamir

The message node is genuinely public. After the prover sends it, a pure prefix guard selects
either termination or a verifier challenge node. The latter queries the typed full-prefix key
before continuing. The ordinary native strategy executor therefore performs no hash query at a
rejected round and never executes the suffix after rejection.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- Public protocol whose tree itself terminates at the first failed prefix guard. -/
def guardedPublicProtocol {Input : Type} : (rounds : List Round) →
    GuardSchedule Input PUnit rounds → Input → Protocol
  | [], _, _ => .done
  | round :: rounds, (guard, next), z =>
      .public .sender round.Message fun message =>
        match guard z message PUnit.unit with
        | false => .done
        | true => .public .receiver round.Challenge fun challenge =>
            guardedPublicProtocol rounds (next message PUnit.unit challenge) z

/-- The continuation chosen after observing one public message and its guard result. -/
def publicRest {Input : Type} (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule Input PUnit rounds)
    (z : Input) (message : round.Message) : Bool → Protocol
  | false => .done
  | true => .public .receiver round.Challenge fun challenge =>
      guardedPublicProtocol rounds (next message PUnit.unit challenge) z

/-- A selected public proof sends its next message at each reached sender node. -/
def scriptedPublicProver {Input : Type} {ι : Type} (ambient : OracleSpec ι) :
    (rounds : List Round) → (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    PublicMessages rounds →
    Prover.Strategy ambient (guardedPublicProtocol rounds guards z).tree
      (guardedPublicProtocol rounds guards z).roles (fun _ => Unit)
  | [], _, _, _ => ()
  | round :: rounds, (guard, next), z, (message, messages) =>
      let rest := publicRest round rounds next z message
      let after : (pass : Bool) →
          Prover.Strategy ambient (rest pass).tree (rest pass).roles (fun _ => Unit)
        | false => ()
        | true => fun challenge => pure (scriptedPublicProver ambient rounds
            (next message PUnit.unit challenge) z messages)
      pure ⟨message, after (guard z message PUnit.unit)⟩

/-- Hash the full-prefix key only after the current public message has passed its guard. -/
def guardedPublicVerifier {Input : Type} {allRounds : List Round} :
    (rounds : List Round) → (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    Verifier.Strategy (oracleSpec Input PUnit allRounds)
      (guardedPublicProtocol rounds guards z).tree
      (guardedPublicProtocol rounds guards z).roles
      (guardedPublicProtocol rounds guards z).oracles 0 (fun _ => Unit)
  | [], _, _, _, _ => pure ()
  | round :: rounds, (guard, next), z, embed, preserve => fun message =>
      let rest := publicRest round rounds next z message
      let after : (pass : Bool) → OracleComp (oracleSpec Input PUnit allRounds + ofPFunctor 0)
        (Verifier.Strategy (oracleSpec Input PUnit allRounds)
          (rest pass).tree (rest pass).roles (rest pass).oracles 0 (fun _ => Unit))
        | true => pure (do
          let response ← liftM
            ((oracleSpec Input PUnit allRounds + ofPFunctor 0).query
              (.inl (embed (Key.here z message PUnit.unit))))
          let challenge : round.Challenge :=
            cast (preserve (Key.here z message PUnit.unit)) response
          pure ⟨challenge,
            guardedPublicVerifier rounds (next message PUnit.unit challenge) z
              (fun key => embed (Key.later message PUnit.unit key))
              (fun key => preserve (Key.later message PUnit.unit key))⟩)
        | false => pure (pure ())
      after (guard z message PUnit.unit)

/-- The actual native strategy execution of one selected public proof. -/
def publicStoppedExecution {Input : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : PublicMessages rounds) :=
  executeStrategies (oracleSpec Input PUnit rounds)
    (guardedPublicProtocol rounds guards z).tree
    (guardedPublicProtocol rounds guards z).roles
    (guardedPublicProtocol rounds guards z).oracles 0
    (fun q => nomatch q)
    (scriptedPublicProver (oracleSpec Input PUnit rounds) rounds guards z messages)
    (guardedPublicVerifier rounds guards z id (fun _ => rfl))

/-- Decode an accepted round using a continuation decoder for the remaining rounds. -/
def decodeAfterGuard {Input : Type} (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule Input PUnit rounds)
    (z : Input) (message : round.Message)
    (decodeTail : (challenge : round.Challenge) →
      (guardedPublicProtocol rounds (next message PUnit.unit challenge) z).tree.ExecutionPath →
        Option (protocol rounds).tree.ExecutionPath) :
    (pass : Bool) → (publicRest round rounds next z message pass).tree.ExecutionPath →
      Option (protocol (round :: rounds)).tree.ExecutionPath
  | false, _ => none
  | true, suffix =>
      (decodeTail suffix.1 suffix.2).map (fun tail => ⟨message, suffix.1, tail⟩)

/-- A reached public path yields a full restoration transcript exactly on acceptance. -/
def acceptedPath {Input : Type} : (rounds : List Round) →
    (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    (guardedPublicProtocol rounds guards z).tree.ExecutionPath →
      Option (protocol rounds).tree.ExecutionPath
  | [], _, _, _ => some PUnit.unit
  | round :: rounds, (guard, next), z, path =>
      decodeAfterGuard round rounds next z path.1
        (fun challenge suffix => acceptedPath rounds
          (next path.1 PUnit.unit challenge) z suffix)
        (guard z path.1 PUnit.unit) path.2

/-- Public stopped verification exposes acceptance together with the full concrete transcript. -/
def publicStoppedVerify {Input : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : PublicMessages rounds) :
    OracleComp (oracleSpec Input PUnit rounds)
      (Option (protocol rounds).tree.ExecutionPath) :=
  (fun result => acceptedPath rounds guards z result.1) <$>
    publicStoppedExecution rounds guards z messages

/-- Route a stopped completion through a fibre-preserving embedding into a larger key domain. -/
def mappedStoppedComplete {Input : Type} {allRounds : List Round} :
    (rounds : List Round) → (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    PublicMessages rounds →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    OracleComp (oracleSpec Input PUnit allRounds)
      (Option (protocol rounds).tree.ExecutionPath)
  | [], _, _, _, _, _ => pure (some PUnit.unit)
  | round :: rounds, (guard, next), z, (message, messages), embed, preserve => do
      if !guard z message PUnit.unit then
        return none
      let response ← liftM ((oracleSpec Input PUnit allRounds).query
        (embed (Key.here z message PUnit.unit)))
      let challenge : round.Challenge := cast (preserve (Key.here z message PUnit.unit)) response
      let suffix ← mappedStoppedComplete rounds (next message PUnit.unit challenge) z
        messages (fun key => embed (Key.later message PUnit.unit key))
        (fun key => preserve (Key.later message PUnit.unit key))
      return suffix.map fun tail => ⟨message, challenge, tail⟩

/-- The same public native executor, with its keys embedded in an enclosing prefix domain. -/
def publicStoppedVerifyWith {Input : Type} {allRounds : List Round}
    (rounds : List Round) (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : PublicMessages rounds)
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    OracleComp (oracleSpec Input PUnit allRounds)
      (Option (protocol rounds).tree.ExecutionPath) :=
  (fun result => acceptedPath rounds guards z result.1) <$>
    executeStrategies (oracleSpec Input PUnit allRounds)
      (guardedPublicProtocol rounds guards z).tree
      (guardedPublicProtocol rounds guards z).roles
      (guardedPublicProtocol rounds guards z).oracles 0
      (fun q => nomatch q)
      (scriptedPublicProver (oracleSpec Input PUnit allRounds) rounds guards z messages)
      (guardedPublicVerifier rounds guards z embed preserve)

theorem publicStoppedVerify_eq_with {Input : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : PublicMessages rounds) :
    publicStoppedVerify rounds guards z messages =
    publicStoppedVerifyWith rounds guards z messages id (fun _ => rfl) := rfl

end Interaction.Oracle.FiatShamir
