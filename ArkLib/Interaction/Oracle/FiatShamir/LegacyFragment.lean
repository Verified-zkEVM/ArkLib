/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.PublicMessage
public import ArkLib.OracleReduction.ProtocolSpec.SeqCompose

/-!
# Alternating finite fragment shared with legacy Fiat–Shamir

The legacy `ProtocolSpec` records each public prover message and verifier challenge as a distinct
step. A native fixed round expands to two such steps, in that order. This module pins that common
schedule before defining data and oracle-query conversions.
-/

@[expose] public section

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- Number of individual message/challenge steps in a fixed native round schedule. -/
def legacySteps : List Round → Nat
  | [] => 0
  | _ :: rounds => legacySteps rounds + 2

/-- Exact alternating legacy schedule, with public message first and challenge second. -/
def legacySpec : (rounds : List Round) → ProtocolSpec (legacySteps rounds)
  | [] => ProtocolSpec.empty
  | round :: rounds =>
      ((legacySpec rounds).cons .V_to_P round.Challenge).cons .P_to_V round.Message

/-- A concrete native public execution path as an alternating legacy transcript. -/
def toLegacyTranscript : (rounds : List Round) →
    (publicProtocol rounds).tree.ExecutionPath → (legacySpec rounds).FullTranscript
  | [], _ => fun i => i.elim0
  | _ :: rounds, path =>
      Fin.hcons path.1 (Fin.hcons path.2.1 (toLegacyTranscript rounds path.2.2))

/-- Decode the full legacy alternating transcript back to the public native path. -/
def fromLegacyTranscript : (rounds : List Round) →
    (legacySpec rounds).FullTranscript → (publicProtocol rounds).tree.ExecutionPath
  | [], _ => PUnit.unit
  | round :: rounds, transcript =>
      let pairTranscript :
          (i : Fin ((legacySteps rounds + 1) + 1)) →
            (Fin.vcons round.Message
              (Fin.vcons round.Challenge (legacySpec rounds).Type)) i := transcript
      let challenge : round.Challenge := by
        simpa only [Fin.tail, Fin.vcons_succ, Fin.vcons_zero] using
          (Fin.tail pairTranscript) 0
      let suffix : (legacySpec rounds).FullTranscript := fun i => by
        simpa only [Fin.tail, Fin.vcons_succ] using
          (Fin.tail (Fin.tail pairTranscript)) i
      ⟨pairTranscript 0, ⟨challenge, fromLegacyTranscript rounds suffix⟩⟩

/-- The total decoder used by a legacy extractor before native backward extraction. -/
def legacyToRestorationPath (rounds : List Round)
    (transcript : (legacySpec rounds).FullTranscript) :
    (protocol rounds).tree.ExecutionPath :=
  toRestorationPath rounds (fromLegacyTranscript rounds transcript)

@[simp]
theorem legacySteps_eq (rounds : List Round) : legacySteps rounds = 2 * rounds.length := by
  induction rounds with
  | nil => rfl
  | cons round rounds ih =>
      simp only [legacySteps, List.length_cons, ih]
      omega

end Interaction.Oracle.FiatShamir
