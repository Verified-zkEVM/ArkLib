/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.OracleReduction.Basic
public import ArkLib.OracleReduction.Security.Guarded
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.ScalarRound

/-!
# Check-then-update round verifiers

Many verifier rounds have one skeleton: **receive a single prover message, run a
deterministic local check on it, and either abort or update the statement.** This file provides
that verifier once, generic over the statement, message, and challenge types, for the two wires
the shape occurs on:

* `pSpecMessage Msg` — the one-message wire: the prover speaks once, the verifier sends no
  challenge. `messageRoundOracleVerifier check accept` is its check-then-update
  verifier — the whole round is one message and one algebraic equation, so a reduction of
  this shape is deterministic (zero challenges, zero soundness error at this round).
* `CoordinateWise.ScalarRound.pSpecScalar Msg C` — the message-then-scalar-challenge wire
  (defined next to the CWSS machinery built on it). `scalarRoundOracleVerifier check accept`
  additionally feeds the challenge into the statement update, so the round can bind
  later work to fresh randomness. Its **check-free limit** — accept always, extend the
  statement by `(msg, challenge)`, defer every check to the output relation — is the
  statement-extending committed-scalar verifier `CoordinateWise.CommittedScalar.verifier`,
  which stays with the CWSS seam because its extractor machinery lives there.

Both verifiers read the message through the default oracle interface (it is an IOP message
sent in the clear) and pass the input oracle statements through unchanged. A failed check
**aborts** (`failure`): no output statement is produced, so no output relation can be met by a
rejected transcript. This is what makes the terminal knowledge-state obligation provable. The
induced plain verifiers are guarded, with guard and verdict as data in
`messageRoundOracleVerifierGuardedForm` and `scalarRoundOracleVerifierGuardedForm`. Both are
instances of the generic query-guard-return form `Verifier.GuardedForm.ofQueryGuard`; the
`…_check` and `…_out` lemmas state their guard and verdict in terms of the sent message.

The verifiers mention no rings; they live in this folder rather than under `OracleReduction/`
because the check-then-update shape is what the ring-switching constructions share on the wire.

## Instances in this folder

* the `Packing` batching round (`Packing/BatchingPhase.lean`): `check` tests the
  incoming claim against the message's coordinate decomposition, `accept` batches the
  coordinates into the next sumcheck target;
* the `Packing` final step (`Packing/SumcheckPhase.lean`): `check` is the closing
  consistency equation of the relocation sumcheck;
* deterministic one-message switch heads — a single carrier element plus a single algebraic
  identity — are `messageRoundOracleVerifier` with that identity as `check` (the [NOZ26] §3
  packing head is of this shape).

## References

* [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J. "Hachi: Efficient Lattice-Based
  Multilinear Polynomial Commitments over Extension Fields." Cryptology ePrint Archive (2026).
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec CoordinateWise.ScalarRound

namespace RingSwitching

/-! ## The one-message wire format -/

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

/-! ## The check-then-update verifiers -/

section Combinators

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
  {ιₛ : Type} {OStmt : ιₛ → Type} [∀ i, OracleInterface (OStmt i)]
  {Msg C : Type}

/-- Check-then-update verifier for the one-message round: query the message, run the
deterministic local `check`, and return the `accept` statement update on success. A failed check
aborts. Input oracle statements pass through unchanged. -/
def messageRoundOracleVerifier
    (check : StmtIn → Msg → Prop) [∀ s m, Decidable (check s m)]
    (accept : StmtIn → Msg → StmtOut) :
    OracleVerifier oSpec StmtIn OStmt StmtOut OStmt (pSpecMessage Msg) where
  verify := fun stmt _ => do
    let msg : Msg ← query (spec := [(pSpecMessage Msg).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
    guard (check stmt msg)
    return accept stmt msg
  outputOracle := .inl {
    embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
    hEq := fun i => rfl
    outputInterface_heq := by
      intro i
      rfl }

/-- Check-then-update verifier for the message-then-scalar-challenge round: query the message,
run the deterministic local `check` (abort on failure), then update the statement from the
message and the scalar challenge. The check-free case `check := fun _ _ => True`,
`accept := fun s m c => (s, m, c)` is the statement-extending committed-scalar verifier shape
(`CoordinateWise.CommittedScalar.verifier`). -/
def scalarRoundOracleVerifier
    (check : StmtIn → Msg → Prop) [∀ s m, Decidable (check s m)]
    (accept : StmtIn → Msg → C → StmtOut) :
    letI : OracleInterface Msg := OracleInterface.instDefault
    OracleVerifier oSpec StmtIn OStmt StmtOut OStmt (pSpecScalar Msg C) :=
  letI : OracleInterface Msg := OracleInterface.instDefault
  { verify := fun stmt chals => do
      let msg : Msg ← query (spec := [(pSpecScalar Msg C).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
      guard (check stmt msg)
      return accept stmt msg (chals ⟨1, rfl⟩)
    outputOracle := .inl {
      embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
      hEq := fun i => rfl
      outputInterface_heq := by
        intro i
        rfl } }

/-! ## Guarded forms: the combinators abort on a failed check -/

variable (check : StmtIn → Msg → Prop) [hcheck : ∀ s m, Decidable (check s m)]

/-- The one-message verifier's guard and verdict as data: it returns the accepted statement with
the input oracle statements when the check passes on the sent message, and aborts otherwise. -/
def messageRoundOracleVerifierGuardedForm (accept : StmtIn → Msg → StmtOut) :
    (messageRoundOracleVerifier (oSpec := oSpec) (OStmt := OStmt) check
      accept).toVerifier.GuardedForm :=
  Verifier.GuardedForm.ofQueryGuard _ ⟨⟨0, rfl⟩, ()⟩ (fun s m _ => check s m)
    (hcheck := fun s m _ => hcheck s m) (fun s m _ => accept s m) (fun _ _ => rfl)

/-- The one-message verifier's guard is the check on the sent message. -/
@[simp]
theorem messageRoundOracleVerifierGuardedForm_check (accept : StmtIn → Msg → StmtOut)
    (s : StmtIn × ∀ i, OStmt i) (tr : (pSpecMessage Msg).FullTranscript) :
    (messageRoundOracleVerifierGuardedForm (oSpec := oSpec) check accept).check s tr =
      decide (check s.1 (tr.messages ⟨0, rfl⟩)) := rfl

/-- The one-message verifier's verdict is the accepted statement at the sent message, with the
input oracle statements. -/
@[simp]
theorem messageRoundOracleVerifierGuardedForm_out (accept : StmtIn → Msg → StmtOut)
    (s : StmtIn × ∀ i, OStmt i) (tr : (pSpecMessage Msg).FullTranscript) :
    (messageRoundOracleVerifierGuardedForm (oSpec := oSpec) check accept).out s tr =
      (accept s.1 (tr.messages ⟨0, rfl⟩), s.2) := rfl

/-- The scalar-round verifier's guard and verdict as data: it returns the accepted statement at the
sent message and challenge, with the input oracle statements, when the check passes on the message,
and aborts otherwise. -/
def scalarRoundOracleVerifierGuardedForm (accept : StmtIn → Msg → C → StmtOut) :
    letI : OracleInterface Msg := OracleInterface.instDefault
    (scalarRoundOracleVerifier (oSpec := oSpec) (OStmt := OStmt) check
      accept).toVerifier.GuardedForm :=
  letI : OracleInterface Msg := OracleInterface.instDefault
  Verifier.GuardedForm.ofQueryGuard _ ⟨⟨0, rfl⟩, ()⟩ (fun s m _ => check s m)
    (hcheck := fun s m _ => hcheck s m) (fun s m chals => accept s m (chals ⟨1, rfl⟩))
    (fun _ _ => rfl)

/-- The scalar-round verifier's guard is the check on the sent message. -/
@[simp]
theorem scalarRoundOracleVerifierGuardedForm_check (accept : StmtIn → Msg → C → StmtOut)
    (s : StmtIn × ∀ i, OStmt i) (tr : (pSpecScalar Msg C).FullTranscript) :
    letI : OracleInterface Msg := OracleInterface.instDefault
    (scalarRoundOracleVerifierGuardedForm (oSpec := oSpec) check accept).check s tr =
      decide (check s.1 (tr.messages ⟨0, rfl⟩)) := rfl

/-- The scalar-round verifier's verdict is the accepted statement at the sent message and
challenge, with the input oracle statements. -/
@[simp]
theorem scalarRoundOracleVerifierGuardedForm_out (accept : StmtIn → Msg → C → StmtOut)
    (s : StmtIn × ∀ i, OStmt i) (tr : (pSpecScalar Msg C).FullTranscript) :
    letI : OracleInterface Msg := OracleInterface.instDefault
    (scalarRoundOracleVerifierGuardedForm (oSpec := oSpec) check accept).out s tr =
      (accept s.1 (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩), s.2) := rfl

end Combinators

end RingSwitching
