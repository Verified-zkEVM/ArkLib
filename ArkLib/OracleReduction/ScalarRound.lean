/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.OracleReduction.Basic
public import ArkLib.OracleReduction.ProtocolSpec.ScalarRound
public import ArkLib.OracleReduction.Security.Guarded

/-!
# Check-then-update oracle rounds

Many verifier rounds have one skeleton: **receive a single prover message, run a
deterministic local check on it, and either abort or update the statement.** This file provides
that verifier once, generic over the statement, message, and challenge types, for the two wires
the shape occurs on:

* `pSpecMessage Msg` — the one-message wire: the prover sends one message and the verifier
  sends no challenge. `messageRoundOracleVerifier check accept` checks the message before
  updating the statement.
* `CoordinateWise.ScalarRound.pSpecScalar Msg C` — the message-then-scalar-challenge wire
  from `ProtocolSpec/ScalarRound.lean`. `scalarRoundOracleVerifier check accept`
  additionally feeds the challenge into the statement update, so the round can bind
  later work to fresh randomness. Its **check-free limit** — accept always, extend the
  statement by `(msg, challenge)`, defer every check to the output relation — is the
  statement-extending committed-scalar verifier `CoordinateWise.CommittedScalar.verifier`,
  which stays with the CWSS seam because its extractor machinery lives there.

The matching prover constructors separate the sent message and retained state from the final
statement and witness update. The retained state can cache the message when the update needs it.

Both verifiers read the message through the default oracle interface (it is an IOP message
sent in the clear) and pass the input oracle statements through unchanged. A failed check
**aborts** (`failure`): no output statement is produced, so no output relation can be met by a
rejected transcript. This is what makes the terminal knowledge-state obligation provable. The
induced plain verifiers are guarded, with guard and verdict as data in
`messageRoundOracleVerifierGuardedForm` and `scalarRoundOracleVerifierGuardedForm`. Both are
instances of the generic query-guard-return form `Verifier.GuardedForm.ofQueryGuard`; the
`…_check` and `…_out` lemmas state their guard and verdict in terms of the sent message.

The constructors apply to any statement and witness types. Binary Basefold uses them for the
fold and final sum-check steps; ring switching uses them for batching and relocation sum-check.
The existing `RingSwitching` namespace preserves the original declaration names.

## Examples

* the `Packing` batching round (`Packing/Head.lean`): `check` tests the
  incoming claim against the message's coordinate decomposition, `accept` batches the
  coordinates into the next sumcheck target;
* the `Packing` final step (`Packing/ProductSumcheck/Terminal.lean`): `check` is the closing
  consistency equation of the relocation sumcheck.

The [NOZ26] §3.1 trace head (`Commitments/Functional/Hachi/TraceHead/`) is
a deterministic one-message head of the same shape: one carrier element and one algebraic
identity. Like the shared oracle verifiers, its plain `Verifier` aborts on a failed check.

## References

* [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J. "Hachi: Efficient Lattice-Based
  Multilinear Polynomial Commitments over Extension Fields." Cryptology ePrint Archive (2026).
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec CoordinateWise.ScalarRound

namespace RingSwitching

/-! ## Prover constructors -/

section Provers

variable {ι : Type} {oSpec : OracleSpec ι} {ιₛ : Type} {OStmt : ιₛ → Type}
  {StmtIn StmtOut WitIn WitOut SentState Msg C : Type}

/-- Send a message and compute the output from the state retained by `prepare`. -/
def messageRoundOracleProver
    (prepare : (StmtIn × (∀ j, OStmt j)) × WitIn → Msg × SentState)
    (finish : SentState → (StmtOut × (∀ j, OStmt j)) × WitOut) :
    OracleProver oSpec StmtIn OStmt WitIn StmtOut OStmt WitOut (pSpecMessage Msg) where
  PrvState
    | ⟨0, _⟩ => (StmtIn × (∀ j, OStmt j)) × WitIn
    | ⟨1, _⟩ => SentState
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (prepare st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun st => pure (finish st)

/-- The one-message prover sends the prepared message and returns the update of its saved state. -/
theorem messageRoundOracleProver_run
    (prepare : (StmtIn × (∀ j, OStmt j)) × WitIn → Msg × SentState)
    (finish : SentState → (StmtOut × (∀ j, OStmt j)) × WitOut)
    (stmt : StmtIn) (ost : ∀ j, OStmt j) (witIn : WitIn) :
    (messageRoundOracleProver (oSpec := oSpec) prepare finish).run (stmt, ost) witIn =
      pure (FullTranscript.mk1 (pSpec := pSpecMessage Msg) (prepare ((stmt, ost), witIn)).1,
        finish (prepare ((stmt, ost), witIn)).2) := by
  have h0 : (pSpecMessage Msg).dir 0 = .P_to_V := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_one,
    Prover.processRound_of_dir_eq_P_to_V 0 h0, messageRoundOracleProver, id_eq,
    pure_bind, liftM_pure, FullTranscript.mk1_eq_snoc]

/-- The input, retained state, and retained state paired with the scalar challenge. -/
abbrev scalarRoundProverState (Input Sent Challenge : Type) : Fin 3 → Type
  | ⟨0, _⟩ => Input
  | ⟨1, _⟩ => Sent
  | ⟨2, _⟩ => Sent × Challenge

/-- Send a message, retain the chosen state, and update it using the received challenge. -/
def scalarRoundOracleProver
    (prepare : (StmtIn × (∀ j, OStmt j)) × WitIn → Msg × SentState)
    (finish : SentState → C → (StmtOut × (∀ j, OStmt j)) × WitOut) :
    OracleProver oSpec StmtIn OStmt WitIn StmtOut OStmt WitOut (pSpecScalar Msg C) where
  PrvState := scalarRoundProverState ((StmtIn × (∀ j, OStmt j)) × WitIn) SentState C
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (prepare st)
    | ⟨1, h⟩ => fun _ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun (st, c) => pure (finish st c)

/-- The scalar-round execution records the prepared message and the verifier's challenge,
then uses the challenge to update the retained prover state. -/
theorem scalarRoundOracleProver_run
    (prepare : (StmtIn × (∀ j, OStmt j)) × WitIn → Msg × SentState)
    (finish : SentState → C → (StmtOut × (∀ j, OStmt j)) × WitOut)
    (stmt : StmtIn) (ost : ∀ j, OStmt j) (witIn : WitIn) :
    (scalarRoundOracleProver (oSpec := oSpec) prepare finish).run (stmt, ost) witIn = (do
      let c ← liftComp ((pSpecScalar Msg C).getChallenge ⟨1, rfl⟩)
        (oSpec + [(pSpecScalar Msg C).Challenge]ₒ'challengeOracleInterface)
      let (msg, saved) := prepare ((stmt, ost), witIn)
      pure (FullTranscript.mk2 (pSpec := pSpecScalar Msg C) msg c, finish saved c)) := by
  have h0 : (pSpecScalar Msg C).dir 0 = .P_to_V := rfl
  have h1 : (pSpecScalar Msg C).dir 1 = .V_to_P := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_P_to_V 0 h0, Prover.processRound_of_dir_eq_V_to_P 1 h1,
    scalarRoundOracleProver, id_eq, pure_bind, liftM_pure, bind_assoc,
    FullTranscript.mk2_eq_snoc_snoc]
  rfl

end Provers

/-! ## The check-then-update verifiers -/

section Combinators

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
  {ιₛ : Type} {OStmt : ιₛ → Type} [∀ i, OracleInterface (OStmt i)]
  {Msg C : Type}

/-- Check-then-update verifier for the one-message round: query the message, run the
deterministic local `check`, and return the `accept` statement update on success. A failed check
aborts. Input oracle statements pass through unchanged. -/
def messageRoundOracleVerifier
    (check : StmtIn → Msg → Prop) [hcheck : ∀ s m, Decidable (check s m)]
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
    (check : StmtIn → Msg → Prop) [hcheck : ∀ s m, Decidable (check s m)]
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
