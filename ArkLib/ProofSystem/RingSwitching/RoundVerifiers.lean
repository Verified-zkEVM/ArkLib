/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.ScalarRound

/-!
# Check-then-update round verifiers

Many verifier rounds have one skeleton: **receive a single prover message, run a
deterministic local check on it, and update the statement — one way on acceptance, another on
rejection.** This file provides that verifier once, generic over the statement, message, and
challenge types, for the two wires the shape occurs on:

* `pSpecMessage Msg` — the one-message wire: the prover speaks once, the verifier sends no
  challenge. `messageRoundOracleVerifier check accept reject` is its check-then-update
  verifier — the whole round is one message and one algebraic equation, so this wire has no
  challenge coordinates. Security still requires the appropriate relation/extractor proof.
* `CoordinateWise.ScalarRound.pSpecScalar Msg C` — the message-then-scalar-challenge wire
  (defined next to the CWSS machinery built on it). `scalarRoundOracleVerifier check accept
  reject` additionally feeds the challenge into the statement update, so the round can bind
  later work to fresh randomness. Its **check-free limit** — accept always, extend the
  statement by `(msg, challenge)`, defer every check to the output relation — is the
  statement-extending committed-scalar verifier `CoordinateWise.CommittedScalar.verifier`,
  which stays with the CWSS seam because its extractor machinery lives there.

The `guardedMessageRoundOracleVerifier` and `guardedScalarRoundOracleVerifier` variants
abort with `failure` when the local check fails. `Packing` uses these guarded variants so
rejection cannot become a valid downstream opening.

All four verifiers read the message through the default oracle interface (it is an IOP message
sent in the clear) and pass the input oracle statements through unchanged. They mention no
rings; they live in this folder rather than under `OracleReduction/` because the
check-then-update shape is what the ring-switching constructions share on the wire.

## Instances in this folder

* the `Packing` batching round (`Packing/BatchingPhase.lean`): `check` tests the
  incoming claim against the message's coordinate decomposition, `accept` batches the
  coordinates into the next sumcheck target;
* the `Packing` final step (`Packing/SumcheckPhase.lean`): `check` is the closing
  consistency equation of the relocation sumcheck;
* deterministic one-message switch heads — a single carrier element plus a single algebraic
  identity — can use `guardedMessageRoundOracleVerifier` with that identity as `check`
  (the [NOZ26] §3 packing head is of this shape).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleSpec OracleComp ProtocolSpec CoordinateWise.ScalarRound

namespace RingSwitching

/-! ## The one-message wire format -/

/-- One-round wire format: the prover sends a single message `Msg`, the verifier sends no
challenge. The one-message sibling of `CoordinateWise.ScalarRound.pSpecScalar`. -/
@[reducible] def pSpecMessage (Msg : Type) : ProtocolSpec 1 := ⟨![.P_to_V], ![Msg]⟩

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
deterministic local `check`, and return the `accept` statement update on success or the
`reject` statement on failure. Input oracle statements pass through unchanged. -/
def messageRoundOracleVerifier
    (check : StmtIn → Msg → Prop) [∀ s m, Decidable (check s m)]
    (accept : StmtIn → Msg → StmtOut) (reject : StmtIn → Msg → StmtOut) :
    OracleVerifier oSpec StmtIn OStmt StmtOut OStmt (pSpecMessage Msg) where
  verify := fun stmt _ => do
    let msg : Msg ← query (spec := [(pSpecMessage Msg).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
    unless check stmt msg do
      return reject stmt msg
    return accept stmt msg
  outputOracle := .inl {
    embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
    hEq := fun i => rfl
    outputInterface_heq := by
      intro i
      rfl }

/-- Check-then-update verifier for the message-then-scalar-challenge round: query the message,
run the deterministic local `check` (reject on failure), then update the statement from the
message and the scalar challenge. The check-free case `check := fun _ _ => True`,
`accept := fun s m c => (s, m, c)` is the statement-extending committed-scalar verifier shape
(`CoordinateWise.CommittedScalar.verifier`). -/
def scalarRoundOracleVerifier
    (check : StmtIn → Msg → Prop) [∀ s m, Decidable (check s m)]
    (accept : StmtIn → Msg → C → StmtOut) (reject : StmtIn → Msg → StmtOut) :
    letI : OracleInterface Msg := OracleInterface.instDefault
    OracleVerifier oSpec StmtIn OStmt StmtOut OStmt (pSpecScalar Msg C) :=
  letI : OracleInterface Msg := OracleInterface.instDefault
  { verify := fun stmt chals => do
      let msg : Msg ← query (spec := [(pSpecScalar Msg C).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
      unless check stmt msg do
        return reject stmt msg
      return accept stmt msg (chals ⟨1, rfl⟩)
    outputOracle := .inl {
      embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
      hEq := fun i => rfl
      outputInterface_heq := by
        intro i
        rfl } }

/-- One-message verifier whose failed local check aborts the computation. No output statement
or downstream oracle opening is produced on rejection. -/
def guardedMessageRoundOracleVerifier
    (check : StmtIn → Msg → Prop) [∀ s m, Decidable (check s m)]
    (accept : StmtIn → Msg → StmtOut) :
    OracleVerifier oSpec StmtIn OStmt StmtOut OStmt (pSpecMessage Msg) where
  verify := fun stmt _ => do
    let msg : Msg ← query (spec := [(pSpecMessage Msg).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
    if check stmt msg then return accept stmt msg else failure
  outputOracle := .inl {
    embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
    hEq := fun _ => rfl
    outputInterface_heq := by intro i; rfl }

/-- Message-then-challenge verifier with absorbing rejection on a failed local check. -/
def guardedScalarRoundOracleVerifier
    (check : StmtIn → Msg → Prop) [∀ s m, Decidable (check s m)]
    (accept : StmtIn → Msg → C → StmtOut) :
    letI : OracleInterface Msg := OracleInterface.instDefault
    OracleVerifier oSpec StmtIn OStmt StmtOut OStmt (pSpecScalar Msg C) :=
  letI : OracleInterface Msg := OracleInterface.instDefault
  { verify := fun stmt chals => do
      let msg : Msg ← query (spec := [(pSpecScalar Msg C).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
      if check stmt msg then return accept stmt msg (chals ⟨1, rfl⟩) else failure
    outputOracle := .inl {
      embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
      hEq := fun _ => rfl
      outputInterface_heq := by intro i; rfl } }

-- Keep the wire aliases transparent when matching the query simulation lemmas on Lean 4.33.
set_option backward.isDefEq.respectTransparency false in
/-- Exact execution of the guarded message round, including oracle passthrough and rejection. -/
theorem guardedMessageRoundOracleVerifier_verify
    (check : StmtIn → Msg → Prop) [∀ s m, Decidable (check s m)]
    (accept : StmtIn → Msg → StmtOut)
    (stmt : StmtIn) (oStmt : ∀ i, OStmt i) (tr : FullTranscript (pSpecMessage Msg)) :
    (guardedMessageRoundOracleVerifier (oSpec := oSpec) (OStmt := OStmt)
      check accept).toVerifier.verify (stmt, oStmt) tr =
      (if (check stmt (tr.messages ⟨0, rfl⟩)) then
        pure (accept stmt (tr.messages ⟨0, rfl⟩), oStmt) else failure) := by
  classical
  apply OptionT.ext
  have hout : (guardedMessageRoundOracleVerifier (oSpec := oSpec) (OStmt := OStmt)
      check accept).materializeOutput tr.challenges oStmt tr.messages = oStmt := by
    funext i
    rfl
  simp only [OracleVerifier.toVerifier, OptionT.run_mk]
  rw [hout]
  change (Option.map fun stmtOut => (stmtOut, oStmt)) <$>
    simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
      (do
        let msg : Msg ← query (spec := [(pSpecMessage Msg).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
        if check stmt msg then pure (accept stmt msg) else failure :
        OptionT (OracleComp (oSpec + ([OStmt]ₒ + [(pSpecMessage Msg).Message]ₒ))) StmtOut).run = _
  have hquery : simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
      (query (spec := [(pSpecMessage Msg).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩ :
        OptionT (OracleComp (oSpec + ([OStmt]ₒ + [(pSpecMessage Msg).Message]ₒ))) Msg).run =
      pure (some (tr.messages ⟨0, rfl⟩)) := by
    change simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
      (some <$> (liftM (([(pSpecMessage Msg).Message]ₒ).query ⟨⟨0, rfl⟩, ()⟩) :
        OracleComp (oSpec + ([OStmt]ₒ + [(pSpecMessage Msg).Message]ₒ)) Msg)) = _
    rw [simulateQ_map]
    have h := QueryImpl.simulateQ_addLift_add_liftM_right (target := OracleComp oSpec)
      (QueryImpl.id oSpec)
      (OracleInterface.simOracle0 OStmt oStmt)
      (OracleInterface.simOracle0 (pSpecMessage Msg).Message tr.messages)
      (([(pSpecMessage Msg).Message]ₒ).query ⟨⟨0, rfl⟩, ()⟩)
    exact (congrArg (fun x => some <$> x) h).trans rfl
  simp only [OptionT.run_bind, Option.elimM, simulateQ_bind, hquery, pure_bind,
    Option.elim_some]
  split <;> simp_all [OptionT.run_pure, OptionT.run_failure]

section ScalarExecution

local instance : OracleInterface Msg := OracleInterface.instDefault

-- Keep the wire aliases transparent when matching the query simulation lemmas on Lean 4.33.
set_option backward.isDefEq.respectTransparency false in
/-- Exact execution of the guarded scalar round, including oracle passthrough and rejection. -/
theorem guardedScalarRoundOracleVerifier_verify
    (check : StmtIn → Msg → Prop) [∀ s m, Decidable (check s m)]
    (accept : StmtIn → Msg → C → StmtOut)
    (stmt : StmtIn) (oStmt : ∀ i, OStmt i) (tr : FullTranscript (pSpecScalar Msg C)) :
    (guardedScalarRoundOracleVerifier (oSpec := oSpec) (OStmt := OStmt)
      check accept).toVerifier.verify (stmt, oStmt) tr =
      (if (check stmt (tr.messages ⟨0, rfl⟩)) then
        pure (accept stmt (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩), oStmt)
      else failure) := by
  classical
  apply OptionT.ext
  have hout : (guardedScalarRoundOracleVerifier (oSpec := oSpec) (OStmt := OStmt)
      check accept).materializeOutput tr.challenges oStmt tr.messages = oStmt := by
    funext i
    rfl
  simp only [OracleVerifier.toVerifier, OptionT.run_mk]
  rw [hout]
  change (Option.map fun stmtOut => (stmtOut, oStmt)) <$>
    simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
      (do
        let msg : Msg ← query (spec := [(pSpecScalar Msg C).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
        if check stmt msg then pure (accept stmt msg (tr.challenges ⟨1, rfl⟩)) else failure :
        OptionT (OracleComp (oSpec + ([OStmt]ₒ + [(pSpecScalar Msg C).Message]ₒ))) StmtOut).run = _
  have hquery : simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
      (query (spec := [(pSpecScalar Msg C).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩ :
        OptionT (OracleComp (oSpec + ([OStmt]ₒ + [(pSpecScalar Msg C).Message]ₒ))) Msg).run =
      pure (some (tr.messages ⟨0, rfl⟩)) := by
    change simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
      (some <$> (liftM (([(pSpecScalar Msg C).Message]ₒ).query ⟨⟨0, rfl⟩, ()⟩) :
        OracleComp (oSpec + ([OStmt]ₒ + [(pSpecScalar Msg C).Message]ₒ)) Msg)) = _
    rw [simulateQ_map]
    have h := QueryImpl.simulateQ_addLift_add_liftM_right (target := OracleComp oSpec)
      (QueryImpl.id oSpec)
      (OracleInterface.simOracle0 OStmt oStmt)
      (OracleInterface.simOracle0 (pSpecScalar Msg C).Message tr.messages)
      (([(pSpecScalar Msg C).Message]ₒ).query ⟨⟨0, rfl⟩, ()⟩)
    exact (congrArg (fun x => some <$> x) h).trans rfl
  simp only [OptionT.run_bind, Option.elimM, simulateQ_bind, hquery, pure_bind,
    Option.elim_some]
  split <;> simp_all [OptionT.run_pure, OptionT.run_failure]

end ScalarExecution

end Combinators

end RingSwitching
