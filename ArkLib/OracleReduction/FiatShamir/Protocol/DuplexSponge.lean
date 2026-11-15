/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.Protocol.Serialization
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Duplex-sponge Fiat–Shamir for interactive protocols

The public compiler returns a canonical byte NARG string and an acceptance bit.
The `Payload` algorithms retain the structured salt/message tuple for the internal security games.
It reuses the existing optimized DSFS runner: initialize from the statement, sample and absorb
one salt using private ambient randomness, and stop after producing the last prover message.
The verifier reconstructs the entire transcript, including any terminal verifier messages.

The payload correspondence lemmas identify the oracle computations with the existing reduction
compiler. The byte boundary serializes generation and rejects invalid inputs before verification,
without running or exposing a terminal reduction output. Uniform salt sampling and
the other security hypotheses remain obligations of the corresponding security experiments.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [Codec pSpec U]

/-- Generate only the salted NARG string, using the optimized CO25 execution schedule.
Delegating to the existing message algorithm preserves its initialization, salt sampling, and
permutation query routing exactly. Its terminal reduction output is never executed. -/
def InteractiveProver.duplexSpongeFiatShamirPayload (δ : ℕ)
    (P : InteractiveProver oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) (stmt : StmtIn) (wit : WitIn) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :=
  Prod.fst <$> (P.toReductionProver.duplexSpongeFiatShamir δ sampleSalt).sendMessage
    ⟨0, rfl⟩ (stmt, P.input (stmt, wit))

/-- Reconstruct the salted transcript using only the permutation and instance hash. -/
def InteractiveVerifier.duplexSpongeFiatShamirPayloadForward (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec) (stmt : StmtIn)
    (nargString : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :
    OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) Bool := do
  let (_, transcript) ← nargString.2.deriveTranscriptDSFS
    (pSpec := pSpec) (oSpec := oSpec) (U := U) stmt nargString.1
  V.verify stmt transcript

/-- Widen the forward-only decision algorithm to the prover's shared oracle interface. -/
def InteractiveVerifier.duplexSpongeFiatShamirPayload (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec) (stmt : StmtIn)
    (nargString : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U) Bool :=
  (V.duplexSpongeFiatShamirPayloadForward δ stmt nargString).liftComp _

/-- Compile an interactive protocol to a non-interactive argument with one public salt. -/
def InteractiveProtocol.duplexSpongeFiatShamirPayload (δ : ℕ)
    (protocol : InteractiveProtocol oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) :
    NonInteractiveArgument (oSpec + duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) where
  prover := protocol.prover.duplexSpongeFiatShamirPayload δ sampleSalt
  verifier := protocol.verifier.duplexSpongeFiatShamirPayload δ

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The existing compiler sends exactly the protocol-facing NARG string
and a trivial local state. -/
theorem InteractiveProver.duplexSpongeFiatShamirPayload_sendMessage (δ : ℕ)
    (P : InteractiveProver oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) (stmt : StmtIn) (wit : WitIn) :
    (P.toReductionProver.duplexSpongeFiatShamir δ sampleSalt).sendMessage
      ⟨0, rfl⟩ (stmt, P.input (stmt, wit)) =
      (fun nargString => (nargString, ())) <$>
        P.duplexSpongeFiatShamirPayload δ sampleSalt stmt wit := by
  simp [InteractiveProver.duplexSpongeFiatShamirPayload, Prover.duplexSpongeFiatShamir,
    Functor.map_map]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Wrapping the Boolean verifier in the reduction interface adds only `some`, not new queries. -/
theorem InteractiveVerifier.duplexSpongeFiatShamirPayload_verify (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec) (stmt : StmtIn)
    (nargString : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :
    ((V.toReductionVerifier.duplexSpongeFiatShamir (U := U) δ).verify stmt
      (Fin.cons nargString (fun i => i.elim0))).run =
      some <$> V.duplexSpongeFiatShamirPayload δ stmt nargString := by
  simp only [Nat.reduceAdd, Fin.vcons_fin_zero, Verifier.duplexSpongeFiatShamir,
    Fin.isValue, ← monadLift_liftM_OptionT, toReductionVerifier, OptionT.run_lift,
    bind_pure_comp, liftM_map, Option.getM, bind_map_left, bind_pure, Fin.cons_zero,
    OptionT.run_bind, OptionT.run_monadLift, monadLift_self, Option.elimM_map,
    Option.elim_some, duplexSpongeFiatShamirPayload, duplexSpongeFiatShamirPayloadForward,
    liftComp_eq_liftM, liftM_bind, map_bind]
  apply bind_congr
  intro t
  induction (V.verify stmt t.2) using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind q k ih =>
    simp only [liftM_bind, map_bind]
    apply bind_congr
    exact ih

/-- Generate the public byte-serialized DSFS NARG string. The serializer is independent of the
sponge alphabet and must enforce every validity condition of the payload type. -/
def InteractiveProver.duplexSpongeFiatShamir (δ : ℕ)
    (P : InteractiveProver oSpec StmtIn WitIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ))
    (sampleSalt : OracleComp oSpec (Vector U δ)) (stmt : StmtIn) (wit : WitIn) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U) DSFSNARGString :=
  serializer.serialize <$> P.duplexSpongeFiatShamirPayload δ sampleSalt stmt wit

/-- Parse the entire byte string before running the forward-only DSFS verifier.
Invalid, noncanonical, and trailing-byte inputs reject without oracle queries. -/
def InteractiveVerifier.duplexSpongeFiatShamirForward (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ))
    (stmt : StmtIn) (bytes : DSFSNARGString) :
    OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) Bool :=
  match serializer.deserialize bytes with
  | none => pure false
  | some payload => V.duplexSpongeFiatShamirPayloadForward δ stmt payload

/-- Byte-facing DSFS verification with the shared prover/verifier oracle interface. -/
def InteractiveVerifier.duplexSpongeFiatShamir (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ))
    (stmt : StmtIn) (bytes : DSFSNARGString) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U) Bool :=
  match serializer.deserialize bytes with
  | none => pure false
  | some payload => V.duplexSpongeFiatShamirPayload δ stmt payload

/-- Compile DSFS with canonical bytes as its public NARG string format. -/
def InteractiveProtocol.duplexSpongeFiatShamir (δ : ℕ)
    (protocol : InteractiveProtocol oSpec StmtIn WitIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ))
    (sampleSalt : OracleComp oSpec (Vector U δ)) :
    NonInteractiveArgument (oSpec + duplexSpongeOracle StmtIn U)
      StmtIn WitIn DSFSNARGString :=
  (protocol.duplexSpongeFiatShamirPayload δ sampleSalt).serialize serializer

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The byte-facing verifier runs the original verifier exactly on a valid encoding. -/
@[simp] theorem InteractiveVerifier.duplexSpongeFiatShamir_serialize (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ))
    (stmt : StmtIn) (payload : DSFSTypedNARGString pSpec U δ) :
    V.duplexSpongeFiatShamir δ serializer stmt (serializer.serialize payload) =
      V.duplexSpongeFiatShamirPayload δ stmt payload := by
  simp [duplexSpongeFiatShamir, serializer.deserialize_serialize]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Appended bytes cause rejection, even when the unextended NARG string would be accepted. -/
theorem InteractiveVerifier.duplexSpongeFiatShamir_append (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ))
    (stmt : StmtIn) (payload : DSFSTypedNARGString pSpec U δ)
    (suffix : ByteArray) (h : suffix.size ≠ 0) :
    V.duplexSpongeFiatShamir δ serializer stmt (serializer.serialize payload ++ suffix) =
      pure false := by
  simp [duplexSpongeFiatShamir, serializer.deserialize_append_eq_none payload suffix h]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Byte serialization preserves the entire honest DSFS execution. -/
@[simp] theorem InteractiveProtocol.duplexSpongeFiatShamir_run (δ : ℕ)
    (protocol : InteractiveProtocol oSpec StmtIn WitIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ))
    (sampleSalt : OracleComp oSpec (Vector U δ)) (stmt : StmtIn) (wit : WitIn) :
    (protocol.duplexSpongeFiatShamir δ serializer sampleSalt).run stmt wit =
      (protocol.duplexSpongeFiatShamirPayload δ sampleSalt).run stmt wit := by
  simp [duplexSpongeFiatShamir]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Every byte string outside the image of serialization rejects before any oracle query. -/
theorem InteractiveVerifier.duplexSpongeFiatShamir_reject (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ)) (stmt : StmtIn)
    (bytes : DSFSNARGString) (h : ∀ payload, serializer.serialize payload ≠ bytes) :
    V.duplexSpongeFiatShamir δ serializer stmt bytes = pure false := by
  simp [duplexSpongeFiatShamir, (serializer.deserialize_eq_none_iff bytes).mpr h]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Narrow byte verification and wide byte verification agree on all inputs, including failures. -/
theorem InteractiveVerifier.duplexSpongeFiatShamirForward_lift (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ))
    (stmt : StmtIn) (bytes : DSFSNARGString) :
    (V.duplexSpongeFiatShamirForward δ serializer stmt bytes).liftComp
      (oSpec + duplexSpongeOracle StmtIn U) =
        V.duplexSpongeFiatShamir δ serializer stmt bytes := by
  cases h : serializer.deserialize bytes <;>
    simp [duplexSpongeFiatShamirForward, duplexSpongeFiatShamir,
      duplexSpongeFiatShamirPayload, h]
