/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù, Devon Tuma
-/
module

public import ArkLib.InteractiveProof.IP
public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Defs
public import ArkLib.NonInteractiveArgument.Serialization

/-!
# The duplex-sponge Fiat–Shamir construction

The prover samples one salt, absorbs it, and runs the rounds needed to produce the NARG string.
The verifier reconstructs the transcript using hash and forward permutation queries.
A salt length of zero requires no separate wire-format marker. The reduction compiler and
the byte-facing argument compiler use the same payload and transcript routines.

## Main definitions

* `Reduction.duplexSpongeFiatShamir` compiles a proof to a single-salt reduction.
* `InteractiveProtocol.duplexSpongeFiatShamir` compiles a protocol with proof
  `(salt, proverMessages)`.
* `InteractiveProtocol.duplexSpongeFiatShamirBytes` compiles it with byte proofs.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize U]
  [Codec pSpec U]

/-! ## Shared transcript reconstruction -/

namespace ProtocolSpec.Messages

/-- **[CO25, Construction 4.4]** Auxiliary function for deriving the transcript up to round `k` from
  the (full) prover messages, via querying the permutation oracle for the verifier messages.

  This is used to define `deriveTranscriptDSFS`. The body uses only permutation queries
  (`squeeze`, `absorb`); the return type is the narrow `duplexSpongeForwardOracle`, encoding
  [CO25, Figure 4, line 3] (`𝒱^{h,p}`) at the type level. -/
def deriveTranscriptDSFSAux {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (sponge : CanonicalDuplexSponge U)
    (messages : pSpec.Messages) (i : Fin (n + 1)) :
      OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)
        (CanonicalDuplexSponge U × pSpec.Transcript i) :=
  Fin.induction
    (pure (sponge, fun i => i.elim0))
    (fun i ih => do
      let ⟨curSponge, prevTranscript⟩ ← ih
      match hDir : pSpec.dir i with
      | .V_to_P =>
        let idx : pSpec.ChallengeIdx := ⟨i, hDir⟩
        let inst : Deserialize (pSpec.Challenge idx) (Vector U (verifierMessageSize idx)) :=
          Codec.instDeserializeChallenge idx
        let ⟨verifierMessage, newSponge⟩ ← liftM (curSponge.squeeze (verifierMessageSize idx))
        let decodedVerifierMessage : pSpec.Challenge idx :=
          inst.deserialize verifierMessage
        return (newSponge, prevTranscript.concat decodedVerifierMessage)
      | .P_to_V =>
        let idx : pSpec.MessageIdx := ⟨i, hDir⟩
        let inst : Serialize (pSpec.Message idx) (Vector U (proverMessageSize idx)) :=
          Codec.instSerializeMessage idx
        let serializedMessage : Vector U (proverMessageSize idx) :=
          inst.serialize (messages idx)
        let newSponge ← liftM (DuplexSponge.absorb curSponge serializedMessage.toList)
        return (newSponge, prevTranscript.concat (messages idx)))
    i

end ProtocolSpec.Messages

section Execution

/-- Route honest sponge operations to the permutation, whose query signature is
identical to the inverse permutation's signature. -/
@[reducible]
def dsfsForwardPermutationLift : MonadLiftT
    (OracleQuery (forwardPermutationOracle (CanonicalSpongeState U)))
    (OracleQuery (oSpec + duplexSpongeOracle StmtIn U)) where
  monadLift query := ⟨Sum.inr (Sum.inr (Sum.inl query.input)), query.cont⟩

namespace DuplexSpongeFS

/-- Infer honest sponge computation lifts to the forward slot, avoiding the identically typed
inverse slot. Enable locally with `open scoped DuplexSpongeFS`. -/
@[reducible] scoped instance forwardPermutationQueryLift : MonadLift
    (OracleQuery (forwardPermutationOracle (CanonicalSpongeState U)))
    (OracleQuery (oSpec + duplexSpongeOracle StmtIn U)) where
  monadLift query := dsfsForwardPermutationLift.monadLift query

end DuplexSpongeFS

open scoped DuplexSpongeFS

/-! ## Shared proof execution

The canonical prover absorbs prover messages immediately when a later verifier message can affect a
subsequent prover message, and stops immediately after the last prover message. The runner takes
an initialized sponge; it neither samples nor requires a salt.
-/

section SharedProofExecution

namespace DuplexSpongeFS

/-- Absorb a prover message only if a later verifier message precedes another prover message. -/
def needsNARGAbsorption (pSpec : ProtocolSpec n) (j : Fin n) : Prop :=
  ∃ k : Fin n, j < k ∧ pSpec.dir k = .V_to_P ∧
    ∃ l : pSpec.MessageIdx, k < l.1

instance (pSpec : ProtocolSpec n) (j : Fin n) :
    Decidable (needsNARGAbsorption pSpec j) :=
  inferInstanceAs (Decidable (∃ k : Fin n, j < k ∧ pSpec.dir k = .V_to_P ∧
    ∃ l : pSpec.MessageIdx, k < l.1))

end DuplexSpongeFS

open DuplexSpongeFS in
/-- Execute one step of the prefix needed to produce the NARG string. Absorption is immediate
and occurs only when a later verifier message can affect a subsequent prover message. -/
def Prover.processRoundDSFS (P : Prover oSpec StmtIn WitIn Bool Unit pSpec) (j : Fin n)
    (previousRound : OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (pSpec.MessagesUpTo j.castSucc × CanonicalDuplexSponge U × P.PrvState j.castSucc)) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (pSpec.MessagesUpTo j.succ × CanonicalDuplexSponge U × P.PrvState j.succ) := do
  let (messages, sponge, prvState) ← previousRound
  match hd : pSpec.dir j with
  | .P_to_V => do
    let (message, nextPrvState) ← P.sendMessage ⟨j, hd⟩ prvState
    let sponge ← if needsNARGAbsorption pSpec j then do
        sponge.absorb ((Codec.instSerializeMessage ⟨j, hd⟩).serialize message).toList
      else pure sponge
    return (messages.concat hd message, sponge, nextPrvState)
  | .V_to_P => do
    let receiveChallenge ← P.receiveChallenge ⟨j, hd⟩ prvState
    let (verifierMessage, sponge) ← sponge.squeeze (verifierMessageSize ⟨j, hd⟩)
    return (messages.extend hd, sponge,
      receiveChallenge ((Codec.instDeserializeChallenge ⟨j, hd⟩).deserialize verifierMessage))

/-- Execute a prover prefix in increasing round order, starting from an initialized sponge.
The prefix must end at or before the last prover message. Beyond that point, the optimized
sponge state can omit absorbed messages needed to reconstruct the verifier's transcript. -/
def Prover.runToRoundDSFS (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (i : Fin (n + 1)) (_hi : i ≤ proverMessageEnd pSpec)
    (sponge : CanonicalDuplexSponge U) (initialPrvState : P.PrvState 0) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (pSpec.MessagesUpTo i × CanonicalDuplexSponge U × P.PrvState i) :=
  Fin.induction
    (zero := pure (default, sponge, initialPrvState))
    (succ := P.processRoundDSFS) i

/-- Generate all NARG messages from an initialized sponge. The stopping boundary and
conversion from a complete prefix are internal; no terminal verifier steps are executed. -/
def Prover.runDSFS (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (sponge : CanonicalDuplexSponge U) (initialPrvState : P.PrvState 0) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U) pSpec.Messages := do
  let (messages, _sponge, _lastPrvState) ←
    P.runToRoundDSFS (proverMessageEnd pSpec) le_rfl sponge initialPrvState
  pure (MessagesUpTo.completeMessages (i := proverMessageEnd pSpec) messages
    (message_lt_proverMessageEnd pSpec))

end SharedProofExecution

/-! ## Salted construction

The prover initializes the sponge, samples and absorbs the salt, then runs the shared prefix.
The NARG string contains the salt and prover messages; the verifier reconstructs the full
transcript.
-/

section SaltedConstruction

/-- **[CO25, Construction 4.4]** Derive the full transcript from prover messages after explicitly
absorbing a public salt `τ`.

This is the transcript path for the salted Construction 4.4 surface.
-/
def ProtocolSpec.Messages.deriveTranscriptDSFS {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {δ : Nat}
    (stmtIn : StmtIn) (salt : Vector U δ) (messages : pSpec.Messages) :
    OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)
      (CanonicalDuplexSponge U × pSpec.FullTranscript) := do
  let sponge0 ← liftM (DuplexSponge.start stmtIn)
  let sponge ← liftM (DuplexSponge.absorb sponge0 salt.toList)
  ProtocolSpec.Messages.deriveTranscriptDSFSAux (pSpec := pSpec) (oSpec := oSpec) (U := U)
    sponge messages (Fin.last n)

namespace DuplexSpongeFS

/-- Reconstruct the payload's transcript before running the supplied verifier.
The caller determines whether its decision can abort. -/
def verifyWithDerivedTranscript {m : Type → Type} [Monad m]
    [MonadLiftT (OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)) m]
    {α : Type} {δ : ℕ} (stmt : StmtIn)
    (payload : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ)
    (verify : pSpec.FullTranscript → m α) : m α := do
  let (_, transcript) ← liftM (payload.2.deriveTranscriptDSFS
    (pSpec := pSpec) (oSpec := oSpec) (U := U) stmt payload.1)
  verify transcript

end DuplexSpongeFS

/-- **[CO25, Construction 4.4]** Narrow-typed salted DSFS verifier surface — [CO25, Figure 4,
line 3] (`𝒱^{h,p}`) for the salted Construction 4.4 path.

Lives at `oSpec + duplexSpongeForwardOracle StmtIn U`, omitting the inverse permutation slot
`p⁻¹` at the type level. Used by the §5.8 hybrid security games to invoke the honest verifier
without granting it syntactic access to `p⁻¹`. -/
def Verifier.duplexSpongeFiatShamirForward (δ : Nat)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeForwardOracle StmtIn U) StmtIn StmtOut where
  verify := fun stmtIn nargString =>
    DuplexSpongeFS.verifyWithDerivedTranscript (oSpec := oSpec) stmtIn (nargString 0)
      fun transcript => do
        let result ← (V.verify stmtIn transcript).run
        result.getM

/-- **[CO25, Construction 4.4]** Embed the forward-only verifier in the shared oracle
specification used by the prover and verifier. -/
def Verifier.duplexSpongeFiatShamir (δ : Nat)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeOracle StmtIn U) StmtIn StmtOut :=
  (V.duplexSpongeFiatShamirForward δ).liftOracles

/-- Initialize the sponge, sample and absorb one salt, and produce the prover's NARG payload.
A pure result conversion can package the payload with the terminal state for a reduction. -/
def Prover.generateDSFSPayload (P : Prover oSpec StmtIn WitIn Bool Unit pSpec) {δ : ℕ}
    (sampleSalt : OracleComp oSpec (Vector U δ)) (stmt : StmtIn)
    (initialPrvState : P.PrvState 0) {α : Type}
    (finish : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ → α) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U) α := do
  let initialSponge : CanonicalDuplexSponge U ← liftM (DuplexSponge.start stmt)
  let salt ← sampleSalt
  let sponge ← initialSponge.absorb salt.toList
  let messages ← P.runDSFS sponge initialPrvState
  pure (finish (salt, messages))

/-- **[CO25, Construction 4.4]** — Argument prover for an interactive proof. The final output is an
accepting claim; only the verifier decides whether the NARG string is accepted. -/
def Prover.duplexSpongeFiatShamir (δ : ℕ)
    (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) :
    NonInteractiveProver (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeOracle StmtIn U) StmtIn WitIn Bool Unit where
  PrvState
    | 0 => StmtIn × P.PrvState 0
    | 1 => Unit
  input := fun ctx => (ctx.1, P.input ctx)
  sendMessage
    | ⟨0, _⟩ => fun (stmt, initialPrvState) =>
      P.generateDSFSPayload sampleSalt stmt initialPrvState fun payload => (payload, ())
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun _lastPrvState => pure (true, ())

/-- **[CO25, Construction 4.4]** — Salted duplex-sponge transformation of an interactive proof.
The prover omits terminal work; the verifier reconstructs the full transcript. -/
def Reduction.duplexSpongeFiatShamir (δ : ℕ) (P : Proof oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) :
    NonInteractiveReduction (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeOracle StmtIn U) StmtIn WitIn Bool Unit where
  prover := P.prover.duplexSpongeFiatShamir δ sampleSalt
  verifier := P.verifier.duplexSpongeFiatShamir δ

namespace DuplexSpongeFS

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Changing the honest prover's stopping behavior does not change the compiled verifier.
The existing stateless soundness and knowledge-soundness theorems therefore apply to this
verifier directly, with the accepting output language `{true}`. -/
@[simp] theorem salted_proof_verifier_eq (δ : ℕ) (P : Proof oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) :
    (Reduction.duplexSpongeFiatShamir (U := U) δ P sampleSalt).verifier =
      P.verifier.duplexSpongeFiatShamir δ := rfl

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The compiled prover claims acceptance independently of its terminal private state. -/
@[simp] theorem salted_proof_prover_output (δ : ℕ) (P : Proof oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (lastPrvState : (Reduction.duplexSpongeFiatShamir (U := U) δ P sampleSalt).prover.PrvState
      (Fin.last 1)) :
    (Reduction.duplexSpongeFiatShamir (U := U) δ P sampleSalt).prover.output lastPrvState =
      pure (true, ()) := rfl

end DuplexSpongeFS

end SaltedConstruction

end Execution

/-! ## Application-facing construction -/

/-- Generate only the salted NARG string, using the optimized CO25 execution schedule.
The shared payload routine runs the rounds needed to produce prover messages and omits
terminal reduction output. -/
def InteractiveProver.duplexSpongeFiatShamir (δ : ℕ)
    (P : InteractiveProver oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) (stmt : StmtIn) (wit : WitIn) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :=
  P.toReductionProver.generateDSFSPayload sampleSalt stmt (P.input (stmt, wit)) id

/-- Reconstruct the salted transcript using only the permutation and instance hash. -/
def InteractiveVerifier.duplexSpongeFiatShamirForward (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec) (stmt : StmtIn)
    (nargString : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :
    OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) Bool :=
  DuplexSpongeFS.verifyWithDerivedTranscript (oSpec := oSpec) stmt nargString fun transcript =>
    liftM (V.verify stmt transcript)

/-- Widen the forward-only decision algorithm to the prover's shared oracle interface. -/
def InteractiveVerifier.duplexSpongeFiatShamir (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec) (stmt : StmtIn)
    (nargString : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U) Bool :=
  (V.duplexSpongeFiatShamirForward δ stmt nargString).liftComp _

/-- Compile an interactive protocol to a non-interactive argument with one public salt. -/
def InteractiveProtocol.duplexSpongeFiatShamir (δ : ℕ)
    (protocol : InteractiveProtocol oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) :
    NonInteractiveArgument (oSpec + duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) where
  prover := protocol.prover.duplexSpongeFiatShamir δ sampleSalt
  verifier := protocol.verifier.duplexSpongeFiatShamir δ

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The existing compiler sends exactly the protocol-facing NARG string
and a trivial local state. -/
theorem InteractiveProver.duplexSpongeFiatShamir_sendMessage (δ : ℕ)
    (P : InteractiveProver oSpec StmtIn WitIn pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) (stmt : StmtIn) (wit : WitIn) :
    (P.toReductionProver.duplexSpongeFiatShamir δ sampleSalt).sendMessage
      ⟨0, rfl⟩ (stmt, P.input (stmt, wit)) =
      (fun nargString => (nargString, ())) <$>
        P.duplexSpongeFiatShamir δ sampleSalt stmt wit := by
  simp [InteractiveProver.duplexSpongeFiatShamir, Prover.duplexSpongeFiatShamir,
    Prover.generateDSFSPayload, map_bind]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Wrapping the Boolean verifier in the reduction interface adds only `some`, not new queries. -/
theorem InteractiveVerifier.duplexSpongeFiatShamir_verify (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec) (stmt : StmtIn)
    (nargString : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :
    ((V.toReductionVerifier.duplexSpongeFiatShamir (U := U) δ).verify stmt
      (Fin.cons nargString (fun i => i.elim0))).run =
      some <$> V.duplexSpongeFiatShamir δ stmt nargString := by
  simp [Verifier.duplexSpongeFiatShamir, Verifier.liftOracles,
    Verifier.duplexSpongeFiatShamirForward, duplexSpongeFiatShamir,
    duplexSpongeFiatShamirForward, DuplexSpongeFS.verifyWithDerivedTranscript,
    toReductionVerifier, ← monadLift_liftM_OptionT,
    Option.getM]

/-- Parse before verifying with the forward-only DSFS oracle interface. -/
def InteractiveVerifier.duplexSpongeFiatShamirBytesForward (δ : ℕ)
    (V : InteractiveVerifier oSpec StmtIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ))
    (stmt : StmtIn) (bytes : DSFSNARGString) :
    OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) Bool :=
  serializer.verifyBytes (V.duplexSpongeFiatShamirForward δ stmt) bytes

/-- Compile DSFS with a serialized proof using the supplied serializer. -/
def InteractiveProtocol.duplexSpongeFiatShamirBytes (δ : ℕ)
    (protocol : InteractiveProtocol oSpec StmtIn WitIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ))
    (sampleSalt : OracleComp oSpec (Vector U δ)) :
    NonInteractiveArgument (oSpec + duplexSpongeOracle StmtIn U)
      StmtIn WitIn DSFSNARGString :=
  (protocol.duplexSpongeFiatShamir δ sampleSalt).serialize serializer

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Lifting the forward-only byte verifier gives the verifier of the serialized argument. -/
theorem InteractiveProtocol.duplexSpongeFiatShamirBytesForward_lift (δ : ℕ)
    (protocol : InteractiveProtocol oSpec StmtIn WitIn pSpec)
    (serializer : Serializer (DSFSTypedNARGString pSpec U δ))
    (sampleSalt : OracleComp oSpec (Vector U δ)) (stmt : StmtIn) (bytes : DSFSNARGString) :
    (protocol.verifier.duplexSpongeFiatShamirBytesForward δ serializer stmt bytes).liftComp
      (oSpec + duplexSpongeOracle StmtIn U) =
        (protocol.duplexSpongeFiatShamirBytes δ serializer sampleSalt).verifier stmt bytes := by
  cases h : serializer.deserialize bytes <;>
    simp [InteractiveVerifier.duplexSpongeFiatShamirBytesForward, duplexSpongeFiatShamirBytes,
      NonInteractiveArgument.serialize, Serializer.verifyBytes, duplexSpongeFiatShamir,
      InteractiveVerifier.duplexSpongeFiatShamir, h]
