/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Michele Orrù, Yuxi Zheng
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.OracleReduction.Security.OracleSampling
public import ArkLib.InteractiveProof.IP
public import ArkLib.NonInteractiveArgument.Serialization
public import ToMathlib.Control.OptionT

/-!
# Canonical Fiat–Shamir construction

The unsalted and single-salt transforms use the same compiler for proof generation and
transcript reconstruction. The unsalted specialization uses a pure unit sampler and keys
verifier-message queries by the statement and preceding prover messages. The single-salt
transform samples once using the ambient oracle, carries the salt in the proof, and keys
queries by the statement, salt, and preceding prover messages. The application statement,
witness, and interactive messages keep their original types. The reduction and application
compilers share proof generation and transcript reconstruction.

The public `fiatShamirSalted` constructors use `Vector U saltLength`. Length zero is the same
construction with an empty salt. The abstract-salt compiler supports the encodings used in the
security reductions.

## Main definitions

* `Reduction.fiatShamir` compiles a reduction with statement-keyed oracle queries.
* `Reduction.fiatShamirSalted` compiles a reduction with one salt of the configured length.
* `InteractiveProtocol.compileFiatShamir` compiles a protocol with proof `(salt, proverMessages)`.
* `InteractiveProtocol.compileFiatShamirBytes` uses a serializer to compile it with byte proofs.
* `InteractiveProver.compileFiatShamirBytes` and `InteractiveVerifier.compileFiatShamirBytes`
  provide the byte algorithms individually.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

/-! ## State lifts for oracle simulation -/

section ProductState

universe u v

variable {σ τ : Type u} {m : Type u → Type v} [Monad m]

variable {n : ℕ} in
/-- Traverse a dependent function indexed by `Fin n` in any monad. -/
def Fin.traverseM {β : Fin n → Type u}
    (f : (i : Fin n) → m (β i)) : m ((i : Fin n) → β i) :=
  let rec aux (k : ℕ) (h : k ≤ n) : m ((i : Fin k) → β (Fin.castLE h i)) :=
    match k with
    | 0 => pure (fun i => i.elim0)
    | k' + 1 => do
      let tail ← aux k' (Nat.le_of_succ_le h)
      let head ← f (Fin.castLE h (Fin.last k'))
      return (Fin.snoc tail head)
  aux n (le_refl n)

instance : MonadLift (StateT σ m) (StateT (σ × τ) m) where
  monadLift := fun x st => do let y ← x st.1; return (y.1, y.2, st.2)

instance : MonadLift (StateT τ m) (StateT (σ × τ) m) where
  monadLift := fun x st => do let y ← x st.2; return (y.1, st.1, y.2)

instance [LawfulMonad m] : LawfulMonadLift (StateT σ m) (StateT (σ × τ) m) where
  monadLift_pure a := by
    funext st
    change (do let y ← (pure (a, st.1) : m _); pure (y.1, y.2, st.2)) = pure (a, st)
    simp only [pure_bind]
  monadLift_bind x f := by
    funext st
    change (do
      let y ← (do let z ← x st.1; f z.1 z.2)
      pure (y.1, y.2, st.2)) = (do
        let z ← (do let y ← x st.1; pure (y.1, y.2, st.2))
        let y ← f z.1 z.2.1
        pure (y.1, y.2, z.2.2))
    simp only [bind_assoc, pure_bind]

/-- Lifting the first state component leaves the second component unchanged. -/
lemma StateT.run_liftLeft {α : Type u} (x : StateT σ m α) (s : σ) (t : τ) :
    (liftM x : StateT (σ × τ) m α).run (s, t) = (do
      let (a, s') ← x.run s
      pure (a, s', t)) := rfl

end ProductState

open ProtocolSpec OracleComp OracleSpec OracleReduction

open scoped BigOperators

section ReductionCompilers

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

/-! ## Shared execution keyed by oracle context -/

/-- Execute one Fiat–Shamir round, accumulating prover messages and retaining the oracle context. -/
@[inline, specialize]
def Prover.processRoundFS {Context : Type} (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + fsVerifierMessageOracle Context pSpec)
      (pSpec.MessagesUpTo j.castSucc × Context × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + fsVerifierMessageOracle Context pSpec)
        (pSpec.MessagesUpTo j.succ × Context × prover.PrvState j.succ) := do
  let ⟨messages, context, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let f ← prover.receiveChallenge ⟨j, hDir⟩ state
    let challenge ← query (spec := fsVerifierMessageOracle Context pSpec)
      ⟨⟨j, hDir⟩, ⟨context, messages⟩⟩
    return ⟨messages.extend hDir, context, f challenge⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨messages.concat hDir msg, context, newState⟩

/-- Execute the first `i` rounds from an initialized prover state and a fixed oracle context. -/
@[inline, specialize]
def Prover.runToRoundFS {Context : Type} (i : Fin (n + 1))
    (context : Context) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + fsVerifierMessageOracle Context pSpec)
          (pSpec.MessagesUpTo i × Context × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, context, state⟩)
    prover.processRoundFS
    i

/-- Sample once, run the prover at the resulting oracle context, and package the messages. -/
@[inline, reducible]
def CanonicalFS.compileProof {Input Context Salt ProofMessage : Type}
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) (oracleContext : Input → Salt → Context)
    (pack : Salt → pSpec.Messages → ProofMessage) (input : Input) (state : P.PrvState 0) :
    OracleComp (oSpec + fsVerifierMessageOracle Context pSpec)
      (ProofMessage × P.PrvState (Fin.last n)) := do
  let salt ← sampleSalt
  let ⟨messages, _, state⟩ ← P.runToRoundFS (Fin.last n) (oracleContext input salt) state
  return ⟨pack salt messages.toMessages, state⟩

/-- Compile a prover using the supplied initial input, oracle context, and proof format. -/
def Prover.compileFiatShamirWith {Input Context Salt ProofMessage : Type}
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (prepare : StmtIn → Input) (sampleSalt : OracleComp oSpec Salt)
    (oracleContext : Input → Salt → Context) (pack : Salt → pSpec.Messages → ProofMessage) :
    NonInteractiveProver ProofMessage (oSpec + fsVerifierMessageOracle Context pSpec)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => Input × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨prepare ctx.1, P.input ctx⟩
  sendMessage | ⟨0, _⟩ => fun ⟨input, state⟩ =>
    CanonicalFS.compileProof P sampleSalt oracleContext pack input state
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/-- Compile with a deterministic oracle context and a proof containing just the prover messages. -/
def Prover.fiatShamirWithContext {Context : Type}
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (oracleContext : StmtIn → Context) :
    NonInteractiveProver pSpec.Messages (oSpec + fsVerifierMessageOracle Context pSpec)
      StmtIn WitIn StmtOut WitOut :=
  P.compileFiatShamirWith oracleContext (pure ()) (fun context _ => context)
    (fun _ messages => messages)

/-- Reconstruct the transcript at the oracle context, then verify the original statement. -/
def Verifier.verifyFiatShamir {Context : Type}
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmt : StmtIn) (context : Context)
    (messages : pSpec.Messages) :
    OptionT (OracleComp (oSpec + fsVerifierMessageOracle Context pSpec)) StmtOut := do
  let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) context
  Option.getM (← (V.verify stmt transcript).run)

/-- Compile a reduction with a supplied oracle context for each statement. -/
def Reduction.fiatShamirWithContext {Context : Type}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (oracleContext : StmtIn → Context) :
    NonInteractiveReduction pSpec.Messages (oSpec + fsVerifierMessageOracle Context pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.fiatShamirWithContext oracleContext
  verifier := {
    verify := fun stmt proof => R.verifier.verifyFiatShamir stmt (oracleContext stmt) (proof 0) }

/-! ## Unsalted Fiat–Shamir -/

/-- Basic Fiat–Shamir for a reduction, keyed by the input statement. -/
def Reduction.fiatShamir (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction pSpec.Messages (oSpec + fsVerifierMessageOracle StmtIn pSpec)
      StmtIn WitIn StmtOut WitOut :=
  R.fiatShamirWithContext id

/-! ## Single-salt Fiat–Shamir -/

/--
Canonical Fiat-Shamir NARG string: pair of a public salt and the prover's messages.
-/
abbrev FSSaltedNARGString (pSpec : ProtocolSpec n) (Salt : Type) :=
  Salt × pSpec.Messages

/-- Sample the salt and run the rounds once, returning the argument and final prover state. -/
@[inline, reducible]
def CanonicalFS.compilePayload {Salt : Type} [VCVCompatible Salt]
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : StmtIn) (state : P.PrvState 0) :
    OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)
      (FSSaltedNARGString pSpec Salt × P.PrvState (Fin.last n)) :=
  CanonicalFS.compileProof P sampleSalt Prod.mk Prod.mk stmt state

/--
Canonical Fiat-Shamir transformation for the prover ([CO25, Construction 3.17] prover surface).

The prover samples a salt `τ ← sampleSalt` using only the ambient oracle `oSpec`, then runs the
underlying interactive prover with all FS queries keyed by the context `(stmtIn, τ)`,
and packages the salt together with the produced messages as the NARG string. The sampler
cannot inspect the statement, witness-bearing prover state, or Fiat–Shamir table.

Adapted from **[snarg-book, Construction 14.1.1]**, which salts every round; here a single salt
is sampled once and keys all rounds.
-/
def Prover.compileFiatShamir {Salt : Type} [VCVCompatible Salt]
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) :
    NonInteractiveProver (Message := FSSaltedNARGString pSpec Salt)
      (oSpec := oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)
      StmtIn WitIn StmtOut WitOut :=
  P.compileFiatShamirWith id sampleSalt Prod.mk Prod.mk

/-- Verify a single-salt Fiat–Shamir proof against the original statement.
The DSFS hybrid games use this same verifier. -/
def fsSaltedVerify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmt : StmtIn) (proof : FSSaltedNARGString pSpec Salt) :
    OptionT (OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)) StmtOut :=
  V.verifyFiatShamir stmt (stmt, proof.1) proof.2

/--
Canonical Fiat-Shamir transformation for the verifier ([CO25, Construction 3.17] verifier
surface).

The verifier reads the salt `τ` and messages from the NARG string, then derives the transcript by
querying the FS oracle keyed at the context `(stmtIn, τ)`.
Adapted from **[snarg-book, Construction 14.1.1]** (single salt instead of per-round salts).
-/
def Verifier.compileFiatShamir {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (FSSaltedNARGString pSpec Salt)
      (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) StmtIn StmtOut where
  verify := fun stmt proof => fsSaltedVerify V stmt (proof 0)

/--
Canonical Fiat-Shamir transformation for an (interactive) reduction ([CO25, Construction 3.17]),
combining the salted prover and verifier surfaces.
Adapted from **[snarg-book, Construction 14.1.1]** (single salt instead of per-round salts).
-/
def Reduction.compileFiatShamir {Salt : Type} [VCVCompatible Salt]
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) :
    NonInteractiveReduction (FSSaltedNARGString pSpec Salt)
      (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.compileFiatShamir sampleSalt
  verifier := R.verifier.compileFiatShamir

/-- Canonical Fiat-Shamir NARG metadata: one fixed-length salt and the unchanged message family.
The salt is not part of the application statement, witness, relation, or interactive messages. -/
abbrev FiatShamirNARGString (pSpec : ProtocolSpec n) (U : Type) (saltLength : Nat) :=
  FSSaltedNARGString pSpec (Vector U saltLength)

/-- Canonical FS keys use separate salt context. The paired context here is a random-oracle key,
not an augmented application statement or relation. -/
abbrev ProtocolSpec.canonicalFSOracle (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (U : Type) (saltLength : Nat) :=
  fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec

/-- Canonical Fiat-Shamir prover. Sample one salt of the configured length using only the ambient
oracle, then reuse it in every verifier-message query. Fresh uniform private salt randomness is
required by the ZK experiment. Length zero uses the same construction with an empty salt. -/
def Prover.fiatShamirSalted {U : Type} [VCVCompatible U] (saltLength : Nat)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    NonInteractiveProver (FiatShamirNARGString pSpec U saltLength)
      (oSpec + canonicalFSOracle StmtIn pSpec U saltLength) StmtIn WitIn StmtOut WitOut :=
  P.compileFiatShamir sampleSalt

/-- Canonical Fiat-Shamir verifier, taking salt metadata separately from the original messages. -/
def Verifier.fiatShamirSalted {U : Type} [VCVCompatible U] (saltLength : Nat)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (Message := FiatShamirNARGString pSpec U saltLength)
      (oSpec + canonicalFSOracle StmtIn pSpec U saltLength) StmtIn StmtOut :=
  V.compileFiatShamir

/-- Canonical Fiat-Shamir transformation with one salt of fixed length per NARG string.
The abstract-salt compiler serves as an encoding adapter for the security reductions. -/
def Reduction.fiatShamirSalted {U : Type} [VCVCompatible U] (saltLength : Nat)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    NonInteractiveReduction (Message := FiatShamirNARGString pSpec U saltLength)
      (oSpec + canonicalFSOracle StmtIn pSpec U saltLength) StmtIn WitIn StmtOut WitOut :=
  R.compileFiatShamir sampleSalt

end ReductionCompilers

/-! ## Canonical Fiat–Shamir for interactive protocols -/

section InteractiveProtocols

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {Statement Witness Salt U : Type}
  [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- Generate a canonical NARG string with one ambient-only salt sample.
No terminal reduction output is executed. -/
def InteractiveProver.compileFiatShamir [VCVCompatible Salt]
    (P : InteractiveProver oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : Statement) (wit : Witness) :
    OracleComp (oSpec + fsVerifierMessageOracle (Statement × Salt) pSpec)
      (FSSaltedNARGString pSpec Salt) :=
  Prod.fst <$> CanonicalFS.compilePayload P.toReductionProver sampleSalt stmt
    (P.input (stmt, wit))

/-- Derive the interactive transcript and return its acceptance decision. -/
def InteractiveVerifier.compileFiatShamir [VCVCompatible Salt]
    (V : InteractiveVerifier oSpec Statement pSpec)
    (stmt : Statement) (nargString : FSSaltedNARGString pSpec Salt) :
    OracleComp (oSpec + fsVerifierMessageOracle (Statement × Salt) pSpec) Bool := do
  let transcript ← nargString.2.deriveTranscriptFS (oSpec := oSpec) (stmt, nargString.1)
  (V.verify stmt transcript).liftComp _

/-- Compile a public-coin protocol with one salt carried in the proof. -/
def InteractiveProtocol.compileFiatShamir [VCVCompatible Salt]
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec Salt) :
    NonInteractiveArgument (oSpec + fsVerifierMessageOracle (Statement × Salt) pSpec)
      Statement Witness (FSSaltedNARGString pSpec Salt) where
  prover := protocol.prover.compileFiatShamir sampleSalt
  verifier := protocol.verifier.compileFiatShamir

/-! ### Byte serialization -/

/-- Generate a serialized Fiat–Shamir proof from an interactive prover. -/
def InteractiveProver.compileFiatShamirBytes [VCVCompatible U] (saltLength : Nat)
    (P : InteractiveProver oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) (stmt : Statement) (wit : Witness) :
    OracleComp (oSpec + canonicalFSOracle Statement pSpec U saltLength) ByteArray :=
  serializer.serialize <$> P.compileFiatShamir sampleSalt stmt wit

/-- Parse a serialized Fiat–Shamir proof before running the compiled verifier. -/
def InteractiveVerifier.compileFiatShamirBytes [VCVCompatible U] (saltLength : Nat)
    (V : InteractiveVerifier oSpec Statement pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (stmt : Statement) (bytes : ByteArray) :
    OracleComp (oSpec + canonicalFSOracle Statement pSpec U saltLength) Bool :=
  serializer.verifyBytes (V.compileFiatShamir stmt) bytes

/-- Compile a public-coin protocol to a byte-valued NARG using the supplied serializer. -/
def InteractiveProtocol.compileFiatShamirBytes [VCVCompatible U] (saltLength : Nat)
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    NonInteractiveArgument (oSpec + canonicalFSOracle Statement pSpec U saltLength)
      Statement Witness ByteArray :=
  (protocol.compileFiatShamir sampleSalt).serialize serializer

/-! ### Agreement with the reduction compiler -/

omit [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The generator is exactly the NARG string sent by the compatibility compiler,
including every oracle effect and excluding its terminal output. -/
theorem InteractiveProver.compileFiatShamir_eq_sendMessage [VCVCompatible Salt]
    (P : InteractiveProver oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : Statement) (wit : Witness) :
    P.compileFiatShamir sampleSalt stmt wit =
      Prod.fst <$> (P.toReductionProver.compileFiatShamir sampleSalt).sendMessage ⟨0, rfl⟩
        ((P.toReductionProver.compileFiatShamir sampleSalt).input (stmt, wit)) := rfl

omit [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Verification has the same oracle computation as the established security interface.
A rejected NARG string returns `some false`; it is not confused with abort. -/
theorem InteractiveVerifier.compileFiatShamir_eq_verify [VCVCompatible Salt]
    (V : InteractiveVerifier oSpec Statement pSpec)
    (stmt : Statement) (nargString : FSSaltedNARGString pSpec Salt) :
    ((V.toReductionVerifier.compileFiatShamir).verify stmt
      (Fin.cons nargString (fun i => i.elim0))).run =
      some <$> V.compileFiatShamir stmt nargString := by
  simp only [ChallengeIdx, Challenge, Nat.reduceAdd, Fin.vcons_fin_zero,
    Verifier.compileFiatShamir, fsSaltedVerify, Verifier.verifyFiatShamir, Fin.isValue,
    InteractiveVerifier.toReductionVerifier,
    OptionT.lift, bind_pure_comp, OptionT.run_mk, liftM_map, bind_map_left,
    Option.getM_some, bind_pure, Fin.cons_zero, OptionT.run_bind, OptionT.run_monadLift,
    monadLift_self, Option.elimM_map, Option.elim_some,
    InteractiveVerifier.compileFiatShamir, liftComp_eq_liftM, map_bind]
  congr 1
  funext transcript
  rw [← OracleComp.monadLift_liftM_OptionT]
  simp only [OptionT.run_monadLift, monadLift_self]

end InteractiveProtocols
