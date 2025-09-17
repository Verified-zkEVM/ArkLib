import ArkLib.Data.Hash.DuplexSponge
import ArkLib.OracleReduction.FiatShamir.Basic

/-!
# Duplex Sponge Fiat-Shamir

We define the (multi-round) Fiat-Shamir transformation using duplex sponges.
-/

/- First, we define the oracle specification, consisting of `(h, p, p⁻¹)` where:
- `h : ByteArray → Vector U SpongePermutationSize.C`
is the hash function (assumed to be random oracle)
(Note: input could be different from `ByteArray`)
- `p : Vector U SpongePermutationSize.N → Vector U SpongePermutationSize.N`
is the forward direction of the random permutation
- `p⁻¹ : Vector U SpongePermutationSize.N → Vector U SpongePermutationSize.N`
is the backward direction of the random permutation
-/

inductive PermOracleIndex where
| Hash
| Forward
| Backward

def duplexSpongeChallengeOracle (StartType : Type) (U : Type)
    [SpongeUnit U] [SpongePermutationSize] : OracleSpec PermOracleIndex
  | PermOracleIndex.Hash => (StartType, Vector U SpongePermutationSize.C)
  | PermOracleIndex.Forward => (Vector U SpongePermutationSize.N, Vector U SpongePermutationSize.N)
  | PermOracleIndex.Backward => (Vector U SpongePermutationSize.N, Vector U SpongePermutationSize.N)


open ProtocolSpec OracleComp OracleSpec

open scoped BigOperators

variable {n : ℕ}

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongePermutationSize]
  -- All messages are serializable to an array of units
  [∀ i, Serialize (Array U) (pSpec.Message i)]
  -- All challenges are deserializable from an array of units
  [∀ i, Deserialize (Array U) (pSpec.Challenge i)]

def ProtocolSpec.Message.deriveTranscriptDSFS (stmtIn : StmtIn) (messages : pSpec.Messages) :
    OracleComp (duplexSpongeChallengeOracle StmtIn U) pSpec.FullTranscript :=
  sorry

-- In order to define the Fiat-Shamir transformation for the prover, we need to define
-- a slightly altered execution for the prover

/--
Prover's function for processing the next round, given the current result of the previous round.

  This is modified for Fiat-Shamir, where we only accumulate the messages and not the challenges.
-/
@[inline, specialize]
def Prover.processRoundDSFS [∀ i, VCVCompatible (pSpec.Challenge i)] (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
      (pSpec.MessagesUpTo j.castSucc × StmtIn × prover.PrvState j.castSucc)) :
      OracleComp (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
        (pSpec.MessagesUpTo j.succ × StmtIn × prover.PrvState j.succ) := do
  let ⟨messages, stmtIn, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let f ← prover.receiveChallenge ⟨j, hDir⟩ state
    let challenge ← query (spec := duplexSpongeChallengeOracle StmtIn U) PermOracleIndex.Forward ⟨stmtIn, messages⟩
    return ⟨messages.extend hDir, stmtIn, f challenge⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨messages.concat hDir msg, stmtIn, newState⟩

/--
Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def Prover.runToRoundDSFS [∀ i, VCVCompatible (pSpec.Challenge i)] (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
          (pSpec.MessagesUpTo i × StmtIn × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, stmt, state⟩)
    prover.processRoundDSFS
    i

/-- The (slow) Fiat-Shamir transformation for the prover. -/
def Prover.duplexSpongeFiatShamir (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveProver (∀ i, pSpec.Message i) (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  -- Compute the messages to send via the modified `runToRoundFS`
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let ⟨messages, _, state⟩ ← P.runToRoundDSFS (Fin.last n) stmtIn state
    return ⟨messages, state⟩
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/-- The (slow) Fiat-Shamir transformation for the verifier. -/
def Verifier.duplexSpongeFiatShamir (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (∀ i, pSpec.Message i) (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let messages : pSpec.Messages := proof 0
    let transcript ← liftM (messages.deriveTranscriptDSFS stmtIn)
    V.verify stmtIn transcript

/-- The Fiat-Shamir transformation for an (interactive) reduction, which consists of applying the
  Fiat-Shamir transformation to both the prover and the verifier. -/
def Reduction.duplexSpongeFiatShamir (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction (∀ i, pSpec.Message i) (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.duplexSpongeFiatShamir
  verifier := R.verifier.duplexSpongeFiatShamir
