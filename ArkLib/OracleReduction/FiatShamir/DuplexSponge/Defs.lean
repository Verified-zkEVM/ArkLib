/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.Data.Hash.DuplexSponge
import ArkLib.OracleReduction.FiatShamir.Basic

/-!
# Duplex Sponge Fiat-Shamir

We define the (multi-round) Fiat-Shamir transformation using duplex sponges.

This file provides:
- an unsalted DSFS surface (`duplexSpongeFiatShamir`) used by existing Section 5 machinery, and
- an explicit salted surface (`duplexSpongeFiatShamirSalted`) matching Construction 4.3 shape,
  where a salt `τ ∈ Σ^δ` is absorbed before round processing and included in the proof string.
-/

namespace ProtocolSpec

-- TODO: unify `HasMessageSize` and `HasChallengeSize` into Codec
-- infrastructure, since these are message length functions

/-- Type class for protocol specifications to specify the size of each message as a natural number
  (to be interpreted as a vector of units `U` of the given size for some sponge unit `U`) -/
class HasMessageSize {n : ℕ} (pSpec : ProtocolSpec n) where
  messageSize : pSpec.MessageIdx → Nat

export HasMessageSize (messageSize)

/-- Type class for protocol specifications to specify the size of each challenge as a natural number
  (to be interpreted as a vector of units `U` of the given size for some sponge unit `U`) -/
class HasChallengeSize {n : ℕ} (pSpec : ProtocolSpec n) where
  challengeSize : pSpec.ChallengeIdx → Nat

export HasChallengeSize (challengeSize)

/-- Paper-facing codec surface for CO25 Definition 4.1.

The existing DSFS implementation is written against `HasMessageSize` / `HasChallengeSize` plus
`Serialize` / `Deserialize` instances. `Codec` packages that data together in one object while also
recording the per-round decoder bias and a preimage sampler needed by later sections of the paper.
-/
structure Codec {n : ℕ} (pSpec : ProtocolSpec n) (U : Type) where
  messageSize : pSpec.MessageIdx → Nat
  challengeSize : pSpec.ChallengeIdx → Nat
  encode : (i : pSpec.MessageIdx) → pSpec.Message i → Vector U (messageSize i)
  encode_injective : ∀ i, Function.Injective (encode i)
  decode : (i : pSpec.ChallengeIdx) → Vector U (challengeSize i) → pSpec.Challenge i
  challengeBias : pSpec.ChallengeIdx → NNReal
  sampleChallengePreimage :
    (i : pSpec.ChallengeIdx) → pSpec.Challenge i → ProbComp (Vector U (challengeSize i))

namespace Codec

variable {n : ℕ} {pSpec : ProtocolSpec n} {U : Type}

instance (cdc : Codec pSpec U) : HasMessageSize pSpec where
  messageSize := cdc.messageSize

instance (cdc : Codec pSpec U) : HasChallengeSize pSpec where
  challengeSize := cdc.challengeSize

instance (cdc : Codec pSpec U) :
    ∀ i, Serialize (pSpec.Message i) (Vector U (cdc.messageSize i)) := by
  intro i
  exact ⟨cdc.encode i⟩

instance (cdc : Codec pSpec U) :
    ∀ i, Serialize.IsInjective (pSpec.Message i) (Vector U (cdc.messageSize i)) := by
  intro i
  exact ⟨cdc.encode_injective i⟩

instance (cdc : Codec pSpec U) :
    ∀ i, Deserialize (pSpec.Challenge i) (Vector U (cdc.challengeSize i)) := by
  intro i
  exact ⟨cdc.decode i⟩

end Codec

variable (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    {U : Type} [SpongeUnit U] [SpongeSize]
    [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
    [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- Number of queries to the permutation oracle needed to absorb the `i`-th message of the
  protocol specification. This is `Lₚ(i)` in the paper block-count notation (Equation 6). -/
def numPermQueriesMessage (i : pSpec.MessageIdx) : Nat :=
  Nat.ceil ((messageSize i : ℚ) / SpongeSize.R)

alias Lₚᵢ := numPermQueriesMessage

/-- Total number of queries to the permutation oracle needed to absorb all messages of the
  protocol specification. This is `Lₚ` in the paper block-count notation (Equation 7). -/
def totalNumPermQueriesMessage : Nat :=
  ∑ i, pSpec.Lₚᵢ i

/-- Number of queries to the permutation oracle needed to absorb the `i`-th challenge of the
  protocol specification. This is `Lᵥ(i)` in the paper block-count notation (Equation 6). -/
def numPermQueriesChallenge (i : pSpec.ChallengeIdx) : Nat :=
  Nat.ceil ((challengeSize i : ℚ) / SpongeSize.R)

alias Lᵥᵢ := numPermQueriesChallenge

/-- Total number of queries to the permutation oracle needed to absorb all challenges of the
  protocol specification. This is `Lᵥ` in the paper block-count notation (Equation 7). -/
def totalNumPermQueriesChallenge : Nat :=
  ∑ i, pSpec.Lᵥᵢ i

/-- Total number of queries to the permutation oracle needed to absorb all messages and challenges
  of the protocol specification. This is `L` in the paper block-count notation (Equation 7). -/
def totalNumPermQueries : Nat :=
  pSpec.totalNumPermQueriesMessage + pSpec.totalNumPermQueriesChallenge

/-- The oracle specification for duplex sponge Fiat-Shamir (Equation 14, written as `𝒟_Σ`).
It is indexed over the challenge rounds of the protocol specification, and for each such round `i`:
- The input is the input statement `stmtIn` and, for each `j < i` that is a message round,
  a vector of units of size `Lₚ(j)` (the number of queries to the permutation oracle needed to
  absorb the `j`-th message)
- The output is a vector of units of size `Lᵥ(i)` (the number of queries to the permutation oracle
  needed to absorb the `i`-th challenge) -/
def duplexSpongeHybridOracle : OracleSpec
    ((i : pSpec.ChallengeIdx) × StmtIn ×
      ((j : pSpec.MessageIdx) → (j.1 < i.1) → Vector U (pSpec.Lₚᵢ j))) :=
  fun i => Vector U (pSpec.Lᵥᵢ i.1)

alias «𝒟_Σ» := duplexSpongeHybridOracle

/-- Salted variant of Equation 14 (Construction 4.3-facing):
query keys also include the absorbed salt `τ ∈ Σ^δ`. -/
def duplexSpongeHybridOracleSalted (δ : Nat) : OracleSpec
    ((i : pSpec.ChallengeIdx) × StmtIn × Vector U δ ×
      ((j : pSpec.MessageIdx) → (j.1 < i.1) → Vector U (pSpec.Lₚᵢ j))) :=
  fun i => Vector U (pSpec.Lᵥᵢ i.1)

end ProtocolSpec

namespace OracleSpec

/-- The oracle specification for duplex sponge Fiat-Shamir (Definition 4.2, written as `𝒟_𝔖`).
The index consists of `(h, p, p⁻¹)`, where:
- `h : ByteArray → Vector U SpongeSize.C`
is the hash function (assumed to be random oracle)
(Note: input could be different from `ByteArray`)
- `p : Vector U SpongeSize.N → Vector U SpongeSize.N`
is the forward direction of the random permutation
- `p⁻¹ : Vector U SpongeSize.N → Vector U SpongeSize.N`
is the backward direction of the random permutation
-/
@[reducible]
def duplexSpongeChallengeOracle (StartType : Type) (U : Type) [SpongeUnit U] [SpongeSize] :
    OracleSpec (StartType ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U) :=
  (StartType →ₒ Vector U SpongeSize.C) + permutationOracle (CanonicalSpongeState U)

alias 𝒟_𝔖 := duplexSpongeChallengeOracle

end OracleSpec

open OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  -- All messages are serializable to an array of units
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  -- All challenges are deserializable from an array of units
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- Proof-string format for the salted DSFS surface (`τ` plus prover messages). -/
abbrev DSSaltedProof (pSpec : ProtocolSpec n) (U : Type) (δ : Nat) :=
  Vector U δ × (∀ i, pSpec.Message i)

namespace ProtocolSpec.Messages

/-- Auxiliary function for deriving the transcript up to round `k` from the (full) messages, via
  querying the permutation oracle for the challenges.

  This is used to define `deriveTranscriptDSFS`. -/
def deriveTranscriptDSFSAux {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (sponge : CanonicalDuplexSponge U)
    (messages : pSpec.Messages) (i : Fin (n + 1)) :
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (CanonicalDuplexSponge U × pSpec.Transcript i) :=
  Fin.induction
    (pure (sponge, fun i => i.elim0))
    (fun i ih => do
      let ⟨curSponge, prevTranscript⟩ ← ih
      match hDir : pSpec.dir i with
      | .V_to_P =>
        let ⟨challenge, newSponge⟩ ← liftM (curSponge.squeeze (challengeSize ⟨i, hDir⟩))
        let deserializedChallenge : pSpec.Challenge ⟨i, hDir⟩ :=
          Deserialize.deserialize challenge
        return (newSponge, prevTranscript.concat deserializedChallenge)
      | .P_to_V =>
        let serializedMessage : Vector U (messageSize ⟨i, hDir⟩) :=
          Serialize.serialize (messages ⟨i, hDir⟩)
        let newSponge ← liftM (DuplexSponge.absorb curSponge serializedMessage.toList)
        return (newSponge, prevTranscript.concat (messages ⟨i, hDir⟩)))
    i

/-- Derive the full transcript from the (full) messages, via doing absorb / squeeze operations on
    the duplex sponge.

  Returns the final state of the duplex sponge and the full transcript -/
def deriveTranscriptDSFS {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmtIn : StmtIn) (messages : pSpec.Messages) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (CanonicalDuplexSponge U × pSpec.FullTranscript) := do
  let sponge ← liftM (DuplexSponge.start stmtIn)
  deriveTranscriptDSFSAux sponge messages (Fin.last n)

end Messages

end ProtocolSpec

open ProtocolSpec

/--
Prover's function for processing the next round, given the current result of the previous round.

This is modified for Fiat-Shamir, where we only accumulate the messages and not the challenges.
-/
@[inline, specialize]
def Prover.processRoundDSFS [∀ i, VCVCompatible (pSpec.Challenge i)]
     (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (pSpec.MessagesUpTo j.castSucc ×
        CanonicalDuplexSponge U × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (pSpec.MessagesUpTo j.succ ×
          CanonicalDuplexSponge U × prover.PrvState j.succ) := do
  let ⟨messages, sponge, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let f ← prover.receiveChallenge ⟨j, hDir⟩ state
    let (challenge, newSponge) ←
      liftM (m := OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
        (DuplexSponge.squeeze sponge (challengeSize ⟨j, hDir⟩))
    -- Deserialize the challenge
    let deserializedChallenge : pSpec.Challenge ⟨j, hDir⟩ := Deserialize.deserialize challenge
    return ⟨messages.extend hDir, newSponge, f deserializedChallenge⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    let serializedMessage : Vector U (messageSize ⟨j, hDir⟩) := Serialize.serialize msg
    let newSponge ← liftM (m := OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (DuplexSponge.absorb sponge serializedMessage.toList)
    return ⟨messages.concat hDir msg, newSponge, newState⟩

/--
Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def Prover.runToRoundDSFS [∀ i, VCVCompatible (pSpec.Challenge i)] (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (pSpec.MessagesUpTo i ×
            DuplexSponge U (Vector U SpongeSize.N) × prover.PrvState i) :=
  Fin.induction
    (do
      -- Initialize the sponge with the input statement
      let sponge ← liftM (DuplexSponge.start stmt)
      return ⟨default, sponge, state⟩
    )
    (prover.processRoundDSFS)
    i

/-- The duplex sponge Fiat-Shamir transformation for the prover. -/
def Prover.duplexSpongeFiatShamir (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveProver (∀ i, pSpec.Message i) (oSpec + duplexSpongeChallengeOracle StmtIn U)
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

/-- The duplex sponge Fiat-Shamir transformation for the verifier. -/
def Verifier.duplexSpongeFiatShamir (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (∀ i, pSpec.Message i) (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    -- Get the messages from the non-interactive proof
    let messages : pSpec.Messages := proof 0
    -- Derive the full transcript based on the messages and the sponge
    let ⟨_, transcript⟩ ← (messages.deriveTranscriptDSFS (oSpec := oSpec) (U := U) stmtIn)
    let v ← (V.verify stmtIn transcript).run
    v.getM
    -- Option.getM (← (V.verify stmtIn transcript).run)

/-- The duplex sponge Fiat-Shamir transformation for an (interactive) reduction, which consists of
  applying the duplex sponge Fiat-Shamir transformation to both the prover and the verifier. -/
def Reduction.duplexSpongeFiatShamir (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction (∀ i, pSpec.Message i) (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.duplexSpongeFiatShamir
  verifier := R.verifier.duplexSpongeFiatShamir

/--
Derive the full transcript from prover messages after explicitly absorbing a public salt `τ`.

This is the transcript path for the salted Construction 4.3 surface.
-/
def ProtocolSpec.Messages.deriveTranscriptDSFSSalted {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {δ : Nat}
    (stmtIn : StmtIn) (salt : Vector U δ) (messages : pSpec.Messages) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (CanonicalDuplexSponge U × pSpec.FullTranscript) := do
  let sponge0 ← liftM (DuplexSponge.start stmtIn)
  let sponge ← liftM (DuplexSponge.absorb sponge0 salt.toList)
  ProtocolSpec.Messages.deriveTranscriptDSFSAux (pSpec := pSpec) (oSpec := oSpec) (U := U)
    sponge messages (Fin.last n)

/--
Run the prover up to round `i` after first absorbing an explicit salt `τ`.
-/
@[inline, specialize]
def Prover.runToRoundDSFSSalted [∀ i, VCVCompatible (pSpec.Challenge i)] {δ : Nat}
    (salt : Vector U δ) (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (pSpec.MessagesUpTo i ×
            DuplexSponge U (Vector U SpongeSize.N) × prover.PrvState i) :=
  Fin.induction
    (do
      let sponge0 ← liftM (DuplexSponge.start stmt)
      let sponge ← liftM (DuplexSponge.absorb sponge0 salt.toList)
      return ⟨default, sponge, state⟩
    )
    (prover.processRoundDSFS)
    i

/-- Salted DSFS prover surface (Construction 4.3-facing). -/
def Prover.duplexSpongeFiatShamirSalted [∀ i, VCVCompatible (pSpec.Challenge i)] (δ : Nat)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : (stmt : StmtIn) → P.PrvState 0 →
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Vector U δ)) :
    NonInteractiveProver (DSSaltedProof (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let salt ← sampleSalt stmtIn state
    let ⟨messages, _, state⟩ ← P.runToRoundDSFSSalted (salt := salt) (Fin.last n) stmtIn state
    return ⟨(salt, messages), state⟩
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/-- Salted DSFS verifier surface (Construction 4.3-facing). -/
def Verifier.duplexSpongeFiatShamirSalted (δ : Nat)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (DSSaltedProof (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let saltedProof : DSSaltedProof (pSpec := pSpec) (U := U) δ := proof 0
    let salt : Vector U δ := saltedProof.1
    let messages : pSpec.Messages := saltedProof.2
    let ⟨_, transcript⟩ ←
      messages.deriveTranscriptDSFSSalted (pSpec := pSpec) (oSpec := oSpec) (U := U) stmtIn salt
    let v ← (V.verify stmtIn transcript).run
    v.getM

/-- Salted DSFS reduction surface (Construction 4.3-facing). -/
def Reduction.duplexSpongeFiatShamirSalted [∀ i, VCVCompatible (pSpec.Challenge i)] (δ : Nat)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : (stmt : StmtIn) → R.prover.PrvState 0 →
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Vector U δ)) :
    NonInteractiveReduction (DSSaltedProof (pSpec := pSpec) (U := U) δ)
      (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.duplexSpongeFiatShamirSalted (δ := δ) sampleSalt
  verifier := R.verifier.duplexSpongeFiatShamirSalted (δ := δ)
