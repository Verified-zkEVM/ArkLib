import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Lemma 5.1 of the Chiesa-Orrù paper

We give the statement (and eventually, proof) of this key lemma, which states that two games
(duplex-sponge vs. basic Fiat-Shamir) have the same distribution, up to two auxiliary procedures
that transform the prover and the query-answer traces, respectively.

Using this key lemma, we can easily conclude preservation of (knowledge) soundness.
-/

open OracleComp OracleSpec ProtocolSpec

namespace ProtocolSpec

variable {n : ℕ} (pSpec : ProtocolSpec n)
    {U : Type} [SpongeUnit U] [SpongeSize]
    [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
    [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- Number of queries to the permutation oracle needed to absorb the `i`-th message of the
  protocol specification. This is `Lₚ(i)` in the paper (Equation 7). -/
def numPermQueriesMessage (i : pSpec.MessageIdx) : Nat :=
  Nat.ceil ((messageSize i : ℚ) / SpongeSize.R)

alias Lₚᵢ := numPermQueriesMessage

/-- Total number of queries to the permutation oracle needed to absorb all messages of the
  protocol specification. This is `Lₚ` in the paper (Equation 8). -/
def totalNumPermQueriesMessage : Nat :=
  ∑ i, pSpec.Lₚᵢ i

/-- Number of queries to the permutation oracle needed to absorb the `i`-th challenge of the
  protocol specification. This is `Lᵥ(i)` in the paper (Equation 7). -/
def numPermQueriesChallenge (i : pSpec.ChallengeIdx) : Nat :=
  Nat.ceil ((challengeSize i : ℚ) / SpongeSize.R)

alias Lᵥᵢ := numPermQueriesChallenge

/-- Total number of queries to the permutation oracle needed to absorb all challenges of the
  protocol specification. This is `Lᵥ` in the paper (Equation 8). -/
def totalNumPermQueriesChallenge : Nat :=
  ∑ i, pSpec.Lᵥᵢ i

/-- Total number of queries to the permutation oracle needed to absorb all messages and challenges
  of the protocol specification. This is `L` in the paper (Equation 8). -/
def totalNumPermQueries : Nat :=
  pSpec.totalNumPermQueriesMessage + pSpec.totalNumPermQueriesChallenge

end ProtocolSpec

namespace DuplexSpongeFS

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  -- All messages are serializable to vectors of units
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  -- All challenges are deserializable from vectors of units
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

section SecurityGames

/-- First game for the key lemma: the basic Fiat-Shamir transform.

We run the malicious prover, then the verifier, then returns:
- the input statement (that the malicious prover chooses)
- the output statement (that the verifier returns)
- the messages / proof sent by the prover
- the query log of the prover
- the query log of the verifier -/
def basicFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec ++ₒ fsChallengeOracle StmtIn pSpec) (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec ++ₒ fsChallengeOracle StmtIn pSpec)
      (StmtIn × StmtOut × pSpec.Messages × QueryLog (oSpec ++ₒ fsChallengeOracle StmtIn pSpec)
        × QueryLog (oSpec ++ₒ fsChallengeOracle StmtIn pSpec)) := do
  let ⟨⟨stmtIn, messages⟩, proveQueryLog⟩ ← (simulateQ loggingOracle P).run
  let ⟨stmtOut, verifyQueryLog⟩ ← (simulateQ loggingOracle
    (V.fiatShamir.run stmtIn (fun i => match i with | ⟨0, _⟩ => messages))).run
  return ⟨stmtIn, stmtOut, messages, proveQueryLog, verifyQueryLog⟩

/-- Second game for the key lemma: the duplex sponge Fiat-Shamir transform.

We run the malicious prover, then the verifier, then returns:
- the input statement (that the malicious prover chooses)
- the output statement (that the verifier returns)
- the messages / proof sent by the prover
- the query log of the prover
- the query log of the verifier -/
def duplexSpongeFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × StmtOut × pSpec.Messages
        × QueryLog (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
        × QueryLog (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)) := do
  let ⟨⟨stmtIn, messages⟩, proveQueryLog⟩ ← (simulateQ loggingOracle P).run
  let ⟨stmtOut, verifyQueryLog⟩ ←
    (simulateQ loggingOracle
      (V.duplexSpongeFiatShamir.run
        stmtIn (fun i => match i with | ⟨0, _⟩ => messages))).run
  return ⟨stmtIn, stmtOut, messages, proveQueryLog, verifyQueryLog⟩

end SecurityGames

section AuxiliaryProcedures

section Backtrack

/-- A backtracking sequence (Definition 5.3) for a given hash-duplex-sponge oracle trace `tr` and
  final duplex-sponge state `s` consists of the following data:
- An input statement `𝕩`
- A list `inputState = [sᵢₙ, ...]` of input states
- A list `outputState = [sₒᵤₜ, ...]` of output states

subject to the following conditions:
- The last of the input states is the given final state
- There is one more input state than output state
- The statement is queried with the hash, and returns the capacity of the first input state
  `(hash, 𝕩, inputState[0].capacitySegment) ∈ tr` -/
structure BacktrackSequence (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) where
  /-- The input statement in a backtracking sequence -/
  stmt : StmtIn
  /-- The list of input states in a backtracking sequence -/
  inputState : List (CanonicalSpongeState U)
  /-- The list of output states in a backtracking sequence -/
  outputState : List (CanonicalSpongeState U)

  /-- The input state list is one longer than the output state list -/
  inputState_length_eq_outputState_length_succ : inputState.length = outputState.length + 1

  /-- The last input state is the given final state -/
  last_inputState_eq_state : inputState[inputState.length - 1] = state

  /-- The query-answer pair `("hash", stmt, inputState[0].capacitySegment)` is in the trace -/
  hash_in_trace : (stmt, (Vector.drop inputState[0] SpongeSize.R)) ∈ trace.getQ (.inl ())

  /-- For all `i < outputState.length`, either
    - `inputState[i]` is permuted to `outputState[i]` in the trace, or
    - `outputState[i]` is inverted to `inputState[i]` in the trace -/
  permute_or_inv_in_trace : ∀ i : Fin outputState.length,
    (inputState[i], outputState[i]) ∈ trace.getQ (.inr .Fwd)
    ∨ (outputState[i], inputState[i]) ∈ trace.getQ (.inr .Bwd)

  /-- For all `i < outputState.length`, the capacity segment of `inputState[i]` is the same as
    the capacity segment of `outputState[i]` -/
  capacitySegment_output_eq_input : ∀ i : Fin outputState.length,
    outputState[i].capacitySegment = inputState[i.val + 1].capacitySegment

  /-- For all `i < outputState.length`, the capacity segment of `inputState[i]` is not the same as
    the capacity segment of `outputState[i]` -/
  capacitySegment_input_ne_output : ∀ i : Fin outputState.length,
    inputState[i].capacitySegment ≠ outputState[i].capacitySegment

/-- The associated indices (first occurrences in the trace) for a backtracking sequence -/
def BacktrackSequence.Index (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (seq : BacktrackSequence trace state) :
    Fin trace.length × (Fin seq.inputState.length → Fin trace.length) :=
  -- TODO: define `List.findFinIdx` that returns `Fin (l.length + 1)` and `List.findFinIdxIfTrue`
  -- that returns `Fin l.length` given the fact that the predicate is true for at least one element
  -- of the list
  (⟨trace.findIdx sorry, sorry⟩, sorry)

/-- A family of backtrack sequences, defined as a finite set of backtrack sequences such that
no two sequences are strict subsets of each other -/
structure BacktrackSequenceFamily (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) where
  /-- The family of backtrack sequences, defined as a finite set -/
  seqFamily : Finset (BacktrackSequence trace state)
  /-- Maximality condition: no strict containment between two sequences, defined in terms of
    - the statements are different, or
    - the input states are not a strict subset of each other, or
    - the output states are not a strict subset of each other -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily,
    (s.stmt ≠ s'.stmt) ∨ ¬ (s.inputState ⊆ s'.inputState) ∨ ¬ (s'.outputState ⊆ s.outputState)

/-- The backtracking procedure in Section 5.2, which takes in:
- the query-answer trace for the oracle `(h, p, p⁻¹)`
- a state (vector of `N` units)

And returns (with potential failure):
- an input statement
- a round index `i ≤ n`
- the protocol messages up to round `i`

NOTE: we do _not_ define the extra data structure `tr▵` as in the paper, as that is entirely derived
from the actual trace and is only present for efficiency (which we do not plan to reason about) -/
def backTrack (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) :
    Option (StmtIn × (i : Fin (n + 1)) × (pSpec.MessagesUpTo i)) :=
  sorry

end Backtrack

section Lookahead

/-- The lookahead procedure in Section 5.2, which takes in:
- A query-answer trace for the oracle `h`
- A permutation state (vector of `N` units)
- A round index `i` for a challenge round

And returns (with potential failure):
- An encoded verifier's challenge (vector of `chalSize i` units)
-/
def lookAhead (hashTrace : QueryLog (StmtIn →ₒ Vector U SpongeSize.C)) (state : CanonicalSpongeState U)
    (i : pSpec.ChallengeIdx) :
    Option (Vector U (challengeSize i)) :=
  sorry

end Lookahead

section D2SAlgo

/-- The query simulation between duplex sponge oracles and basic Fiat-Shamir oracles. This is then
  composed with the duplex-sponge malicious prover to obtain a basic F-S malicious prover -/
def duplexSpongeToBasicFSQueryImpl :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (OracleComp (fsChallengeOracle StmtIn pSpec)) :=
  sorry

/-- The transformation of a duplex-sponge Fiat-Shamir malicious prover to a basic Fiat-Shamir one.

Note: this transformation needs to be an oracle computation itself -/
def duplexSpongeToBasicFSAlgo
    (P : OracleComp (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec ++ₒ fsChallengeOracle StmtIn pSpec) (StmtIn × pSpec.Messages) :=
  sorry

end D2SAlgo

section D2STrace

/-- The transformation of basic Fiat-Shamir query-answer traces (from both prover and verifier)
to duplex-sponge Fiat-Shamir query-answer traces (from both prover and verifier)

Note: this goes the opposite direction as the prover transformation -/
def basicToDuplexSpongeFSTrace
    (proveQueryLog : QueryLog (oSpec ++ₒ fsChallengeOracle StmtIn pSpec))
    (verifyQueryLog : QueryLog (oSpec ++ₒ fsChallengeOracle StmtIn pSpec)) :
      QueryLog (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U) :=
  sorry

end D2STrace

end AuxiliaryProcedures

section KeyLemma

open scoped NNReal

variable [DecidableEq ι]

/-- `θStar` in the paper, which is just equal to `tₚ`, the bound for number of forward permutation
  queries made by the malicious prover -/
def θStar (_tₕ tₚ _tₚᵢ : ℕ) : ℕ := tₚ

/-!
`ηStar` in the paper, is the bound on the statistical distance between two experiments in Lemma 5.1
-/
noncomputable def ηStar (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ : ℕ) (L : ℕ) (εcodec : pSpec.ChallengeIdx → ℝ≥0) : ℝ≥0 :=
  let tTotal : ℕ := (tₕ + tₚ + tₚᵢ)
  -- First term in Equation (5)
  -- Numerator: `7 * t ^ 2 + (28 * L + 25) * t + (14 * L + 1) * (L + 1)`
  -- Note: we rewrote the numerator to make it clear that the term is nonnegative (no subtraction)
  -- Original: `7 * t ^ 2 + 28 * (L + 1) * t + 14 * (L + 1) ^ 2 - 3 * t - 13 * (L + 1)`
  let firstTermNumerator : ℝ≥0 :=
    7 * tTotal ^2 + (28 * L + 25) * tTotal + (14 * L + 1) * (L + 1)
  let firstTermDenominator : ℝ≥0 := 2 * ((Fintype.card U) ^ (SpongeSize.C + 1))
  -- Second term in Equation (5)
  let secondTerm : ℝ≥0 := θStar tₕ tₚ tₚᵢ * (iSup εcodec)
  -- Third term in Equation (5)
  let thirdTerm : ℝ≥0 := ∑ i, εcodec i
  -- η⋆ = (7 t^2 + (28 L + 25) t + (14 L + 1) (L + 1)) / (2 · |Σ|^c) + θ⋆ · max ε + ∑ ε
  firstTermNumerator / firstTermDenominator + secondTerm + thirdTerm

/-- Lemma 5.1 in the paper: given the two games and the auxiliary procedures to transform the
  malicious prover and the query-answer traces, the two games have outputs that are statistically
  indistinguishable, up to an error term

TODO: fully fill in this lemma -/
lemma duplexSpongeToFSGameStatDist
    (maliciousProver : OracleComp (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₒ : ι → ℕ) (tₕ tₚ tₚᵢ : ℕ)
    -- TODO: state query bound only for subset of the oracles
    (hQuery : IsQueryBound maliciousProver (tₒ ⊕ᵥ (tₕ ⊕ᵥ (tₚ ⊕ᵥ tₚᵢ)))) : True :=
  sorry

end KeyLemma

end DuplexSpongeFS
