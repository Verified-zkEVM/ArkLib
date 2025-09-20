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

variable {n : ℕ} {pSpec : ProtocolSpec n}
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
  ∑ i, Lₚᵢ (pSpec := pSpec) i

/-- Number of queries to the permutation oracle needed to absorb the `i`-th challenge of the
  protocol specification -/
def numPermQueriesChallenge (i : pSpec.ChallengeIdx) : Nat :=
  Nat.ceil ((challengeSize i : ℚ) / SpongeSize.R)

alias Lᵥᵢ := numPermQueriesChallenge

/-- Total number of queries to the permutation oracle needed to absorb all challenges of the
  protocol specification. This is `Lᵥ` in the paper (Equation 9). -/
def totalNumPermQueriesChallenge : Nat :=
  ∑ i, Lᵥᵢ (pSpec := pSpec) i

/-- Total number of queries to the permutation oracle needed to absorb all messages and challenges
  of the protocol specification. This is `L` in the paper (Equation 10). -/
def totalNumPermQueries : Nat :=
  totalNumPermQueriesMessage (pSpec := pSpec) + totalNumPermQueriesChallenge (pSpec := pSpec)

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
    (state : Vector U SpongeSize.N) :
    Option (StmtIn × (i : Fin (n + 1)) × (pSpec.MessagesUpTo i)) :=
  sorry

/-- The lookahead procedure in Section 5.2, which takes in:
- A query-answer trace for the oracle `h`
- A permutation state (vector of `N` units)
- A round index `i` for a challenge round

And returns (with potential failure):
- An encoded verifier's challenge (vector of `chalSize i` units)
-/
def lookAhead (hashTrace : QueryLog (StmtIn →ₒ Vector U SpongeSize.C)) (state : Vector U SpongeSize.N)
    (i : pSpec.ChallengeIdx) :
    Option (Vector U (challengeSize i)) :=
  sorry

-- #check IsQueryBound tₚ tₕ

/-- The transformation of a duplex-sponge Fiat-Shamir malicious prover to a basic Fiat-Shamir one.

Note: this transformation needs to be an oracle computation itself -/
def duplexSpongeToBasicFSProver
    (P : OracleComp (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec ++ₒ fsChallengeOracle StmtIn pSpec) (StmtIn × pSpec.Messages) :=
  sorry

/-- The transformation of basic Fiat-Shamir query-answer traces (from both prover and verifier)
to duplex-sponge Fiat-Shamir query-answer traces (from both prover and verifier)

Note: this goes the opposite direction as the prover transformation -/
def basicToDuplexSpongeFSQueryLog
    (proveQueryLog : QueryLog (oSpec ++ₒ fsChallengeOracle StmtIn pSpec))
    (verifyQueryLog : QueryLog (oSpec ++ₒ fsChallengeOracle StmtIn pSpec)) :
      QueryLog (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U) :=
  sorry

end AuxiliaryProcedures

section KeyLemma

open scoped NNReal

variable [DecidableEq ι]

/-- `θStar` in the paper, which is just equal to `tₚ`, the bound for number of forward permutation
  queries made by the malicious prover -/
def θStar (_tₕ tₚ _tₚᵢ : ℕ) : ℕ := tₚ

/-!
`ηStar th tp tpm1 L permBound epsCdcMax epsCdcSum` encodes the bound η⋆ from the paper
with the following stubs supplied as parameters:
- `permBound` stands for 1 / (2 · |Σ|^c)
- `epsCdcMax` stands for maxᵢ ε_cdc,i(λ, n)
- `epsCdcSum` stands for ∑ᵢ ε_cdc,i(λ, n)
-/
noncomputable def ηStar (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ : ℕ) (L : ℕ) (εcodec : pSpec.ChallengeIdx → ℝ≥0) : ℝ≥0 :=
  let tTotal : ℕ := (tₕ + tₚ + tₚᵢ)
  -- First term in Equation (5)
  -- Numerator: `7 * t ^ 2 + (28 * L + 25) * t + (14 * L + 1) * (L + 1)`
  -- Note: we rewrote the numerator to make it clear that the term is nonnegative (no subtraction)
  -- Original: `7 * t ^ 2 + 28 * (L + 1) * t + 14 * (L + 1)^2 - 3 * t - 13 * (L + 1)`
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
    (hQuery : IsQueryBound maliciousProver (tₒ ⊕ᵥ (tₕ ⊕ᵥ (tₚ ⊕ᵥ tₚᵢ)))) : True :=
  sorry

end KeyLemma

end DuplexSpongeFS
