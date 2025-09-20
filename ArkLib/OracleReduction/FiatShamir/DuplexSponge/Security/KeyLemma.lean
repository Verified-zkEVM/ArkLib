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
