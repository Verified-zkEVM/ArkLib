/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import VCVio.OracleComp.EvalDist.DiscreteTVDistBind
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Honest-verifier zero knowledge for public-coin interactive proofs

These definitions use the legacy prover and transcript representation. A supplied simulator
is compared with the honest verifier view; existential simulation has no computational bound.
The unique-witness lemma records the resulting zero-error collapse.

## References

* [Chiesa, A. and Orrù, M., *A Fiat--Shamir Transformation From Duplex Sponges*][CO25]

-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

/-- For every fixed instance–witness pair in the relation, every possible first honest prover
message occurs with probability at most `μ`. Intuitively, when `0 < μ < 1`, the first prover
message is somewhat random, with min-entropy at least `−log₂ μ`. The probability is taken only
over the prover's private randomness, and the prover has no public-oracle access. -/
def Prover.FirstMessageProbabilityBound
    {n : ℕ} {pSpec : ProtocolSpec (n + 1)} {StmtIn WitIn StmtOut WitOut : Type}
    (P : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hFirst : pSpec.StartsWithProverMessage) (relation : Set (StmtIn × WitIn))
    (μ : NNReal) : Prop :=
  ∀ stmt wit, (stmt, wit) ∈ relation → ∀ a,
    Pr{let result ← P.sendMessage ⟨0, hFirst⟩ (P.input (stmt, wit))}[result.1 = a] ≤
      (μ : ENNReal)

namespace Reduction

section Interactive

variable {n : ℕ} {pSpec : ProtocolSpec n}
  {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)]

/-- **[CO25, Definition 7.2]** The public-coin verifier's view. -/
abbrev IPVerifierView (StmtIn : Type) (pSpec : ProtocolSpec n) :=
  StmtIn × pSpec.FullTranscript

/-- Run the honest prover against a fixed complete tuple of public challenges, retaining the
messages visible in the verifier view. -/
def runProverWithChallenges
    (impl : QueryImpl oSpec ProbComp)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (challenges : pSpec.Challenges) :
    ProbComp pSpec.Messages := do
  let challengeImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp :=
    fun query => pure (challenges query.1)
  let ⟨transcript, _⟩ ←
    simulateQ (impl + challengeImpl) (prover.runToRound (Fin.last n) stmt wit)
  pure transcript.messages

/-- The public-coin honest-verifier view: the statement and complete transcript.

Each verifier message is sampled independently and uniformly, then revealed only at its turn.
The prover's private randomness and state are not returned. The final verifier check is not
executed: this view is unconditional and contains no acceptance decision. No verifier argument
is needed: the protocol specifies the message spaces, and this experiment samples them uniformly.
The ambient oracle interface `oSpec` is interpreted by `impl`. DSFS instantiates it with
`unifSpec` and its uniform-sampling handler, supplying the prover's private randomness here.
The finite challenge sampler chooses its enumeration classically, so this view is noncomputable. -/
noncomputable def honestVerifierView
    (impl : QueryImpl oSpec ProbComp)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) : ProbComp (IPVerifierView StmtIn pSpec) := by
  letI : Nonempty pSpec.Challenges := ⟨fun _ => default⟩
  letI : SampleableType pSpec.Challenges := SampleableType.ofFintype _
  exact do
    let challenges ← $ᵗ pSpec.Challenges
    let messages ← runProverWithChallenges impl prover stmt wit challenges
    pure (stmt, FullTranscript.ofMessagesChallenges messages challenges)

/-- **[CO25, Definition 7.3]** The simulator `S(𝕩)` takes a statement and returns a
verifier view. -/
abbrev HonestVerifierSimulator (StmtIn : Type) (pSpec : ProtocolSpec n) :=
  StmtIn → ProbComp (IPVerifierView StmtIn pSpec)

/-- **[CO25, Definition 7.3]** Statistical honest-verifier zero knowledge for a public-coin
interactive proof with a supplied simulator.

For each relation member `(stmt, wit)`, the honest and simulated verifier views have total
variation distance at most `error stmt`. A uniform bound is expressed by `error := fun _ => zIP`.
This is denoted `z_IP(𝕩)` in **[snarg-book, Definition 13.1.7]**.
The simulator receives only the statement. Discrepancies in the statement and transcript both
contribute to the distance. The views are unconditional and contain no verifier decision.
Efficiency of the supplied simulator requires a separate resource bound. -/
def honestVerifierZeroKnowledgeWithSimulator
    (impl : QueryImpl oSpec ProbComp)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (simulator : HonestVerifierSimulator StmtIn pSpec)
    (relation : Set (StmtIn × WitIn)) (error : StmtIn → ℝ) : Prop :=
  ∀ stmt wit, (stmt, wit) ∈ relation →
    discreteTVDist (honestVerifierView impl prover stmt wit) (simulator stmt) ≤ error stmt

/-- Existential honest-verifier zero knowledge. With unique witnesses and an inhabited witness
type, classical choice supplies a simulator with error zero for any prover
(`honestVerifierZeroKnowledge_of_uniqueWitness`). -/
def honestVerifierZeroKnowledge
    (impl : QueryImpl oSpec ProbComp)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (relation : Set (StmtIn × WitIn)) (error : StmtIn → ℝ) : Prop :=
  ∃ simulator, honestVerifierZeroKnowledgeWithSimulator impl prover simulator relation error

/-- For a relation with unique witnesses, a simulator can choose a witness classically and run
the honest prover, giving error zero for every prover. -/
theorem honestVerifierZeroKnowledge_of_uniqueWitness [Inhabited WitIn]
    (impl : QueryImpl oSpec ProbComp)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (relation : Set (StmtIn × WitIn))
    (hUnique : ∀ stmt wit wit', (stmt, wit) ∈ relation → (stmt, wit') ∈ relation → wit = wit') :
    honestVerifierZeroKnowledge impl prover relation (fun _ => 0) := by
  classical
  refine ⟨fun stmt => honestVerifierView impl prover stmt
    (if h : ∃ wit, (stmt, wit) ∈ relation then h.choose else default), ?_⟩
  intro stmt wit hMem
  have h : ∃ wit, (stmt, wit) ∈ relation := ⟨wit, hMem⟩
  change discreteTVDist (honestVerifierView impl prover stmt wit)
    (honestVerifierView impl prover stmt (if h : ∃ wit, (stmt, wit) ∈ relation
      then h.choose else default)) ≤ 0
  rw [dite_eq_left h, hUnique stmt _ _ h.choose_spec hMem, discreteTVDist.self]

/-- **[CO25, Definition 7.3; snarg-book, Definition 13.1.7]** The size-dependent HVZK
error envelope in the extended nonnegative reals. It is zero with no valid instances and
`⊤` for unbounded errors. For nonnegative errors, an attained maximum agrees with the paper.
This mathematical supremum is noncomputable. -/
noncomputable def honestVerifierErrorEnvelope (relation : Set (StmtIn × WitIn)) (size : StmtIn → ℕ)
    (error : StmtIn → ℝ) (n : ℕ) : ENNReal :=
  sSup {e | ∃ x w, (x, w) ∈ relation ∧ size x ≤ n ∧ e = ENNReal.ofReal (error x)}

end Interactive

end Reduction
