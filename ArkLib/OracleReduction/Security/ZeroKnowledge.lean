/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.OracleReduction.Security.OracleSampling
public import VCVio.OracleComp.EvalDist.DiscreteTVDistBind
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Zero-knowledge definitions

This file formalizes the transformation-independent definitions used in [CO25] Section 7.1.
It lives outside the duplex-sponge development because the public-coin view and the two-stage
adaptive NARG experiment can be reused by other Fiat--Shamir transformations.

## Paper correspondence

* `IPVerifierView` and `honestVerifierView` capture the information-theoretic content of
  the public-coin specialization of [CO25] Definition 7.2.
* `HonestVerifierSimulator` and `honestVerifierZeroKnowledgeWithSimulator` do the same for
  Definition 7.3.
* `NARGZKAdversary`, `adaptiveNARGZKRealExp`, `adaptiveNARGZKSimExp`, and
  `adaptiveNARGZeroKnowledgeWithSimulator` do the same for Definition 7.4.

The real and simulated experiments sample one public oracle shared by both adversarial stages.
The simulator sees the unprogrammed oracle and returns a proof and a program; only the second
adversarial stage sees the programmed oracle.  Private randomness is represented by an explicit
`unifSpec`, separate from the public oracle. The interface takes a `ProbComp Carrier` sampler,
a `Carrier → QueryImpl publicSpec ProbComp` interpreter and, for simulated experiments,
a programming function explicitly. No distribution wrapper is needed.

## Formalization boundary

The predicates for supplied simulators bound statistical distance. Efficiency requires a
separate resource bound. The public adaptive definition includes the security parameter,
instance-size bound, and query budget. The oracle model and algorithm types may vary with the
public parameters. One simulator family works for all relevant budgets and adversaries.
The programming operation is abstract here; a concrete transformation must define its program
type and prove the required consistency properties.

## References

* [Chiesa, A. and Orrù, M., *A Fiat--Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

noncomputable section

open OracleComp OracleSpec ProtocolSpec

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
`unifSpec` and its uniform-sampling handler, supplying the prover's private randomness here. -/
def honestVerifierView
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
error envelope. For nonnegative errors, when the maximum exists this is the paper's
maximum (with zero for no valid instances). Its use requires the displayed set to be
bounded above. -/
def honestVerifierErrorEnvelope (relation : Set (StmtIn × WitIn)) (size : StmtIn → ℕ)
    (error : StmtIn → ℝ) (n : ℕ) : ℝ :=
  sSup ({0} ∪ {e | ∃ x w, (x, w) ∈ relation ∧ size x ≤ n ∧ e = error x})

end Interactive

section AdaptiveNARG

variable {ιPublic : Type} {publicSpec : OracleSpec ιPublic}
  {StmtIn WitIn Proof Program Output : Type}

/-- **[CO25, Definition 7.4]** The two-stage adversary.

The subtype returned by `choose` makes admissibility structural: every possible first-stage output
satisfies `admissible stmt wit`.  Both stages have explicit private coins and access to the public
oracle. -/
structure NARGZKAdversary
    (publicSpec : OracleSpec ιPublic)
    (StmtIn WitIn Proof Output : Type) (admissible : StmtIn → WitIn → Prop) where
  State : Type
  choose : OracleComp (publicSpec + unifSpec)
    ({xw : StmtIn × WitIn // admissible xw.1 xw.2} × State)
  distinguish : State → Proof → OracleComp (publicSpec + unifSpec) Output

/-- A shared public-query budget for the two adaptive stages. The bound is checked on their
composition, so the second stage can use the budget left by the actual first-stage path.
It holds for every supplied NARG string; private-coin queries are ignored. The explicit prefix
bound also covers an empty NARG-string type, where the continuation condition would be vacuous. -/
def NARGZKAdversary.HasAggregateQueryBound
    {admissible : StmtIn → WitIn → Prop}
    (adversary : NARGZKAdversary
      publicSpec StmtIn WitIn Proof Output admissible)
    (counts : publicSpec.Domain → Prop) [DecidablePred counts]
    (budget : ℕ) : Prop := by
  classical
  let counted : (publicSpec + unifSpec).Domain → Prop := publicQuerySelector counts
  exact OracleComp.IsQueryBoundP adversary.choose counted budget ∧
    ∀ proof, OracleComp.IsQueryBoundP
      (adversary.choose >>= fun choice => adversary.distinguish choice.2 proof)
      counted budget

section

attribute [local instance] Classical.propDecidable

/-- Fixed stage bounds whose sum fits the budget suffice for the shared-budget predicate. -/
theorem NARGZKAdversary.hasAggregateQueryBound_of_stage_bounds
    {admissible : StmtIn → WitIn → Prop}
    (adversary : NARGZKAdversary
      publicSpec StmtIn WitIn Proof Output admissible)
    (counts : publicSpec.Domain → Prop) [DecidablePred counts]
    {chooseBudget distinguishBudget budget : ℕ}
    (hBudget : chooseBudget + distinguishBudget ≤ budget)
    (hChoose : OracleComp.IsQueryBoundP adversary.choose
      (publicQuerySelector counts) chooseBudget)
    (hDistinguish : ∀ state proof, OracleComp.IsQueryBoundP (adversary.distinguish state proof)
      (publicQuerySelector counts) distinguishBudget) :
    adversary.HasAggregateQueryBound counts budget := by
  constructor
  · exact hChoose.mono (m := budget) (by omega)
  · intro proof
    exact (OracleComp.isQueryBoundP_bind hChoose
      (fun choice _ => hDistinguish choice.2 proof)).mono hBudget

end

/-- An honest NARG prover with a syntactically separate private-coin oracle. -/
abbrev NARGZKProver
    (publicSpec : OracleSpec ιPublic)
    (StmtIn WitIn Proof : Type) :=
  StmtIn → WitIn → OracleComp (publicSpec + unifSpec) Proof

/-- **[CO25, Definition 7.4]** Expose a one-message ArkLib prover through the prover interface.

The post-protocol output is deliberately not executed: the NARG experiment observes only the
NARG string sent to the verifier. The resulting interface places public oracles before
private sampling. -/
def NonInteractiveProver.toNARGZKProver
    {ιPrivate : Type} {privateSpec : OracleSpec ιPrivate}
    {StmtOut WitOut : Type}
    (prover : NonInteractiveProver Proof (privateSpec + publicSpec)
      StmtIn WitIn StmtOut WitOut) :
    StmtIn → WitIn → OracleComp (publicSpec + privateSpec) Proof :=
  fun stmt wit => OracleComp.swapOracles do
    let state := prover.input (stmt, wit)
    let ⟨proof, _⟩ ← prover.sendMessage ⟨0, rfl⟩ state
    pure proof

/-- A NARG simulator returns a simulated NARG string and the program installed before the
second adversarial stage. It receives only the public statement. -/
abbrev NARGZKSimulator
    (publicSpec : OracleSpec ιPublic)
    (StmtIn Proof Program : Type) :=
  StmtIn → OracleComp (publicSpec + unifSpec) (Proof × Program)

/-- Compile a statement and interactive-protocol view into a NARG string and public-oracle
program, using the public oracles and private randomness. Used by `adaptiveNARGZKViewExp`. -/
abbrev NARGZKViewCompiler
    (publicSpec : OracleSpec ιPublic)
    (StmtIn View Proof Program : Type) :=
  StmtIn → View → OracleComp (publicSpec + unifSpec) (Proof × Program)

/-- Common prefix of all adaptive NARG zero-knowledge hybrids: sample one public oracle and run
the first adversarial stage against it. -/
def adaptiveNARGZKPrefix
    {admissible : StmtIn → WitIn → Prop}
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl publicSpec ProbComp)
    (adversary : NARGZKAdversary publicSpec StmtIn WitIn Proof Output admissible) :
    ProbComp
      (Carrier ×
        ({xw : StmtIn × WitIn // admissible xw.1 xw.2} × adversary.State)) := do
  let realization ← sampleOracle
  let choice ← simulateQ (oracleImpl realization + QueryImpl.id' unifSpec) adversary.choose
  pure (realization, choice)

/-- Common postprocessing of one supplied interactive view: compile it under the base oracle,
install the resulting program, and run the second adversarial stage. -/
def adaptiveNARGZKViewPostprocess
    {admissible : StmtIn → WitIn → Prop} {View : Type}
    {Carrier : Type}
    (oracleImpl : Carrier → QueryImpl publicSpec ProbComp)
    (programImpl : Carrier → Program → QueryImpl publicSpec ProbComp)
    (compiler : NARGZKViewCompiler
      publicSpec StmtIn View Proof Program)
    (adversary : NARGZKAdversary
      publicSpec StmtIn WitIn Proof Output admissible)
    (realization : Carrier) (state : adversary.State)
    (stmt : StmtIn) (sampledView : View) : ProbComp Output := do
  let ⟨proof, program⟩ ← simulateQ (oracleImpl realization + QueryImpl.id' unifSpec)
    (compiler stmt sampledView)
  simulateQ (programImpl realization program + QueryImpl.id' unifSpec)
    (adversary.distinguish state proof)

/-- An adaptive hybrid factored through an arbitrary interactive-view distribution.  The view is
sampled after the first adversarial stage; its compiler sees the original public oracle, while the
second stage sees the compiler's program installed into that same oracle realization. -/
def adaptiveNARGZKViewExp
    {admissible : StmtIn → WitIn → Prop} {View : Type}
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl publicSpec ProbComp)
    (programImpl : Carrier → Program → QueryImpl publicSpec ProbComp)
    (view : StmtIn → WitIn → ProbComp View)
    (compiler : NARGZKViewCompiler
      publicSpec StmtIn View Proof Program)
    (adversary : NARGZKAdversary
      publicSpec StmtIn WitIn Proof Output admissible) :
    ProbComp Output := do
  let ⟨realization, xw, state⟩ ← adaptiveNARGZKPrefix sampleOracle oracleImpl adversary
  let stmt := xw.1.1
  let wit := xw.1.2
  let sampledView ← view stmt wit
  adaptiveNARGZKViewPostprocess oracleImpl programImpl compiler adversary
    realization state stmt sampledView

/-- **[CO25, Claim 7.11, adapted]** If the view distributions are at distance at most `ε ≥ 0`
for every admissible instance–witness pair, their adaptive experiments are at distance at most `ε`.
Both experiments use the same oracle sampler, adversary, compiler, and programming operation. -/
theorem discreteTVDist_adaptiveNARGZKViewExp_le
    {admissible : StmtIn → WitIn → Prop} {View : Type}
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl publicSpec ProbComp)
    (programImpl : Carrier → Program → QueryImpl publicSpec ProbComp)
    (view₁ view₂ : StmtIn → WitIn → ProbComp View)
    (compiler : NARGZKViewCompiler
      publicSpec StmtIn View Proof Program)
    (adversary : NARGZKAdversary
      publicSpec StmtIn WitIn Proof Output admissible)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hView : ∀ stmt wit, admissible stmt wit →
      discreteTVDist (view₁ stmt wit) (view₂ stmt wit) ≤ ε) :
    discreteTVDist
      (adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl view₁ compiler adversary)
      (adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl view₂ compiler
        adversary) ≤ ε := by
  refine discreteTVDist.bind_bind_le_of_forall_le _ _ _ hε fun ⟨realization, xw, state⟩ => ?_
  exact (discreteTVDist.bind_le _ _ _).trans (hView xw.1.1 xw.1.2 xw.property)

/-- If the view distributions agree for every admissible instance–witness pair, the adaptive
experiments have the same output distribution, including the programmed second adversarial stage.
Distributions are compared as discrete measures. -/
theorem evalDist_adaptiveNARGZKViewExp_congr
    {admissible : StmtIn → WitIn → Prop} {View : Type}
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl publicSpec ProbComp)
    (programImpl : Carrier → Program → QueryImpl publicSpec ProbComp)
    (view₁ view₂ : StmtIn → WitIn → ProbComp View)
    (compiler : NARGZKViewCompiler
      publicSpec StmtIn View Proof Program)
    (adversary : NARGZKAdversary
      publicSpec StmtIn WitIn Proof Output admissible)
    (hView : ∀ stmt wit, admissible stmt wit →
      (letI : MeasurableSpace View := ⊤; 𝒟[view₁ stmt wit] = 𝒟[view₂ stmt wit])) :
    (letI : MeasurableSpace Output := ⊤;
      𝒟[adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl view₁ compiler
          adversary] =
        𝒟[adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl view₂ compiler
          adversary]) := by
  refine evalDistEq_iff_evalDist_eq.mp (.of_forall_prEvent_eq fun p => ?_)
  refine prEvent_bind_congr _ _ _ p p fun ⟨realization, xw, state⟩ => ?_
  let : MeasurableSpace View := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete,
    hView xw.1.1 xw.1.2 xw.property]

/-- **[CO25, Definition 7.4]** The real experiment. One sampled public-oracle realization is
shared by both adversarial stages and the honest prover. -/
def adaptiveNARGZKRealExp
    {admissible : StmtIn → WitIn → Prop}
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl publicSpec ProbComp)
    (prover : NARGZKProver publicSpec StmtIn WitIn Proof)
    (adversary : NARGZKAdversary publicSpec StmtIn WitIn Proof Output admissible) :
    ProbComp Output := do
  let realization ← sampleOracle
  let impl : QueryImpl (publicSpec + unifSpec) ProbComp :=
    oracleImpl realization + QueryImpl.id' unifSpec
  let ⟨xw, state⟩ ← simulateQ impl adversary.choose
  let proof ← simulateQ impl (prover xw.1.1 xw.1.2)
  simulateQ impl (adversary.distinguish state proof)

/-- **[CO25, Definition 7.4]** The simulated experiment. The first adversarial stage and
simulator see the original sampled oracle; only the second stage sees the programmed oracle
`f[mu]`. -/
def adaptiveNARGZKSimExp
    {admissible : StmtIn → WitIn → Prop}
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl publicSpec ProbComp)
    (programImpl : Carrier → Program → QueryImpl publicSpec ProbComp)
    (simulator : NARGZKSimulator publicSpec StmtIn Proof Program)
    (adversary : NARGZKAdversary publicSpec StmtIn WitIn Proof Output admissible) :
    ProbComp Output := do
  let realization ← sampleOracle
  let baseImpl : QueryImpl (publicSpec + unifSpec) ProbComp :=
    oracleImpl realization + QueryImpl.id' unifSpec
  let ⟨xw, state⟩ ← simulateQ baseImpl adversary.choose
  let ⟨proof, program⟩ ← simulateQ baseImpl (simulator xw.1.1)
  simulateQ (programImpl realization program + QueryImpl.id' unifSpec)
    (adversary.distinguish state proof)

end AdaptiveNARG

section Parameterized

variable {Statement Witness : Type}
  {ι Carrier NARGString Program : ℕ → ℕ → Type}
  (publicSpec : ∀ securityParameter sizeBound, OracleSpec (ι securityParameter sizeBound))
  (sampleOracle : ∀ securityParameter sizeBound, ProbComp (Carrier securityParameter sizeBound))
  (oracleImpl : ∀ securityParameter sizeBound, Carrier securityParameter sizeBound →
    QueryImpl (publicSpec securityParameter sizeBound) ProbComp)
  (programImpl : ∀ securityParameter sizeBound, Carrier securityParameter sizeBound →
    Program securityParameter sizeBound →
      QueryImpl (publicSpec securityParameter sizeBound) ProbComp)
  (prover : ∀ securityParameter sizeBound,
    NARGZKProver (publicSpec securityParameter sizeBound) Statement Witness
      (NARGString securityParameter sizeBound))
  (relation : Set (Statement × Witness)) (statementSize : Statement → ℕ)

/-- **[CO25, Definition 7.4; snarg-book, general-oracle adaptive zero knowledge]**
Adaptive statistical zero knowledge for a supplied simulator family and every public security
parameter, instance-size bound, and public-query budget. The sampled oracle models `D(λ,n)`.
Each adversary chooses a valid instance–witness pair of size at most `n`, and both stages share
the public-query budget. Efficiency of the supplied simulator requires a separate resource bound. -/
def adaptiveNARGZeroKnowledgeWithSimulator
    (simulator : ∀ securityParameter sizeBound,
      NARGZKSimulator (publicSpec securityParameter sizeBound) Statement
        (NARGString securityParameter sizeBound) (Program securityParameter sizeBound))
    (error : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ securityParameter sizeBound t (Output : Type)
    (adversary : NARGZKAdversary (publicSpec securityParameter sizeBound) Statement Witness
      (NARGString securityParameter sizeBound) Output
      (fun x w => (x, w) ∈ relation ∧ statementSize x ≤ sizeBound)),
    adversary.HasAggregateQueryBound (fun _ => True) t →
      discreteTVDist
        (adaptiveNARGZKRealExp (sampleOracle securityParameter sizeBound)
          (oracleImpl securityParameter sizeBound) (prover securityParameter sizeBound)
          adversary)
        (adaptiveNARGZKSimExp (sampleOracle securityParameter sizeBound)
          (oracleImpl securityParameter sizeBound) (programImpl securityParameter sizeBound)
          (simulator securityParameter sizeBound) adversary) ≤
        error securityParameter sizeBound t

/-- Existential adaptive NARG zero knowledge. A single simulator family works for every public
parameter, budget, output type, and adversary. For a relation with unique witnesses, an inhabited
witness type, and a no-op program, classical choice gives error zero for any prover
(`adaptiveNARGZeroKnowledge_of_uniqueWitness`). -/
def adaptiveNARGZeroKnowledge (error : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ simulator, adaptiveNARGZeroKnowledgeWithSimulator publicSpec sampleOracle oracleImpl
    programImpl prover relation statementSize simulator error

/-- For a relation with unique witnesses and a no-op oracle program, a simulator can choose
the witness classically and run the honest prover. This gives error zero even when the NARG
string reveals the witness. -/
theorem adaptiveNARGZeroKnowledge_of_uniqueWitness [Inhabited Witness]
    (noop : ∀ l n, Program l n)
    (hNoop : ∀ l n realization,
      programImpl l n realization (noop l n) = oracleImpl l n realization)
    (hUnique : ∀ stmt wit wit', (stmt, wit) ∈ relation → (stmt, wit') ∈ relation → wit = wit') :
    adaptiveNARGZeroKnowledge publicSpec sampleOracle oracleImpl programImpl prover
      relation statementSize (fun _ _ _ => 0) := by
  classical
  let witness : Statement → Witness := fun stmt =>
    if h : ∃ wit, (stmt, wit) ∈ relation then h.choose else default
  let simulator : ∀ l n, NARGZKSimulator (publicSpec l n) Statement
      (NARGString l n) (Program l n) := fun l n stmt =>
    (fun proof => (proof, noop l n)) <$> prover l n stmt (witness stmt)
  refine ⟨simulator, ?_⟩
  intro l n _ Output adversary _
  have hExp :
      adaptiveNARGZKRealExp (sampleOracle l n) (oracleImpl l n) (prover l n) adversary =
        adaptiveNARGZKSimExp (sampleOracle l n) (oracleImpl l n) (programImpl l n)
          (simulator l n) adversary := by
    unfold adaptiveNARGZKRealExp adaptiveNARGZKSimExp
    refine bind_congr fun realization => bind_congr fun ⟨xw, state⟩ => ?_
    have h : ∃ wit, (xw.1.1, wit) ∈ relation := ⟨xw.1.2, xw.property.1⟩
    have hWitness : witness xw.1.1 = xw.1.2 := by
      simpa only [witness, dite_eq_left h] using hUnique _ _ _ h.choose_spec xw.property.1
    simp [simulator, hWitness, simulateQ_map, hNoop]
  rw [hExp, discreteTVDist.self]

variable {publicSpec sampleOracle oracleImpl programImpl prover relation statementSize}

/-- Pure NARG-string encoding preserves the bound for the simulator that encodes its output
and retains its programming instructions. -/
theorem adaptiveNARGZeroKnowledgeWithSimulator.map {Encoded : ℕ → ℕ → Type}
    {simulator : ∀ l n, NARGZKSimulator (publicSpec l n) Statement
      (NARGString l n) (Program l n)}
    (encode : ∀ l n, NARGString l n → Encoded l n) {error : ℕ → ℕ → ℕ → ℝ}
    (h : adaptiveNARGZeroKnowledgeWithSimulator publicSpec sampleOracle oracleImpl programImpl
      prover relation statementSize simulator error) :
    adaptiveNARGZeroKnowledgeWithSimulator publicSpec sampleOracle oracleImpl programImpl
      (fun l n stmt wit => encode l n <$> prover l n stmt wit)
      relation statementSize
      (fun l n stmt => (fun result => (encode l n result.1, result.2)) <$> simulator l n stmt)
      error := by
  intro l n t Output adversary hQueries
  let reduced : NARGZKAdversary (publicSpec l n) Statement Witness (NARGString l n) Output
      (fun x w => (x, w) ∈ relation ∧ statementSize x ≤ n) :=
    { State := adversary.State
      choose := adversary.choose
      distinguish := fun state payload => adversary.distinguish state (encode l n payload) }
  have hr : reduced.HasAggregateQueryBound (fun _ => True) t :=
    ⟨hQueries.1, fun payload => hQueries.2 (encode l n payload)⟩
  have bound := h l n t Output reduced hr
  simpa [adaptiveNARGZKRealExp, adaptiveNARGZKSimExp, reduced, simulateQ_map,
    bind_map_left] using bound

/-- Pure NARG-string encoding preserves existential zero knowledge with the same error and
aggregate public-query budget. -/
theorem adaptiveNARGZeroKnowledge.map {Encoded : ℕ → ℕ → Type}
    (encode : ∀ l n, NARGString l n → Encoded l n) {error : ℕ → ℕ → ℕ → ℝ}
    (h : adaptiveNARGZeroKnowledge publicSpec sampleOracle oracleImpl programImpl prover
      relation statementSize error) :
    adaptiveNARGZeroKnowledge publicSpec sampleOracle oracleImpl programImpl
      (fun l n stmt wit => encode l n <$> prover l n stmt wit)
      relation statementSize error := by
  obtain ⟨simulator, hSimulator⟩ := h
  exact ⟨_, hSimulator.map encode⟩

end Parameterized

end Reduction
