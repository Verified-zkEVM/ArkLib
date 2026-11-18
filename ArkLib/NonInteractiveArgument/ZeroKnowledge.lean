/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.Security.PrivateCoins
public import VCVio.OracleComp.EvalDist.DiscreteTVDistBind
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Adaptive NARG zero knowledge

Both adversarial stages share one sampled public oracle. The simulator sees the original oracle
and returns a proof and a program; only the second stage sees the programmed oracle. Private
coins are neither counted as public queries nor programmed. A named simulator family is fixed
before all budgets and adversaries. The existential form imposes no computational bound, and
the unique-witness lemma records its zero-error collapse.

The Reduction namespace is retained for existing callers; the definitions use only OracleComp
and do not import either protocol representation.

## References

* [Chiesa, A. and Orrù, M., *A Fiat--Shamir Transformation From Duplex Sponges*][CO25]

-/

@[expose] public section

open OracleComp OracleSpec
open scoped NNReal ProbabilityTheory

namespace Reduction

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
