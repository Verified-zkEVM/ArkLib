/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.OracleVerifier
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Adversary models and completeness

A model supplies a class of adversaries and the subprobability law of each completed outcome.
The classical model interprets ambient queries with shared state and challenges with a separate
stateless implementation. Rejection is an outcome with a negative verdict; missing mass
remains missing mass. Completeness requires acceptance, matching output statements and a valid
output witness. The relation objects retain their explicit admissibility boundary.
-/

@[expose] public section

universe u uA v uS uW uI wI wJ dI q

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp Oracle MeasureTheory
open scoped ENNReal

/-- A claim problem with no additional public context. Context can be included in the statement. -/
abbrev StatementProblem (S : Type*) := Problem (⟨fun _ : Unit => S⟩ : ClaimFamily Unit)

/-- An adversary class and the outcome distribution it induces on each input. -/
structure AdversaryModel (S Obs : Type*) [MeasurableSpace Obs] where
  Adv : S → Type*
  outcome : (stmt : S) → Adv stmt → Measure Obs
  mass_le_one : ∀ stmt adv, outcome stmt adv Set.univ ≤ 1

/-- A claim problem whose claim type is indexed by a protocol's shape path. -/
abbrev PathProblem {P : PFunctor.{uA, u}} (s : FreeM P PUnit.{u + 1}) (T : Path s → Type v) :=
  Problem (⟨T⟩ : ClaimFamily (Path s))

/-- The path problem that judges a claim at every shape path by one statement problem. -/
abbrev StatementProblem.toPathProblem {P : PFunctor.{uA, u}} {S : Type v}
    (s : FreeM P PUnit.{u + 1}) (problem : StatementProblem S) : PathProblem s (fun _ => S) where
  Witness _ claim := problem.Witness () claim
  admissible _ claim := problem.admissible () claim
  rel _ claim wit := problem.rel () claim wit
  rel_admissible _ claim wit h := problem.rel_admissible () claim wit h

/-- The accepted claim and witness used to judge a completed outcome.

The claim type may depend on a public context read from the outcome, such as the shape path
of the run; a judgement with one claim type uses the context `Unit`. The witness may depend on the
context and the accepted claim. A rejected outcome need not supply one. The prover's claimed
statement is retained separately to state honest output agreement.
-/
structure OutputJudgement (Obs : Type*) {Ctx : Type*} {T : ClaimFamily Ctx} (P : Problem T) where
  /-- The public context of an outcome, which selects its claim type. -/
  context : Obs → Ctx
  /-- The verifier's verdict, a claim at the outcome's context. -/
  verdict : (obs : Obs) → Option (T.Claim (context obs))
  /-- The prover's claimed statement at the outcome's context. -/
  proverStatement : (obs : Obs) → T.Claim (context obs)
  /-- The witness judged against an accepted claim. -/
  witness : ∀ obs stmt, verdict obs = some stmt → P.Witness (context obs) stmt

/-- Judge an actual outcome using its verifier verdict and decoded prover output. The claim
type is indexed by the shape path of the outcome's transcript. -/
def OutputJudgement.ofOutcome {P : PFunctor.{uA, 0}}
    {l : PFunctor.Lens P rolePoly} {s : FreeM P PUnit}
    {Out : Transcript l s → Type} {T : Path s → Type} (output : PathProblem s T)
    (readStatement : ∀ tr, Out tr → T tr.path)
    (readWitness : ∀ obs : Outcome l s Out T, ∀ t,
      obs.2.2 = some t → output.Witness (Transcript.path obs.1) t) :
    OutputJudgement (Outcome l s Out T) output where
  context obs := Transcript.path obs.1
  verdict obs := obs.2.2
  proverStatement obs := readStatement obs.1 obs.2.1
  witness := readWitness

/-- Acceptance together with an output pair in the declared relation. -/
def OutputJudgement.valid {Obs Ctx : Type*} {T : ClaimFamily Ctx} {P : Problem T}
    (J : OutputJudgement Obs P) (obs : Obs) : Prop :=
  ∃ stmt, ∃ h : J.verdict obs = some stmt, P.rel (J.context obs) stmt (J.witness obs stmt h)

/-- Honest acceptance also requires the two parties to agree on the output statement. -/
def OutputJudgement.honest {Obs Ctx : Type*} {T : ClaimFamily Ctx} {P : Problem T}
    (J : OutputJudgement Obs P) (obs : Obs) : Prop :=
  ∃ stmt, ∃ h : J.verdict obs = some stmt,
    J.proverStatement obs = stmt ∧ P.rel (J.context obs) stmt (J.witness obs stmt h)

/-- Completeness is defined once over a model and an honest choice of its adversaries. -/
def completeness {S Obs Ctx : Type*} {T : ClaimFamily Ctx} [MeasurableSpace Obs]
    (M : AdversaryModel S Obs) (input : StatementProblem S) (output : Problem T)
    (J : OutputJudgement Obs output)
    (honest : ∀ stmt, input.Witness () stmt → M.Adv stmt) (ε : ℝ≥0∞) : Prop :=
  MeasurableSet {obs | J.honest obs} ∧
  ∀ stmt wit, input.rel () stmt wit →
    1 - ε ≤ M.outcome stmt (honest stmt wit) {obs | J.honest obs}

/-- Stateful ambient interpretation with a stateless challenge handler, as in the legacy game. -/
def experiment {ι κ σ α : Type} {ambient : OracleSpec ι} {chal : OracleSpec κ}
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (challengeQueryImpl : QueryImpl chal ProbComp) (program : OracleComp (ambient + chal) α) :
    ProbComp α := do
  let handler : QueryImpl (ambient + chal) (StateT σ ProbComp) :=
    QueryImpl.addLift impl challengeQueryImpl
  (simulateQ handler program).run' (← init)

/-- Running a mapped program in the experiment maps the experiment's result. -/
theorem experiment_map {ι κ σ α β : Type} {ambient : OracleSpec ι} {chal : OracleSpec κ}
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (challengeQueryImpl : QueryImpl chal ProbComp) (f : α → β)
    (program : OracleComp (ambient + chal) α) :
    experiment init impl challengeQueryImpl (f <$> program) =
      f <$> experiment init impl challengeQueryImpl program := by
  simp only [experiment, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
    _root_.map_bind]

/-- The usual fresh challenge implementation, sampled separately from shared oracle state. -/
@[simps]
def challengeQueryImpl {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly)
    (s : FreeM P PUnit) [∀ c, SampleableType (challengeSpec l s c)] :
    QueryImpl (challengeSpec l s) ProbComp where
  toFun c := $ᵗ (challengeSpec l s c)

/-- The default classical model contains every focal prover over the ambient oracle interface.
The input statement is an argument of the run, so its type may lie in any universe. -/
noncomputable def Verifier.classicalModel {ι σ : Type} {ambient : OracleSpec ι}
    {s : Protocol} {S : Type uS} {T : Path s → Type} {Out : Transcript plainSig s → Type}
    [MeasurableSpace (Outcome plainSig s Out T)]
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp) :
    AdversaryModel S (Outcome plainSig s Out T) where
  Adv _ := Prover plainSig ambient s Out
  outcome stmt adv := 𝒟[experiment init impl challenges (V.run stmt adv)]
  mass_le_one _ _ := evalDist_apply_univ_le_one _

/-- The classical oracle model also supplies the input oracle data to the run.

The verifier itself obtains that data only through its declared query interface. The input
statement, the input index and the input query type are arguments of the run, so they may lie in
any universe.
-/
noncomputable def OracleVerifier.classicalModel {ι σ : Type}
    {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, q}} {S : Type uS} {T : Path s → Type}
    {J : Path s → Type} {B : (p : Path s) → J p → Type}
    {inputs : OracleBundle.{0, uI, dI}}
    {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
    {Out : Transcript oracleSig s → Type}
    [MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T B))]
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp) :
    AdversaryModel (S × inputs.Data)
      (Outcome oracleSig s Out (OracleVerifier.Output T B)) where
  Adv _ := Prover oracleSig ambient s Out
  outcome stmt adv := 𝒟[experiment init impl challenges (V.run stmt.1 stmt.2 adv)]
  mass_le_one _ _ := evalDist_apply_univ_le_one _

/-- The ordinary reduction specializes model completeness without changing its experiment. The
output problem's claims are indexed by the shape path. The input statement and the honest input
witness are arguments of the run, so their types may lie in any universe. -/
abbrev Reduction.completeness {ι σ : Type} {S : Type uS} {W : Type uW} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type} {Out : Transcript plainSig s → Type}
    (R : Reduction ambient s S W T Out) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    (input : StatementProblem S) (output : PathProblem s T)
    (readStatement : ∀ tr, Out tr → T tr.path)
    (readWitness : ∀ obs : Outcome plainSig s Out T, ∀ t,
      obs.2.2 = some t → output.Witness (Transcript.path obs.1) t)
    (witness : ∀ stmt, input.Witness () stmt → W) (ε : ℝ≥0∞) : Prop :=
  letI : MeasurableSpace (Outcome plainSig s Out T) := ⊤
  Interaction.completeness (R.verifier.classicalModel init impl challenges) input output
    (OutputJudgement.ofOutcome output readStatement readWitness)
    (fun stmt w => R.prover stmt (witness stmt w)) ε

end Interaction
