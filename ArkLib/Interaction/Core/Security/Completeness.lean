/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.OracleVerifier
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Adversary models and completeness

A model supplies a class of adversaries and the subprobability law of each completed observation.
The classical model interprets ambient queries with shared state and challenges with a separate
stateless implementation. Rejection is an observation with a negative verdict; missing mass
remains missing mass. Completeness requires acceptance, matching output statements and a valid
output witness. The relation objects retain their explicit admissibility boundary.
-/

@[expose] public section

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle MeasureTheory
open scoped ENNReal

/-- A claim problem with no additional public context. Context can be included in the statement. -/
abbrev StatementProblem (S : Type*) := Problem (⟨fun _ : Unit => S⟩ : ClaimFamily Unit)

/-- An adversary class and the observation distribution it induces on each input. -/
structure AdversaryModel (S Obs : Type*) [MeasurableSpace Obs] where
  Adv : S → Type*
  outcome : (stmt : S) → Adv stmt → Measure Obs
  mass_le_one : ∀ stmt adv, outcome stmt adv Set.univ ≤ 1

/-- The accepted claim and witness used to judge a completed observation.

The witness may depend on the accepted claim. A rejected observation need not supply one.
The prover's claimed statement is retained separately to state honest output agreement.
-/
structure OutputJudgement (Obs T : Type*) (P : StatementProblem T) where
  verdict : Obs → Option T
  proverStatement : Obs → T
  witness : ∀ obs stmt, verdict obs = some stmt → P.Witness () stmt

/-- Judge an actual observation using its verifier verdict and decoded prover output. -/
def OutputJudgement.ofObservation {P : PFunctor.{1, 0}}
    {l : PFunctor.Lens P rolePoly} {s : FreeM P PUnit}
    {Out : PathAlong l s → Type} {T : Type} (output : StatementProblem T)
    (readStatement : ∀ tr, Out tr → T)
    (readWitness : ∀ obs : Observation l s Out T, ∀ t,
      obs.2.2 = some t → output.Witness () t) :
    OutputJudgement (Observation l s Out T) T output where
  verdict obs := obs.2.2
  proverStatement obs := readStatement obs.1 obs.2.1
  witness := readWitness

/-- Acceptance together with an output pair in the declared relation. -/
def OutputJudgement.valid {Obs T : Type*} {P : StatementProblem T}
    (J : OutputJudgement Obs T P) (obs : Obs) : Prop :=
  ∃ stmt, ∃ h : J.verdict obs = some stmt, P.rel () stmt (J.witness obs stmt h)

/-- Honest acceptance also requires the two parties to agree on the output statement. -/
def OutputJudgement.honest {Obs T : Type*} {P : StatementProblem T}
    (J : OutputJudgement Obs T P) (obs : Obs) : Prop :=
  ∃ stmt, ∃ h : J.verdict obs = some stmt,
    J.proverStatement obs = stmt ∧ P.rel () stmt (J.witness obs stmt h)

/-- Completeness is defined once over a model and an honest choice of its adversaries. -/
def completeness {S Obs T : Type*} [MeasurableSpace Obs]
    (M : AdversaryModel S Obs) (input : StatementProblem S) (output : StatementProblem T)
    (J : OutputJudgement Obs T output)
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

/-- The usual fresh challenge implementation, sampled separately from shared oracle state. -/
def challengeQueryImpl {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly)
    (s : FreeM P PUnit) [∀ c, SampleableType (challengeSpec l s c)] :
    QueryImpl (challengeSpec l s) ProbComp := fun c => $ᵗ (challengeSpec l s c)

/-- The default classical model contains every focal prover over the ambient oracle interface. -/
noncomputable def Verifier.classicalModel {ι σ : Type} {ambient : OracleSpec ι}
    {s : Protocol} {S T : Type} {Out : PathAlong plainSig s → Type}
    [MeasurableSpace (Observation plainSig s Out T)]
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp) :
    AdversaryModel S (Observation plainSig s Out T) where
  Adv _ := Prover plainSig ambient s Out
  outcome stmt adv := 𝒟[experiment init impl challenges (V.run stmt adv)]
  mass_le_one _ _ := evalDist_apply_univ_le_one _

/-- The classical oracle model also supplies the input oracle data to the run.

The verifier itself obtains that data only through its declared query interface.
-/
noncomputable def OracleVerifier.classicalModel {ι I J σ : Type} {ambient : OracleSpec ι}
    {s : OracleProtocol} {S T : Type} {A : I → Type} {B : J → Type}
    {inputs : OracleFamily I A} {outputs : OracleFamily J B}
    {Out : PathAlong oracleSig s → Type}
    [MeasurableSpace (Observation oracleSig s Out (T × (∀ j, B j)))]
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp) :
    AdversaryModel (S × (∀ i, A i)) (Observation oracleSig s Out (T × (∀ j, B j))) where
  Adv _ := Prover oracleSig ambient s Out
  outcome stmt adv := 𝒟[experiment init impl challenges (V.run stmt.1 stmt.2 adv)]
  mass_le_one _ _ := evalDist_apply_univ_le_one _

/-- The ordinary reduction specializes model completeness without changing its experiment. -/
abbrev Reduction.completeness {ι σ S W T : Type} {ambient : OracleSpec ι}
    {s : Protocol} {Out : PathAlong plainSig s → Type}
    (R : Reduction ambient s S W T Out) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    (input : StatementProblem S) (output : StatementProblem T)
    (readStatement : ∀ tr, Out tr → T)
    (readWitness : ∀ obs : Observation plainSig s Out T, ∀ t,
      obs.2.2 = some t → output.Witness () t)
    (witness : ∀ stmt, input.Witness () stmt → W) (ε : ℝ≥0∞) : Prop :=
  letI : MeasurableSpace (Observation plainSig s Out T) := ⊤
  Core.completeness (R.verifier.classicalModel init impl challenges) input output
    (OutputJudgement.ofObservation output readStatement readWitness)
    (fun stmt w => R.prover stmt (witness stmt w)) ε

end Interaction.Core
