/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.LiftContext
public import ArkLib.Interaction.Composition

/-!
# Lifting oracle verifiers into a larger context

An oracle statement lens adds two oracle maps to a statement lens. The input map answers the
inner input oracles from the outer ones. The output map builds the outer output oracles from the
outer inputs and the inner outputs. Both see only the outer input statement.

`OracleVerifier.liftContext` runs the inner decision with its bundle queries routed through the
input map, beside the path's oracle messages, and lifts an accepted output statement. Bundle
queries still happen only in the decision. The lifted output map is the lens's output map after
the fan-out `OracleMap.pair` of the outer inputs and the routed inner output map.

The materialized statement lens `OracleStatementLens.toStatementLens` acts on statements paired
with their oracle data. A lifted run is a post-map of the inner run along it
(`OracleVerifier.liftContext_run`), so the conditions and transfers of
`ArkLib.Interaction.LiftContext` apply with the compatibility predicate
`OracleVerifier.Compatible`.
-/

@[expose] public section

universe u q uι uS uS' uI uI' dI dI' wJ wJ' uX uY uZ dX dY dZ uW uW' uO uO' uK

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp Oracle
open scoped ENNReal

/-- Answer two bundles' queries from the same input bundle. -/
def OracleMap.pair {In : OracleBundle.{u, uX, dX}} {Mid : OracleBundle.{u, uY, dY}}
    {Out : OracleBundle.{u, uZ, dZ}} (h : OracleMap In Mid) (g : OracleMap In Out) :
    OracleMap In (Mid.sum Out) where
  f x := (h.f x, g.f x)
  impl
    | .inl q => h.impl q
    | .inr q => g.impl q
  law x q := by
    cases q with
    | inl q => exact h.law x q
    | inr q => exact g.law x q

/-- A statement lens with oracle maps for the input and output oracles. The input map answers
inner input queries from outer input data. The output map builds the outer output oracles from
the outer input oracles and the inner output oracles. -/
structure OracleStatementLens (s : OracleProtocol.{u, q}) (OuterIn : Type uS)
    (InnerIn : Type uS') (OuterOut InnerOut : Path s → Type u)
    (inputsO : OracleBundle.{u, uI, dI}) (inputsI : OracleBundle.{u, uI', dI'})
    {JO JI : Path s → Type u}
    {BO : (p : Path s) → JO p → Type u} {BI : (p : Path s) → JI p → Type u}
    (outputsO : (p : Path s) → OracleFamily.{u, u, wJ} (JO p) (BO p))
    (outputsI : (p : Path s) → OracleFamily.{u, u, wJ'} (JI p) (BI p)) where
  /-- The statement part. -/
  stmt : StatementLens s OuterIn InnerIn OuterOut InnerOut
  /-- Inner input oracles, answered from outer input oracles. -/
  projOracle : OuterIn → OracleMap inputsO inputsI
  /-- Outer output oracles, built from outer input oracles and inner output oracles. -/
  liftOracle : OuterIn → (p : Path s) →
    OracleMap (inputsO.sum (OracleBundle.ofFamily (outputsI p)))
      (OracleBundle.ofFamily (outputsO p))

namespace OracleStatementLens

variable {s : OracleProtocol.{u, q}} {OuterIn : Type uS} {InnerIn : Type uS'}
  {OuterOut InnerOut : Path s → Type u}
  {inputsO : OracleBundle.{u, uI, dI}} {inputsI : OracleBundle.{u, uI', dI'}}
  {JO JI : Path s → Type u}
  {BO : (p : Path s) → JO p → Type u} {BI : (p : Path s) → JI p → Type u}
  {outputsO : (p : Path s) → OracleFamily.{u, u, wJ} (JO p) (BO p)}
  {outputsI : (p : Path s) → OracleFamily.{u, u, wJ'} (JI p) (BI p)}

/-- The statement lens on statements paired with their oracle data. -/
def toStatementLens
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI) :
    StatementLens s (OuterIn × inputsO.Data) (InnerIn × inputsI.Data)
      (OracleVerifier.Output OuterOut BO) (OracleVerifier.Output InnerOut BI) where
  proj x := (lens.stmt.proj x.1, (lens.projOracle x.1).f x.2)
  lift x p o := (lens.stmt.lift x.1 p o.1, (lens.liftOracle x.1 p).f (x.2, o.2))

/-- Route a decision's bundle at a path: input queries through the input map, oracle-message
queries unchanged. -/
def inputRoute
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI) (stmt : OuterIn) (p : Path s) :
    OracleMap (pathBundle inputsO s p) (pathBundle inputsI s p) :=
  (lens.projOracle stmt).par (OracleMap.id _)

/-- The extractor lens on statements paired with their oracle data. -/
def toExtractorLens
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI)
    {OuterWitIn : OuterIn × inputsO.Data → Type uW} {InnerWitIn : InnerIn × inputsI.Data → Type uW'}
    {OuterWitOut : OuterIn × inputsO.Data → Transcript oracleSig s → Type uO}
    {InnerWitOut : InnerIn × inputsI.Data → Transcript oracleSig s → Type uO'}
    (witOutProj : ∀ x tr, OuterWitOut x tr → InnerWitOut (lens.toStatementLens.proj x) tr)
    (witInLift : ∀ x tr, OuterWitOut x tr → InnerWitIn (lens.toStatementLens.proj x) →
      OuterWitIn x) :
    ExtractorLens oracleSig s (OuterIn × inputsO.Data) (InnerIn × inputsI.Data)
      (OracleVerifier.Output OuterOut BO) (OracleVerifier.Output InnerOut BI)
      OuterWitIn InnerWitIn OuterWitOut InnerWitOut where
  stmt := lens.toStatementLens
  witOutProj := witOutProj
  witInLift := witInLift

end OracleStatementLens

namespace OracleVerifier

section Lift

variable {ι : Type uι} {ambient : OracleSpec.{uι, u} ι}
  {s : OracleProtocol.{u, q}} {OuterIn : Type uS} {InnerIn : Type uS'}
  {OuterOut InnerOut : Path s → Type u}
  {inputsO : OracleBundle.{u, uI, dI}} {inputsI : OracleBundle.{u, uI', dI'}}
  {JO JI : Path s → Type u}
  {BO : (p : Path s) → JO p → Type u} {BI : (p : Path s) → JI p → Type u}
  {outputsO : (p : Path s) → OracleFamily.{u, u, wJ} (JO p) (BO p)}
  {outputsI : (p : Path s) → OracleFamily.{u, u, wJ'} (JI p) (BI p)}

/-- Decide with the inner verifier on the projected statement, routing its input queries
through the lens's input map, and lift an accepted output. The output map is the lens's output
map after the outer inputs and the routed inner output map. -/
def liftContext
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI)
    (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI) :
    OracleVerifier ambient s OuterIn OuterOut inputsO outputsO where
  decide stmt p v := lens.stmt.lift stmt p <$> OptionT.mk
    (simulateQ ((lens.inputRoute stmt p).withAmbient ambient)
      (V.decide (lens.stmt.proj stmt) p v).run)
  outputMap stmt p v := (lens.liftOracle stmt p).comp
    ((OracleMap.fst inputsO _).pair
      ((V.outputMap (lens.stmt.proj stmt) p v).comp (lens.inputRoute stmt p)))

/-- The lifted decision on concrete data is the inner decision on the routed data, with an
accepted output lifted. -/
theorem liftContext_decideWith
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI)
    (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI) (stmt : OuterIn)
    (p : Path s) (v : View s p) (data : (pathBundle inputsO s p).Data) :
    (V.liftContext lens).decideWith stmt p v data =
      Option.map (lens.stmt.lift stmt p) <$>
        V.decideWith (lens.stmt.proj stmt) p v ((lens.inputRoute stmt p).f data) := by
  simp only [decideWith, liftContext, OptionT.run_map, OptionT.run_mk, simulateQ_map]
  congr 1
  exact OracleMap.simulate_withAmbient (lens.inputRoute stmt p) data _

/-- The lifted output data is the lens's output map applied to the outer inputs and the inner
output data on the routed data. -/
theorem liftContext_outputMap_f
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI)
    (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI) (stmt : OuterIn)
    (p : Path s) (v : View s p) (data : (pathBundle inputsO s p).Data) :
    ((V.liftContext lens).outputMap stmt p v).f data =
      (lens.liftOracle stmt p).f
        (data.1, (V.outputMap (lens.stmt.proj stmt) p v).f ((lens.inputRoute stmt p).f data)) :=
  rfl

/-- An inner output, with its output data, is compatible with an inner input and its data at a
path when the decision can return the statement on some view and oracle messages of that path,
and the data is the output map's value there. -/
def Compatible (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI)
    (stmt : InnerIn × inputsI.Data) (p : Path s) (t : OracleVerifier.Output InnerOut BI p) :
    Prop :=
  ∃ (v : View s p) (msgs : ∀ i, OracleMessage s p i),
    some t.1 ∈ support (V.decideWith stmt.1 p v (stmt.2, msgs)) ∧
      t.2 = (V.outputMap stmt.1 p v).f (stmt.2, msgs)

end Lift

section Run

variable {ι : Type u} {ambient : OracleSpec.{u, u} ι}
  {s : OracleProtocol.{u, q}} {OuterIn : Type uS} {InnerIn : Type uS'}
  {OuterOut InnerOut : Path s → Type u}
  {inputsO : OracleBundle.{u, uI, dI}} {inputsI : OracleBundle.{u, uI', dI'}}
  {JO : Path s → Type u} {JI : Path s → Type u}
  {BO : (p : Path s) → JO p → Type u} {BI : (p : Path s) → JI p → Type u}
  {outputsO : (p : Path s) → OracleFamily.{u, u, wJ} (JO p) (BO p)}
  {outputsI : (p : Path s) → OracleFamily.{u, u, wJ'} (JI p) (BI p)}
  {Out : Transcript oracleSig s → Type u}

/-- A lifted oracle verifier's run against any prover is the inner run on the projected
statement and data, with an accepted output and its data lifted. -/
theorem liftContext_run
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI)
    (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI) (stmt : OuterIn)
    (data : inputsO.Data) (prover : Prover oracleSig ambient s Out) :
    (V.liftContext lens).run stmt data prover =
      (fun obs => ⟨obs.1, obs.2.1,
          obs.2.2.map (lens.toStatementLens.lift (stmt, data) obs.1.path)⟩) <$>
        V.run (lens.stmt.proj stmt) ((lens.projOracle stmt).f data) prover := by
  rw [run_eq_decideWith, run_eq_decideWith]
  simp only [liftContext_decideWith, simulateQ_map]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun r => ?_
  obtain ⟨tr, out, ⟨⟩⟩ := r
  refine bind_congr fun o => ?_
  cases o <;> rfl

/-- Running against a prover with a mapped output maps the prover output of the outcome. -/
theorem run_mapOutput (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI)
    (stmt : InnerIn) (data : inputsI.Data) {A B : Transcript oracleSig s → Type u}
    (f : ∀ tr, A tr → B tr) (prover : Prover oracleSig ambient s A) :
    V.run stmt data (Strategy.mapOutput f prover) =
      (fun obs => ⟨obs.1, f obs.1 obs.2.1, obs.2.2⟩) <$> V.run stmt data prover := by
  rw [run_eq_decideWith, run_eq_decideWith, Prover.simulate_mapOutput, run_mapOutput_focal]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun r => ?_
  obtain ⟨tr, a, ⟨⟩⟩ := r
  simp

/-- Every accepted output of a run, with its output data, is compatible with the input statement
and data. -/
theorem compatible_of_mem_support_run
    (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI) (stmt : InnerIn)
    (data : inputsI.Data) (prover : Prover oracleSig ambient s Out)
    {obs : Outcome oracleSig s Out (OracleVerifier.Output InnerOut BI)}
    (h : obs ∈ support (V.run stmt data prover)) {t : OracleVerifier.Output InnerOut BI obs.1.path}
    (ht : obs.2.2 = some t) : V.Compatible (stmt, data) obs.1.path t := by
  rw [run_eq_decideWith] at h
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
  obtain ⟨⟨tr, out, ⟨⟩⟩, -, verdict, hv, rfl⟩ := h
  obtain ⟨t', rfl, rfl⟩ := Option.map_eq_some_iff.mp ht
  exact ⟨toView s tr, oracleMessages s tr, support_simulateQ_subset _ _ hv, rfl⟩

end Run

section Security

variable {ι σ : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, q}}
  {OuterIn : Type uS} {InnerIn : Type uS'} {OuterOut InnerOut : Path s → Type}
  {inputsO : OracleBundle.{0, uI, dI}} {inputsI : OracleBundle.{0, uI', dI'}}
  {JO : Path s → Type} {JI : Path s → Type}
  {BO : (p : Path s) → JO p → Type} {BI : (p : Path s) → JI p → Type}
  {outputsO : (p : Path s) → OracleFamily.{0, 0, wJ} (JO p) (BO p)}
  {outputsI : (p : Path s) → OracleFamily.{0, 0, wJ'} (JI p) (BI p)}

/-- Every accepted output with positive acceptance probability is compatible with its input
statement and data. -/
theorem compatible_of_mem_support_simulateQ
    (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (stmt : InnerIn × inputsI.Data)
    (tr : Transcript oracleSig s) {state final : σ} {t : InnerOut tr.path}
    (h : (some t, final) ∈ support ((simulateQ impl (V.decideWith stmt.1 tr.path
      (toView s tr) (stmt.2, oracleMessages s tr))).run state)) :
    V.Compatible stmt tr.path
      (t, (V.outputMap stmt.1 tr.path (toView s tr)).f (stmt.2, oracleMessages s tr)) :=
  ⟨toView s tr, oracleMessages s tr, mem_support_of_mem_support_simulateQ_run impl _ state h, rfl⟩

/-- The lifted decision accepts with positive probability exactly when the inner decision
accepts, at the projected statement and data, an output whose lift satisfies the event. -/
theorem validAcceptance_liftContext
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI)
    (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (stmt : OuterIn × inputsO.Data)
    (tr : Transcript oracleSig s) (event : OracleVerifier.Output OuterOut BO tr.path → Prop) :
    (V.liftContext lens).validAcceptance impl stmt tr event ↔
      V.validAcceptance impl (lens.toStatementLens.proj stmt) tr
        (fun t => event (lens.toStatementLens.lift stmt tr.path t)) := by
  rw [validAcceptance_iff_support, validAcceptance_iff_support]
  simp only [liftContext_decideWith, simulateQ_map, StateT.run_map, _root_.support_map,
    Set.mem_image,
    Prod.mk.injEq]
  constructor
  · rintro ⟨state, t, final, ⟨⟨o, final'⟩, hmem, ho, rfl⟩, ht⟩
    obtain ⟨t', rfl, rfl⟩ := Option.map_eq_some_iff.mp ho
    exact ⟨state, t', final', hmem, ht⟩
  · rintro ⟨state, t, final, hmem, ht⟩
    exact ⟨state, _, final, ⟨⟨some t, final⟩, hmem, rfl, rfl⟩, ht⟩

/-- Oracle soundness lifts along a sound materialized statement lens, at the same error. -/
theorem liftContext_soundness
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI)
    (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp)
    {inputO : StatementProblem (OuterIn × inputsO.Data)}
    {inputI : StatementProblem (InnerIn × inputsI.Data)}
    {outputO : PathProblem s (OracleVerifier.Output OuterOut BO)}
    {outputI : PathProblem s (OracleVerifier.Output InnerOut BI)} {ε : ℝ≥0∞}
    (hlens : lens.toStatementLens.IsSound inputO inputI outputO outputI V.Compatible)
    (h : V.soundness init impl challenges inputI outputI ε) :
    (V.liftContext lens).soundness init impl challenges inputO outputO ε := by
  rw [soundness_iff_soundnessUsing] at h ⊢
  intro Out stmt hadm hlang p
  obtain ⟨hadmI, hlangI⟩ := hlens.proj_sound stmt hadm hlang
  refine le_trans ?_ (h Out (lens.toStatementLens.proj stmt) hadmI hlangI p)
  rw [liftContext_run]
  dsimp only
  rw [experiment_map]
  refine prEvent_map_le_of_support _ _ _ _ fun obs hobs => ?_
  rintro ⟨t, ht, hout⟩
  obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
  refine ⟨t', ht', hlens.lift_sound stmt _ t' hadm hlang ?_ hout⟩
  exact V.compatible_of_mem_support_run _ _ p (support_experiment_subset _ _ _ _ hobs) ht'

/-- Oracle completeness lifts along a complete context lens on statements paired with their
oracle data, at the same error. With `ε = 0` this is the transfer of perfect completeness. -/
theorem liftContext_completeness {OuterWit : Type uW} {InnerWit : Type uW'}
    {OuterO InnerO : Transcript oracleSig s → Type}
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI)
    (witLens : WitnessLens oracleSig s (OuterIn × inputsO.Data) OuterWit InnerWit OuterO InnerO)
    (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI)
    (prover : InnerIn × inputsI.Data → InnerWit → Prover oracleSig ambient s InnerO)
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp)
    {inputO : StatementProblem (OuterIn × inputsO.Data)}
    {inputI : StatementProblem (InnerIn × inputsI.Data)}
    {outputO : PathProblem s (OracleVerifier.Output OuterOut BO)}
    {outputI : PathProblem s (OracleVerifier.Output InnerOut BI)}
    {readStatementO : ∀ tr, OuterO tr → OracleVerifier.Output OuterOut BO tr.path}
    {readStatementI : ∀ tr, InnerO tr → OracleVerifier.Output InnerOut BI tr.path}
    {readWitnessO : ∀ obs : Outcome oracleSig s OuterO (OracleVerifier.Output OuterOut BO), ∀ t,
      obs.2.2 = some t → outputO.Witness (Transcript.path obs.1) t}
    {readWitnessI : ∀ obs : Outcome oracleSig s InnerO (OracleVerifier.Output InnerOut BI), ∀ t,
      obs.2.2 = some t → outputI.Witness (Transcript.path obs.1) t}
    {witnessO : ∀ stmt, inputO.Witness () stmt → OuterWit}
    {witnessI : ∀ stmt, inputI.Witness () stmt → InnerWit} {ε : ℝ≥0∞}
    (hlens : ContextLens.IsComplete ⟨lens.toStatementLens, witLens⟩ inputO inputI witnessO
      witnessI (OutputJudgement.ofOutcome outputO readStatementO readWitnessO).honest
      (OutputJudgement.ofOutcome outputI readStatementI readWitnessI).honest V.Compatible)
    (h : letI : MeasurableSpace (Outcome oracleSig s InnerO
          (OracleVerifier.Output InnerOut BI)) := ⊤
      Interaction.completeness (V.classicalModel init impl challenges) inputI outputI
        (OutputJudgement.ofOutcome outputI readStatementI readWitnessI)
        (fun x w => prover x (witnessI x w)) ε) :
    letI : MeasurableSpace (Outcome oracleSig s OuterO
        (OracleVerifier.Output OuterOut BO)) := ⊤
    Interaction.completeness ((V.liftContext lens).classicalModel init impl challenges) inputO
      outputO (OutputJudgement.ofOutcome outputO readStatementO readWitnessO)
      (fun x w => Prover.liftContext lens.toStatementLens.proj witLens prover x (witnessO x w))
      ε := by
  let : MeasurableSpace (Outcome oracleSig s OuterO (OracleVerifier.Output OuterOut BO)) := ⊤
  let : MeasurableSpace (Outcome oracleSig s InnerO (OracleVerifier.Output InnerOut BI)) := ⊤
  refine ⟨MeasurableSpace.measurableSet_top, fun stmt w hrel => ?_⟩
  obtain ⟨w', hrel', hw'⟩ := hlens.proj_complete stmt w hrel
  have hI := h.2 _ w' hrel'
  change 1 - ε ≤ 𝒟[experiment init impl challenges
    ((V.liftContext lens).run stmt.1 stmt.2
      (Strategy.mapOutput (witLens.lift stmt (witnessO stmt w))
        (prover (lens.toStatementLens.proj stmt) (witLens.proj stmt (witnessO stmt w)))))] _
  change 1 - ε ≤ 𝒟[experiment init impl challenges
    (V.run (lens.toStatementLens.proj stmt).1 (lens.toStatementLens.proj stmt).2
      (prover (lens.toStatementLens.proj stmt) (witnessI _ w')))] _ at hI
  rw [hw'] at hI
  rw [liftContext_run, run_mapOutput, Functor.map_map, experiment_map]
  rw [← prEvent_eq_evalDist_of_discrete] at hI ⊢
  refine le_trans hI (prEvent_le_map_of_support _ _ _ _ fun obs hobs hhon => ?_)
  obtain ⟨tr, o, verdict⟩ := obs
  cases verdict with
  | none =>
    obtain ⟨t, ht, _⟩ := hhon
    exact absurd ht (by simp [OutputJudgement.ofOutcome])
  | some t =>
    exact hlens.lift_complete stmt w hrel tr o t
      (V.compatible_of_mem_support_run _ _ _ (support_experiment_subset _ _ _ _ hobs) rfl) hhon

/-- Oracle round-by-round soundness lifts along a sound materialized statement lens, with the
same draw and error. -/
theorem liftContext_rbrSoundness
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI)
    (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    {inputO : StatementProblem (OuterIn × inputsO.Data)}
    {inputI : StatementProblem (InnerIn × inputsI.Data)}
    {outputO : PathProblem s (OracleVerifier.Output OuterOut BO)}
    {outputI : PathProblem s (OracleVerifier.Output InnerOut BI)}
    {draw : QueryImpl (challengeSpec oracleSig s) ProbComp}
    {ε : ChallengeNode oracleSig s → ℝ≥0∞}
    (hlens : lens.toStatementLens.IsSound inputO inputI outputO outputI V.Compatible)
    (h : V.rbrSoundness impl inputI outputI draw ε) :
    (V.liftContext lens).rbrSoundness impl inputO outputO draw ε := by
  refine rbrSoundness_liftContext lens.toStatementLens.proj hlens.proj_sound
    (fun x tr hadm hlang hacc => ?_) h
  rw [validAcceptance_liftContext, validAcceptance_iff_support] at hacc
  rw [validAcceptance_iff_support]
  obtain ⟨state, t, final, hmem, hout⟩ := hacc
  exact ⟨state, t, final, hmem, hlens.lift_sound x _ _ hadm hlang
    (V.compatible_of_mem_support_simulateQ impl _ tr hmem) hout⟩

/-- Oracle round-by-round knowledge soundness lifts along a knowledge-sound extractor lens on
statements paired with their oracle data, with the same draw and error. -/
theorem liftContext_rbrKnowledgeSoundness
    {OuterWitIn : OuterIn × inputsO.Data → Type uW} {InnerWitIn : InnerIn × inputsI.Data → Type uW'}
    {OuterWitOut : OuterIn × inputsO.Data → Transcript oracleSig s → Type uO}
    {InnerWitOut : InnerIn × inputsI.Data → Transcript oracleSig s → Type uO'}
    (lens : OracleStatementLens s OuterIn InnerIn OuterOut InnerOut inputsO inputsI outputsO
      outputsI)
    (witOutProj : ∀ x tr, OuterWitOut x tr → InnerWitOut (lens.toStatementLens.proj x) tr)
    (witInLift : ∀ x tr, OuterWitOut x tr → InnerWitIn (lens.toStatementLens.proj x) →
      OuterWitIn x)
    (V : OracleVerifier ambient s InnerIn InnerOut inputsI outputsI)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    {admissibleO : OuterIn × inputsO.Data → Prop} {admissibleI : InnerIn × inputsI.Data → Prop}
    {relInO : (stmt : OuterIn × inputsO.Data) → OuterWitIn stmt → Prop}
    {relInI : (stmt : InnerIn × inputsI.Data) → InnerWitIn stmt → Prop}
    {relOutO : (stmt : OuterIn × inputsO.Data) → (tr : Transcript oracleSig s) →
      OracleVerifier.Output OuterOut BO tr.path → OuterWitOut stmt tr → Prop}
    {relOutI : (stmt : InnerIn × inputsI.Data) → (tr : Transcript oracleSig s) →
      OracleVerifier.Output InnerOut BI tr.path → InnerWitOut stmt tr → Prop}
    {draw : PrefixDraw viewSig ProbComp s} {ε : PrefixError oracleSig s}
    (hlens : (lens.toExtractorLens witOutProj witInLift).IsKnowledgeSound admissibleO admissibleI
      relInO relInI relOutO relOutI V.Compatible)
    (h : V.rbrKnowledgeSoundness.{uS', uW', uK, uO', uI', wJ', dI', q} impl admissibleI relInI
      relOutI draw ε) :
    (V.liftContext lens).rbrKnowledgeSoundness.{uS, uW, max uO uK, uO, uI, wJ, dI, q} impl
      admissibleO relInO relOutO draw ε := by
  refine rbrKnowledgeSoundness_liftContext lens.toStatementLens.proj witOutProj witInLift
    hlens.proj_admissible hlens.lift_knowledgeSound (fun x tr wo hacc => ?_) h
  rw [validAcceptance_liftContext, validAcceptance_iff_support] at hacc
  obtain ⟨state, t, final, hmem, hout⟩ := hacc
  refine (hlens.proj_knowledgeSound x tr _ wo
    (V.compatible_of_mem_support_simulateQ impl _ tr hmem) hout).imp (fun hI => ?_) id
  rw [validAcceptance_iff_support]
  exact ⟨state, t, final, hmem, hI⟩

end Security

end OracleVerifier

end Interaction
