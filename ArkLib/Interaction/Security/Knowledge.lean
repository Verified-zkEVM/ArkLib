/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Security.Soundness
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Extraction interfaces and knowledge soundness

An extraction interface specifies programs, their joint outcome/witness experiment and their
adversary-access cost. Knowledge soundness requires that the experiment preserve the model's
outcome marginal. The classical straight-line interface runs after acceptance, with the
full transcript and separate ambient query logs, so it always preserves the outcome
marginal. Its transcript-only subinterface ignores logs. The output witness an extractor receives
is indexed by the transcript, and the games read it from the prover output at that transcript.
An explicit failed extraction remains in the bad event; rejection and missing mass remain distinct.
For general measurable spaces, the error is an upper bound on the outer measure of the bad event.
-/

@[expose] public section

universe w

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec MeasureTheory
open scoped ENNReal

/-- The programs and experiment allowed to an extractor over a specified adversary model. -/
structure ExtractionInterface {S Obs : Type} [MeasurableSpace Obs]
    (M : AdversaryModel.{w} S Obs) (Witness : S → Type)
    [∀ stmt, MeasurableSpace (Witness stmt)] where
  Ext : Type w
  experiment : Ext → (stmt : S) → M.Adv stmt → Measure (Obs × Option (Witness stmt))
  /-- Expected adversary re-entry operations; straight-line extraction makes zero such calls. -/
  cost : Ext → (stmt : S) → M.Adv stmt → ℝ≥0∞

/-- A named extractor preserves the run, meets its access budget and rarely misses a witness. -/
def knowledgeSoundnessWith {S Obs Ctx : Type} {T : ClaimFamily.{0, 0} Ctx} [MeasurableSpace Obs]
    (M : AdversaryModel S Obs) (input : StatementProblem S) (output : Problem.{0, 0, 0} T)
    [∀ stmt, MeasurableSpace (input.Witness () stmt)]
    (J : OutputJudgement Obs output)
    (I : ExtractionInterface M (input.Witness ())) (E : I.Ext) (ε : ℝ≥0∞)
    (budget : ℝ≥0∞ := 0) : Prop :=
  ∀ stmt, input.admissible () stmt → ∀ adv : M.Adv stmt,
    (I.experiment E stmt adv).map Prod.fst = M.outcome stmt adv ∧
    I.cost E stmt adv ≤ budget ∧
    I.experiment E stmt adv {z | J.valid z.1 ∧
      ∀ wit ∈ z.2, ¬ input.rel () stmt wit} ≤ ε

/-- One extractor must work for every adversary and admissible input. -/
def knowledgeSoundness {S Obs Ctx : Type} {T : ClaimFamily.{0, 0} Ctx} [MeasurableSpace Obs]
    (M : AdversaryModel S Obs) (input : StatementProblem S) (output : Problem.{0, 0, 0} T)
    [∀ stmt, MeasurableSpace (input.Witness () stmt)]
    (J : OutputJudgement Obs output)
    (I : ExtractionInterface M (input.Witness ())) (ε : ℝ≥0∞)
    (budget : ℝ≥0∞ := 0) : Prop :=
  ∃ E : I.Ext, knowledgeSoundnessWith M input output J I E ε budget

/-- The full interaction log and the separate decision log, with challenge entries filtered out. -/
def Verifier.runWithLog {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    {Out : Transcript plainSig s → Type}
    (V : Verifier ambient s S T) (stmt : S) (prover : Prover plainSig ambient s Out) :
    OracleComp (ambient + challengeSpec plainSig s)
      (Outcome plainSig s Out T × QueryLog ambient × QueryLog ambient) := do
  let full := ambient + challengeSpec plainSig s
  let ⟨⟨tr, out, _⟩, proveLog⟩ ← (simulateQ (QueryImpl.id' full).withLogging
    (TwoParty.Lens.run s
      (prover.simulate ((QueryImpl.id' full).restrictLeft))
      (sampler plainSig s ((QueryImpl.id' full).restrictRight)))).run
  let ⟨verdict, verifyLog⟩ ← (simulateQ
    (QueryImpl.withLogging
      (((QueryImpl.id' full).restrictLeft) : QueryImpl ambient (OracleComp full)))
    (V.decide stmt (Transcript.path tr) (toPlainView s tr)).run).run
  pure (⟨tr, out, verdict⟩, proveLog.fst, verifyLog)

private theorem bind_logged {ι α β : Type} {spec : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (program : OracleComp spec α) (next : α → m β) :
    ((simulateQ impl.withLogging program).run >>= fun z => next z.1) =
      simulateQ impl program >>= next := by
  rw [← bind_map_left Prod.fst, QueryImpl.fst_map_run_withLogging]

/-- Forgetting the logs preserves the entire run as an oracle program. -/
theorem Verifier.runWithLog_fst {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    {Out : Transcript plainSig s → Type}
    (V : Verifier ambient s S T) (stmt : S) (prover : Prover plainSig ambient s Out) :
    Prod.fst <$> V.runWithLog stmt prover = V.run stmt prover := by
  simp only [runWithLog, _root_.map_bind, LawfulApplicative.map_pure]
  conv_lhs =>
    arg 2
    intro a
    rw [bind_logged _ _ (fun verdict =>
      pure (⟨a.1.1, a.1.2.1, verdict⟩ : Outcome plainSig s Out T))]
  erw [bind_logged (QueryImpl.id' (ambient + challengeSpec plainSig s)) _
    (fun result : (tr : Transcript plainSig s) × Out tr × PUnit => do
    let verdict ← simulateQ
      ((fun q => liftM ((ambient + challengeSpec plainSig s).query (.inl q))) :
        QueryImpl ambient (OracleComp (ambient + challengeSpec plainSig s)))
      (V.decide stmt (Transcript.path result.1) (toPlainView s result.1)).run
    pure (⟨result.1, result.2.1, verdict⟩ : Outcome plainSig s Out T))]
  rw [simulateQ_id']
  rfl

namespace Extractor

/-- Classical straight-line extraction has no strategy or continuation argument to re-enter.
The output witness type `Wout tr` is indexed by the transcript `tr` passed with it. -/
abbrev StraightLine {ι : Type} {S : Type} (ambient : OracleSpec ι) (s : Protocol.{0})
    (Witness : S → Type) (Wout : Transcript plainSig s → Type) :=
  (stmt : S) → (tr : Transcript plainSig s) → Wout tr → QueryLog ambient → QueryLog ambient →
    OptionT (OracleComp ambient) (Witness stmt)

/-- A transcript-only extractor cannot inspect either participant's query log. The output
witness type `Wout tr` is indexed by the transcript `tr`. -/
abbrev TranscriptOnly {ι : Type} {S : Type} (ambient : OracleSpec ι) (s : Protocol.{0})
    (Witness : S → Type) (Wout : Transcript plainSig s → Type) :=
  (stmt : S) → (tr : Transcript plainSig s) → Wout tr →
    OptionT (OracleComp ambient) (Witness stmt)

/-- Forgetting the logs embeds transcript-only extraction into the straight-line interface. -/
def TranscriptOnly.withLogs {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {Witness : S → Type} {Wout : Transcript plainSig s → Type}
    (E : TranscriptOnly ambient s Witness Wout) :
    StraightLine ambient s Witness Wout := fun stmt tr out _ _ => E stmt tr out

end Extractor

/-- The classical logged game keeps explicit extractor failure as a returned `none` witness.
The extractor receives the output witness `readOut tr out : Wout tr` at the run's transcript. -/
def extractionGame {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    {Out Wout : Transcript plainSig s → Type} {Witness : S → Type}
    (V : Verifier ambient s S T) (readOut : ∀ tr, Out tr → Wout tr)
    (E : Extractor.StraightLine ambient s Witness Wout)
    (stmt : S) (prover : Prover plainSig ambient s Out) :
    OracleComp (ambient + challengeSpec plainSig s)
      (Outcome plainSig s Out T × Option (Witness stmt)) := do
  let (obs, proveLog, verifyLog) ← V.runWithLog stmt prover
  match obs.2.2 with
  | none => pure (obs, none)
  | some _ => do
    let extracted ← OracleComp.liftComp
      (E stmt obs.1 (readOut obs.1 obs.2.1) proveLog verifyLog).run
      (ambient + challengeSpec plainSig s)
    pure (obs, extracted)

/-- A possible extraction outcome records a possible run, no witness after rejection, and a
possible extractor result on some participant logs after acceptance. -/
theorem mem_support_extractionGame {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    {Out Wout : Transcript plainSig s → Type} {Witness : S → Type}
    (V : Verifier ambient s S T) (readOut : ∀ tr, Out tr → Wout tr)
    (E : Extractor.StraightLine ambient s Witness Wout)
    (stmt : S) (prover : Prover plainSig ambient s Out)
    {z : Outcome plainSig s Out T × Option (Witness stmt)}
    (h : z ∈ support (extractionGame V readOut E stmt prover)) :
    z.1 ∈ support (V.run stmt prover) ∧ (z.1.2.2 = none → z.2 = none) ∧
      (z.1.2.2 ≠ none → ∃ proveLog verifyLog,
        z.2 ∈ support (E stmt z.1.1 (readOut z.1.1 z.1.2.1) proveLog verifyLog).run) := by
  simp only [extractionGame, mem_support_bind_iff] at h
  obtain ⟨⟨obs, proveLog, verifyLog⟩, hy, hz⟩ := h
  have hobs : obs ∈ support (V.run stmt prover) := by
    rw [← V.runWithLog_fst]
    rw [map_eq_bind_pure_comp]
    simp only [mem_support_bind_iff, Function.comp_apply, support_pure, Set.mem_singleton_iff]
    exact ⟨_, hy, rfl⟩
  rcases obs with ⟨tr, out, verdict⟩
  cases verdict with
  | none =>
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hobs, fun _ => rfl, fun h => absurd rfl h⟩
  | some t =>
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
      mem_support_liftComp_iff] at hz
    obtain ⟨e, he, rfl⟩ := hz
    exact ⟨hobs, (fun h => nomatch h), fun _ => ⟨proveLog, verifyLog, he⟩⟩

/-- The default straight-line interface uses the same shared state as the classical run.

The knowledge predicate separately checks outcome preservation, so an extractor that loses
probability mass cannot obtain security by deleting inconvenient accepted outcomes.
-/
noncomputable def classicalStraightLine {ι σ : Type} {S : Type} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type} {Out Wout : Transcript plainSig s → Type}
      (Witness : S → Type)
    [MeasurableSpace (Outcome plainSig s Out T)] [∀ stmt, MeasurableSpace (Witness stmt)]
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    (readOut : ∀ tr, Out tr → Wout tr) :
    ExtractionInterface (V.classicalModel (Out := Out) init impl challenges) Witness where
  Ext := Extractor.StraightLine ambient s Witness Wout
  experiment E stmt adv := 𝒟[Interaction.experiment init impl challenges
    (extractionGame V readOut E stmt adv)]
  cost _ _ _ := 0

/-- Transcript-only extraction is the same classical experiment with the two logs inaccessible. -/
noncomputable def classicalTranscriptOnly {ι σ : Type} {S : Type} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type} {Out Wout : Transcript plainSig s → Type}
      (Witness : S → Type)
    [MeasurableSpace (Outcome plainSig s Out T)] [∀ stmt, MeasurableSpace (Witness stmt)]
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    (readOut : ∀ tr, Out tr → Wout tr) :
    ExtractionInterface (V.classicalModel (Out := Out) init impl challenges) Witness where
  Ext := Extractor.TranscriptOnly ambient s Witness Wout
  experiment E :=
    (classicalStraightLine Witness V init impl challenges readOut).experiment E.withLogs
  cost _ _ _ := 0

private theorem run'_bind_map_const {ι σ α β γ : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec (StateT σ ProbComp)) (A : OracleComp spec α)
    (K : α → OracleComp spec β) (f : α → γ) (st : σ) :
    (simulateQ H (A >>= fun a => (fun _ => f a) <$> K a)).run' st =ᵈ
      (simulateQ H (f <$> A)).run' st := by
  simp only [simulateQ_bind, simulateQ_map, StateT.run'_eq, StateT.run_bind, StateT.run_map,
    _root_.map_bind, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  refine EvalDistEq.bind_right (m := ProbComp) _ fun z => ?_
  exact EvalDistEq.map_const ((simulateQ H (K z.1)).run z.2) (f z.1)

/-- Classical straight-line extraction preserves the run's outcome law.

The extractor runs after the outcome is fixed, so its own queries and state changes cannot
change the outcome marginal. -/
theorem classicalStraightLine_marginal {ι σ : Type} {S : Type} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type} {Out Wout : Transcript plainSig s → Type}
      (Witness : S → Type)
    [MeasurableSpace (Outcome plainSig s Out T)] [∀ stmt, MeasurableSpace (Witness stmt)]
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    (readOut : ∀ tr, Out tr → Wout tr) (E : Extractor.StraightLine ambient s Witness Wout)
    (stmt : S) (adv : Prover plainSig ambient s Out) :
    ((classicalStraightLine Witness V init impl challenges readOut).experiment E stmt adv).map
      Prod.fst = (V.classicalModel init impl challenges).outcome stmt adv := by
  change (𝒟[Interaction.experiment init impl challenges
    (extractionGame V readOut E stmt adv)]).map Prod.fst =
      𝒟[Interaction.experiment init impl challenges (V.run stmt adv)]
  rw [← evalDist_map _ measurable_fst]
  refine EvalDistEq.evalDist_eq ?_
  simp only [Interaction.experiment, _root_.map_bind]
  refine EvalDistEq.bind_right (m := ProbComp) _ fun st => ?_
  have hgame : Prod.fst <$> extractionGame V readOut E stmt adv =
      V.runWithLog stmt adv >>= fun y => (fun _ => y.1) <$> (match y.1.2.2 with
        | none => pure none
        | some _ => OracleComp.liftComp (E stmt y.1.1 (readOut y.1.1 y.1.2.1) y.2.1 y.2.2).run
            (ambient + challengeSpec plainSig s)) := by
    simp only [extractionGame, _root_.map_bind]
    congr 1
    funext y
    rcases y with ⟨⟨tr, out, verdict⟩, proveLog, verifyLog⟩
    cases verdict <;> simp
  have hmap : ∀ H : QueryImpl (ambient + challengeSpec plainSig s) (StateT σ ProbComp),
      Prod.fst <$> (simulateQ H (extractionGame V readOut E stmt adv)).run' st =
        (simulateQ H (Prod.fst <$> extractionGame V readOut E stmt adv)).run' st := by
    intro H
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [hmap, hgame]
  refine (run'_bind_map_const _ _ _ _ st).trans ?_
  rw [V.runWithLog_fst]

/-- Transcript-only extraction also preserves the run's outcome law. -/
theorem classicalTranscriptOnly_marginal {ι σ : Type} {S : Type} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type} {Out Wout : Transcript plainSig s → Type}
      (Witness : S → Type)
    [MeasurableSpace (Outcome plainSig s Out T)] [∀ stmt, MeasurableSpace (Witness stmt)]
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    (readOut : ∀ tr, Out tr → Wout tr) (E : Extractor.TranscriptOnly ambient s Witness Wout)
    (stmt : S) (adv : Prover plainSig ambient s Out) :
    ((classicalTranscriptOnly Witness V init impl challenges readOut).experiment E stmt adv).map
      Prod.fst = (V.classicalModel init impl challenges).outcome stmt adv :=
  classicalStraightLine_marginal Witness V init impl challenges readOut E.withLogs stmt adv

/-- Logging every query of a routed program, then keeping the ambient entries, is the same as
logging only its ambient queries. Answers to the routed queries come from pure behaviors. -/
theorem map_run_withLogging_addLift_fst {ι κ ι' α : Type} {ambient : OracleSpec ι}
    {R : OracleSpec κ} {full : OracleSpec ι'} (lift : QueryImpl ambient (OracleComp full))
    (beh : QueryImpl R Id) (oa : OracleComp (ambient + R) α) :
    (fun z => (z.1, z.2.fst)) <$> (simulateQ (QueryImpl.addLift lift beh).withLogging oa).run =
      (simulateQ (QueryImpl.addLift lift.withLogging beh :
        QueryImpl (ambient + R) (WriterT (QueryLog ambient) (OracleComp full))) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [QueryLog.fst]
  | query_bind t k ih =>
    simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self] at ih
    rcases t with q | r
    · simp [QueryImpl.addLift_def, WriterT.run_liftM, WriterT.run_tell, ← ih, Functor.map_map,
        QueryLog.fst]
    · refine Eq.trans ?_ ((ih (beh r)).trans ?_)
      · have hl : (liftM (beh r) : OracleComp full _) = pure (beh r) := rfl
        simp [QueryImpl.addLift_def, WriterT.run_liftM, WriterT.run_tell, hl, QueryLog.fst]
      · have hl : ((liftM (beh r) : WriterT (QueryLog ambient) (OracleComp full) _).run) =
            pure (beh r, ∅) := rfl
        simp [QueryImpl.addLift_def, hl]

/-- Logging only the ambient queries of a routed program, then forgetting the log, is the plain
routed program. Answers to the routed queries come from pure behaviors. -/
theorem map_fst_run_addLift_withLogging {ι ι' α : Type} {κ : Type} {ambient : OracleSpec ι}
    {R : OracleSpec.{0, 0} κ} {full : OracleSpec ι'} (lift : QueryImpl ambient (OracleComp full))
    (beh : QueryImpl R Id) (oa : OracleComp (ambient + R) α) :
    Prod.fst <$> (simulateQ (QueryImpl.addLift lift.withLogging beh :
        QueryImpl (ambient + R) (WriterT (QueryLog ambient) (OracleComp full))) oa).run =
      simulateQ (QueryImpl.addLift lift beh) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self] at ih
    rcases t with q | r
    · simp only [QueryImpl.addLift_def, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        WriterT.run_bind, QueryImpl.liftTarget_self, _root_.map_bind, Functor.map_map]
      simp [QueryImpl.withLogging_apply, WriterT.run_tell, ← ih]
    · have hl : ((liftM (beh r) : WriterT (QueryLog ambient) (OracleComp full) _).run) =
          pure (beh r, ∅) := rfl
      have hl' : (liftM (beh r) : OracleComp full _) = pure (beh r) := rfl
      simp [QueryImpl.addLift_def, hl, hl', ← ih]

namespace OracleVerifier

/-- Execute an oracle verifier, logging the prover's ambient queries and every query of the
decision before routing: ambient queries and queries to the input and message oracles.

The decision log records input queries, so it is returned by the run. Like `run` and
`runWithQueriesByMove`, it executes through `executeWith`, and it logs the interaction and the
decision directly with `withLogging`. -/
def runWithLog {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
    {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
    {inputs : OracleBundle.{0, 0, 0}}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    {Out : Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s)
      ((obs : Outcome oracleSig s Out (OracleVerifier.Output T B)) × QueryLog ambient ×
        QueryLog (ambient +
          (pathBundle inputs s (Transcript.path obs.1)).spec)) :=
  let full := ambient + challengeSpec oracleSig s
  let toFull : QueryImpl ambient (OracleComp full) := (QueryImpl.id' full).restrictLeft
  V.executeWith stmt data (m := OracleComp full)
    (ITrace := QueryLog ambient)
    (DTrace := fun p => QueryLog (ambient + (pathBundle inputs s p).spec))
    (fun action => (fun z => (z.1, z.2.fst)) <$>
      (simulateQ (QueryImpl.id' full).withLogging action).run)
    (prover.simulate toFull)
    (sampler oracleSig s ((QueryImpl.id' full).restrictRight))
    (fun p view pathData => (simulateQ (QueryImpl.addLift
      toFull
      ((pathBundle inputs s p).answer pathData)).withLogging
      (V.decide stmt p view).run).run)

/-- The full logged specialization retains the original interaction and decision equations. -/
theorem runWithLog_eq {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
    {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
    {inputs : OracleBundle.{0, 0, 0}}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    {Out : Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    V.runWithLog stmt data prover = (do
  let full := ambient + challengeSpec oracleSig s
  let ⟨⟨tr, out, _⟩, proveLog⟩ ← (simulateQ (QueryImpl.id' full).withLogging
    (TwoParty.Lens.run s
      (prover.simulate (fun q => liftM (full.query (.inl q))))
      (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))).run
  let p := Transcript.path tr
  let view := toView s tr
  let pathData : (pathBundle inputs s p).Data := (data, oracleMessages s tr)
  let handler : QueryImpl (ambient + (pathBundle inputs s p).spec)
      (OracleComp full) := QueryImpl.addLift
    ((fun q => liftM (full.query (.inl q))) : QueryImpl ambient (OracleComp full))
    ((pathBundle inputs s p).answer pathData)
  let ⟨verdict, verifyLog⟩ ← (simulateQ handler.withLogging (V.decide stmt p view).run).run
  pure ⟨⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f pathData)⟩,
    proveLog.fst, verifyLog⟩) := by
  simp only [runWithLog, executeWith, bind_map_left]
  rfl

/-- The ambient part of the decision log is the log of an ambient-only logger, which the oracle
extraction interfaces receive; `map_runWithLog_eq_runWithAmbientLog` names the right side. -/
theorem runWithLog_fst {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
    {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
    {inputs : OracleBundle.{0, 0, 0}}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    {Out : Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    let full := ambient + challengeSpec oracleSig s
    let toFull : QueryImpl ambient (OracleComp full) := fun q => liftM (full.query (.inl q))
    (fun z => (z.1, z.2.1, z.2.2.fst)) <$> V.runWithLog stmt data prover =
      (simulateQ (QueryImpl.id' full).withLogging (TwoParty.Lens.run s (prover.simulate toFull)
        (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))).run >>= fun x =>
      let tr := x.1.1
      let p := Transcript.path tr
      let pathData : (pathBundle inputs s p).Data := (data, oracleMessages s tr)
      (simulateQ (QueryImpl.addLift toFull.withLogging
          ((pathBundle inputs s p).answer pathData) :
            QueryImpl _ (WriterT (QueryLog ambient) (OracleComp full)))
        (V.decide stmt p (toView s tr)).run).run >>= fun y =>
      pure (⟨tr, x.1.2.1, y.1.map fun t => (t, (V.outputMap stmt p (toView s tr)).f pathData)⟩,
        x.2.fst, y.2) := by
  simp only [runWithLog_eq, _root_.map_bind]
  refine bind_congr fun x => ?_
  rw [← map_run_withLogging_addLift_fst, bind_map_left]
  simp

/-- Forgetting both logs preserves the entire oracle run. -/
theorem map_fst_runWithLog {ι : Type} {S : Type} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}}
    {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
    {inputs : OracleBundle.{0, 0, 0}}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    {Out : Transcript oracleSig s → Type} (V : OracleVerifier ambient s S T inputs outputs)
    (stmt : S) (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    Sigma.fst <$> V.runWithLog stmt data prover = V.run stmt data prover := by
  simp only [runWithLog_eq, _root_.map_bind, LawfulApplicative.map_pure]
  rw [OracleVerifier.run_eq]
  conv_lhs =>
    arg 2
    intro a
    rw [bind_logged _ _ (fun (verdict : Option (T (Transcript.path a.1.1))) =>
      pure (⟨a.1.1, a.1.2.1, verdict.map fun t =>
        (t, (V.outputMap stmt (Transcript.path a.1.1) (toView s a.1.1)).f
          ((data, oracleMessages s a.1.1) : (pathBundle inputs s _).Data))⟩ :
            Outcome oracleSig s Out (OracleVerifier.Output T B)))]
  rw [bind_logged (QueryImpl.id' (ambient + challengeSpec oracleSig s)) _
    (fun result : (tr : Transcript oracleSig s) × Out tr × PUnit => do
      let verdict ← simulateQ (QueryImpl.addLift
        ((fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) :
          QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)))
        ((pathBundle inputs s (Transcript.path result.1)).answer
          (data, oracleMessages s result.1)))
        (V.decide stmt (Transcript.path result.1) (toView s result.1)).run
      pure (⟨result.1, result.2.1, verdict.map fun t =>
        (t, (V.outputMap stmt (Transcript.path result.1) (toView s result.1)).f
          ((data, oracleMessages s result.1) : (pathBundle inputs s _).Data))⟩ :
        Outcome oracleSig s Out (OracleVerifier.Output T B)))]
  rw [simulateQ_id']

/-- Execute an oracle verifier, logging the prover's ambient queries and the decision's ambient
queries. The decision's bundle queries are answered from the input data and the path's oracle
messages and are not logged, so the result holds only ambient logs. It executes through
`executeWith` and logs both phases directly with `withLogging`. -/
def runWithAmbientLog {ι : Type} {S : Type} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleBundle.{0, 0, 0}}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    {Out : Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s)
      (Outcome oracleSig s Out (OracleVerifier.Output T B) × QueryLog ambient ×
        QueryLog ambient) :=
  let full := ambient + challengeSpec oracleSig s
  let toFull : QueryImpl ambient (OracleComp full) := (QueryImpl.id' full).restrictLeft
  (fun r => (r.1, r.2.1, r.2.2)) <$> V.executeWith stmt data (m := OracleComp full)
    (ITrace := QueryLog ambient) (DTrace := fun _ => QueryLog ambient)
    (fun action => (fun z => (z.1, z.2.fst)) <$>
      (simulateQ (QueryImpl.id' full).withLogging action).run)
    (prover.simulate toFull) (sampler oracleSig s ((QueryImpl.id' full).restrictRight))
    (fun p view pathData => (simulateQ
      (QueryImpl.addLift toFull.withLogging ((pathBundle inputs s p).answer pathData) :
        QueryImpl _ (WriterT (QueryLog ambient) (OracleComp full)))
      (V.decide stmt p view).run).run)

/-- The ambient logged specialization retains the original interaction and decision equation. -/
theorem runWithAmbientLog_eq {ι : Type} {S : Type} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleBundle.{0, 0, 0}}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    {Out : Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    V.runWithAmbientLog stmt data prover = (
      let full := ambient + challengeSpec oracleSig s
      let toFull : QueryImpl ambient (OracleComp full) := fun q => liftM (full.query (.inl q))
      (simulateQ (QueryImpl.id' full).withLogging (TwoParty.Lens.run s (prover.simulate toFull)
        (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))).run >>= fun x =>
      let tr := x.1.1
      let p := Transcript.path tr
      let pathData : (pathBundle inputs s p).Data := (data, oracleMessages s tr)
      (simulateQ (QueryImpl.addLift toFull.withLogging
          ((pathBundle inputs s p).answer pathData) :
            QueryImpl _ (WriterT (QueryLog ambient) (OracleComp full)))
        (V.decide stmt p (toView s tr)).run).run >>= fun y =>
      pure (⟨tr, x.1.2.1, y.1.map fun t => (t, (V.outputMap stmt p (toView s tr)).f pathData)⟩,
        x.2.fst, y.2)) := by
  simp only [runWithAmbientLog, executeWith, _root_.map_bind, bind_map_left]
  rfl

/-- The ambient-log run is the full-log run with the decision log restricted to its ambient
entries. -/
theorem map_runWithLog_eq_runWithAmbientLog {ι : Type} {S : Type} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleBundle.{0, 0, 0}}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    {Out : Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    (fun z => (z.1, z.2.1, z.2.2.fst)) <$> V.runWithLog stmt data prover =
      V.runWithAmbientLog stmt data prover := by
  rw [runWithAmbientLog_eq]
  exact V.runWithLog_fst stmt data prover

/-- Forgetting both ambient logs preserves the entire oracle run. -/
theorem map_fst_runWithAmbientLog {ι : Type} {S : Type}
    {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}} {T : Path s → Type}
    {J : Path s → Type} {B : (p : Path s) → J p → Type} {inputs : OracleBundle.{0, 0, 0}}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    {Out : Transcript oracleSig s → Type} (V : OracleVerifier ambient s S T inputs outputs)
    (stmt : S) (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    Prod.fst <$> V.runWithAmbientLog stmt data prover = V.run stmt data prover := by
  simp only [runWithAmbientLog_eq, OracleVerifier.run_eq, _root_.map_bind,
    LawfulApplicative.map_pure]
  simp only [← map_fst_run_addLift_withLogging, bind_map_left]
  conv_rhs =>
    arg 1
    rw [← simulateQ_id' (TwoParty.Lens.run s _ _),
      ← QueryImpl.fst_map_run_withLogging (QueryImpl.id' (ambient + challengeSpec oracleSig s))]
  rw [bind_map_left]

end OracleVerifier

namespace Extractor

/-- Straight-line extraction from an oracle protocol sees the full transcript, oracle messages
included. The output witness type `Wout tr` is indexed by that transcript `tr`. -/
abbrev OracleStraightLine {ι : Type} {S : Type} (ambient : OracleSpec ι)
    (s : OracleProtocol.{0, 0})
    (Witness : S → Type) (Wout : Transcript oracleSig s → Type) :=
  (stmt : S) → (tr : Transcript oracleSig s) → Wout tr → QueryLog ambient → QueryLog ambient →
    OptionT (OracleComp ambient) (Witness stmt)

/-- The oracle transcript-only interface omits both ambient logs. The output witness type
`Wout tr` is indexed by the transcript `tr`. -/
abbrev OracleTranscriptOnly {ι : Type} {S : Type} (ambient : OracleSpec ι)
    (s : OracleProtocol.{0, 0})
    (Witness : S → Type) (Wout : Transcript oracleSig s → Type) :=
  (stmt : S) → (tr : Transcript oracleSig s) → Wout tr →
    OptionT (OracleComp ambient) (Witness stmt)

/-- Embed the oracle transcript-only interface by ignoring the two logs. -/
def OracleTranscriptOnly.withLogs {ι : Type} {S : Type} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}}
    {Witness : S → Type} {Wout : Transcript oracleSig s → Type}
    (E : OracleTranscriptOnly ambient s Witness Wout) :
    OracleStraightLine ambient s Witness Wout := fun stmt tr out _ _ => E stmt tr out

end Extractor

namespace OracleVerifier
variable {ι σ : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : OracleBundle.{0, 0, 0}}
  {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
  {Out Wout : Transcript oracleSig s → Type}

/-- Oracle extraction uses actual inputs, full transcripts, and the ambient logs of the run.
The extractor receives the output witness `readOut tr out : Wout tr` at the run's transcript.
The run logs only ambient queries. -/
def extractionGame (V : OracleVerifier ambient s S T inputs outputs)
    {Witness : (S × inputs.Data) → Type} (readOut : ∀ tr, Out tr → Wout tr)
    (E : Extractor.OracleStraightLine ambient s Witness Wout)
    (stmt : S × inputs.Data) (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s)
      (Outcome oracleSig s Out (OracleVerifier.Output T B) × Option (Witness stmt)) := do
  let ⟨obs, proveLog, verifyLog⟩ ← V.runWithAmbientLog stmt.1 stmt.2 prover
  match obs.2.2 with
  | none => pure (obs, none)
  | some _ => do
    let extracted ← OracleComp.liftComp
      (E stmt obs.1 (readOut obs.1 obs.2.1) proveLog verifyLog).run
      (ambient + challengeSpec oracleSig s)
    pure (obs, extracted)

/-- The classical logged extraction interface for passive oracle verifiers. -/
noncomputable def classicalStraightLine (Witness : (S × inputs.Data) → Type)
    [MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T B))]
    [∀ stmt, MeasurableSpace (Witness stmt)]
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (readOut : ∀ tr, Out tr → Wout tr) :
    ExtractionInterface (V.classicalModel (Out := Out) init impl challenges) Witness where
  Ext := Extractor.OracleStraightLine ambient s Witness Wout
  experiment E stmt adv := 𝒟[Interaction.experiment init impl challenges
    (V.extractionGame readOut E stmt adv)]
  cost _ _ _ := 0

/-- Oracle transcript-only extraction uses the same game without access to the query logs. -/
noncomputable def classicalTranscriptOnly (Witness : (S × inputs.Data) → Type)
    [MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T B))]
    [∀ stmt, MeasurableSpace (Witness stmt)]
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (readOut : ∀ tr, Out tr → Wout tr) :
    ExtractionInterface (V.classicalModel (Out := Out) init impl challenges) Witness where
  Ext := Extractor.OracleTranscriptOnly ambient s Witness Wout
  experiment E :=
    (V.classicalStraightLine Witness init impl challenges readOut).experiment E.withLogs
  cost _ _ _ := 0

/-- Classical straight-line oracle extraction preserves the run's outcome law: the
extractor runs after the outcome is fixed. -/
theorem classicalStraightLine_marginal (Witness : (S × inputs.Data) → Type)
    [MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T B))]
    [∀ stmt, MeasurableSpace (Witness stmt)]
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (readOut : ∀ tr, Out tr → Wout tr) (E : Extractor.OracleStraightLine ambient s Witness Wout)
    (stmt : S × inputs.Data) (adv : Prover oracleSig ambient s Out) :
    ((V.classicalStraightLine Witness init impl challenges readOut).experiment E stmt adv).map
      Prod.fst = (V.classicalModel init impl challenges).outcome stmt adv := by
  change (𝒟[Interaction.experiment init impl challenges
    (V.extractionGame readOut E stmt adv)]).map Prod.fst =
      𝒟[Interaction.experiment init impl challenges (V.run stmt.1 stmt.2 adv)]
  rw [← evalDist_map _ measurable_fst]
  refine EvalDistEq.evalDist_eq ?_
  simp only [Interaction.experiment, _root_.map_bind]
  refine EvalDistEq.bind_right (m := ProbComp) _ fun st => ?_
  have hgame : Prod.fst <$> V.extractionGame readOut E stmt adv =
      V.runWithAmbientLog stmt.1 stmt.2 adv >>= fun y => (fun _ => y.1) <$> (match y.1.2.2 with
        | none => pure none
        | some _ => OracleComp.liftComp
            (E stmt y.1.1 (readOut y.1.1 y.1.2.1) y.2.1 y.2.2).run
            (ambient + challengeSpec oracleSig s)) := by
    simp only [extractionGame, _root_.map_bind]
    congr 1
    funext y
    rcases y with ⟨⟨tr, out, verdict⟩, proveLog, verifyLog⟩
    cases verdict <;> simp
  have hmap : ∀ H : QueryImpl (ambient + challengeSpec oracleSig s) (StateT σ ProbComp),
      Prod.fst <$> (simulateQ H (V.extractionGame readOut E stmt adv)).run' st =
        (simulateQ H (Prod.fst <$> V.extractionGame readOut E stmt adv)).run' st := by
    intro H
    simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [hmap, hgame]
  refine (run'_bind_map_const _ _ _ _ st).trans ?_
  rw [V.map_fst_runWithAmbientLog]

/-- Oracle transcript-only extraction also preserves the run's outcome law. -/
theorem classicalTranscriptOnly_marginal (Witness : (S × inputs.Data) → Type)
    [MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T B))]
    [∀ stmt, MeasurableSpace (Witness stmt)]
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (readOut : ∀ tr, Out tr → Wout tr) (E : Extractor.OracleTranscriptOnly ambient s Witness Wout)
    (stmt : S × inputs.Data) (adv : Prover oracleSig ambient s Out) :
    ((V.classicalTranscriptOnly Witness init impl challenges readOut).experiment E stmt adv).map
      Prod.fst = (V.classicalModel init impl challenges).outcome stmt adv :=
  V.classicalStraightLine_marginal Witness init impl challenges readOut E.withLogs stmt adv

end OracleVerifier

end Interaction
