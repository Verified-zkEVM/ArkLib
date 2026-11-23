/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.OracleVerifier
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# The step log of an oracle verifier run

A run of an oracle protocol is a sequence of steps. A step is one action of one participant: a
prover move, a challenge draw, or the verifier's final decision. For each step, this file records
the transcript so far, the actor, and the oracle queries the step made.

* `TranscriptPrefix s` is the transcript so far: the moves already made, including challenges and
  oracle payloads.
* `StepActor` says who acts in a step. The runner takes the actor from the participant whose
  action it executes. The passive verifier's decision is a separate step at the end.
* `LoggedStep` is one step with its transcript so far, its actor and its queries.
* `StepInstrumentation.mapStepsWith` wraps each participant action so that it logs a step. The
  core runner `TwoParty.Lens.run` still executes every move.
* `OracleVerifier.StepLog` is the log of a whole run, and `runWithStepLog` produces it. Each step
  logs its own queries. The log therefore keeps their order and multiplicity.
-/

@[expose] public section

universe u q uA vC uS uI dI wJ

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec

/-- The transcript so far: the moves already made along the protocol, which may stop before the
leaf. -/
def TranscriptPrefix : (s : OracleProtocol.{u, q}) → Type u
  | .pure _ => Option PEmpty
  | .liftBind a next => Option ((x : Move oracleSig a) ×
      TranscriptPrefix (next (oracleSig.toFunB a x)))

namespace TranscriptPrefix

/-- The empty transcript, with no moves made yet. -/
def empty {s : OracleProtocol.{u, q}} : TranscriptPrefix s := by cases s <;> exact none

/-- The transcript that starts with move `x` and continues with the transcript `tail` of the rest
of the protocol. -/
def cons {a : OraclePos.{u, q}} {next : OraclePoly.B a → OracleProtocol}
    (x : Move oracleSig a) (tail : TranscriptPrefix (next (oracleSig.toFunB a x))) :
    TranscriptPrefix (.liftBind a next) := some ⟨x, tail⟩

/-- The number of moves already made. -/
def length : {s : OracleProtocol.{u, q}} → TranscriptPrefix s → Nat
  | .pure _, _ => 0
  | .liftBind _ _, none => 0
  | .liftBind _ _, some ⟨_, tail⟩ => tail.length + 1

/-- A completed transcript as a transcript prefix. It keeps every move. -/
def ofTranscript : (s : OracleProtocol.{u, q}) → PathAlong oracleSig s → TranscriptPrefix s
  | .pure _, _ => none
  | .liftBind _ next, ⟨x, tr⟩ => .cons x (ofTranscript (next (oracleSig.toFunB _ x)) tr)

end TranscriptPrefix

/-- The participant who acts in a step. The constructor fixes the participant. -/
inductive StepActor where
  | prover
  | challenger
  | decision
  deriving DecidableEq

/-- The two-party role of the actor. The prover sends, and the challenger and the decision
receive. The actor alone fixes the role, with no extra role decoration of the exchanged move. -/
def StepActor.role : StepActor → TwoParty.Role
  | .prover => .sender
  | .challenger | .decision => .receiver

/-- One executed step: the transcript so far before its action, the actor, and all its queries. -/
structure LoggedStep {ι : Type} (spec : OracleSpec ι) (s : OracleProtocol.{0, q}) where
  /-- The moves made before this step. -/
  before : TranscriptPrefix s
  /-- The participant who acted in this step. -/
  actor : StepActor
  /-- The queries and their successful responses, in order and with repeats. -/
  queries : QueryLog spec

namespace LoggedStep

/-- The role of the step's actor. It is read from the actor, with no extra role decoration. -/
def role {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (step : LoggedStep spec s) : TwoParty.Role := step.actor.role

/-- Put the move that led to the child protocol in front of the step's transcript so far. -/
def cons {ι : Type} {spec : OracleSpec ι} {a : OraclePos.{0, q}}
    {next : OraclePoly.B a → OracleProtocol} (x : Move oracleSig a)
    (step : LoggedStep spec (next (oracleSig.toFunB a x))) : LoggedStep spec (.liftBind a next) :=
  ⟨.cons x step.before, step.actor, step.queries⟩

end LoggedStep

/-- Concatenate the queries of the steps, in execution order. -/
def concatQueries {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (steps : List (LoggedStep spec s)) : QueryLog spec := steps.flatMap (·.queries)

namespace StepInstrumentation

/-- A monad morphism applied to PolyFun's exchange `step` equals `step` of the morphism applied to
each part. -/
theorem map_step {m n : Type u → Type u} [Monad m] [Monad n]
    (F : m →ᵐ n) {X R : Type u} {A B : X → Type u} (role : TwoParty.Role)
    (p : m (Choice .focal role X A)) (c : m (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → m R) :
    F.toFun R (step role .focalFirst p c k) =
      step role .focalFirst (F.toFun _ p) (F.toFun _ c)
        (fun x a b => F.toFun R (k x a b)) := by
  cases role <;> simp only [step, Schedule.seq, F.toFun_bind']

section Strategies
variable {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
  {m n k : Type u → Type u} [Monad m] [Monad n] [Monad k]
  {C : FreeM P PUnit.{u + 1} → Type vC}

/-- Wrap each participant action and carry the wrapper down to the continuations. This maps
strategies only. The core runner `TwoParty.Lens.run` still does every move exchange and
execution. -/
def mapStepsWith
    (action : {s : FreeM P PUnit.{u + 1}} → {A : Type u} →
      C s → Participant.{u} → m A → n A)
    (descend : (a : P.A) → (next : P.B a → FreeM P PUnit.{u + 1}) →
      (x : Move l a) → C (.liftBind a next) → C (next (l.toFunB a x))) :
    {s : FreeM P PUnit.{u + 1}} → {Out : PathAlong l s → Type u} →
    C s → (agent : Participant.{u}) → Strategy l m agent s Out → Strategy l n agent s Out
  | .pure _, _, env, agent, p => action env agent p
  | .liftBind a next, _, env, agent, p =>
    Choice.map agent (owner l a)
      (fun x child => mapStepsWith (@action) descend (descend a next x env) agent child) <$>
        action env agent p

/-- The core runner `TwoParty.Lens.run` commutes with wrapping each action by `mapStepsWith`.
It suffices that applying `F` to each wrapped action agrees with applying `G` to the unwrapped
action. The polynomial, the lens, the environment and all three monads are arbitrary. This
supplies the missing general PolyFun law without introducing a new executor. -/
theorem run_mapStepsWith [LawfulMonad m] [LawfulMonad n] [LawfulMonad k]
    (F : n →ᵐ k) (G : m →ᵐ k)
    (action : {s : FreeM P PUnit.{u + 1}} → {A : Type u} →
      C s → Participant.{u} → m A → n A)
    (descend : (a : P.A) → (next : P.B a → FreeM P PUnit.{u + 1}) →
      (x : Move l a) → C (.liftBind a next) → C (next (l.toFunB a x)))
    (comm : ∀ {s A} (env : C s) agent (p : m A), F.toFun A (action env agent p) = G.toFun A p) :
    (s : FreeM P PUnit.{u + 1}) → {OutP OutC : PathAlong l s → Type u} →
    (env : C s) → (p : Focal l m s OutP) → (c : Counterpart l m s OutC) →
    F.toFun _ (TwoParty.Lens.run s (mapStepsWith (C := C) (@action) descend env .focal p)
      (mapStepsWith (C := C) (@action) descend env .counterpart c)) =
      G.toFun _ (TwoParty.Lens.run s p c)
  | .pure leaf, _, _, env, p, c => by
    cases leaf
    simp only [mapStepsWith, FreeM.pure_eq_pure, run_done, F.toFun_bind', G.toFun_bind',
      F.toFun_pure', G.toFun_pure', comm]
  | .liftBind a next, _, _, env, p, c => by
    rw [run_node, run_node]
    simp only [mapStepsWith, step_map_left, step_map_right]
    rw [map_step F, map_step G]
    simp only [comm]
    congr 1
    funext x pn cn
    simp only [F.toFun_bind', G.toFun_bind', F.toFun_pure', G.toFun_pure']
    rw [run_mapStepsWith F G (@action) descend comm]

end Strategies

/-- Map each entry of a list-valued writer to a list, and concatenate the results. This is a monad
morphism. -/
def writerMap {m : Type u → Type u} [Monad m] [LawfulMonad m] {A B : Type u}
    (f : A → List B) : WriterT (List A) m →ᵐ WriterT (List B) m where
  toFun _ p := WriterT.mk ((fun r => (r.1, r.2.flatMap f)) <$> p.run)
  toFun_pure' _ := by
    apply WriterT.ext
    simp [WriterT.run_mk]
  toFun_bind' p k := by
    apply WriterT.ext
    simp only [WriterT.run_mk, WriterT.run_bind, _root_.map_bind,
      Functor.map_map, bind_map_left]
    congr 1
    funext r
    congr 1
    funext t
    simp only [List.flatMap_append]

end StepInstrumentation

/-- Run one participant action and log it as a step. The step records the transcript so far, the
actor and the successful queries. The actor is the prover for the focal participant and the
challenger for the counterpart. -/
def logStep {ι : Type} {spec : OracleSpec ι} {root s : OracleProtocol.{0, q}} {A : Type}
    (embed : TranscriptPrefix s → TranscriptPrefix root) (agent : Participant)
    (p : OracleComp spec A) : WriterT (List (LoggedStep spec root)) (OracleComp spec) A :=
  WriterT.mk ((fun r => (r.1, [⟨embed .empty,
    match agent with | .focal => .prover | .counterpart => .challenger, r.2⟩])) <$>
      p.withQueryLog)

/-- Extend the embedding of transcripts into the root protocol by the move that the core runner
delivered. -/
def extendPrefix {root : OracleProtocol.{0, q}} (a : OraclePos.{0, q})
    (next : OraclePoly.B a → OracleProtocol) (x : Move oracleSig a)
    (embed : TranscriptPrefix (.liftBind a next) → TranscriptPrefix root) :
    TranscriptPrefix (next (oracleSig.toFunB a x)) → TranscriptPrefix root :=
  fun tail => embed (.cons x tail)

/-- Run the core runner `TwoParty.Lens.run` on participant strategies wrapped by `logStep`. The
writer layer collects one logged step per action. -/
def runLoggingSteps {ι : Type} {spec : OracleSpec ι} (s : OracleProtocol.{0, q})
    {OutP OutC : PathAlong oracleSig s → Type}
    (p : Focal oracleSig (OracleComp spec) s OutP)
    (c : Counterpart oracleSig (OracleComp spec) s OutC) :
    OracleComp spec (((tr : PathAlong oracleSig s) × OutP tr × OutC tr) ×
      List (LoggedStep spec s)) :=
  (TwoParty.Lens.run s
    (StepInstrumentation.mapStepsWith (C := fun t => TranscriptPrefix t → TranscriptPrefix s)
      (@logStep ι spec s) (@extendPrefix s) id .focal p)
    (StepInstrumentation.mapStepsWith (C := fun t => TranscriptPrefix t → TranscriptPrefix s)
      (@logStep ι spec s) (@extendPrefix s) id .counterpart c)).run

/-- Concatenating the queries of the logged steps forgets the step boundaries and gives the query
log of the ordinary run. The proof applies `run_mapStepsWith`. -/
theorem runLoggingSteps_log {ι : Type} {spec : OracleSpec ι} (s : OracleProtocol.{0, q})
    {OutP OutC : PathAlong oracleSig s → Type}
    (p : Focal oracleSig (OracleComp spec) s OutP)
    (c : Counterpart oracleSig (OracleComp spec) s OutC) :
    (fun r => (r.1, concatQueries r.2)) <$> runLoggingSteps s p c =
      (TwoParty.Lens.run s p c).withQueryLog := by
  have comm {t A} (env : TranscriptPrefix t → TranscriptPrefix s) agent
      (program : OracleComp spec A) :
      (StepInstrumentation.writerMap (fun step : LoggedStep spec s => step.queries))
        (logStep env agent program) = simulateQ spec.loggingOracle program := by
    apply WriterT.ext
    simp only [StepInstrumentation.writerMap, logStep, WriterT.run_mk, Functor.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change (fun a => (a.1, a.2)) <$> program.withQueryLog = program.withQueryLog
    exact LawfulFunctor.id_map _
  have natural := StepInstrumentation.run_mapStepsWith
    (StepInstrumentation.writerMap (fun step : LoggedStep spec s => step.queries))
    (simulateQ' spec.loggingOracle) (@logStep ι spec s)
    (@extendPrefix s)
    (fun env agent program => comm env agent program) s id p c
  exact congrArg WriterT.run natural

/-- Putting a move in front of the transcript of each child step does not change the concatenated
queries. -/
theorem concatQueries_cons {ι : Type} {spec : OracleSpec ι} {a : OraclePos.{0, q}}
    {next : OraclePoly.B a → OracleProtocol} (x : Move oracleSig a)
    (steps : List (LoggedStep spec (next (oracleSig.toFunB a x)))) :
    concatQueries (steps.map (LoggedStep.cons x)) = concatQueries steps := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
    simpa only [concatQueries, List.map_cons, List.flatMap_cons, LoggedStep.cons] using
      congrArg (step.queries ++ ·) ih

/-- Keeping only the ambient queries of each step commutes with concatenating the steps' queries
in order. -/
theorem concatQueries_fst {ι κ : Type} {a : OracleSpec ι} {b : OracleSpec κ}
    {s : OracleProtocol.{0, q}} (steps : List (LoggedStep (a + b) s)) :
    concatQueries (steps.map (fun step =>
      (⟨step.before, step.actor, step.queries.fst⟩ : LoggedStep a s))) =
      (concatQueries steps).fst := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    simpa only [concatQueries, List.map_cons, List.flatMap_cons, QueryLog.fst_append] using
      congrArg (step.queries.fst ++ ·) ih

namespace OracleVerifier

variable {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : Resources.{0, 0, dI}} {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : PathAlong oracleSig s → Type}

/-- The log of a completed run: the participant steps, and the full query log of the final
decision. -/
structure StepLog (V : OracleVerifier ambient s S T inputs outputs)
    (Out : PathAlong oracleSig s → Type) where
  /-- The ordinary run observation, including rejection and private prover output. -/
  observation : Observation oracleSig s Out (OracleVerifier.Output T B)
  /-- The participant steps before the final decision, in execution order. -/
  steps : List (LoggedStep (ambient + challengeSpec oracleSig s) s)
  /-- The decision's queries, before resource routing. -/
  decisionQueries : QueryLog
    (ambient + (pathResources inputs s (projectPathAlong oracleSig s observation.1)).spec)

namespace StepLog

/-- Forget the step boundaries and keep exactly the two existing query logs. -/
def toLog {V : OracleVerifier ambient s S T inputs outputs} (r : StepLog V Out) :=
  (⟨r.observation, (concatQueries r.steps).fst, r.decisionQueries⟩ :
    (obs : Observation oracleSig s Out (OracleVerifier.Output T B)) × QueryLog ambient ×
      QueryLog (ambient + (pathResources inputs s (projectPathAlong oracleSig s obs.1)).spec))

/-- The verifier's decision as a step. Its transcript so far is the whole transcript of the run,
and its actor is `decision`, which has the receiver role. -/
def decisionStep {V : OracleVerifier ambient s S T inputs outputs} (r : StepLog V Out) :
    LoggedStep ambient s :=
  ⟨TranscriptPrefix.ofTranscript s r.observation.1, .decision, r.decisionQueries.fst⟩

/-- The steps of the run with only their ambient queries, ending with the decision step. Under P1,
the decision is a step of its own. -/
def allSteps {V : OracleVerifier ambient s S T inputs outputs} (r : StepLog V Out) :
    List (LoggedStep ambient s) :=
  r.steps.map (fun step => ⟨step.before, step.actor, step.queries.fst⟩) ++
    [r.decisionStep]

/-- Every selected step is one of the steps of this run. -/
theorem step_mem {V : OracleVerifier ambient s S T inputs outputs} (r : StepLog V Out)
    (i : Fin r.allSteps.length) : r.allSteps[i] ∈ r.allSteps := List.getElem_mem _

/-- Keeping only the ambient queries of each participant step commutes with concatenating the
steps' queries. -/
theorem steps_queries {V : OracleVerifier ambient s S T inputs outputs}
    (r : StepLog V Out) :
    concatQueries (r.steps.map (fun step =>
      (⟨step.before, step.actor, step.queries.fst⟩ : LoggedStep ambient s))) =
      (concatQueries r.steps).fst := concatQueries_fst r.steps

/-- The concatenated queries of `allSteps` are the participant steps' ambient queries followed by
the decision's ambient queries. -/
theorem allSteps_queries {V : OracleVerifier ambient s S T inputs outputs} (r : StepLog V Out) :
    concatQueries r.allSteps = (concatQueries r.steps).fst ++ r.decisionQueries.fst := by
  change (List.flatMap (fun step : LoggedStep ambient s => step.queries) (_ ++ _)) = _
  rw [List.flatMap_append]
  simpa only [concatQueries, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    decisionStep] using
    congrArg (· ++ r.decisionQueries.fst) r.steps_queries

/-- Add a separate prover setup step, with the given queries, in front of the participant steps.
It sits at the empty transcript. -/
def withSetupStep {V : OracleVerifier ambient s S T inputs outputs}
    (r : StepLog V Out) (queries : QueryLog ambient) : StepLog V Out :=
  { r with steps := ⟨.empty, .prover, QueryLog.inl queries⟩ :: r.steps }

/-- The setup step's queries come before the queries of all participant steps. -/
theorem toLog_withSetupStep {V : OracleVerifier ambient s S T inputs outputs}
    (r : StepLog V Out) (queries : QueryLog ambient) :
    (r.withSetupStep queries).toLog =
      ⟨r.observation, queries ++ (concatQueries r.steps).fst, r.decisionQueries⟩ := by
  simp only [toLog, withSetupStep, concatQueries, List.flatMap_cons, QueryLog.fst_append,
    QueryLog.fst_inl]
  rfl

/-- The decision step is one of the steps of the run. -/
theorem decisionStep_mem {V : OracleVerifier ambient s S T inputs outputs} (r : StepLog V Out) :
    r.decisionStep ∈ r.allSteps := by simp [allSteps]

/-- The transcript so far at the decision step is exactly the whole transcript of this run. -/
theorem decisionStep_before {V : OracleVerifier ambient s S T inputs outputs}
    (r : StepLog V Out) :
    r.decisionStep.before = TranscriptPrefix.ofTranscript s r.observation.1 := rfl

end StepLog

/-- Run the verifier once. Log each participant step with its transcript so far and its queries,
then log the verifier's decision. The decision's log has both its resource queries and its
ambient queries. -/
def runWithStepLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s) (StepLog V Out) :=
  let full := ambient + challengeSpec oracleSig s
  (fun r => ⟨r.1, r.2.1, r.2.2⟩) <$> V.executeWith stmt data
    (ITrace := List (LoggedStep full s))
    (DTrace := fun p => QueryLog (ambient + (pathResources inputs s p).spec))
    (fun action => action.run)
    (StepInstrumentation.mapStepsWith (C := fun t => TranscriptPrefix t → TranscriptPrefix s)
      (@logStep _ full s) (@extendPrefix s) id .focal
      (prover.simulate (fun q => liftM (full.query (.inl q)))))
    (StepInstrumentation.mapStepsWith (C := fun t => TranscriptPrefix t → TranscriptPrefix s)
      (@logStep _ full s) (@extendPrefix s) id .counterpart
      (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))
    (fun p view resources => (simulateQ (QueryImpl.addLift
      ((fun q => liftM (full.query (.inl q))) : QueryImpl ambient (OracleComp full))
      ((pathResources inputs s p).answer resources)).withLogging
      (V.decide stmt p view).run).run)

/-- Forgetting the step boundaries gives the ordinary logging of the interaction and of the
decision. -/
theorem runWithStepLog_toLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    StepLog.toLog <$> V.runWithStepLog stmt data prover = (do
  let full := ambient + challengeSpec oracleSig s
  let ⟨⟨tr, out, _⟩, proveLog⟩ ← (simulateQ (QueryImpl.id' full).withLogging
    (TwoParty.Lens.run s
      (prover.simulate (fun q => liftM (full.query (.inl q))))
      (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))).run
  let p := projectPathAlong oracleSig s tr
  let view := toView s tr
  let resources : (pathResources inputs s p).Data := (data, payloads s tr)
  let handler : QueryImpl (ambient + (pathResources inputs s p).spec)
      (OracleComp full) := QueryImpl.addLift
    ((fun q => liftM (full.query (.inl q))) : QueryImpl ambient (OracleComp full))
    ((pathResources inputs s p).answer resources)
  let ⟨verdict, verifyLog⟩ ← (simulateQ handler.withLogging (V.decide stmt p view).run).run
  pure ⟨⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f resources)⟩,
    proveLog.fst, verifyLog⟩) := by
  simp only [runWithStepLog, executeWith, Functor.map_map, _root_.map_bind]
  have id_logging {α : Type} (p : OracleComp (ambient + challengeSpec oracleSig s) α) :
      (simulateQ (QueryImpl.id' (ambient + challengeSpec oracleSig s)).withLogging p).run =
        p.withQueryLog := rfl
  rw [id_logging, ← runLoggingSteps_log, bind_map_left]
  refine bind_congr fun r => ?_
  simp [StepLog.toLog]

section AmbientStepLog

variable {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol.{0, q}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : Resources.{0, uI, dI}} {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : PathAlong oracleSig s → Type}

/-- The ambient step log lets the input oracles and the oracle nodes have independent query
universes. It returns only ambient requests and challenge draws, whose indices are small. -/
structure AmbientStepLog (V : OracleVerifier ambient s S T inputs outputs)
    (Out : PathAlong oracleSig s → Type) where
  /-- The ordinary completed observation, including output resources and rejection. -/
  observation : Observation oracleSig s Out (OracleVerifier.Output T B)
  /-- The participant steps, produced by the same runner as in `StepLog`. -/
  steps : List (LoggedStep (ambient + challengeSpec oracleSig s) s)
  /-- The decision's ambient requests and the responses it received. -/
  decisionQueries : QueryLog ambient

namespace AmbientStepLog

/-- Forget the step boundaries to recover the two existing ambient logs. -/
def toLog {V : OracleVerifier ambient s S T inputs outputs} (r : AmbientStepLog V Out) :=
  (r.observation, (concatQueries r.steps).fst, r.decisionQueries)

/-- The verifier's decision as a step. Its transcript so far is the whole transcript of the run,
and its actor is `decision`, which has the receiver role. -/
def decisionStep {V : OracleVerifier ambient s S T inputs outputs} (r : AmbientStepLog V Out) :
    LoggedStep ambient s :=
  ⟨TranscriptPrefix.ofTranscript s r.observation.1, .decision, r.decisionQueries⟩

/-- The steps of the run with only their ambient queries, ending with the decision as its own
step. -/
def allSteps {V : OracleVerifier ambient s S T inputs outputs} (r : AmbientStepLog V Out) :
    List (LoggedStep ambient s) :=
  r.steps.map (fun step => ⟨step.before, step.actor, step.queries.fst⟩) ++
    [r.decisionStep]

/-- Every selected step is one of the steps of this ambient step log. -/
theorem step_mem {V : OracleVerifier ambient s S T inputs outputs} (r : AmbientStepLog V Out)
    (i : Fin r.allSteps.length) : r.allSteps[i] ∈ r.allSteps := List.getElem_mem _

/-- The decision step is one of the steps of this ambient step log. -/
theorem decisionStep_mem {V : OracleVerifier ambient s S T inputs outputs}
    (r : AmbientStepLog V Out) : r.decisionStep ∈ r.allSteps := by simp [allSteps]

/-- The concatenated queries of `allSteps` are the participant steps' ambient queries followed by
the decision's ambient queries. -/
theorem allSteps_queries {V : OracleVerifier ambient s S T inputs outputs}
    (r : AmbientStepLog V Out) :
    concatQueries r.allSteps = (concatQueries r.steps).fst ++ r.decisionQueries := by
  change (List.flatMap (fun step : LoggedStep ambient s => step.queries) (_ ++ _)) = _
  rw [List.flatMap_append]
  simpa only [concatQueries, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    decisionStep] using congrArg (· ++ r.decisionQueries) (concatQueries_fst r.steps)

end AmbientStepLog

/-- Log the same participant steps, but log only the ambient queries of the final decision.
Resource indices and input data keep their independent universes. -/
def runWithAmbientStepLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s) (AmbientStepLog V Out) :=
  let full := ambient + challengeSpec oracleSig s
  let toFull : QueryImpl ambient (OracleComp full) := fun r => liftM (full.query (.inl r))
  (fun r => ⟨r.1, r.2.1, r.2.2⟩) <$> V.executeWith stmt data
    (ITrace := List (LoggedStep full s)) (DTrace := fun _ => QueryLog ambient)
    (fun action => action.run)
    (StepInstrumentation.mapStepsWith (C := fun t => TranscriptPrefix t → TranscriptPrefix s)
      (@logStep _ full s) (@extendPrefix s) id .focal (prover.simulate toFull))
    (StepInstrumentation.mapStepsWith (C := fun t => TranscriptPrefix t → TranscriptPrefix s)
      (@logStep _ full s) (@extendPrefix s) id .counterpart
      (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))
    (fun p view resources => (simulateQ
      (QueryImpl.addLift toFull.withLogging ((pathResources inputs s p).answer resources) :
        QueryImpl _ (WriterT (QueryLog ambient) (OracleComp full)))
      (V.decide stmt p view).run).run)

/-- Forgetting the step boundaries gives the original ambient logging equation. -/
theorem runWithAmbientStepLog_toLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientStepLog.toLog <$> V.runWithAmbientStepLog stmt data prover = (
let full := ambient + challengeSpec oracleSig s
  let toFull : QueryImpl ambient (OracleComp full) := fun q => liftM (full.query (.inl q))
  (simulateQ (QueryImpl.id' full).withLogging (TwoParty.Lens.run s (prover.simulate toFull)
    (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))).run >>= fun x =>
  let tr := x.1.1
  let p := projectPathAlong oracleSig s tr
  let resources : (pathResources inputs s p).Data := (data, payloads s tr)
  (simulateQ (QueryImpl.addLift toFull.withLogging
      ((pathResources inputs s p).answer resources) :
        QueryImpl _ (WriterT (QueryLog ambient) (OracleComp full)))
    (V.decide stmt p (toView s tr)).run).run >>= fun y =>
  pure (⟨tr, x.1.2.1, y.1.map fun t => (t, (V.outputMap stmt p (toView s tr)).f resources)⟩,
    x.2.fst, y.2)) := by
  simp only [runWithAmbientStepLog, executeWith, Functor.map_map,
    _root_.map_bind]
  have id_logging {α : Type} (p : OracleComp (ambient + challengeSpec oracleSig s) α) :
      (simulateQ (QueryImpl.id' (ambient + challengeSpec oracleSig s)).withLogging p).run =
        p.withQueryLog := rfl
  rw [id_logging, ← runLoggingSteps_log, bind_map_left]
  refine bind_congr fun r => ?_
  simp [AmbientStepLog.toLog]

end AmbientStepLog

end OracleVerifier
end Interaction.Core
