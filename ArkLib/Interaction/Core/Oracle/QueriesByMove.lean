/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.OracleVerifier
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# The queries of an oracle verifier run, by move

A run of an oracle protocol is a sequence of moves: prover messages, challenge draws and oracle
messages. For each move, this file records the queries made at that point. The prover and the
sampler each query at their moves. The verifier makes its queries once, in its decision after the
last move. The decision and a separate prover setup are not moves, so an entry of the log is
named for what it holds: the queries that one querier made at one partial transcript.

* `PartialTranscript oracleSig s` (from `Core/Transcript.lean`) is the partial transcript at one
  point: the moves already made, including challenges and oracle messages.
* `Querier` says who queries. The runner takes the querier from the participant whose action it
  executes. The passive verifier's decision is a separate querier at the end.
* `QueriesAt` is one entry: a partial transcript, the querier that made queries there, and its
  queries.
* `MoveInstrumentation.mapMovesWith` wraps each participant action so that it logs an entry. The
  core runner `TwoParty.Lens.run` still executes every move.
* `OracleVerifier.QueriesByMove` is the log of a whole run, and `runWithQueriesByMove` produces
  it. Each move logs its own queries. The log therefore keeps their order and multiplicity.
-/

@[expose] public section

universe u q uA vC uS uI dI wJ

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec

/-- The party that makes the queries of an entry. The constructor fixes the party. -/
inductive Querier where
  | prover
  | sampler
  | decision
  deriving DecidableEq

/-- The two-party role of the querier. The prover sends, and the sampler and the decision
receive. The querier alone fixes the role, with no extra role decoration of the exchanged move. -/
def Querier.role : Querier → TwoParty.Role
  | .prover => .sender
  | .sampler | .decision => .receiver

/-- The queries that one querier made at one partial transcript: the moves made before them, the
querier and all its queries. -/
structure QueriesAt {ι : Type} (spec : OracleSpec ι) (s : OracleProtocol.{0, q}) where
  /-- The moves made before these queries. -/
  before : PartialTranscript oracleSig s
  /-- The party that made these queries. -/
  querier : Querier
  /-- The queries and their successful responses, in order and with repeats. -/
  queries : QueryLog spec

namespace QueriesAt

/-- The role of the entry's querier. It is read from the querier, with no extra role
decoration. -/
def role {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (entry : QueriesAt spec s) : TwoParty.Role := entry.querier.role

/-- Put the move that led to the child protocol in front of the entry's partial transcript. -/
def cons {ι : Type} {spec : OracleSpec ι} {a : OraclePos.{0, q}}
    {next : OraclePoly.B a → OracleProtocol} (x : Move oracleSig a)
    (entry : QueriesAt spec (next (oracleSig.toFunB a x))) : QueriesAt spec (.liftBind a next) :=
  ⟨.cons x entry.before, entry.querier, entry.queries⟩

end QueriesAt

/-- Concatenate the queries of the entries, in execution order. -/
def concatQueries {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (entries : List (QueriesAt spec s)) : QueryLog spec := entries.flatMap (·.queries)

namespace MoveInstrumentation

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
def mapMovesWith
    (action : {s : FreeM P PUnit.{u + 1}} → {A : Type u} →
      C s → Participant.{u} → m A → n A)
    (descend : (a : P.A) → (next : P.B a → FreeM P PUnit.{u + 1}) →
      (x : Move l a) → C (.liftBind a next) → C (next (l.toFunB a x))) :
    {s : FreeM P PUnit.{u + 1}} → {Out : Transcript l s → Type u} →
    C s → (agent : Participant.{u}) → Strategy l m agent s Out → Strategy l n agent s Out
  | .pure _, _, env, agent, p => action env agent p
  | .liftBind a next, _, env, agent, p =>
    Choice.map agent (owner l a)
      (fun x child => mapMovesWith (@action) descend (descend a next x env) agent child) <$>
        action env agent p

/-- The core runner `TwoParty.Lens.run` commutes with wrapping each action by `mapMovesWith`.
It suffices that applying `F` to each wrapped action agrees with applying `G` to the unwrapped
action. The polynomial, the lens, the environment and all three monads are arbitrary. This
supplies the missing general PolyFun law without introducing a new executor. -/
theorem run_mapMovesWith [LawfulMonad m] [LawfulMonad n] [LawfulMonad k]
    (F : n →ᵐ k) (G : m →ᵐ k)
    (action : {s : FreeM P PUnit.{u + 1}} → {A : Type u} →
      C s → Participant.{u} → m A → n A)
    (descend : (a : P.A) → (next : P.B a → FreeM P PUnit.{u + 1}) →
      (x : Move l a) → C (.liftBind a next) → C (next (l.toFunB a x)))
    (comm : ∀ {s A} (env : C s) agent (p : m A), F.toFun A (action env agent p) = G.toFun A p) :
    (s : FreeM P PUnit.{u + 1}) → {OutP OutC : Transcript l s → Type u} →
    (env : C s) → (p : Focal l m s OutP) → (c : Counterpart l m s OutC) →
    F.toFun _ (TwoParty.Lens.run s (mapMovesWith (C := C) (@action) descend env .focal p)
      (mapMovesWith (C := C) (@action) descend env .counterpart c)) =
      G.toFun _ (TwoParty.Lens.run s p c)
  | .pure leaf, _, _, env, p, c => by
    cases leaf
    simp only [mapMovesWith, FreeM.pure_eq_pure, run_done, F.toFun_bind', G.toFun_bind',
      F.toFun_pure', G.toFun_pure', comm]
  | .liftBind a next, _, _, env, p, c => by
    rw [run_node, run_node]
    simp only [mapMovesWith, step_map_left, step_map_right]
    rw [map_step F, map_step G]
    simp only [comm]
    congr 1
    funext x pn cn
    simp only [F.toFun_bind', G.toFun_bind', F.toFun_pure', G.toFun_pure']
    rw [run_mapMovesWith F G (@action) descend comm]

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

end MoveInstrumentation

/-- Run one participant action and log it as an entry. The entry records the partial transcript,
the querier and the successful queries. The querier is the prover for the focal participant and
the sampler for the counterpart. -/
def logMove {ι : Type} {spec : OracleSpec ι} {root s : OracleProtocol.{0, q}} {A : Type}
    (embed : PartialTranscript oracleSig s → PartialTranscript oracleSig root)
    (agent : Participant)
    (p : OracleComp spec A) : WriterT (List (QueriesAt spec root)) (OracleComp spec) A :=
  WriterT.mk ((fun r => (r.1, [⟨embed .empty,
    match agent with | .focal => .prover | .counterpart => .sampler, r.2⟩])) <$>
      p.withQueryLog)

/-- Extend the embedding of partial transcripts into the root protocol by the move that the core
runner delivered. -/
def embedAfterMove {root : OracleProtocol.{0, q}} (a : OraclePos.{0, q})
    (next : OraclePoly.B a → OracleProtocol) (x : Move oracleSig a)
    (embed : PartialTranscript oracleSig (.liftBind a next) → PartialTranscript oracleSig root) :
    PartialTranscript oracleSig (next (oracleSig.toFunB a x)) →
      PartialTranscript oracleSig root :=
  fun tail => embed (.cons x tail)

/-- Run the core runner `TwoParty.Lens.run` on participant strategies wrapped by `logMove`. The
writer layer collects one logged entry per action. -/
def runLoggingMoves {ι : Type} {spec : OracleSpec ι} (s : OracleProtocol.{0, q})
    {OutP OutC : Transcript oracleSig s → Type}
    (p : Focal oracleSig (OracleComp spec) s OutP)
    (c : Counterpart oracleSig (OracleComp spec) s OutC) :
    OracleComp spec (((tr : Transcript oracleSig s) × OutP tr × OutC tr) ×
      List (QueriesAt spec s)) :=
  (TwoParty.Lens.run s
    (MoveInstrumentation.mapMovesWith
      (C := fun t => PartialTranscript oracleSig t → PartialTranscript oracleSig s)
      (@logMove ι spec s) (@embedAfterMove s) id .focal p)
    (MoveInstrumentation.mapMovesWith
      (C := fun t => PartialTranscript oracleSig t → PartialTranscript oracleSig s)
      (@logMove ι spec s) (@embedAfterMove s) id .counterpart c)).run

/-- Concatenating the queries of the logged entries forgets the move boundaries and gives the
query log of the ordinary run. The proof applies `run_mapMovesWith`. -/
theorem runLoggingMoves_log {ι : Type} {spec : OracleSpec ι} (s : OracleProtocol.{0, q})
    {OutP OutC : Transcript oracleSig s → Type}
    (p : Focal oracleSig (OracleComp spec) s OutP)
    (c : Counterpart oracleSig (OracleComp spec) s OutC) :
    (fun r => (r.1, concatQueries r.2)) <$> runLoggingMoves s p c =
      (TwoParty.Lens.run s p c).withQueryLog := by
  have comm {t A} (env : PartialTranscript oracleSig t → PartialTranscript oracleSig s) agent
      (program : OracleComp spec A) :
      (MoveInstrumentation.writerMap (fun entry : QueriesAt spec s => entry.queries))
        (logMove env agent program) = simulateQ spec.loggingOracle program := by
    apply WriterT.ext
    simp only [MoveInstrumentation.writerMap, logMove, WriterT.run_mk, Functor.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change (fun a => (a.1, a.2)) <$> program.withQueryLog = program.withQueryLog
    exact LawfulFunctor.id_map _
  have natural := MoveInstrumentation.run_mapMovesWith
    (MoveInstrumentation.writerMap (fun entry : QueriesAt spec s => entry.queries))
    (simulateQ' spec.loggingOracle) (@logMove ι spec s)
    (@embedAfterMove s)
    (fun env agent program => comm env agent program) s id p c
  exact congrArg WriterT.run natural

/-- Putting a move in front of the partial transcript of each child entry does not change the
concatenated queries. -/
theorem concatQueries_cons {ι : Type} {spec : OracleSpec ι} {a : OraclePos.{0, q}}
    {next : OraclePoly.B a → OracleProtocol} (x : Move oracleSig a)
    (entries : List (QueriesAt spec (next (oracleSig.toFunB a x)))) :
    concatQueries (entries.map (QueriesAt.cons x)) = concatQueries entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simpa only [concatQueries, List.map_cons, List.flatMap_cons, QueriesAt.cons] using
      congrArg (entry.queries ++ ·) ih

/-- Keeping only the ambient queries of each entry commutes with concatenating the entries'
queries in order. -/
theorem concatQueries_fst {ι κ : Type} {a : OracleSpec ι} {b : OracleSpec κ}
    {s : OracleProtocol.{0, q}} (entries : List (QueriesAt (a + b) s)) :
    concatQueries (entries.map (fun entry =>
      (⟨entry.before, entry.querier, entry.queries.fst⟩ : QueriesAt a s))) =
      (concatQueries entries).fst := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simpa only [concatQueries, List.map_cons, List.flatMap_cons, QueryLog.fst_append] using
      congrArg (entry.queries.fst ++ ·) ih

namespace OracleVerifier

variable {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : Resources.{0, 0, dI}} {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : Transcript oracleSig s → Type}

/-- The queries of a completed run by move: the entries of the prover and the sampler, and the full
query log of the final decision. -/
structure QueriesByMove (V : OracleVerifier ambient s S T inputs outputs)
    (Out : Transcript oracleSig s → Type) where
  /-- The ordinary run outcome, including rejection and private prover output. -/
  outcome : Outcome oracleSig s Out (OracleVerifier.Output T B)
  /-- The entries of the moves before the final decision, in execution order. -/
  moves : List (QueriesAt (ambient + challengeSpec oracleSig s) s)
  /-- The decision's queries, before resource routing. -/
  decisionQueries : QueryLog
    (ambient + (pathResources inputs s (Transcript.path outcome.1)).spec)

namespace QueriesByMove

/-- Forget the move boundaries and keep exactly the two existing query logs. -/
def toLog {V : OracleVerifier ambient s S T inputs outputs} (r : QueriesByMove V Out) :=
  (⟨r.outcome, (concatQueries r.moves).fst, r.decisionQueries⟩ :
    (obs : Outcome oracleSig s Out (OracleVerifier.Output T B)) × QueryLog ambient ×
      QueryLog (ambient + (pathResources inputs s (Transcript.path obs.1)).spec))

/-- The verifier's decision as an entry. Its partial transcript is the whole transcript of the
run, and its querier is `decision`, which has the receiver role. -/
def decision {V : OracleVerifier ambient s S T inputs outputs} (r : QueriesByMove V Out) :
    QueriesAt ambient s :=
  ⟨PartialTranscript.ofTranscript s r.outcome.1, .decision, r.decisionQueries.fst⟩

/-- The moves of the run with only their ambient queries, followed by the decision. Under P1, the
decision is an entry of its own. -/
def withDecision {V : OracleVerifier ambient s S T inputs outputs} (r : QueriesByMove V Out) :
    List (QueriesAt ambient s) :=
  r.moves.map (fun entry => ⟨entry.before, entry.querier, entry.queries.fst⟩) ++
    [r.decision]

/-- Every selected entry is one of the entries of this run. -/
theorem mem_withDecision {V : OracleVerifier ambient s S T inputs outputs}
    (r : QueriesByMove V Out) (i : Fin r.withDecision.length) :
    r.withDecision[i] ∈ r.withDecision := List.getElem_mem _

/-- Keeping only the ambient queries of each move's entry commutes with concatenating the
moves' queries. -/
theorem moves_queries {V : OracleVerifier ambient s S T inputs outputs}
    (r : QueriesByMove V Out) :
    concatQueries (r.moves.map (fun entry =>
      (⟨entry.before, entry.querier, entry.queries.fst⟩ : QueriesAt ambient s))) =
      (concatQueries r.moves).fst := concatQueries_fst r.moves

/-- The concatenated queries of `withDecision` are the moves' ambient queries followed by the
decision's ambient queries. -/
theorem withDecision_queries {V : OracleVerifier ambient s S T inputs outputs}
    (r : QueriesByMove V Out) :
    concatQueries r.withDecision = (concatQueries r.moves).fst ++ r.decisionQueries.fst := by
  change (List.flatMap (fun entry : QueriesAt ambient s => entry.queries) (_ ++ _)) = _
  rw [List.flatMap_append]
  simpa only [concatQueries, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    decision] using
    congrArg (· ++ r.decisionQueries.fst) r.moves_queries

/-- Add a separate prover setup entry, with the given queries, in front of the moves' entries. It
sits at the empty partial transcript. -/
def withProverSetup {V : OracleVerifier ambient s S T inputs outputs}
    (r : QueriesByMove V Out) (queries : QueryLog ambient) : QueriesByMove V Out :=
  { r with moves := ⟨.empty, .prover, QueryLog.inl queries⟩ :: r.moves }

/-- The setup entry's queries come before the queries of all moves. -/
theorem toLog_withProverSetup {V : OracleVerifier ambient s S T inputs outputs}
    (r : QueriesByMove V Out) (queries : QueryLog ambient) :
    (r.withProverSetup queries).toLog =
      ⟨r.outcome, queries ++ (concatQueries r.moves).fst, r.decisionQueries⟩ := by
  simp only [toLog, withProverSetup, concatQueries, List.flatMap_cons, QueryLog.fst_append,
    QueryLog.fst_inl]
  rfl

/-- The decision is one of the entries of the run. -/
theorem decision_mem_withDecision {V : OracleVerifier ambient s S T inputs outputs}
    (r : QueriesByMove V Out) :
    r.decision ∈ r.withDecision := by simp [withDecision]

/-- The partial transcript at the decision is exactly the whole transcript of this run. -/
theorem decision_before {V : OracleVerifier ambient s S T inputs outputs}
    (r : QueriesByMove V Out) :
    r.decision.before = PartialTranscript.ofTranscript s r.outcome.1 := rfl

end QueriesByMove

/-- Run the verifier once. Log each move's queries with the partial transcript before the move,
then log the verifier's decision. The decision's log has both its resource queries and its
ambient queries. -/
def runWithQueriesByMove (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s) (QueriesByMove V Out) :=
  let full := ambient + challengeSpec oracleSig s
  (fun r => ⟨r.1, r.2.1, r.2.2⟩) <$> V.executeWith stmt data
    (ITrace := List (QueriesAt full s))
    (DTrace := fun p => QueryLog (ambient + (pathResources inputs s p).spec))
    (fun action => action.run)
    (MoveInstrumentation.mapMovesWith
      (C := fun t => PartialTranscript oracleSig t → PartialTranscript oracleSig s)
      (@logMove _ full s) (@embedAfterMove s) id .focal
      (prover.simulate (fun q => liftM (full.query (.inl q)))))
    (MoveInstrumentation.mapMovesWith
      (C := fun t => PartialTranscript oracleSig t → PartialTranscript oracleSig s)
      (@logMove _ full s) (@embedAfterMove s) id .counterpart
      (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))
    (fun p view resources => (simulateQ (QueryImpl.addLift
      ((fun q => liftM (full.query (.inl q))) : QueryImpl ambient (OracleComp full))
      ((pathResources inputs s p).answer resources)).withLogging
      (V.decide stmt p view).run).run)

/-- Forgetting the move boundaries gives the ordinary logging of the interaction and of the
decision. -/
theorem runWithQueriesByMove_toLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    QueriesByMove.toLog <$> V.runWithQueriesByMove stmt data prover = (do
  let full := ambient + challengeSpec oracleSig s
  let ⟨⟨tr, out, _⟩, proveLog⟩ ← (simulateQ (QueryImpl.id' full).withLogging
    (TwoParty.Lens.run s
      (prover.simulate (fun q => liftM (full.query (.inl q))))
      (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))).run
  let p := Transcript.path tr
  let view := toView s tr
  let resources : (pathResources inputs s p).Data := (data, oracleMessages s tr)
  let handler : QueryImpl (ambient + (pathResources inputs s p).spec)
      (OracleComp full) := QueryImpl.addLift
    ((fun q => liftM (full.query (.inl q))) : QueryImpl ambient (OracleComp full))
    ((pathResources inputs s p).answer resources)
  let ⟨verdict, verifyLog⟩ ← (simulateQ handler.withLogging (V.decide stmt p view).run).run
  pure ⟨⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f resources)⟩,
    proveLog.fst, verifyLog⟩) := by
  simp only [runWithQueriesByMove, executeWith, Functor.map_map, _root_.map_bind]
  have id_logging {α : Type} (p : OracleComp (ambient + challengeSpec oracleSig s) α) :
      (simulateQ (QueryImpl.id' (ambient + challengeSpec oracleSig s)).withLogging p).run =
        p.withQueryLog := rfl
  rw [id_logging, ← runLoggingMoves_log, bind_map_left]
  refine bind_congr fun r => ?_
  simp [QueriesByMove.toLog]

section AmbientQueriesByMove

variable {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol.{0, q}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : Resources.{0, uI, dI}} {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : Transcript oracleSig s → Type}

/-- The ambient queries by move let the input oracles and the oracle nodes have independent query
universes. It returns only ambient requests and challenge draws, whose indices are small. -/
structure AmbientQueriesByMove (V : OracleVerifier ambient s S T inputs outputs)
    (Out : Transcript oracleSig s → Type) where
  /-- The ordinary completed outcome, including output resources and rejection. -/
  outcome : Outcome oracleSig s Out (OracleVerifier.Output T B)
  /-- The entries of the moves, produced by the same runner as in `QueriesByMove`. -/
  moves : List (QueriesAt (ambient + challengeSpec oracleSig s) s)
  /-- The decision's ambient requests and the responses it received. -/
  decisionQueries : QueryLog ambient

namespace AmbientQueriesByMove

/-- Forget the move boundaries to recover the two existing ambient logs. -/
def toLog {V : OracleVerifier ambient s S T inputs outputs} (r : AmbientQueriesByMove V Out) :=
  (r.outcome, (concatQueries r.moves).fst, r.decisionQueries)

/-- The verifier's decision as an entry. Its partial transcript is the whole transcript of the
run, and its querier is `decision`, which has the receiver role. -/
def decision {V : OracleVerifier ambient s S T inputs outputs}
    (r : AmbientQueriesByMove V Out) :
    QueriesAt ambient s :=
  ⟨PartialTranscript.ofTranscript s r.outcome.1, .decision, r.decisionQueries⟩

/-- The moves of the run with only their ambient queries, ending with the decision as its own
entry. -/
def withDecision {V : OracleVerifier ambient s S T inputs outputs}
    (r : AmbientQueriesByMove V Out) :
    List (QueriesAt ambient s) :=
  r.moves.map (fun entry => ⟨entry.before, entry.querier, entry.queries.fst⟩) ++
    [r.decision]

/-- Every selected entry is one of the entries of these ambient queries by move. -/
theorem mem_withDecision {V : OracleVerifier ambient s S T inputs outputs}
    (r : AmbientQueriesByMove V Out) (i : Fin r.withDecision.length) :
    r.withDecision[i] ∈ r.withDecision := List.getElem_mem _

/-- The decision is one of the entries of these ambient queries by move. -/
theorem decision_mem_withDecision {V : OracleVerifier ambient s S T inputs outputs}
    (r : AmbientQueriesByMove V Out) : r.decision ∈ r.withDecision := by simp [withDecision]

/-- The concatenated queries of `withDecision` are the moves' ambient queries followed by the
decision's ambient queries. -/
theorem withDecision_queries {V : OracleVerifier ambient s S T inputs outputs}
    (r : AmbientQueriesByMove V Out) :
    concatQueries r.withDecision = (concatQueries r.moves).fst ++ r.decisionQueries := by
  change (List.flatMap (fun entry : QueriesAt ambient s => entry.queries) (_ ++ _)) = _
  rw [List.flatMap_append]
  simpa only [concatQueries, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    decision] using congrArg (· ++ r.decisionQueries) (concatQueries_fst r.moves)

end AmbientQueriesByMove

/-- Log the same moves, but log only the ambient queries of the final decision.
Resource indices and input data keep their independent universes. -/
def runWithAmbientQueriesByMove (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s) (AmbientQueriesByMove V Out) :=
  let full := ambient + challengeSpec oracleSig s
  let toFull : QueryImpl ambient (OracleComp full) := fun r => liftM (full.query (.inl r))
  (fun r => ⟨r.1, r.2.1, r.2.2⟩) <$> V.executeWith stmt data
    (ITrace := List (QueriesAt full s)) (DTrace := fun _ => QueryLog ambient)
    (fun action => action.run)
    (MoveInstrumentation.mapMovesWith
      (C := fun t => PartialTranscript oracleSig t → PartialTranscript oracleSig s)
      (@logMove _ full s) (@embedAfterMove s) id .focal (prover.simulate toFull))
    (MoveInstrumentation.mapMovesWith
      (C := fun t => PartialTranscript oracleSig t → PartialTranscript oracleSig s)
      (@logMove _ full s) (@embedAfterMove s) id .counterpart
      (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))
    (fun p view resources => (simulateQ
      (QueryImpl.addLift toFull.withLogging ((pathResources inputs s p).answer resources) :
        QueryImpl _ (WriterT (QueryLog ambient) (OracleComp full)))
      (V.decide stmt p view).run).run)

/-- Forgetting the move boundaries gives the original ambient logging equation. -/
theorem runWithAmbientQueriesByMove_toLog (V : OracleVerifier ambient s S T inputs outputs)
    (stmt : S) (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientQueriesByMove.toLog <$> V.runWithAmbientQueriesByMove stmt data prover = (
let full := ambient + challengeSpec oracleSig s
  let toFull : QueryImpl ambient (OracleComp full) := fun q => liftM (full.query (.inl q))
  (simulateQ (QueryImpl.id' full).withLogging (TwoParty.Lens.run s (prover.simulate toFull)
    (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))).run >>= fun x =>
  let tr := x.1.1
  let p := Transcript.path tr
  let resources : (pathResources inputs s p).Data := (data, oracleMessages s tr)
  (simulateQ (QueryImpl.addLift toFull.withLogging
      ((pathResources inputs s p).answer resources) :
        QueryImpl _ (WriterT (QueryLog ambient) (OracleComp full)))
    (V.decide stmt p (toView s tr)).run).run >>= fun y =>
  pure (⟨tr, x.1.2.1, y.1.map fun t => (t, (V.outputMap stmt p (toView s tr)).f resources)⟩,
    x.2.fst, y.2)) := by
  simp only [runWithAmbientQueriesByMove, executeWith, Functor.map_map,
    _root_.map_bind]
  have id_logging {α : Type} (p : OracleComp (ambient + challengeSpec oracleSig s) α) :
      (simulateQ (QueryImpl.id' (ambient + challengeSpec oracleSig s)).withLogging p).run =
        p.withQueryLog := rfl
  rw [id_logging, ← runLoggingMoves_log, bind_map_left]
  refine bind_congr fun r => ?_
  simp [AmbientQueriesByMove.toLog]

end AmbientQueriesByMove

end OracleVerifier
end Interaction.Core
