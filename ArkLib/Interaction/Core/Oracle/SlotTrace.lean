/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.OracleVerifier
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Per-slot execution provenance

Prefixes contain the actual moves, including challenges and oracle payloads. Slot owners come
from the participant whose action the runner executes. The passive verifier's decision is a
separate terminal phase. Logging each slot preserves the order and multiplicity of queries.
-/

@[expose] public section

universe u q uA vC uS uI dI wJ

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec

/-- The actual moves before an execution boundary, possibly stopping before the leaf. -/
def FullPrefix : (s : OracleProtocol.{u, q}) → Type u
  | .pure _ => Option PEmpty
  | .liftBind a next => Option ((x : Move oracleSig a) ×
      FullPrefix (next (oracleSig.toFunB a x)))

namespace FullPrefix

/-- The empty actual prefix. -/
def here {s : OracleProtocol.{u, q}} : FullPrefix s := by cases s <;> exact none

/-- Extend a child prefix by the preceding actual move. -/
def cons {a : OraclePos.{u, q}} {next : OraclePoly.B a → OracleProtocol}
    (x : Move oracleSig a) (tail : FullPrefix (next (oracleSig.toFunB a x))) :
    FullPrefix (.liftBind a next) := some ⟨x, tail⟩

/-- Number of moves already made at this boundary. -/
def length : {s : OracleProtocol.{u, q}} → FullPrefix s → Nat
  | .pure _, _ => 0
  | .liftBind _ _, none => 0
  | .liftBind _ _, some ⟨_, tail⟩ => tail.length + 1

/-- The prefix at the terminal boundary retains every move of a completed transcript. -/
def complete : (s : OracleProtocol.{u, q}) → PathAlong oracleSig s → FullPrefix s
  | .pure _, _ => none
  | .liftBind _ next, ⟨x, tr⟩ => .cons x (complete (next (oracleSig.toFunB _ x)) tr)

end FullPrefix

/-- A slot's participant is intrinsic to its constructor. -/
inductive SlotOwner where
  | prover
  | sampler
  | decision
  deriving DecidableEq

/-- The participant's role, independent of ownership of the exchanged move. -/
def SlotOwner.party : SlotOwner → TwoParty.Role
  | .prover => .sender
  | .sampler | .decision => .receiver

/-- One executed slot, with the actual prefix before its action and all its queries. -/
structure SlotPhase {ι : Type} (spec : OracleSpec ι) (s : OracleProtocol.{0, q}) where
  /-- Moves preceding this action. -/
  «prefix» : FullPrefix s
  /-- Participant whose slot was executed. -/
  slot : SlotOwner
  /-- Queries and successful responses, with repetitions and order preserved. -/
  queries : QueryLog spec

namespace SlotPhase

/-- Ownership is read from the executed slot, without a replacement role decoration. -/
def party {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (phase : SlotPhase spec s) : TwoParty.Role := phase.slot.party

/-- Prepend the move that led to the child execution. -/
def cons {ι : Type} {spec : OracleSpec ι} {a : OraclePos.{0, q}}
    {next : OraclePoly.B a → OracleProtocol} (x : Move oracleSig a)
    (phase : SlotPhase spec (next (oracleSig.toFunB a x))) : SlotPhase spec (.liftBind a next) :=
  ⟨.cons x phase.prefix, phase.slot, phase.queries⟩

end SlotPhase

/-- Concatenate the slot logs in execution order. -/
def slotQueries {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (phases : List (SlotPhase spec s)) : QueryLog spec := phases.flatMap (·.queries)

namespace SlotInstrumentation

/-- Interpret PolyFun's exchange law through any monad morphism. -/
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

/-- Wrap participant actions and translate their continuations. This transforms strategies;
move exchange and execution remain exclusively in `TwoParty.Lens.run`. -/
def transform
    (action : {s : FreeM P PUnit.{u + 1}} → {A : Type u} →
      C s → Participant.{u} → m A → n A)
    (descend : (a : P.A) → (next : P.B a → FreeM P PUnit.{u + 1}) →
      (x : Move l a) → C (.liftBind a next) → C (next (l.toFunB a x))) :
    {s : FreeM P PUnit.{u + 1}} → {Out : PathAlong l s → Type u} →
    C s → (agent : Participant.{u}) → Strategy l m agent s Out → Strategy l n agent s Out
  | .pure _, _, env, agent, p => action env agent p
  | .liftBind a next, _, env, agent, p =>
    Choice.map agent (owner l a)
      (fun x child => transform (@action) descend (descend a next x env) agent child) <$>
        action env agent p

/-- Naturality of the authoritative runner for labelled action instrumentation. Local action
interpretations suffice; the polynomial, lens, environment and all three monads are arbitrary.
This supplies the missing general PolyFun law without introducing an executor. -/
theorem run_natural [LawfulMonad m] [LawfulMonad n] [LawfulMonad k]
    (F : n →ᵐ k) (G : m →ᵐ k)
    (action : {s : FreeM P PUnit.{u + 1}} → {A : Type u} →
      C s → Participant.{u} → m A → n A)
    (descend : (a : P.A) → (next : P.B a → FreeM P PUnit.{u + 1}) →
      (x : Move l a) → C (.liftBind a next) → C (next (l.toFunB a x)))
    (comm : ∀ {s A} (env : C s) agent (p : m A), F.toFun A (action env agent p) = G.toFun A p) :
    (s : FreeM P PUnit.{u + 1}) → {OutP OutC : PathAlong l s → Type u} →
    (env : C s) → (p : Focal l m s OutP) → (c : Counterpart l m s OutC) →
    F.toFun _ (TwoParty.Lens.run s (transform (C := C) (@action) descend env .focal p)
      (transform (C := C) (@action) descend env .counterpart c)) =
      G.toFun _ (TwoParty.Lens.run s p c)
  | .pure leaf, _, _, env, p, c => by
    cases leaf
    simp only [transform, FreeM.pure_eq_pure, run_done, F.toFun_bind', G.toFun_bind',
      F.toFun_pure', G.toFun_pure', comm]
  | .liftBind a next, _, _, env, p, c => by
    rw [run_node, run_node]
    simp only [transform, step_map_left, step_map_right]
    rw [map_step F, map_step G]
    simp only [comm]
    congr 1
    funext x pn cn
    simp only [F.toFun_bind', G.toFun_bind', F.toFun_pure', G.toFun_pure']
    rw [run_natural F G (@action) descend comm]

end Strategies

/-- Map a list-valued writer through a monoid map given by list concatenation. -/
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

end SlotInstrumentation

/-- Instrument a slot with its actual prefix, intrinsic participant and successful queries. -/
def observeSlot {ι : Type} {spec : OracleSpec ι} {root s : OracleProtocol.{0, q}} {A : Type}
    (embed : FullPrefix s → FullPrefix root) (agent : Participant)
    (p : OracleComp spec A) : WriterT (List (SlotPhase spec root)) (OracleComp spec) A :=
  WriterT.mk ((fun r => (r.1, [⟨embed .here,
    match agent with | .focal => .prover | .counterpart => .sampler, r.2⟩])) <$> p.withQueryLog)

/-- Extend the instrumentation environment by the move delivered by the authoritative runner. -/
def descendPrefix {root : OracleProtocol.{0, q}} (a : OraclePos.{0, q})
    (next : OraclePoly.B a → OracleProtocol) (x : Move oracleSig a)
    (embed : FullPrefix (.liftBind a next) → FullPrefix root) :
    FullPrefix (next (oracleSig.toFunB a x)) → FullPrefix root :=
  fun tail => embed (.cons x tail)

/-- Run PolyFun itself in the writer layer on instrumented participant strategies. -/
def observeInteraction {ι : Type} {spec : OracleSpec ι} (s : OracleProtocol.{0, q})
    {OutP OutC : PathAlong oracleSig s → Type}
    (p : Focal oracleSig (OracleComp spec) s OutP)
    (c : Counterpart oracleSig (OracleComp spec) s OutC) :
    OracleComp spec (((tr : PathAlong oracleSig s) × OutP tr × OutC tr) ×
      List (SlotPhase spec s)) :=
  (TwoParty.Lens.run s
    (SlotInstrumentation.transform (C := fun t => FullPrefix t → FullPrefix s)
      (@observeSlot ι spec s) (@descendPrefix s) id .focal p)
    (SlotInstrumentation.transform (C := fun t => FullPrefix t → FullPrefix s)
      (@observeSlot ι spec s) (@descendPrefix s) id .counterpart c)).run

/-- Concatenating slot logs erases the writer's boundaries by runner naturality. -/
theorem observeInteraction_log {ι : Type} {spec : OracleSpec ι} (s : OracleProtocol.{0, q})
    {OutP OutC : PathAlong oracleSig s → Type}
    (p : Focal oracleSig (OracleComp spec) s OutP)
    (c : Counterpart oracleSig (OracleComp spec) s OutC) :
    (fun r => (r.1, slotQueries r.2)) <$> observeInteraction s p c =
      (TwoParty.Lens.run s p c).withQueryLog := by
  have comm {t A} (env : FullPrefix t → FullPrefix s) agent (program : OracleComp spec A) :
      (SlotInstrumentation.writerMap (fun phase : SlotPhase spec s => phase.queries))
        (observeSlot env agent program) = simulateQ spec.loggingOracle program := by
    apply WriterT.ext
    simp only [SlotInstrumentation.writerMap, observeSlot, WriterT.run_mk, Functor.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change (fun a => (a.1, a.2)) <$> program.withQueryLog = program.withQueryLog
    exact LawfulFunctor.id_map _
  have natural := SlotInstrumentation.run_natural
    (SlotInstrumentation.writerMap (fun phase : SlotPhase spec s => phase.queries))
    (simulateQ' spec.loggingOracle) (@observeSlot ι spec s)
    (@descendPrefix s)
    (fun env agent program => comm env agent program) s id p c
  exact congrArg WriterT.run natural

/-- Concatenation ignores the prefix extension of child phases. -/
theorem slotQueries_cons {ι : Type} {spec : OracleSpec ι} {a : OraclePos.{0, q}}
    {next : OraclePoly.B a → OracleProtocol} (x : Move oracleSig a)
    (phases : List (SlotPhase spec (next (oracleSig.toFunB a x)))) :
    slotQueries (phases.map (SlotPhase.cons x)) = slotQueries phases := by
  induction phases with
  | nil => rfl
  | cons phase phases ih =>
    simpa only [slotQueries, List.map_cons, List.flatMap_cons, SlotPhase.cons] using
      congrArg (phase.queries ++ ·) ih

/-- Projecting each slot to ambient queries commutes with chronological concatenation. -/
theorem slotQueries_fst {ι κ : Type} {a : OracleSpec ι} {b : OracleSpec κ}
    {s : OracleProtocol.{0, q}} (phases : List (SlotPhase (a + b) s)) :
    slotQueries (phases.map (fun phase =>
      (⟨phase.prefix, phase.slot, phase.queries.fst⟩ : SlotPhase a s))) =
      (slotQueries phases).fst := by
  induction phases with
  | nil => rfl
  | cons phase rest ih =>
    simpa only [slotQueries, List.map_cons, List.flatMap_cons, QueryLog.fst_append] using
      congrArg (phase.queries.fst ++ ·) ih

namespace OracleVerifier

variable {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : Resources.{0, 0, dI}} {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : PathAlong oracleSig s → Type}

/-- A completed run with participant slots and the final decision's full query log. -/
structure TracedRun (V : OracleVerifier ambient s S T inputs outputs)
    (Out : PathAlong oracleSig s → Type) where
  /-- The ordinary run observation, including rejection and private prover output. -/
  observation : Observation oracleSig s Out (OracleVerifier.Output T B)
  /-- Participant slots, before the final decision, in execution order. -/
  interaction : List (SlotPhase (ambient + challengeSpec oracleSig s) s)
  /-- The terminal decision's queries before resource routing. -/
  decisionQueries : QueryLog
    (ambient + (pathResources inputs s (projectPathAlong oracleSig s observation.1)).spec)

namespace TracedRun

/-- Forget slot boundaries while retaining exactly the two existing query logs. -/
def logView {V : OracleVerifier ambient s S T inputs outputs} (r : TracedRun V Out) :=
  (⟨r.observation, (slotQueries r.interaction).fst, r.decisionQueries⟩ :
    (obs : Observation oracleSig s Out (OracleVerifier.Output T B)) × QueryLog ambient ×
      QueryLog (ambient + (pathResources inputs s (projectPathAlong oracleSig s obs.1)).spec))

/-- The terminal verifier decision has the completed actual prefix and receiver ownership. -/
def terminalPhase {V : OracleVerifier ambient s S T inputs outputs} (r : TracedRun V Out) :
    SlotPhase ambient s :=
  ⟨FullPrefix.complete s r.observation.1, .decision, r.decisionQueries.fst⟩

/-- Ambient phases of the produced run, including the final decision under P1. -/
def phases {V : OracleVerifier ambient s S T inputs outputs} (r : TracedRun V Out) :
    List (SlotPhase ambient s) :=
  r.interaction.map (fun phase => ⟨phase.prefix, phase.slot, phase.queries.fst⟩) ++
    [r.terminalPhase]

/-- Every selected phase belongs to this produced execution. -/
theorem phase_mem {V : OracleVerifier ambient s S T inputs outputs} (r : TracedRun V Out)
    (i : Fin r.phases.length) : r.phases[i] ∈ r.phases := List.getElem_mem _

/-- Concatenating the ambient logs commutes with forgetting individual slot boundaries. -/
theorem interaction_queries {V : OracleVerifier ambient s S T inputs outputs}
    (r : TracedRun V Out) :
    slotQueries (r.interaction.map (fun phase =>
      (⟨phase.prefix, phase.slot, phase.queries.fst⟩ : SlotPhase ambient s))) =
      (slotQueries r.interaction).fst := slotQueries_fst r.interaction

/-- Aggregate ambient logs are the ordered concatenation of all per-slot queries. -/
theorem phases_queries {V : OracleVerifier ambient s S T inputs outputs} (r : TracedRun V Out) :
    slotQueries r.phases = (slotQueries r.interaction).fst ++ r.decisionQueries.fst := by
  change (List.flatMap (fun phase : SlotPhase ambient s => phase.queries) (_ ++ _)) = _
  rw [List.flatMap_append]
  simpa only [slotQueries, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    terminalPhase] using
    congrArg (· ++ r.decisionQueries.fst) r.interaction_queries

/-- Retain an explicitly separate prover setup slot before the interaction. -/
def prependSetup {V : OracleVerifier ambient s S T inputs outputs}
    (r : TracedRun V Out) (queries : QueryLog ambient) : TracedRun V Out :=
  { r with interaction := ⟨.here, .prover, QueryLog.inl queries⟩ :: r.interaction }

/-- The setup slot contributes its queries before every interaction query. -/
theorem logView_prependSetup {V : OracleVerifier ambient s S T inputs outputs}
    (r : TracedRun V Out) (queries : QueryLog ambient) :
    (r.prependSetup queries).logView =
      ⟨r.observation, queries ++ (slotQueries r.interaction).fst, r.decisionQueries⟩ := by
  simp only [logView, prependSetup, slotQueries, List.flatMap_cons, QueryLog.fst_append,
    QueryLog.fst_inl]
  rfl

/-- The final verifier decision belongs to the produced phase list. -/
theorem terminalPhase_mem {V : OracleVerifier ambient s S T inputs outputs} (r : TracedRun V Out) :
    r.terminalPhase ∈ r.phases := by simp [phases]

/-- The terminal prefix is exactly the full transcript of this run. -/
theorem terminalPhase_prefix {V : OracleVerifier ambient s S T inputs outputs}
    (r : TracedRun V Out) :
    r.terminalPhase.prefix = FullPrefix.complete s r.observation.1 := rfl

end TracedRun

/-- Run once, recording the actual prefix and queries of each participant slot, then the final
verifier decision. Both resource queries and ambient queries of the decision remain available. -/
def runWithTrace (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s) (TracedRun V Out) :=
  let full := ambient + challengeSpec oracleSig s
  (fun r => ⟨r.1, r.2.1, r.2.2⟩) <$> V.executeWith stmt data
    (ITrace := List (SlotPhase full s))
    (DTrace := fun p => QueryLog (ambient + (pathResources inputs s p).spec))
    (fun action => action.run)
    (SlotInstrumentation.transform (C := fun t => FullPrefix t → FullPrefix s)
      (@observeSlot _ full s) (@descendPrefix s) id .focal
      (prover.simulate (fun q => liftM (full.query (.inl q)))))
    (SlotInstrumentation.transform (C := fun t => FullPrefix t → FullPrefix s)
      (@observeSlot _ full s) (@descendPrefix s) id .counterpart
      (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))
    (fun p view resources => (simulateQ (QueryImpl.addLift
      ((fun q => liftM (full.query (.inl q))) : QueryImpl ambient (OracleComp full))
      ((pathResources inputs s p).answer resources)).withLogging
      (V.decide stmt p view).run).run)

/-- Concatenating slot queries gives the full logger on the ordinary interaction and decision. -/
theorem runWithTrace_log (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    TracedRun.logView <$> V.runWithTrace stmt data prover = (do
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
  simp only [runWithTrace, executeWith, Functor.map_map, _root_.map_bind]
  have id_logging {α : Type} (p : OracleComp (ambient + challengeSpec oracleSig s) α) :
      (simulateQ (QueryImpl.id' (ambient + challengeSpec oracleSig s)).withLogging p).run =
        p.withQueryLog := rfl
  rw [id_logging, ← observeInteraction_log, bind_map_left]
  refine bind_congr fun r => ?_
  simp [TracedRun.logView]

section AmbientTrace

variable {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol.{0, q}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : Resources.{0, uI, dI}} {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : PathAlong oracleSig s → Type}

/-- Ambient provenance permits independent input and oracle-node query universes. The only
returned queries are ambient requests and challenge draws, whose indices are small. -/
structure AmbientTracedRun (V : OracleVerifier ambient s S T inputs outputs)
    (Out : PathAlong oracleSig s → Type) where
  /-- The ordinary completed observation, including output resources and rejection. -/
  observation : Observation oracleSig s Out (OracleVerifier.Output T B)
  /-- The slots produced by the same interaction runner used by the full trace. -/
  interaction : List (SlotPhase (ambient + challengeSpec oracleSig s) s)
  /-- The decision's ambient requests and their actual responses. -/
  decisionQueries : QueryLog ambient

namespace AmbientTracedRun

/-- Forget the phase boundaries to recover the existing two ambient logs. -/
def logView {V : OracleVerifier ambient s S T inputs outputs} (r : AmbientTracedRun V Out) :=
  (r.observation, (slotQueries r.interaction).fst, r.decisionQueries)

/-- The final verifier decision has the completed actual prefix and receiver ownership. -/
def terminalPhase {V : OracleVerifier ambient s S T inputs outputs} (r : AmbientTracedRun V Out) :
    SlotPhase ambient s :=
  ⟨FullPrefix.complete s r.observation.1, .decision, r.decisionQueries⟩

/-- Ambient phases, including the decision as its own terminal phase. -/
def phases {V : OracleVerifier ambient s S T inputs outputs} (r : AmbientTracedRun V Out) :
    List (SlotPhase ambient s) :=
  r.interaction.map (fun phase => ⟨phase.prefix, phase.slot, phase.queries.fst⟩) ++
    [r.terminalPhase]

/-- Every selected phase belongs to the produced ambient trace. -/
theorem phase_mem {V : OracleVerifier ambient s S T inputs outputs} (r : AmbientTracedRun V Out)
    (i : Fin r.phases.length) : r.phases[i] ∈ r.phases := List.getElem_mem _

/-- The terminal decision belongs to the produced ambient trace. -/
theorem terminalPhase_mem {V : OracleVerifier ambient s S T inputs outputs}
    (r : AmbientTracedRun V Out) : r.terminalPhase ∈ r.phases := by simp [phases]

/-- The ambient aggregate logs concatenate the produced per-slot query groups in order. -/
theorem phases_queries {V : OracleVerifier ambient s S T inputs outputs}
    (r : AmbientTracedRun V Out) :
    slotQueries r.phases = (slotQueries r.interaction).fst ++ r.decisionQueries := by
  change (List.flatMap (fun phase : SlotPhase ambient s => phase.queries) (_ ++ _)) = _
  rw [List.flatMap_append]
  simpa only [slotQueries, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    terminalPhase] using congrArg (· ++ r.decisionQueries) (slotQueries_fst r.interaction)

end AmbientTracedRun

/-- Instrument the same participant slots, logging only ambient queries of the final decision.
Resource indices and input data retain their independent universes. -/
def runWithAmbientTrace (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s) (AmbientTracedRun V Out) :=
  let full := ambient + challengeSpec oracleSig s
  let toFull : QueryImpl ambient (OracleComp full) := fun r => liftM (full.query (.inl r))
  (fun r => ⟨r.1, r.2.1, r.2.2⟩) <$> V.executeWith stmt data
    (ITrace := List (SlotPhase full s)) (DTrace := fun _ => QueryLog ambient)
    (fun action => action.run)
    (SlotInstrumentation.transform (C := fun t => FullPrefix t → FullPrefix s)
      (@observeSlot _ full s) (@descendPrefix s) id .focal (prover.simulate toFull))
    (SlotInstrumentation.transform (C := fun t => FullPrefix t → FullPrefix s)
      (@observeSlot _ full s) (@descendPrefix s) id .counterpart
      (sampler oracleSig s (fun c => liftM (full.query (.inr c)))))
    (fun p view resources => (simulateQ
      (QueryImpl.addLift toFull.withLogging ((pathResources inputs s p).answer resources) :
        QueryImpl _ (WriterT (QueryLog ambient) (OracleComp full)))
      (V.decide stmt p view).run).run)

/-- Erasing ambient slot boundaries gives the original ambient logging equation. -/
theorem runWithAmbientTrace_log (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientTracedRun.logView <$> V.runWithAmbientTrace stmt data prover = (
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
  simp only [runWithAmbientTrace, executeWith, Functor.map_map,
    _root_.map_bind]
  have id_logging {α : Type} (p : OracleComp (ambient + challengeSpec oracleSig s) α) :
      (simulateQ (QueryImpl.id' (ambient + challengeSpec oracleSig s)).withLogging p).run =
        p.withQueryLog := rfl
  rw [id_logging, ← observeInteraction_log, bind_map_left]
  refine bind_congr fun r => ?_
  simp [AmbientTracedRun.logView]

end AmbientTrace

end OracleVerifier
end Interaction.Core
