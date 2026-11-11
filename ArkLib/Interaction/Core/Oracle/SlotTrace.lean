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

universe u q uS uI dI wJ

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

/-- Execute a focal-first exchange, logging the two participant slots separately. -/
def loggedStep {ι : Type} {spec : OracleSpec ι} {X : Type} {A B : X → Type} {R : Type}
    (role : TwoParty.Role) (p : OracleComp spec (Choice .focal role X A))
    (c : OracleComp spec (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → QueryLog spec → QueryLog spec → OracleComp spec R) :
    OracleComp spec R :=
  match role with
  | .sender => do
    let (v, lp) ← p.withQueryLog
    let (f, lc) ← c.withQueryLog
    k v.1 v.2 (f v.1) lp lc
  | .receiver => do
    let (f, lp) ← p.withQueryLog
    let (v, lc) ← c.withQueryLog
    k v.1 (f v.1) v.2 lp lc

/-- Mapping the result of a logged exchange maps its continuation. -/
theorem map_loggedStep {ι : Type} {spec : OracleSpec ι} {X : Type} {A B : X → Type}
    {R R' : Type} (role : TwoParty.Role) (p : OracleComp spec (Choice .focal role X A))
    (c : OracleComp spec (Choice .counterpart role X B)) (f : R → R')
    (k : ∀ x, A x → B x → QueryLog spec → QueryLog spec → OracleComp spec R) :
    f <$> loggedStep role p c k =
      loggedStep role p c (fun x pn cn lp lc => f <$> k x pn cn lp lc) := by
  cases role <;> simp [loggedStep, _root_.map_bind]

/-- Erasing the boundary between two slots concatenates their logs. -/
theorem loggedStep_log {ι : Type} {spec : OracleSpec ι} {X : Type} {A B : X → Type}
    {R : Type} (role : TwoParty.Role) (p : OracleComp spec (Choice .focal role X A))
    (c : OracleComp spec (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → OracleComp spec R) :
    loggedStep role p c (fun x pn cn lp lc =>
      (fun r => (r.1, lp ++ lc ++ r.2)) <$> (k x pn cn).withQueryLog) =
      (step role .focalFirst p c k).withQueryLog := by
  cases role <;>
    simp only [loggedStep, step, Schedule.seq, withQueryLog_bind, _root_.map_bind,
      Functor.map_map]
  all_goals
    refine bind_congr fun v => ?_
    refine bind_congr fun w => ?_
    congr 1
    funext r
    change (r.1, (v.2 ++ w.2) ++ r.2) = (r.1, v.2 ++ (w.2 ++ r.2))
    rw [List.append_assoc]

/-- Any result of a logged exchange comes from one of its actual continuation calls. -/
theorem mem_support_loggedStep {ι : Type} {spec : OracleSpec ι} {X : Type} {A B : X → Type}
    {R : Type} (role : TwoParty.Role) (p : OracleComp spec (Choice .focal role X A))
    (c : OracleComp spec (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → QueryLog spec → QueryLog spec → OracleComp spec R)
    {r : R} (h : r ∈ support (loggedStep role p c k)) :
    ∃ x pn cn lp lc, r ∈ support (k x pn cn lp lc) := by
  cases role <;> simp only [loggedStep, mem_support_bind_iff] at h
  · obtain ⟨v, _, w, _, h⟩ := h
    exact ⟨v.1.1, v.1.2, w.1 v.1.1, v.2, w.2, h⟩
  · obtain ⟨v, _, w, _, h⟩ := h
    exact ⟨w.1.1, v.1 w.1.1, w.1.2, v.2, w.2, h⟩

/-- The interaction runner with one phase for each executed participant slot. -/
def runSlotTrace {ι : Type} {spec : OracleSpec ι} :
    (s : OracleProtocol.{0, q}) → {OutP OutC : PathAlong oracleSig s → Type} →
    Focal oracleSig (OracleComp spec) s OutP → Counterpart oracleSig (OracleComp spec) s OutC →
    OracleComp spec (((tr : PathAlong oracleSig s) × OutP tr × OutC tr) ×
      List (SlotPhase spec s))
  | .pure _, _, _, p, c => do
    let (op, lp) ← p.withQueryLog
    let (oc, lc) ← c.withQueryLog
    pure (⟨⟨⟩, op, oc⟩, [⟨.here, .prover, lp⟩, ⟨.here, .sampler, lc⟩])
  | .liftBind a next, _, _, p, c =>
    loggedStep (owner oracleSig a) p c fun x pn cn lp lc => do
      let (result, phases) ← runSlotTrace (next (oracleSig.toFunB a x)) pn cn
      pure (⟨⟨x, result.1⟩, result.2⟩,
        ⟨.here, .prover, lp⟩ :: ⟨.here, .sampler, lc⟩ :: phases.map (SlotPhase.cons x))

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

/-- Forgetting slot boundaries gives exactly the ordinary query logger on the interaction. -/
theorem runSlotTrace_log {ι : Type} {spec : OracleSpec ι} :
    (s : OracleProtocol.{0, q}) → {OutP OutC : PathAlong oracleSig s → Type} →
    (p : Focal oracleSig (OracleComp spec) s OutP) →
    (c : Counterpart oracleSig (OracleComp spec) s OutC) →
    (fun r => (r.1, slotQueries r.2)) <$> runSlotTrace s p c =
      (TwoParty.Lens.run s p c).withQueryLog
  | .pure leaf, _, _, p, c => by
    cases leaf
    simp [runSlotTrace, run_done, withQueryLog_bind, slotQueries, monad_norm]
  | .liftBind a next, _, _, p, c => by
    rw [runSlotTrace, run_node, map_loggedStep]
    trans loggedStep (owner oracleSig a) p c (fun x pn cn lp lc =>
      (fun r => (r.1, lp ++ lc ++ r.2)) <$>
        (TwoParty.Lens.run (next (oracleSig.toFunB a x)) pn cn >>= fun r =>
          pure ⟨⟨x, r.1⟩, r.2⟩).withQueryLog)
    · congr 1
      funext x pn cn lp lc
      simp only [_root_.map_bind, LawfulApplicative.map_pure, withQueryLog_bind,
        withQueryLog_pure]
      rw [← runSlotTrace_log]
      simp only [bind_map_left]
      congr 1
      funext r
      change pure (_, lp ++ (lc ++ slotQueries (r.2.map (SlotPhase.cons x)))) =
        pure (_, (lp ++ lc) ++ (slotQueries r.2 ++ []))
      rw [slotQueries_cons, List.append_nil, List.append_assoc]
      rfl
    · exact loggedStep_log _ _ _ _

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
    OracleComp (ambient + challengeSpec oracleSig s) (TracedRun V Out) := do
  let full := ambient + challengeSpec oracleSig s
  let ⟨⟨tr, out, _⟩, phases⟩ ← runSlotTrace s
    (prover.simulate (fun q => liftM (full.query (.inl q))))
    (sampler oracleSig s (fun c => liftM (full.query (.inr c))))
  let p := projectPathAlong oracleSig s tr
  let view := toView s tr
  let resources : (pathResources inputs s p).Data := (data, payloads s tr)
  let handler : QueryImpl (ambient + (pathResources inputs s p).spec) (OracleComp full) :=
    QueryImpl.addLift ((fun q => liftM (full.query (.inl q))) : QueryImpl ambient (OracleComp full))
      ((pathResources inputs s p).answer resources)
  let (verdict, queries) ← (simulateQ handler.withLogging (V.decide stmt p view).run).run
  pure ⟨⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f resources)⟩, phases, queries⟩

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
  simp only [runWithTrace, _root_.map_bind]
  have id_logging {α : Type} (p : OracleComp (ambient + challengeSpec oracleSig s) α) :
      (simulateQ (QueryImpl.id' (ambient + challengeSpec oracleSig s)).withLogging p).run =
        p.withQueryLog := rfl
  rw [id_logging, ← runSlotTrace_log, bind_map_left]
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
    OracleComp (ambient + challengeSpec oracleSig s) (AmbientTracedRun V Out) := do
  let full := ambient + challengeSpec oracleSig s
  let toFull : QueryImpl ambient (OracleComp full) := fun r => liftM (full.query (.inl r))
  let ⟨⟨tr, out, _⟩, phases⟩ ← runSlotTrace s (prover.simulate toFull)
    (sampler oracleSig s (fun c => liftM (full.query (.inr c))))
  let p := projectPathAlong oracleSig s tr
  let view := toView s tr
  let resources : (pathResources inputs s p).Data := (data, payloads s tr)
  let (verdict, queries) ← (simulateQ
    (QueryImpl.addLift toFull.withLogging ((pathResources inputs s p).answer resources) :
      QueryImpl _ (WriterT (QueryLog ambient) (OracleComp full)))
    (V.decide stmt p view).run).run
  pure ⟨⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f resources)⟩, phases, queries⟩

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
  simp only [runWithAmbientTrace, _root_.map_bind]
  have id_logging {α : Type} (p : OracleComp (ambient + challengeSpec oracleSig s) α) :
      (simulateQ (QueryImpl.id' (ambient + challengeSpec oracleSig s)).withLogging p).run =
        p.withQueryLog := rfl
  rw [id_logging, ← runSlotTrace_log, bind_map_left]
  refine bind_congr fun r => ?_
  simp [AmbientTracedRun.logView]

end AmbientTrace

end OracleVerifier
end Interaction.Core
