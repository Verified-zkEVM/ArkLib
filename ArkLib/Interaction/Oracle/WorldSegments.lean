/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Prefix
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.ResourceProfile

/-!
# World queries at concrete protocol boundaries

Each crossed protocol node has two local actions in ownership order; the terminal node has
one verifier action. `WorldSegments` stores those logs indexed by the actual concrete path.
Their execution-prefix labels are derived from that path, never accepted as separate evidence.
The interface uses small types, matching the upstream query-log composition laws.
The producer and its world-execution correspondence are defined in `PhasedExecution`.
-/

@[expose] public section

namespace Interaction.Oracle

open OracleSpec PFunctor.FreeM TwoParty

namespace TypeTree.ExecutionPrefix

/-- The boundary immediately after one public move. -/
def afterPublic {Moves : Type} {rest : Moves → Oracle.TypeTree} (move : Moves) :
    ExecutionPrefix (.public Moves rest) :=
  ⟨Cursor.down move (Cursor.root (rest move)), PUnit.unit⟩

/-- The boundary immediately after one concrete oracle message. -/
def afterOracle {Messages : Type} {rest : PUnit → Oracle.TypeTree} (message : Messages) :
    ExecutionPrefix (.oracle Messages rest) :=
  ⟨Cursor.down PUnit.unit (Cursor.root (rest PUnit.unit)), ⟨message, PUnit.unit⟩⟩

/-- A concrete extension remains an extension after a shared concrete prefix. -/
def Extends.prepend {tree : Oracle.TypeTree} (first : ExecutionPrefix tree)
    {earlier later : ExecutionPrefix first.cursor.residual} (extension : Extends earlier later) :
    Extends (first.comp earlier) (first.comp later) :=
  ⟨extension.continuation, by rw [comp_assoc, extension.comp_eq]⟩

end TypeTree.ExecutionPrefix

/-- The local action responsible for a chronological segment. -/
inductive PhaseParty where
  | prover
  | verifier
  deriving DecidableEq

/-- One segment's boundary and queries, derived together from a concrete-path-indexed trace. -/
structure WorldPhase {ι : Type} (ambient : OracleSpec ι) (tree : Oracle.TypeTree) where
  private mk ::
  /-- All public choices and hidden messages already crossed before the action. -/
  «prefix» : TypeTree.ExecutionPrefix tree
  /-- Participant performing this local action. -/
  party : PhaseParty
  /-- World-surface queries in their original order, including repeated queries. -/
  queries : QueryLog ambient

/-- Two local actions per crossed node and one terminal verifier action. This carrier alone
asserts no execution provenance; the phased runner supplies the observations. -/
@[implicit_reducible]
def WorldSegments {ι : Type} (ambient : OracleSpec ι) :
    (tree : Oracle.TypeTree) → tree.ExecutionPath → Type
  | .done, _ => QueryLog ambient
  | .public _ rest, path =>
      QueryLog ambient × QueryLog ambient × WorldSegments ambient (rest path.1) path.2
  | .oracle _ rest, path =>
      QueryLog ambient × QueryLog ambient × WorldSegments ambient (rest PUnit.unit) path.2

namespace WorldSegments

variable {ι : Type} {ambient : OracleSpec ι}

/-- Flatten local actions in actual execution order. -/
def flatten : {tree : Oracle.TypeTree} → {path : tree.ExecutionPath} →
    WorldSegments ambient tree path → QueryLog ambient
  | .done, _, trace => trace
  | .public _ _, _, trace => trace.1 ++ trace.2.1 ++ flatten trace.2.2
  | .oracle _ _, _, trace => trace.1 ++ trace.2.1 ++ flatten trace.2.2

/-- Prefix labels on a residual phase are lifted through the already crossed concrete edge. -/
@[no_expose]
private def prepend {tree : Oracle.TypeTree} (before : TypeTree.ExecutionPrefix tree)
    (phase : WorldPhase ambient before.cursor.residual) : WorldPhase ambient tree :=
  ⟨before.comp phase.prefix, phase.party, phase.queries⟩

/-- List actual local actions with their full stopping boundaries. Sender actions occur before
crossing their edge; the other party's response occurs after it. At receiver-owned public nodes,
the verifier is the sender and therefore goes first. -/
@[no_expose]
def phases : {tree : Oracle.TypeTree} → (roles : tree.RoleDecoration) →
    {path : tree.ExecutionPath} → WorldSegments ambient tree path →
      List (WorldPhase ambient tree)
  | .done, _, _, trace => [⟨.root .done, .verifier, trace⟩]
  | .public _ _, ⟨role, roles⟩, path, trace =>
      let crossed := TypeTree.ExecutionPrefix.afterPublic path.1
      let first := match role with | .sender => PhaseParty.prover | .receiver => .verifier
      let second := match role with | .sender => PhaseParty.verifier | .receiver => .prover
      ⟨.root _, first, trace.1⟩ :: ⟨crossed, second, trace.2.1⟩ ::
        (phases (roles path.1) trace.2.2).map (prepend crossed)
  | .oracle _ _, roles, path, trace =>
      let crossed := TypeTree.ExecutionPrefix.afterOracle path.1
      ⟨.root _, .prover, trace.1⟩ :: ⟨crossed, .verifier, trace.2.1⟩ ::
        (phases (roles.2 PUnit.unit) trace.2.2).map (prepend crossed)

set_option backward.isDefEq.respectTransparency false in
/-- Decorating segments with concrete protocol boundaries preserves their chronological log. -/
theorem phases_flatten {tree : Oracle.TypeTree} (roles : tree.RoleDecoration)
    {path : tree.ExecutionPath} (trace : WorldSegments ambient tree path) :
    ((phases roles trace).map WorldPhase.queries).flatten = flatten trace := by
  induction tree with
  | done => simp [phases, flatten]
  | «public» Moves rest ih =>
      rcases roles with ⟨role, roles⟩
      simp only [phases, flatten, List.map_cons, List.flatten_cons, List.map_map,
        Function.comp_def, prepend, List.append_assoc]
      congr 1
      congr 1
      exact ih path.1 (roles path.1) trace.2.2
  | «oracle» Messages rest ih =>
      simp only [phases, flatten, List.map_cons, List.flatten_cons, List.map_map,
        Function.comp_def, prepend, List.append_assoc]
      congr 1
      congr 1
      exact ih (roles.2 PUnit.unit) trace.2.2

/-- Count one participant's queries by folding the existing boundary-labelled phases.
This observation does not assert that an arbitrary segment carrier came from execution. -/
def queryCount {tree : Oracle.TypeTree} (party : PhaseParty) (roles : tree.RoleDecoration)
    {path : tree.ExecutionPath} (trace : WorldSegments ambient tree path) : Nat :=
  ((phases roles trace).map fun phase =>
    if phase.party = party then phase.queries.length else 0).sum

/-- The terminal local action belongs to the verifier. -/
theorem queryCount_done (party : PhaseParty) (trace : QueryLog ambient) :
    queryCount (tree := .done) (path := PUnit.unit) party ⟨⟩ trace =
      if party = .verifier then trace.length else 0 := by
  cases party <;> simp [queryCount, phases]

set_option backward.isDefEq.respectTransparency false in
/-- A sender-owned public node places the prover action before the verifier response. -/
theorem queryCount_public_sender {Moves : Type} {rest : Moves → Oracle.TypeTree}
    (party : PhaseParty) (roles : (move : Moves) → (rest move).RoleDecoration)
    (path : (Oracle.TypeTree.public Moves rest).ExecutionPath)
    (trace : WorldSegments ambient (.public Moves rest) path) :
    queryCount (tree := .public Moves rest) party ⟨.sender, roles⟩ trace =
      (if party = .prover then trace.1.length else 0) +
      (if party = .verifier then trace.2.1.length else 0) +
      queryCount party (roles path.1) trace.2.2 := by
  cases party <;>
    (simp [queryCount, phases, List.map_map, Function.comp_def, prepend]; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- A receiver-owned public node places the verifier action before the prover response. -/
theorem queryCount_public_receiver {Moves : Type} {rest : Moves → Oracle.TypeTree}
    (party : PhaseParty) (roles : (move : Moves) → (rest move).RoleDecoration)
    (path : (Oracle.TypeTree.public Moves rest).ExecutionPath)
    (trace : WorldSegments ambient (.public Moves rest) path) :
    queryCount (tree := .public Moves rest) party ⟨.receiver, roles⟩ trace =
      (if party = .verifier then trace.1.length else 0) +
      (if party = .prover then trace.2.1.length else 0) +
      queryCount party (roles path.1) trace.2.2 := by
  cases party <;>
    (simp [queryCount, phases, List.map_map, Function.comp_def, prepend]; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- An oracle node places the private sender before the verifier's receive action. -/
theorem queryCount_oracle {Messages : Type} {rest : PUnit → Oracle.TypeTree}
    (party : PhaseParty) (roles : (Oracle.TypeTree.oracle Messages rest).RoleDecoration)
    (path : (Oracle.TypeTree.oracle Messages rest).ExecutionPath)
    (trace : WorldSegments ambient (.oracle Messages rest) path) :
    queryCount party roles trace =
      (if party = .prover then trace.1.length else 0) +
      (if party = .verifier then trace.2.1.length else 0) +
      queryCount party (roles.2 PUnit.unit) trace.2.2 := by
  cases party <;>
    (simp [queryCount, phases, List.map_map, Function.comp_def, prepend]; rfl)

/-- The existing prover and verifier phases partition the complete chronological world log. -/
theorem queryCount_partition {tree : Oracle.TypeTree} (roles : tree.RoleDecoration)
    {path : tree.ExecutionPath} (trace : WorldSegments ambient tree path) :
    queryCount .prover roles trace + queryCount .verifier roles trace = trace.flatten.length := by
  unfold queryCount
  rw [← List.sum_map_add]
  have h (phase : WorldPhase ambient tree) :
      (if phase.party = .prover then phase.queries.length else 0) +
        (if phase.party = .verifier then phase.queries.length else 0) = phase.queries.length := by
    cases phase.party <;> simp
  simp_rw [h]
  simpa only [List.length_flatten, List.map_map, Function.comp_def] using
    congrArg List.length (phases_flatten roles trace)

set_option backward.isDefEq.respectTransparency false in
/-- Every recorded action boundary is a concrete prefix of this same complete execution,
including agreement of hidden payloads. This is structural reachability, not a strategy claim. -/
theorem phases_reached {tree : Oracle.TypeTree} (roles : tree.RoleDecoration)
    {path : tree.ExecutionPath} (trace : WorldSegments ambient tree path)
    (phase : WorldPhase ambient tree) (member : phase ∈ phases roles trace) :
    Nonempty (TypeTree.ExecutionPrefix.Extends phase.prefix
      (TypeTree.ExecutionPrefix.ofExecutionPath path)) := by
  induction tree with
  | done =>
      simp only [phases, List.mem_singleton] at member
      subst phase
      exact ⟨TypeTree.ExecutionPrefix.Extends.refl _⟩
  | «public» Moves rest ih =>
      rcases roles with ⟨role, roles⟩
      simp only [phases, List.mem_cons, List.mem_map] at member
      rcases member with rfl | rfl | ⟨prior, hprior, rfl⟩
      · exact ⟨⟨TypeTree.ExecutionPrefix.ofExecutionPath path,
          TypeTree.ExecutionPrefix.root_comp _⟩⟩
      · exact ⟨⟨TypeTree.ExecutionPrefix.ofExecutionPath path.2, rfl⟩⟩
      · exact ⟨(ih path.1 (roles path.1) trace.2.2 prior hprior).some.prepend
          (TypeTree.ExecutionPrefix.afterPublic path.1)⟩
  | «oracle» Messages rest ih =>
      simp only [phases, List.mem_cons, List.mem_map] at member
      rcases member with rfl | rfl | ⟨prior, hprior, rfl⟩
      · exact ⟨⟨TypeTree.ExecutionPrefix.ofExecutionPath path,
          TypeTree.ExecutionPrefix.root_comp _⟩⟩
      · exact ⟨⟨TypeTree.ExecutionPrefix.ofExecutionPath path.2, rfl⟩⟩
      · exact ⟨(ih (roles.2 PUnit.unit) trace.2.2 prior hprior).some.prepend
          (TypeTree.ExecutionPrefix.afterOracle path.1)⟩

/-- Include the prover's setup action at the root boundary before all protocol-local actions. -/
@[no_expose]
def phasesWithSetup {tree : Oracle.TypeTree} (setup : QueryLog ambient)
    (roles : tree.RoleDecoration) {path : tree.ExecutionPath}
    (trace : WorldSegments ambient tree path) : List (WorldPhase ambient tree) :=
  ⟨.root tree, .prover, setup⟩ :: phases roles trace

/-- Setup and protocol-local regions cover the complete chronological surface query log. -/
theorem phasesWithSetup_flatten {tree : Oracle.TypeTree} (setup : QueryLog ambient)
    (roles : tree.RoleDecoration) {path : tree.ExecutionPath}
    (trace : WorldSegments ambient tree path) :
    ((phasesWithSetup setup roles trace).map WorldPhase.queries).flatten =
      setup ++ trace.flatten := by
  simp [phasesWithSetup, phases_flatten]

end WorldSegments

namespace WorldPhase

/-- The available stable resource schema is determined by this action's concrete prefix. -/
def availableContext {ι : Type} {ambient : OracleSpec ι} {tree : Oracle.TypeTree}
    (phase : WorldPhase ambient tree) (InputId : Type) := phase.prefix.availableContext InputId

/-- Charge each observed query using one fixed stable-resource classification. This is symbolic
accounting, not an assumption that all queried capabilities satisfy a feasibility predicate. -/
noncomputable def queryProfile {ι κ : Type} {ambient : OracleSpec ι} {tree : Oracle.TypeTree}
    (phase : WorldPhase ambient tree) (classify : ambient.Domain → κ) : ResourceProfile ℕ κ :=
  (phase.queries.map fun entry => ResourceProfile.single (classify entry.1)).sum

/-- Concatenating local query logs adds their profiles with the same resource classification. -/
theorem queryProfile_sum {ι κ : Type} {ambient : OracleSpec ι} {tree : Oracle.TypeTree}
    (phases : List (WorldPhase ambient tree)) (classify : ambient.Domain → κ) :
    (phases.map (fun phase => phase.queryProfile classify)).sum =
      (((phases.map WorldPhase.queries).flatten).map
        (fun entry => ResourceProfile.single (ω := ℕ) (classify entry.1))).sum := by
  simp [queryProfile, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]

end WorldPhase
end Interaction.Oracle
