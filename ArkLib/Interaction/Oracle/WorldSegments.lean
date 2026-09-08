/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Prefix
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.ResourceProfile

/-!
# World queries at concrete protocol boundaries

Each crossed protocol node has two local actions in ownership order; the terminal node has
one verifier action. `WorldSegments` stores those logs indexed by the actual concrete path.
Their full-prefix labels are derived from that path, never accepted as separate evidence.
The interface uses small types, matching the upstream query-log composition laws.
The producer and its world-execution correspondence are defined in `PhasedExecution`.
-/

namespace Interaction.Oracle

open OracleSpec PFunctor.FreeM TwoParty

namespace TypeTree.FullPrefix

/-- The boundary immediately after one public move. -/
def afterPublic {Moves : Type} {rest : Moves → Oracle.TypeTree} (move : Moves) :
    FullPrefix (.public Moves rest) :=
  ⟨Cursor.down move (Cursor.root (rest move)), PUnit.unit⟩

/-- The boundary immediately after one concrete oracle message. -/
def afterOracle {Messages : Type} {rest : PUnit → Oracle.TypeTree} (message : Messages) :
    FullPrefix (.oracle Messages rest) :=
  ⟨Cursor.down PUnit.unit (Cursor.root (rest PUnit.unit)), ⟨message, PUnit.unit⟩⟩

/-- A concrete extension remains an extension after a shared concrete prefix. -/
def Extends.prepend {tree : Oracle.TypeTree} (first : FullPrefix tree)
    {earlier later : FullPrefix first.cursor.residual} (extension : Extends earlier later) :
    Extends (first.comp earlier) (first.comp later) :=
  ⟨extension.continuation, by rw [comp_assoc, extension.comp_eq]⟩

end TypeTree.FullPrefix

/-- The local action responsible for a chronological segment. -/
inductive PhaseParty where
  | prover
  | verifier
  deriving DecidableEq

/-- One segment's boundary and queries, derived together from a concrete-path-indexed trace. -/
structure WorldPhase {ι : Type} (ambient : OracleSpec ι) (tree : Oracle.TypeTree) where
  private mk ::
  /-- All public choices and hidden messages already crossed before the action. -/
  «prefix» : TypeTree.FullPrefix tree
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
private def prepend {tree : Oracle.TypeTree} (before : TypeTree.FullPrefix tree)
    (phase : WorldPhase ambient before.cursor.residual) : WorldPhase ambient tree :=
  ⟨before.comp phase.prefix, phase.party, phase.queries⟩

/-- List actual local actions with their full stopping boundaries. Sender actions occur before
crossing their edge; the other party's response occurs after it. At receiver-owned public nodes,
the verifier is the sender and therefore goes first. -/
def phases : {tree : Oracle.TypeTree} → (roles : tree.RoleDecoration) →
    {path : tree.ExecutionPath} → WorldSegments ambient tree path → List (WorldPhase ambient tree)
  | .done, _, _, trace => [⟨.root .done, .verifier, trace⟩]
  | .public _ _, ⟨role, roles⟩, path, trace =>
      let crossed := TypeTree.FullPrefix.afterPublic path.1
      let first := match role with | .sender => PhaseParty.prover | .receiver => .verifier
      let second := match role with | .sender => PhaseParty.verifier | .receiver => .prover
      ⟨.root _, first, trace.1⟩ :: ⟨crossed, second, trace.2.1⟩ ::
        (phases (roles path.1) trace.2.2).map (prepend crossed)
  | .oracle _ _, roles, path, trace =>
      let crossed := TypeTree.FullPrefix.afterOracle path.1
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

set_option backward.isDefEq.respectTransparency false in
/-- Every recorded action boundary is a concrete prefix of this same complete execution,
including agreement of hidden payloads. This is structural reachability, not a strategy claim. -/
theorem phases_reached {tree : Oracle.TypeTree} (roles : tree.RoleDecoration)
    {path : tree.ExecutionPath} (trace : WorldSegments ambient tree path)
    (phase : WorldPhase ambient tree) (member : phase ∈ phases roles trace) :
    Nonempty (TypeTree.FullPrefix.Extends phase.prefix
      (TypeTree.FullPrefix.ofExecutionPath path)) := by
  induction tree with
  | done =>
      simp only [phases, List.mem_singleton] at member
      subst phase
      exact ⟨TypeTree.FullPrefix.Extends.refl _⟩
  | «public» Moves rest ih =>
      rcases roles with ⟨role, roles⟩
      simp only [phases, List.mem_cons, List.mem_map] at member
      rcases member with rfl | rfl | ⟨prior, hprior, rfl⟩
      · exact ⟨⟨TypeTree.FullPrefix.ofExecutionPath path,
          TypeTree.FullPrefix.root_comp _⟩⟩
      · exact ⟨⟨TypeTree.FullPrefix.ofExecutionPath path.2, rfl⟩⟩
      · exact ⟨(ih path.1 (roles path.1) trace.2.2 prior hprior).some.prepend
          (TypeTree.FullPrefix.afterPublic path.1)⟩
  | «oracle» Messages rest ih =>
      simp only [phases, List.mem_cons, List.mem_map] at member
      rcases member with rfl | rfl | ⟨prior, hprior, rfl⟩
      · exact ⟨⟨TypeTree.FullPrefix.ofExecutionPath path,
          TypeTree.FullPrefix.root_comp _⟩⟩
      · exact ⟨⟨TypeTree.FullPrefix.ofExecutionPath path.2, rfl⟩⟩
      · exact ⟨(ih (roles.2 PUnit.unit) trace.2.2 prior hprior).some.prepend
          (TypeTree.FullPrefix.afterOracle path.1)⟩

/-- Include the prover's setup action at the root boundary before all protocol-local actions. -/
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
def resources {ι : Type} {ambient : OracleSpec ι} {tree : Oracle.TypeTree}
    (phase : WorldPhase ambient tree) (InputId : Type) := phase.prefix.resources InputId

/-- Charge each observed query using one fixed stable-resource classification. This is symbolic
accounting, not an assumption that all queried capabilities satisfy a feasibility predicate. -/
noncomputable def profile {ι κ : Type} {ambient : OracleSpec ι} {tree : Oracle.TypeTree}
    (phase : WorldPhase ambient tree) (classify : ambient.Domain → κ) : ResourceProfile ℕ κ :=
  (phase.queries.map fun entry => ResourceProfile.single (classify entry.1)).sum

/-- Concatenating local query logs adds their profiles with the same resource classification. -/
theorem profile_sum {ι κ : Type} {ambient : OracleSpec ι} {tree : Oracle.TypeTree}
    (phases : List (WorldPhase ambient tree)) (classify : ambient.Domain → κ) :
    (phases.map (fun phase => phase.profile classify)).sum =
      (((phases.map WorldPhase.queries).flatten).map
        (fun entry => ResourceProfile.single (ω := ℕ) (classify entry.1))).sum := by
  simp [profile, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]

end WorldPhase
end Interaction.Oracle
