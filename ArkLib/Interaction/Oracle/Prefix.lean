/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.RunSources
public import ArkLib.Interaction.Oracle.Resource
public import PolyFun.PFunctor.Free.Cursor.Append

/-!
# Concrete execution prefixes

An `ExecutionPrefix` pairs a structural cursor with exactly the concrete oracle realizations along
that prefix. Crossing a send supplies its realization, without assuming future send types are
inhabited. This is structural traversal, not strategy reachability or runtime support. Residual
decorations are inherited from the tree. Available oracle names are crossed send occurrences in
the original tree, disjoint from input names.

`queryIndex` maps the actual accumulated query signature into this available context. `queryName`
identifies a raw input query or a received oracle's send occurrence. Continuing execution preserves
earlier names; appending a later protocol transports names and the same concrete messages.
Runtime trace alignment belongs to the logged and phased execution layers.
-/

@[expose] public section

universe u v i

namespace Interaction.Oracle.TypeTree

open PFunctor.FreeM

namespace PrefixMessages

/-- Concrete realizations for precisely the oracle edges crossed by a structural spine. -/
def Along : {tree residual : Oracle.TypeTree.{u}} → Cursor.Spine tree residual → Type u
  | _, _, .root _ => PUnit
  | _, _, .down (a := Position.public _) _ tail => Along tail
  | _, _, .down (a := Position.oracle Messages) _ tail => Messages × Along tail

/-- Concatenate realizations in the same order as structural cursor composition. -/
def comp : {tree middle residual : Oracle.TypeTree.{u}} →
    (first : Cursor.Spine tree middle) → (second : Cursor.Spine middle residual) →
    Along first → Along second → Along (first.comp second)
  | _, _, _, .root _, _, _, right => right
  | _, _, _, .down (a := Position.public _) _ tail, second, left, right =>
      comp tail second left right
  | _, _, _, .down (a := Position.oracle _) _ tail, second, left, right =>
      ⟨left.1, comp tail second left.2 right⟩

/-- Complete a finite concrete prefix with an actual residual execution path. -/
def plug : {tree residual : Oracle.TypeTree.{u}} → (spine : Cursor.Spine tree residual) →
    Along spine → residual.ExecutionPath → tree.ExecutionPath
  | _, _, .root _, _, path => path
  | _, _, .down (a := Position.public _) move tail, messages, path =>
      ⟨move, plug tail messages path⟩
  | _, _, .down (a := Position.oracle _) _ tail, tailMessages, path =>
      ⟨tailMessages.1, plug tail tailMessages.2 path⟩

/-- Completing a concrete prefix projects to the same structural cursor completion. -/
theorem project_plug {tree residual : Oracle.TypeTree.{u}}
    (spine : Cursor.Spine tree residual) (messages : Along spine)
    (path : residual.ExecutionPath) :
    (plug spine messages path).toBranchPath = spine.plug path.toBranchPath := by
  induction spine with
  | root => rfl
  | @down position next residual answer tail ih =>
    cases position with
    | «public» Moves =>
      change Along tail at messages
      change (⟨answer, (plug tail messages path).toBranchPath⟩ :
        (TypeTree.public Moves next).BranchPath) = ⟨answer, tail.plug path.toBranchPath⟩
      rw [ih]
    | «oracle» Messages =>
      cases answer
      change (⟨PUnit.unit, (plug tail messages.2 path).toBranchPath⟩ :
        (TypeTree.oracle Messages next).BranchPath) = ⟨PUnit.unit, tail.plug path.toBranchPath⟩
      rw [ih]

end PrefixMessages

/-- A concrete prefix containing the oracle realizations sent along its structural cursor. -/
structure ExecutionPrefix (tree : Oracle.TypeTree.{u}) where
  /-- Public choices and the exact stopping point. -/
  cursor : Cursor tree
  /-- Concrete oracle realizations, only at crossed edges. -/
  messages : PrefixMessages.Along cursor.spine

namespace ExecutionPrefix

variable {tree : Oracle.TypeTree.{u}}

/-- The empty prefix exists even if a later oracle realization type is empty. -/
def root (tree : Oracle.TypeTree.{u}) : ExecutionPrefix tree :=
  ⟨Cursor.root tree, PUnit.unit⟩

/-- Prepend an actual public move to a concrete prefix of its selected continuation. -/
def prependPublic {Moves : Type u} {rest : Moves → Oracle.TypeTree.{u}}
    (move : Moves) (pfx : ExecutionPrefix (rest move)) :
    ExecutionPrefix (.public Moves rest) :=
  ⟨Cursor.down move pfx.cursor, pfx.messages⟩

/-- Prepend an actual oracle message, retaining its realization in the concrete prefix. -/
def prependOracle {Messages : Type u} {rest : PUnit.{u + 1} → Oracle.TypeTree.{u}}
    (message : Messages) (pfx : ExecutionPrefix (rest PUnit.unit)) :
    ExecutionPrefix (.oracle Messages rest) :=
  ⟨Cursor.down PUnit.unit pfx.cursor, ⟨message, pfx.messages⟩⟩

/-- Continue with a concrete prefix of the selected residual. -/
def comp (first : ExecutionPrefix tree) (second : ExecutionPrefix first.cursor.residual) :
    ExecutionPrefix tree :=
  ⟨first.cursor.comp second.cursor,
    PrefixMessages.comp first.cursor.spine second.cursor.spine first.messages second.messages⟩

/-- Concrete continuation commutes with prepending a public move. -/
theorem prependPublic_comp {Moves : Type u} {rest : Moves → Oracle.TypeTree.{u}}
    (move : Moves) (first : ExecutionPrefix (rest move))
    (second : ExecutionPrefix first.cursor.residual) :
    (prependPublic move first).comp second = prependPublic move (first.comp second) := rfl

/-- Concrete continuation commutes with prepending an oracle realization. -/
theorem prependOracle_comp {Messages : Type u}
    {rest : PUnit.{u + 1} → Oracle.TypeTree.{u}} (message : Messages)
    (first : ExecutionPrefix (rest PUnit.unit)) (second : ExecutionPrefix first.cursor.residual) :
    (prependOracle message first).comp second = prependOracle message (first.comp second) := rfl

@[simp]
theorem root_comp (pfx : ExecutionPrefix tree) : (root tree).comp pfx = pfx := by
  cases pfx
  rfl

@[simp]
theorem comp_root (pfx : ExecutionPrefix tree) : pfx.comp (root pfx.cursor.residual) = pfx := by
  rcases pfx with ⟨⟨residual, spine⟩, messages⟩
  induction spine with
  | root => cases messages; rfl
  | @down position next residual answer tail ih =>
    cases position with
    | «public» =>
      change PrefixMessages.Along tail at messages
      exact congrArg (fun p : ExecutionPrefix (next answer) =>
        ExecutionPrefix.mk (Cursor.down answer p.cursor) p.messages) (ih messages)
    | «oracle» =>
      exact congrArg (fun p : ExecutionPrefix (next answer) =>
        ExecutionPrefix.mk (Cursor.down answer p.cursor) ⟨messages.1, p.messages⟩)
        (ih messages.2)

/-- Ordered concrete prefix composition is associative. -/
theorem comp_assoc (first : ExecutionPrefix tree) (second : ExecutionPrefix first.cursor.residual)
    (third : ExecutionPrefix second.cursor.residual) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  rcases first with ⟨⟨residual, spine⟩, messages⟩
  induction spine with
  | root => rfl
  | @down position next residual answer tail ih =>
    cases position with
    | «public» =>
      change PrefixMessages.Along tail at messages
      exact congrArg (fun p : ExecutionPrefix (next answer) =>
        ExecutionPrefix.mk (Cursor.down answer p.cursor) p.messages) (ih messages second third)
    | «oracle» =>
      exact congrArg (fun p : ExecutionPrefix (next answer) =>
        ExecutionPrefix.mk (Cursor.down answer p.cursor) ⟨messages.1, p.messages⟩)
        (ih messages.2 second third)

/-- Concrete prefix continuation preserves the order of complete execution paths. -/
theorem PrefixMessages_plug_comp {middle residual : Oracle.TypeTree.{u}}
    (first : Cursor.Spine tree middle) (second : Cursor.Spine middle residual)
    (left : PrefixMessages.Along first) (right : PrefixMessages.Along second)
    (path : residual.ExecutionPath) :
    PrefixMessages.plug (first.comp second) (PrefixMessages.comp first second left right) path =
      PrefixMessages.plug first left (PrefixMessages.plug second right path) := by
  induction first with
  | root => rfl
  | @down position next residual answer tail ih =>
    cases position with
    | «public» =>
      change PrefixMessages.Along tail at left
      change Sigma.mk answer _ = Sigma.mk answer _
      congr 1
      exact ih second left right
    | «oracle» =>
      cases answer
      change Sigma.mk left.1 _ = Sigma.mk left.1 _
      congr 1
      exact ih second left.2 right

/-- Concrete execution paths supply terminal prefixes without an inhabitance assumption. -/
def ofExecutionPath : {tree : Oracle.TypeTree.{u}} → tree.ExecutionPath → ExecutionPrefix tree
  | .done, _ => root .done
  | .public _ _, path =>
      let tail := ofExecutionPath path.2
      ⟨Cursor.down path.1 tail.cursor, tail.messages⟩
  | .oracle _ _, path =>
      let tail := ofExecutionPath path.2
      ⟨Cursor.down PUnit.unit tail.cursor, ⟨path.1, tail.messages⟩⟩

/-- A complete public path retains its first move and the concrete terminal suffix. -/
theorem ofExecutionPath_public {Moves : Type u} {rest : Moves → Oracle.TypeTree.{u}}
    (path : (.public Moves rest : Oracle.TypeTree.{u}).ExecutionPath) :
    ofExecutionPath path = prependPublic path.1 (ofExecutionPath path.2) := rfl

/-- A complete oracle path retains its first realization and the concrete terminal suffix. -/
theorem ofExecutionPath_oracle {Messages : Type u}
    {rest : PUnit.{u + 1} → Oracle.TypeTree.{u}}
    (path : (.oracle Messages rest : Oracle.TypeTree.{u}).ExecutionPath) :
    ofExecutionPath path = prependOracle path.1 (ofExecutionPath path.2) := rfl

/-- Terminal prefix projection is the existing structural projection of execution paths. -/
theorem cursor_ofExecutionPath : {tree : Oracle.TypeTree.{u}} →
    (path : tree.ExecutionPath) →
    (ofExecutionPath path).cursor = Cursor.ofPath tree path.toBranchPath
  | .done, _ => rfl
  | .public Moves rest, path => by
      change Cursor.down (P := basePFunctor) (a := Position.public Moves) (next := rest)
        path.1 (ofExecutionPath path.2).cursor =
        Cursor.down (P := basePFunctor) (a := Position.public Moves) (next := rest)
          path.1 (Cursor.ofPath (rest path.1) (ExecutionPath.toBranchPath path.2))
      rw [cursor_ofExecutionPath]
      rfl
  | .oracle Messages rest, path => by
      change Cursor.down (P := basePFunctor) (a := Position.oracle Messages) (next := rest)
        PUnit.unit (ofExecutionPath path.2).cursor =
        Cursor.down (P := basePFunctor) (a := Position.oracle Messages) (next := rest)
          PUnit.unit (Cursor.ofPath (rest PUnit.unit) (ExecutionPath.toBranchPath path.2))
      rw [cursor_ofExecutionPath]

/-- Roles restricted to the exact residual selected by this prefix. -/
def roles (pfx : ExecutionPrefix tree) (decoration : tree.RoleDecoration) :
    RoleDecoration pfx.cursor.residual :=
  Displayed.Decoration.restrict pfx.cursor decoration

/-- Restricting after a prepended public move uses the role decoration of that continuation. -/
theorem roles_prependPublic {Moves : Type u} {rest : Moves → Oracle.TypeTree.{u}}
    (move : Moves) (pfx : ExecutionPrefix (rest move))
    (decoration : (TypeTree.public Moves rest).RoleDecoration) :
    (prependPublic move pfx).roles decoration = pfx.roles (decoration.2 move) := rfl

/-- An oracle realization retains the role decoration of its structural continuation. -/
theorem roles_prependOracle {Messages : Type u}
    {rest : PUnit.{u + 1} → Oracle.TypeTree.{u}} (message : Messages)
    (pfx : ExecutionPrefix (rest PUnit.unit))
    (decoration : (TypeTree.oracle Messages rest).RoleDecoration) :
    (prependOracle message pfx).roles decoration = pfx.roles (decoration.2 PUnit.unit) := rfl

/-- Oracle interfaces restricted to the selected residual, preserving branch dependence. -/
def oracles (pfx : ExecutionPrefix tree) (decoration : tree.OracleDecoration.{u, v}) :
    OracleDecoration.{u, v} pfx.cursor.residual :=
  Displayed.Decoration.restrict pfx.cursor decoration

/-- Restriction commutes with witnessed continuation. -/
theorem roles_comp (first : ExecutionPrefix tree) (second : ExecutionPrefix first.cursor.residual)
    (decoration : tree.RoleDecoration) :
    (first.comp second).roles decoration = second.roles (first.roles decoration) :=
  Displayed.Decoration.restrict_comp first.cursor second.cursor decoration

/-- Interface restriction commutes with witnessed continuation. -/
theorem oracles_comp (first : ExecutionPrefix tree) (second : ExecutionPrefix first.cursor.residual)
    (decoration : tree.OracleDecoration.{u, v}) :
    (first.comp second).oracles decoration = second.oracles (first.oracles decoration) :=
  Displayed.Decoration.restrict_comp first.cursor second.cursor decoration

/-- Complete a prefix using the concrete residual path, without choosing future messages. -/
def plug (pfx : ExecutionPrefix tree) (path : ExecutionPath pfx.cursor.residual) :
    tree.ExecutionPath :=
  PrefixMessages.plug pfx.cursor.spine pfx.messages path

/-- Completing a prepended public prefix retains the actual first move. -/
theorem prependPublic_plug {Moves : Type u} {rest : Moves → Oracle.TypeTree.{u}}
    (move : Moves) (pfx : ExecutionPrefix (rest move))
    (path : ExecutionPath pfx.cursor.residual) :
    (prependPublic move pfx).plug path = ⟨move, pfx.plug path⟩ := rfl

/-- Completing a prepended oracle prefix retains the actual first realization. -/
theorem prependOracle_plug {Messages : Type u}
    {rest : PUnit.{u + 1} → Oracle.TypeTree.{u}} (message : Messages)
    (pfx : ExecutionPrefix (rest PUnit.unit)) (path : ExecutionPath pfx.cursor.residual) :
    (prependOracle message pfx).plug path = ⟨message, pfx.plug path⟩ := rfl

/-- Completing two consecutive prefixes agrees with their single ordered composition. -/
theorem plug_comp (first : ExecutionPrefix tree) (second : ExecutionPrefix first.cursor.residual)
    (path : ExecutionPath second.cursor.residual) :
    (first.comp second).plug path = first.plug (second.plug path) :=
  PrefixMessages_plug_comp first.cursor.spine second.cursor.spine first.messages second.messages
    path

/-- Public projection of a completed prefix agrees with PolyFun cursor completion. -/
theorem project_plug (pfx : ExecutionPrefix tree) (path : ExecutionPath pfx.cursor.residual) :
    (pfx.plug path).toBranchPath = pfx.cursor.plug path.toBranchPath :=
  PrefixMessages.project_plug pfx.cursor.spine pfx.messages path

/-- Extension retains earlier concrete realizations as well as its public choices. -/
structure Extends (earlier later : ExecutionPrefix tree) where
  /-- Concrete continuation of the earlier prefix. -/
  continuation : ExecutionPrefix earlier.cursor.residual
  /-- Both structural choices and hidden realizations agree. -/
  comp_eq : earlier.comp continuation = later

/-- Every execution prefix extends itself. -/
def Extends.refl (pfx : ExecutionPrefix tree) : Extends pfx pfx :=
  ⟨root pfx.cursor.residual, comp_root pfx⟩

/-- Execution-prefix extension is transitive, preserving public choices and hidden realizations. -/
def Extends.trans {first second third : ExecutionPrefix tree}
    (left : Extends first second) (right : Extends second third) : Extends first third := by
  rcases left with ⟨middle, rfl⟩
  rcases right with ⟨last, rfl⟩
  exact ⟨middle.comp last, (comp_assoc first middle last).symm⟩

/-- Forget only hidden-realization agreement from an execution-prefix extension witness. -/
def Extends.toCursor {earlier later : ExecutionPrefix tree} (extension : Extends earlier later) :
    Cursor.Extends earlier.cursor later.cursor :=
  ⟨extension.continuation.cursor, congrArg ExecutionPrefix.cursor extension.comp_eq⟩

/-- The canonical access signature at the stopping boundary. -/
def access (pfx : ExecutionPrefix tree) (decoration : tree.OracleDecoration.{u, v})
    (initial : PFunctor.{v, u}) : PFunctor.{v, u} :=
  accessAt pfx.cursor decoration initial

/-- Access accumulation decomposes in exactly the same order as concrete prefixes. -/
theorem access_comp (first : ExecutionPrefix tree) (second : ExecutionPrefix first.cursor.residual)
    (decoration : tree.OracleDecoration.{u, v}) (initial : PFunctor.{v, u}) :
    (first.comp second).access decoration initial =
      second.access (first.oracles decoration) (first.access decoration initial) :=
  accessAt_comp first.cursor second.cursor decoration initial

/-- Dependent append classification retains messages indexed by the joined cursor. This avoids
asserting that a prefix reaches the suffix when it stops inside the left protocol. -/
abbrev AppendView (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u}) :=
  (view : Cursor.AppendView tree suffix) × PrefixMessages.Along view.join.spine

/-- Reassemble a classified execution prefix without forgetting its realizations. -/
def joinAppend {suffix : tree.BranchPath → Oracle.TypeTree.{u}}
    (view : AppendView tree suffix) : ExecutionPrefix (PFunctor.FreeM.append tree suffix) :=
  ⟨view.1.join, view.2⟩

/-- Classify the stopping boundary of a dependent append using PolyFun's canonical split. -/
def splitAppend {suffix : tree.BranchPath → Oracle.TypeTree.{u}}
    (pfx : ExecutionPrefix (PFunctor.FreeM.append tree suffix)) : AppendView tree suffix :=
  ⟨Cursor.split tree suffix pfx.cursor,
    (Cursor.join_split tree suffix pfx.cursor).symm ▸ pfx.messages⟩

/-- Append decomposition preserves the execution prefix, including hidden realizations. -/
theorem join_splitAppend {suffix : tree.BranchPath → Oracle.TypeTree.{u}}
    (pfx : ExecutionPrefix (PFunctor.FreeM.append tree suffix)) :
    joinAppend pfx.splitAppend = pfx := by
  have transport : ∀ (left right : Cursor (append tree suffix))
      (h : left = right) (messages : PrefixMessages.Along right.spine),
      (ExecutionPrefix.mk left (h.symm ▸ messages)) = ExecutionPrefix.mk right messages := by
    intro left right h messages
    cases h
    rfl
  exact transport _ _ (Cursor.join_split tree suffix pfx.cursor) pfx.messages

/-- Classifying a reassembled append view recovers its boundary and concrete realizations. -/
theorem split_joinAppend {suffix : tree.BranchPath → Oracle.TypeTree.{u}}
    (view : AppendView tree suffix) : (joinAppend view).splitAppend = view := by
  apply Sigma.ext (Cursor.split_join view.1)
  simp only [splitAppend, joinAppend]
  exact eqRec_heq_iff.mpr HEq.rfl

/-- This occurrence is immediately after an oracle send. Structural positions distinguish oracle
sends from public moves even when their message types coincide. -/
def IsOracleOccurrence (occurrence : Cursor tree) : Prop :=
  ∃ (before : Cursor tree) (Messages : Type u)
    (rest : PUnit.{u + 1} → Oracle.TypeTree.{u})
    (shape : before.residual = TypeTree.oracle Messages rest),
    occurrence = before.comp
      (shape.symm ▸ Cursor.down (P := basePFunctor) (a := Position.oracle Messages)
        (next := rest) PUnit.unit
      (Cursor.root (rest PUnit.unit)))

/-- An oracle occurrence is structurally available only after its edge has been crossed. -/
def Available (pfx : ExecutionPrefix tree) (occurrence : Cursor tree) : Prop :=
  IsOracleOccurrence occurrence ∧ Nonempty (Cursor.Extends occurrence pfx.cursor)

/-- Input names and available tree-scoped oracle occurrences form disjoint name spaces. -/
def availableContext (pfx : ExecutionPrefix tree) (InputId : Type i) :
    NamedContext (InputId ⊕ Cursor tree) where
  Index := InputId ⊕ {occurrence : Cursor tree // pfx.Available occurrence}
  name := ⟨Sum.map id Subtype.val, by
    intro x y h
    cases x <;> cases y <;> simp_all only [Sum.map_inl, Sum.map_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, id_eq]
    exact Subtype.ext h⟩

/-- Availability never exposes an oracle occurrence beyond the stopping boundary. -/
theorem available_length_le (pfx : ExecutionPrefix tree) (occurrence : Cursor tree)
    (h : pfx.Available occurrence) : occurrence.length ≤ pfx.cursor.length :=
  h.2.some.length_le

/-- Witnessed extension preserves every previously available oracle occurrence. -/
theorem available_mono {earlier later : ExecutionPrefix tree}
    (extension : Cursor.Extends earlier.cursor later.cursor) (occurrence : Cursor tree)
    (h : earlier.Available occurrence) : later.Available occurrence :=
  ⟨h.1, ⟨h.2.some.trans extension⟩⟩

/-- Structural extension includes previously available context indices without changing their
names. It does not assert equality of hidden realizations; use `Extends.toCursor` for an
execution-prefix extension witness. -/
def contextInclusion {earlier later : ExecutionPrefix tree}
    (extension : Cursor.Extends earlier.cursor later.cursor) (InputId : Type i) :
    NamedContext.Inclusion (earlier.availableContext InputId) (later.availableContext InputId) where
  map := Sum.map id (fun occurrence => ⟨occurrence.1, available_mono extension _ occurrence.2⟩)
  name_eq := by intro x; cases x <;> rfl

private theorem occurrence_down {position : Position} {next : basePFunctor.B position → TypeTree}
    (answer : basePFunctor.B position) (occurrence : Cursor (next answer))
    (h : IsOracleOccurrence occurrence) : IsOracleOccurrence (Cursor.down answer occurrence) := by
  rcases h with ⟨before, Messages, rest, shape, h⟩
  refine ⟨Cursor.down answer before, Messages, rest, shape, ?_⟩
  exact congrArg (Cursor.down answer) h

private theorem available_down {position : Position}
    {next : basePFunctor.B position → TypeTree} (answer : basePFunctor.B position)
    (tail : Cursor (next answer)) (occurrence : Cursor (next answer))
    (h : IsOracleOccurrence occurrence ∧ Nonempty (Cursor.Extends occurrence tail)) :
    IsOracleOccurrence (Cursor.down answer occurrence) ∧
      Nonempty (Cursor.Extends (Cursor.down answer occurrence) (Cursor.down answer tail)) := by
  refine ⟨occurrence_down answer occurrence h.1, ?_⟩
  rcases h.2 with ⟨extension⟩
  exact ⟨⟨extension.continuation, by
    simpa only [Cursor.down_comp] using congrArg (Cursor.down answer) extension.comp_eq⟩⟩

private def latestCursor {Messages : Type u} {rest : PUnit.{u + 1} → Oracle.TypeTree.{u}} :
    Cursor (TypeTree.oracle Messages rest) :=
  Cursor.down (P := basePFunctor.{u}) (α := PUnit.{u + 1}) (a := Position.oracle Messages)
      (next := rest) PUnit.unit (Cursor.root _)

private theorem available_latest {Messages : Type u} {rest : PUnit.{u + 1} → Oracle.TypeTree.{u}}
    (tail : Cursor (rest PUnit.unit)) :
    IsOracleOccurrence (latestCursor (Messages := Messages) (rest := rest)) ∧
      Nonempty (Cursor.Extends (latestCursor (Messages := Messages) (rest := rest))
        (Cursor.down (P := basePFunctor.{u}) (α := PUnit.{u + 1}) (a := Position.oracle Messages)
      (next := rest) PUnit.unit tail)) := by
  refine ⟨?_, ⟨⟨tail, rfl⟩⟩⟩
  exact ⟨Cursor.root (TypeTree.oracle Messages rest), Messages, rest, rfl, rfl⟩

/-- Compute the available-resource index along a concrete prefix spine. -/
def queryIndexAlong : {tree residual : TypeTree} →
    (spine : Cursor.Spine tree residual) → (messages : PrefixMessages.Along spine) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor) →
    (accessAlong spine oracles initial).A →
    ((ExecutionPrefix.mk ⟨residual, spine⟩ messages).availableContext initial.A).Index
  | _, _, .root _, _, _, _, q => .inl q
  | _, _, .down (a := Position.public _) answer tail, messages, oracles, initial, q =>
      match queryIndexAlong tail messages (oracles.2 answer) initial q with
      | .inl q => .inl q
      | .inr occurrence => .inr ⟨Cursor.down answer occurrence.1,
          by exact available_down answer ⟨_, tail⟩ occurrence.1 occurrence.2⟩
  | _, _, .down (a := Position.oracle _) answer tail, messages, oracles, initial, q =>
      match queryIndexAlong tail messages.2 (oracles.2 answer)
          (Access.extend initial oracles.1) q with
      | .inl (.inl q) => .inl q
      | .inl (.inr _) => .inr ⟨Cursor.down answer (Cursor.root _), by
          cases answer
          exact available_latest ⟨_, tail⟩⟩
      | .inr occurrence => .inr ⟨Cursor.down answer occurrence.1,
          by exact available_down answer ⟨_, tail⟩ occurrence.1 occurrence.2⟩

/-- Each actual access query names an initial query or an oracle edge already crossed. -/
def queryIndex {tree : TypeTree} (pfx : ExecutionPrefix tree) (oracles : tree.OracleDecoration)
    (initial : PFunctor) : (pfx.access oracles initial).A →
      (pfx.availableContext initial.A).Index :=
  queryIndexAlong pfx.cursor.spine pfx.messages oracles initial

/-- The stable name is derived from its canonical available-context index.
Initial names identify raw input queries. Names for sent oracles identify the crossed send edge,
so different query arguments to the same received oracle intentionally share its name. -/
def queryName {tree : TypeTree} (pfx : ExecutionPrefix tree) (oracles : tree.OracleDecoration)
    (initial : PFunctor) : (pfx.access oracles initial).A → initial.A ⊕ Cursor tree :=
  fun q => (pfx.availableContext initial.A).name (pfx.queryIndex oracles initial q)

theorem queryName_available {tree : TypeTree} (pfx : ExecutionPrefix tree)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (q : (pfx.access oracles initial).A) :
    ∃ index : (pfx.availableContext initial.A).Index,
      (pfx.availableContext initial.A).name index = pfx.queryName oracles initial q :=
  ⟨pfx.queryIndex oracles initial q, rfl⟩

/-- No actual query at this prefix names an oracle occurrence that is unavailable here. -/
theorem queryName_ne_of_not_available {tree : TypeTree} (pfx : ExecutionPrefix tree)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (q : (pfx.access oracles initial).A) (occurrence : Cursor tree)
    (unavailable : ¬ pfx.Available occurrence) :
    pfx.queryName oracles initial q ≠ .inr occurrence := by
  intro equal
  obtain ⟨index, named⟩ := queryName_available pfx oracles initial q
  rw [equal] at named
  cases index with
  | inl input =>
    change Sum.inl input = Sum.inr occurrence at named
    cases named
  | inr available =>
    change Sum.inr available.1 = Sum.inr occurrence at named
    exact unavailable (Sum.inr.inj named ▸ available.2)

/-- An oracle send beyond the current prefix cannot be named by any currently available query. -/
theorem queryName_ne_future {tree : TypeTree} (pfx : ExecutionPrefix tree)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (q : (pfx.access oracles initial).A) (occurrence : Cursor tree)
    (future : pfx.cursor.length < occurrence.length) :
    pfx.queryName oracles initial q ≠ .inr occurrence :=
  queryName_ne_of_not_available pfx oracles initial q occurrence
    (fun h => (Nat.not_le_of_gt future) (available_length_le pfx occurrence h))

/-- Embed an earlier query through precisely the crossed old-slot injections. -/
def includeQueryAlong : {tree residual : TypeTree} →
    (spine : Cursor.Spine tree residual) → (oracles : tree.OracleDecoration) →
    (initial : PFunctor) → initial.A → (accessAlong spine oracles initial).A
  | _, _, .root _, _, _, q => q
  | _, _, .down (a := Position.public _) answer tail, oracles, initial, q =>
      includeQueryAlong tail (oracles.2 answer) initial q
  | _, _, .down (a := Position.oracle _) answer tail, oracles, initial, q =>
      includeQueryAlong tail (oracles.2 answer) (Access.extend initial oracles.1) (.inl q)

/-- Canonical old-slot routing preserves an initial raw query's identity. -/
private theorem queryIndexAlong_include {tree residual : TypeTree}
    (spine : Cursor.Spine tree residual) (messages : PrefixMessages.Along spine)
    (oracles : tree.OracleDecoration) (initial : PFunctor) (q : initial.A) :
    queryIndexAlong spine messages oracles initial (includeQueryAlong spine oracles initial q) =
      .inl q := by
  induction spine generalizing initial with
  | root => rfl
  | @down position next residual answer tail ih =>
    cases position with
    | «public» Moves =>
      change PrefixMessages.Along tail at messages
      simp only [includeQueryAlong, queryIndexAlong]
      rw [ih messages (oracles.2 answer) initial q]
    | «oracle» Messages =>
      simp only [includeQueryAlong, queryIndexAlong]
      rw [ih messages.2 (oracles.2 answer) (Access.extend initial oracles.1) (.inl q)]

/-- The earlier resource name is unchanged after old-slot inclusion. -/
theorem queryName_include {tree : TypeTree} (pfx : ExecutionPrefix tree)
    (oracles : tree.OracleDecoration) (initial : PFunctor) (q : initial.A) :
    pfx.queryName oracles initial
      (includeQueryAlong pfx.cursor.spine oracles initial q) = .inl q := by
  unfold queryName queryIndex
  rw [queryIndexAlong_include]
  rfl

private def nameAlong : {tree residual : TypeTree} →
    (spine : Cursor.Spine tree residual) → (oracles : tree.OracleDecoration) →
    (initial : PFunctor) → (accessAlong spine oracles initial).A → initial.A ⊕ Cursor tree
  | _, _, .root _, _, _, q => .inl q
  | _, _, .down (a := Position.public _) answer tail, oracles, initial, q =>
      Sum.map id (Cursor.down answer) (nameAlong tail (oracles.2 answer) initial q)
  | _, _, .down (a := Position.oracle _) answer tail, oracles, initial, q =>
      match nameAlong tail (oracles.2 answer) (Access.extend initial oracles.1) q with
      | .inl (.inl q) => .inl q
      | .inl (.inr _) => .inr (Cursor.down answer (Cursor.root _))
      | .inr occurrence => .inr (Cursor.down answer occurrence)

private theorem queryName_eq_nameAlong {tree residual : TypeTree}
    (spine : Cursor.Spine tree residual) (messages : PrefixMessages.Along spine)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (q : (accessAlong spine oracles initial).A) :
    (ExecutionPrefix.mk ⟨residual, spine⟩ messages).queryName oracles initial q =
      nameAlong spine oracles initial q := by
  induction spine generalizing initial with
  | root => rfl
  | @down position next residual answer tail ih =>
    cases position with
    | «public» Moves =>
      change PrefixMessages.Along tail at messages
      have h := ih messages (oracles.2 answer) initial q
      simp only [queryName, queryIndex, availableContext] at h ⊢
      simp only [queryIndexAlong, nameAlong]
      rw [← h]
      cases queryIndexAlong tail messages (oracles.2 answer) initial q <;> rfl
    | «oracle» Messages =>
      have h := ih messages.2 (oracles.2 answer) (Access.extend initial oracles.1) q
      simp only [queryName, queryIndex, availableContext] at h ⊢
      simp only [queryIndexAlong, nameAlong]
      rw [← h]
      cases hq : queryIndexAlong tail messages.2 (oracles.2 answer)
          (Access.extend initial oracles.1) q with
      | inl tag => cases tag <;> rfl
      | inr occurrence => rfl

private theorem nameAlong_include {tree residual : TypeTree}
    (spine : Cursor.Spine tree residual) (oracles : tree.OracleDecoration)
    (initial : PFunctor) (q : initial.A) :
    nameAlong spine oracles initial (includeQueryAlong spine oracles initial q) = .inl q := by
  induction spine generalizing initial with
  | root => rfl
  | @down position next residual answer tail ih =>
    cases position with
    | «public» Moves =>
      simp only [includeQueryAlong, nameAlong, ih, Sum.map_inl, id_eq]
    | «oracle» Messages =>
      simp only [includeQueryAlong, nameAlong, ih]

private theorem nameAlong_comp_include {tree middle residual : TypeTree}
    (first : Cursor.Spine tree middle) (second : Cursor.Spine middle residual)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (q : (accessAlong first oracles initial).A) :
    nameAlong (first.comp second) oracles initial
      (cast (congrArg PFunctor.A (accessAlong_comp first second oracles initial)).symm
        (includeQueryAlong second (OracleDecoration.restrict ⟨middle, first⟩ oracles)
          (accessAlong first oracles initial) q)) = nameAlong first oracles initial q := by
  induction first generalizing initial with
  | root => exact nameAlong_include second oracles initial q
  | @down position next middle answer tail ih =>
    cases position with
    | «public» Moves =>
      exact congrArg (Sum.map id (Cursor.down answer))
        (ih second (oracles.2 answer) initial q)
    | «oracle» Messages =>
      have h := ih second (oracles.2 answer) (Access.extend initial oracles.1) q
      simp only [OracleDecoration.restrict, Displayed.Decoration.restrict, Displayed.restrict,
        Displayed.Decoration.childProjection] at h
      simp only [Cursor.Spine.comp, nameAlong, accessAlong, OracleDecoration.restrict,
        Displayed.Decoration.restrict, Displayed.restrict, Displayed.restrictSpine,
        Displayed.Decoration.childProjection]
      rw [h]

/-- Continuing execution retains the canonical name of every earlier query, including queries
into previously sent oracles. The inclusion follows the actual accumulated access signature. -/
theorem queryName_comp {tree : TypeTree}
    (first : ExecutionPrefix tree) (second : ExecutionPrefix first.cursor.residual)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (q : (first.access oracles initial).A) :
    (first.comp second).queryName oracles initial
      (cast (congrArg PFunctor.A (first.access_comp second oracles initial)).symm
        (includeQueryAlong second.cursor.spine (first.oracles oracles)
          (first.access oracles initial) q)) = first.queryName oracles initial q := by
  rcases first with ⟨⟨middle, left⟩, leftMessages⟩
  rcases second with ⟨⟨residual, right⟩, rightMessages⟩
  exact (queryName_eq_nameAlong (left.comp right)
    (PrefixMessages.comp left right leftMessages rightMessages) oracles initial _).trans
    ((nameAlong_comp_include left right oracles initial q).trans
      (queryName_eq_nameAlong left leftMessages oracles initial q).symm)

private theorem nameAlong_liftAppend {tree residual : TypeTree}
    (spine : Cursor.Spine tree residual) (suffix : tree.BranchPath → TypeTree)
    (first : tree.OracleDecoration)
    (second : (p : tree.BranchPath) → (suffix p).OracleDecoration) (initial : PFunctor)
    (q : (accessAlong spine first initial).A) :
    nameAlong (spine.liftAppend suffix) (Displayed.Decoration.append first second) initial
      (cast (congrArg PFunctor.A
        (accessAlong_liftAppend spine suffix first second initial)).symm q) =
      Sum.map id (fun cursor => cursor.liftAppend suffix) (nameAlong spine first initial q) := by
  induction spine generalizing initial with
  | root => rfl
  | @down position next residual answer tail ih =>
    cases position with
    | «public» Moves =>
      have h := ih (fun p => suffix ⟨answer, p⟩) (first.2 answer)
        (fun p => second ⟨answer, p⟩) initial q
      simp only [Cursor.Spine.liftAppend, Cursor.Spine.plug, nameAlong, accessAlong,
        Displayed.Decoration.append_liftBind]
      rw [h]
      cases nameAlong tail (first.2 answer) initial q <;> rfl
    | «oracle» Messages =>
      have h := ih (fun p => suffix ⟨answer, p⟩) (first.2 answer)
        (fun p => second ⟨answer, p⟩) (Access.extend initial first.1) q
      simp only [Cursor.Spine.liftAppend, Cursor.Spine.plug, nameAlong, accessAlong,
        Displayed.Decoration.append_liftBind]
      rw [h]
      cases nameAlong tail (first.2 answer) (Access.extend initial first.1) q with
      | inl tag => cases tag <;> rfl
      | inr cursor => rfl

end ExecutionPrefix

namespace PrefixMessages

/-- Transport the same concrete messages when a continuation is appended after the protocol. -/
def liftAppend : {tree residual : TypeTree} → (spine : Cursor.Spine tree residual) →
    (suffix : tree.BranchPath → TypeTree) → Along spine → Along (spine.liftAppend suffix)
  | _, _, .root _, _, _ => PUnit.unit
  | _, _, .down (a := Position.public _) answer tail, suffix, messages =>
      liftAppend tail (fun p => suffix ⟨answer, p⟩) messages
  | _, _, .down (a := Position.oracle _) answer tail, suffix, messages =>
      ⟨messages.1, liftAppend tail (fun p => suffix ⟨answer, p⟩) messages.2⟩

end PrefixMessages

namespace ExecutionPrefix

/-- The same concrete prefix inside an appended protocol. No later message is added. -/
def liftAppend {tree : TypeTree} (pfx : ExecutionPrefix tree)
    (suffix : tree.BranchPath → TypeTree) : ExecutionPrefix (PFunctor.FreeM.append tree suffix) :=
  ⟨pfx.cursor.liftAppend suffix, PrefixMessages.liftAppend pfx.cursor.spine suffix pfx.messages⟩

/-- Appending a later protocol transports earlier resource names by the canonical cursor map.
The query itself uses the equality of accumulated signatures, with the same concrete messages. -/
theorem queryName_liftAppend {tree : TypeTree} (pfx : ExecutionPrefix tree)
    (suffix : tree.BranchPath → TypeTree) (first : tree.OracleDecoration)
    (second : (p : tree.BranchPath) → (suffix p).OracleDecoration) (initial : PFunctor)
    (q : (pfx.access first initial).A) :
    (pfx.liftAppend suffix).queryName (Displayed.Decoration.append first second) initial
      (cast (congrArg PFunctor.A
        (accessAlong_liftAppend pfx.cursor.spine suffix first second initial)).symm q) =
      Sum.map id (fun cursor => cursor.liftAppend suffix) (pfx.queryName first initial q) := by
  rcases pfx with ⟨⟨residual, spine⟩, messages⟩
  exact (queryName_eq_nameAlong (spine.liftAppend suffix)
    (PrefixMessages.liftAppend spine suffix messages)
    (Displayed.Decoration.append first second) initial _).trans
      ((nameAlong_liftAppend spine suffix first second initial q).trans
        (congrArg (Sum.map id (fun cursor => cursor.liftAppend suffix))
          (queryName_eq_nameAlong spine messages first initial q).symm))

end ExecutionPrefix
end Interaction.Oracle.TypeTree
