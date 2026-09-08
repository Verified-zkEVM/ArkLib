/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.RunSources
import ArkLib.Interaction.Oracle.Resource
import PolyFun.PFunctor.Free.Cursor.Append

/-!
# Full structural prefixes

A `FullPrefix` pairs a structural cursor with exactly its concrete oracle messages. This witnesses
finite structural reachability, including sends of possibly empty message types; it does not assert
reachability under any strategy or oracle world. Residual decorations are inherited from the tree.
Resource identities below are structural occurrences scoped to the original tree, separate from
user-supplied input identities. Allocation requires a witnessed crossed oracle edge, never merely
an inhabited backing type. Runtime trace alignment belongs to the logged-execution layer.
-/

universe u v i

namespace Interaction.Oracle.TypeTree

open PFunctor.FreeM

namespace PrefixMessages

/-- Concrete payloads for precisely the oracle edges crossed by a structural spine. -/
def Along : {tree residual : Oracle.TypeTree.{u}} → Cursor.Spine tree residual → Type u
  | _, _, .root _ => PUnit
  | _, _, .down (a := Position.public _) _ tail => Along tail
  | _, _, .down (a := Position.oracle Messages) _ tail => Messages × Along tail

/-- Concatenate payloads in the same order as structural cursor composition. -/
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

/-- A finite structural prefix with all actual messages sent along it. -/
structure FullPrefix (tree : Oracle.TypeTree.{u}) where
  /-- Public choices and the exact stopping point. -/
  cursor : Cursor tree
  /-- Concrete oracle payloads, only at crossed edges. -/
  messages : PrefixMessages.Along cursor.spine

namespace FullPrefix

variable {tree : Oracle.TypeTree.{u}}

/-- The empty prefix is reachable even if a later message type is empty. -/
def root (tree : Oracle.TypeTree.{u}) : FullPrefix tree :=
  ⟨Cursor.root tree, PUnit.unit⟩

/-- Continue with a concrete prefix of the selected residual. -/
def comp (first : FullPrefix tree) (second : FullPrefix first.cursor.residual) :
    FullPrefix tree :=
  ⟨first.cursor.comp second.cursor,
    PrefixMessages.comp first.cursor.spine second.cursor.spine first.messages second.messages⟩

@[simp]
theorem root_comp (pfx : FullPrefix tree) : (root tree).comp pfx = pfx := by
  cases pfx
  rfl

@[simp]
theorem comp_root (pfx : FullPrefix tree) : pfx.comp (root pfx.cursor.residual) = pfx := by
  rcases pfx with ⟨⟨residual, spine⟩, messages⟩
  induction spine with
  | root => cases messages; rfl
  | @down position next residual answer tail ih =>
    cases position with
    | «public» =>
      change PrefixMessages.Along tail at messages
      exact congrArg (fun p : FullPrefix (next answer) =>
        FullPrefix.mk (Cursor.down answer p.cursor) p.messages) (ih messages)
    | «oracle» =>
      exact congrArg (fun p : FullPrefix (next answer) =>
        FullPrefix.mk (Cursor.down answer p.cursor) ⟨messages.1, p.messages⟩) (ih messages.2)

/-- Ordered concrete prefix composition is associative. -/
theorem comp_assoc (first : FullPrefix tree) (second : FullPrefix first.cursor.residual)
    (third : FullPrefix second.cursor.residual) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  rcases first with ⟨⟨residual, spine⟩, messages⟩
  induction spine with
  | root => rfl
  | @down position next residual answer tail ih =>
    cases position with
    | «public» =>
      change PrefixMessages.Along tail at messages
      exact congrArg (fun p : FullPrefix (next answer) =>
        FullPrefix.mk (Cursor.down answer p.cursor) p.messages) (ih messages second third)
    | «oracle» =>
      exact congrArg (fun p : FullPrefix (next answer) =>
        FullPrefix.mk (Cursor.down answer p.cursor) ⟨messages.1, p.messages⟩)
        (ih messages.2 second third)

/-- Concrete prefix continuation preserves the order of full execution paths. -/
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

/-- Complete execution paths supply a full terminal prefix without any inhabitance assumption. -/
def ofExecutionPath : {tree : Oracle.TypeTree.{u}} → tree.ExecutionPath → FullPrefix tree
  | .done, _ => root .done
  | .public _ _, path =>
      let tail := ofExecutionPath path.2
      ⟨Cursor.down path.1 tail.cursor, tail.messages⟩
  | .oracle _ _, path =>
      let tail := ofExecutionPath path.2
      ⟨Cursor.down PUnit.unit tail.cursor, ⟨path.1, tail.messages⟩⟩

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
def roles (pfx : FullPrefix tree) (decoration : tree.RoleDecoration) :
    RoleDecoration pfx.cursor.residual :=
  Displayed.Decoration.restrict pfx.cursor decoration

/-- Oracle interfaces restricted to the selected residual, preserving branch dependence. -/
def oracles (pfx : FullPrefix tree) (decoration : tree.OracleDecoration.{u, v}) :
    OracleDecoration.{u, v} pfx.cursor.residual :=
  Displayed.Decoration.restrict pfx.cursor decoration

/-- Restriction commutes with witnessed continuation. -/
theorem roles_comp (first : FullPrefix tree) (second : FullPrefix first.cursor.residual)
    (decoration : tree.RoleDecoration) :
    (first.comp second).roles decoration = second.roles (first.roles decoration) :=
  Displayed.Decoration.restrict_comp first.cursor second.cursor decoration

/-- Interface restriction commutes with witnessed continuation. -/
theorem oracles_comp (first : FullPrefix tree) (second : FullPrefix first.cursor.residual)
    (decoration : tree.OracleDecoration.{u, v}) :
    (first.comp second).oracles decoration = second.oracles (first.oracles decoration) :=
  Displayed.Decoration.restrict_comp first.cursor second.cursor decoration

/-- Complete a prefix using the concrete residual path, without choosing future messages. -/
def plug (pfx : FullPrefix tree) (path : ExecutionPath pfx.cursor.residual) :
    tree.ExecutionPath :=
  PrefixMessages.plug pfx.cursor.spine pfx.messages path

/-- Completing two consecutive prefixes agrees with their single ordered composition. -/
theorem plug_comp (first : FullPrefix tree) (second : FullPrefix first.cursor.residual)
    (path : ExecutionPath second.cursor.residual) :
    (first.comp second).plug path = first.plug (second.plug path) :=
  PrefixMessages_plug_comp first.cursor.spine second.cursor.spine first.messages second.messages
    path

/-- Public projection of a completed prefix agrees with PolyFun cursor completion. -/
theorem project_plug (pfx : FullPrefix tree) (path : ExecutionPath pfx.cursor.residual) :
    (pfx.plug path).toBranchPath = pfx.cursor.plug path.toBranchPath :=
  PrefixMessages.project_plug pfx.cursor.spine pfx.messages path

/-- Extension retains the earlier concrete messages as well as its public choices. -/
structure Extends (earlier later : FullPrefix tree) where
  /-- Concrete continuation of the earlier prefix. -/
  continuation : FullPrefix earlier.cursor.residual
  /-- Both structural choices and hidden messages agree. -/
  comp_eq : earlier.comp continuation = later

/-- Every full prefix extends itself. -/
def Extends.refl (pfx : FullPrefix tree) : Extends pfx pfx :=
  ⟨root pfx.cursor.residual, comp_root pfx⟩

/-- Full extension is transitive, preserving both public and hidden messages. -/
def Extends.trans {first second third : FullPrefix tree}
    (left : Extends first second) (right : Extends second third) : Extends first third := by
  rcases left with ⟨middle, rfl⟩
  rcases right with ⟨last, rfl⟩
  exact ⟨middle.comp last, (comp_assoc first middle last).symm⟩

/-- Forget only the hidden-message agreement of a full extension witness. -/
def Extends.toCursor {earlier later : FullPrefix tree} (extension : Extends earlier later) :
    Cursor.Extends earlier.cursor later.cursor :=
  ⟨extension.continuation.cursor, congrArg FullPrefix.cursor extension.comp_eq⟩

/-- The canonical access signature at the stopping boundary. -/
def access (pfx : FullPrefix tree) (decoration : tree.OracleDecoration.{u, v})
    (initial : PFunctor.{v, u}) : PFunctor.{v, u} :=
  accessAt pfx.cursor decoration initial

/-- Access accumulation decomposes in exactly the same order as concrete prefixes. -/
theorem access_comp (first : FullPrefix tree) (second : FullPrefix first.cursor.residual)
    (decoration : tree.OracleDecoration.{u, v}) (initial : PFunctor.{v, u}) :
    (first.comp second).access decoration initial =
      second.access (first.oracles decoration) (first.access decoration initial) :=
  accessAt_comp first.cursor second.cursor decoration initial

/-- Dependent append classification retains messages indexed by the joined cursor. This avoids
asserting that a prefix reaches the suffix when it stops inside the left protocol. -/
abbrev AppendView (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u}) :=
  (view : Cursor.AppendView tree suffix) × PrefixMessages.Along view.join.spine

/-- Reassemble a classified full prefix without forgetting its payloads. -/
def joinAppend {suffix : tree.BranchPath → Oracle.TypeTree.{u}}
    (view : AppendView tree suffix) : FullPrefix (PFunctor.FreeM.append tree suffix) :=
  ⟨view.1.join, view.2⟩

/-- Classify the stopping boundary of a dependent append using PolyFun's canonical split. -/
def splitAppend {suffix : tree.BranchPath → Oracle.TypeTree.{u}}
    (pfx : FullPrefix (PFunctor.FreeM.append tree suffix)) : AppendView tree suffix :=
  ⟨Cursor.split tree suffix pfx.cursor,
    (Cursor.join_split tree suffix pfx.cursor).symm ▸ pfx.messages⟩

/-- Append decomposition preserves the full prefix, including hidden payloads. -/
theorem join_splitAppend {suffix : tree.BranchPath → Oracle.TypeTree.{u}}
    (pfx : FullPrefix (PFunctor.FreeM.append tree suffix)) :
    joinAppend pfx.splitAppend = pfx := by
  have transport : ∀ (left right : Cursor (append tree suffix))
      (h : left = right) (messages : PrefixMessages.Along right.spine),
      (FullPrefix.mk left (h.symm ▸ messages)) = FullPrefix.mk right messages := by
    intro left right h messages
    cases h
    rfl
  exact transport _ _ (Cursor.join_split tree suffix pfx.cursor) pfx.messages

/-- Classifying a reassembled append view recovers its boundary and concrete payloads. -/
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

/-- Available message allocations have crossed an oracle edge on this same structural history. -/
def Available (pfx : FullPrefix tree) (occurrence : Cursor tree) : Prop :=
  IsOracleOccurrence occurrence ∧ Nonempty (Cursor.Extends occurrence pfx.cursor)

/-- Stable input identities and tree-scoped oracle occurrences form disjoint identity spaces. -/
def resources (pfx : FullPrefix tree) (InputId : Type i) :
    ResourceSchema (InputId ⊕ Cursor tree) where
  Slot := InputId ⊕ {occurrence : Cursor tree // pfx.Available occurrence}
  key := ⟨Sum.map id Subtype.val, by
    intro x y h
    cases x <;> cases y <;> simp_all only [Sum.map_inl, Sum.map_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, id_eq]
    exact Subtype.ext h⟩

/-- Availability never exposes an oracle occurrence beyond the stopping boundary. -/
theorem no_future (pfx : FullPrefix tree) (occurrence : Cursor tree)
    (h : pfx.Available occurrence) : occurrence.length ≤ pfx.cursor.length :=
  h.2.some.length_le

/-- Witnessed extension preserves all previously allocated oracle occurrences. -/
theorem available_mono {earlier later : FullPrefix tree}
    (extension : Cursor.Extends earlier.cursor later.cursor) (occurrence : Cursor tree)
    (h : earlier.Available occurrence) : later.Available occurrence :=
  ⟨h.1, ⟨h.2.some.trans extension⟩⟩

/-- Structural extension includes old slots without changing resource identities. It does not
assert equality of hidden payloads; use `Extends.toCursor` for a full extension witness. -/
def resourceInclusion {earlier later : FullPrefix tree}
    (extension : Cursor.Extends earlier.cursor later.cursor) (InputId : Type i) :
    SchemaHom (earlier.resources InputId) (later.resources InputId) where
  map := Sum.map id (fun occurrence => ⟨occurrence.1, available_mono extension _ occurrence.2⟩)
  key_eq := by intro x; cases x <;> rfl

end FullPrefix
end Interaction.Oracle.TypeTree
