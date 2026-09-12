/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Protocol
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Accumulated oracle access

An access signature says which queries are available, not which concrete messages were sent.
Public values select dependent continuations. An oracle message extends access only after its
send node. The canonical access at a prefix is computed from the initial signature, the oracle
decoration, and a real PolyFun cursor; it remains available at terminal leaves.

`AccessDecoration.build` is a derived node-local presentation, not an authorization certificate.
Execution must use the canonical construction rather than trust an arbitrary decoration. A
structural cursor likewise describes a syntactic prefix, not evidence that a strategy reached it.
Concrete handlers, reachability, resource identity, and verifier execution are separate concerns.
-/

@[expose] public section

universe u v

open OracleComp OracleSpec

namespace Interaction.Oracle

/-! Access uses the existing `PFunctor` carrier through `OracleSpec.ofPFunctor` / `toPFunctor`.
There is no second packed-signature record. Query and response universes remain independent. -/

namespace Access

/-- Add a disjoint query slot for a newly sent oracle message. This is signature extension, not a
claim that two same-signature resources have the same identity. The signature's query domain must
reduce at implicit transparency when checking dependent query arguments in interpreter laws. -/
@[implicit_reducible]
def extend {Messages : Type u} (access : PFunctor.{v, u})
    (interface : OracleInterface.{u, v} Messages) : PFunctor.{v, u} :=
  ((OracleSpec.ofPFunctor access) + @OracleInterface.spec _ interface).toPFunctor

/-- Extend a pure handler with the observable behavior of the concrete message just sent. -/
def extendImpl {Messages : Type u} (access : PFunctor.{v, u})
    (interface : OracleInterface.{u, v} Messages)
    (prior : QueryImpl (OracleSpec.ofPFunctor access) Id) (message : Messages) :
    QueryImpl (OracleSpec.ofPFunctor (Access.extend access interface)) Id :=
  QueryImpl.add prior
    (show QueryImpl (@OracleInterface.spec _ interface) Id from
      fun q => @OracleInterface.answer _ interface message q)

@[simp]
theorem extendImpl_prior {Messages : Type u} (access : PFunctor.{v, u})
    (interface : OracleInterface.{u, v} Messages)
    (prior : QueryImpl (OracleSpec.ofPFunctor access) Id) (message : Messages) (q : access.A) :
    Access.extendImpl access interface prior message (.inl q) = prior q :=
  rfl

@[simp]
theorem extendImpl_latest {Messages : Type u} (access : PFunctor.{v, u})
    (interface : OracleInterface.{u, v} Messages)
    (prior : QueryImpl (OracleSpec.ofPFunctor access) Id) (message : Messages)
    (q : interface.Query) :
    Access.extendImpl access interface prior message (.inr q) =
      @OracleInterface.answer _ interface message q :=
  rfl

/-- Query a prior resource after extension. Explicit routing distinguishes equal signatures. -/
def queryPrior {Messages : Type u} (access : PFunctor.{v, u})
    (interface : OracleInterface.{u, v} Messages) :
    QueryImpl (OracleSpec.ofPFunctor access)
      (OracleComp (OracleSpec.ofPFunctor (Access.extend access interface))) :=
  fun q => liftM ((OracleSpec.ofPFunctor (Access.extend access interface)).query (.inl q))

/-- Query the most recently sent message through its interface, without exposing its payload. -/
def queryLatest {Messages : Type u} (access : PFunctor.{v, u})
    (interface : OracleInterface.{u, v} Messages) :
    QueryImpl (@OracleInterface.spec _ interface)
      (OracleComp (OracleSpec.ofPFunctor (Access.extend access interface))) :=
  fun q => liftM ((OracleSpec.ofPFunctor (Access.extend access interface)).query (.inr q))

@[simp]
theorem eval_queryPrior {Messages : Type u} (access : PFunctor.{v, u})
    (interface : OracleInterface.{u, v} Messages)
    (prior : QueryImpl (OracleSpec.ofPFunctor access) Id) (message : Messages) (q : access.A) :
    simulateQ (Access.extendImpl access interface prior message)
        (Access.queryPrior access interface q) =
      prior q := by
  rw [queryPrior, simulateQ_spec_query, extendImpl_prior]

@[simp]
theorem eval_queryLatest {Messages : Type u} (access : PFunctor.{v, u})
    (interface : OracleInterface.{u, v} Messages)
    (prior : QueryImpl (OracleSpec.ofPFunctor access) Id) (message : Messages)
    (q : interface.Query) :
    simulateQ (Access.extendImpl access interface prior message)
        (Access.queryLatest access interface q) =
      @OracleInterface.answer _ interface message q := by
  rw [queryLatest, simulateQ_spec_query, extendImpl_latest]

end Access

namespace TypeTree

open PFunctor.FreeM.Displayed (Decoration)

/-- Signature accumulated along a structural spine, including spines ending at a leaf. The
signature depends on public choices and interfaces, never on concrete oracle payloads. -/
def accessAlong :
    {tree residual : Oracle.TypeTree.{u}} →
    PFunctor.FreeM.Cursor.Spine tree residual → OracleDecoration.{u, v} tree →
    PFunctor.{v, u} → PFunctor.{v, u}
  | _, _, .root _, _, access => access
  | _, _, .down (a := Oracle.Position.public _) move tail, oracles, access =>
      accessAlong tail (oracles.2 move) access
  | _, _, .down (a := Oracle.Position.oracle _) marker tail, oracles, access =>
      accessAlong tail (oracles.2 marker) (Access.extend access oracles.1)

/-- Canonical available signature at a syntactic protocol prefix. A terminal cursor still retains
all earlier slots; a node-only decoration would lose that information at its unit-valued leaf. -/
def accessAt {tree : Oracle.TypeTree.{u}} (cursor : PFunctor.FreeM.Cursor tree)
    (oracles : OracleDecoration.{u, v} tree) (initial : PFunctor.{v, u}) :
    PFunctor.{v, u} :=
  accessAlong cursor.spine oracles initial

@[simp]
theorem accessAt_root (tree : Oracle.TypeTree.{u}) (oracles : OracleDecoration.{u, v} tree)
    (initial : PFunctor.{v, u}) :
    accessAt (PFunctor.FreeM.Cursor.root tree) oracles initial = initial :=
  rfl

@[simp]
theorem accessAt_public {Moves : Type u} {rest : Moves → Oracle.TypeTree.{u}}
    (move : Moves) (tail : PFunctor.FreeM.Cursor (rest move))
    (oracles : OracleDecoration.{u, v} (.public Moves rest)) (initial : PFunctor.{v, u}) :
    accessAt (PFunctor.FreeM.Cursor.down move tail) oracles initial =
      accessAt tail (oracles.2 move) initial :=
  rfl

@[simp]
theorem accessAt_oracle {Messages : Type u} {rest : PUnit.{u + 1} → Oracle.TypeTree.{u}}
    (marker : PUnit.{u + 1}) (tail : PFunctor.FreeM.Cursor (rest marker))
    (oracles : OracleDecoration.{u, v} (.oracle Messages rest)) (initial : PFunctor.{v, u}) :
    accessAt (PFunctor.FreeM.Cursor.down marker tail) oracles initial =
      accessAt tail (oracles.2 marker) (Access.extend initial oracles.1) :=
  rfl

/-- Accumulation respects actual spine composition; the suffix uses the restricted interfaces. -/
theorem accessAlong_comp :
    {tree middle residual : Oracle.TypeTree.{u}} →
    (first : PFunctor.FreeM.Cursor.Spine tree middle) →
    (second : PFunctor.FreeM.Cursor.Spine middle residual) →
    (oracles : OracleDecoration.{u, v} tree) → (initial : PFunctor.{v, u}) →
    accessAlong (first.comp second) oracles initial =
      accessAlong second (OracleDecoration.restrict ⟨middle, first⟩ oracles)
        (accessAlong first oracles initial)
  | _, _, _, .root _, _, _, _ => rfl
  | _, _, _, .down (a := Oracle.Position.public _) move tail, second, oracles, initial =>
      accessAlong_comp tail second (oracles.2 move) initial
  | _, _, _, .down (a := Oracle.Position.oracle _) marker tail, second, oracles, initial =>
      accessAlong_comp tail second (oracles.2 marker) (Access.extend initial oracles.1)

/-- Continuing a cursor computes exactly the access accumulated by continuing from its residual. -/
theorem accessAt_comp {tree : Oracle.TypeTree.{u}} (first : PFunctor.FreeM.Cursor tree)
    (second : PFunctor.FreeM.Cursor first.residual) (oracles : OracleDecoration.{u, v} tree)
    (initial : PFunctor.{v, u}) :
    accessAt (first.comp second) oracles initial =
      accessAt second (OracleDecoration.restrict first oracles) (accessAt first oracles initial) :=
  accessAlong_comp first.spine second.spine oracles initial

/-- Available signature after a complete structural path, derived from the terminal cursor. -/
def accessAfter (tree : Oracle.TypeTree.{u}) (oracles : OracleDecoration.{u, v} tree)
    (initial : PFunctor.{v, u}) (path : BranchPath tree) : PFunctor.{v, u} :=
  accessAt (PFunctor.FreeM.Cursor.ofPath tree path) oracles initial

@[simp]
theorem accessAfter_done (oracles : OracleDecoration.{u, v} (.done : Oracle.TypeTree.{u}))
    (initial : PFunctor.{v, u}) (path : BranchPath .done) :
    accessAfter .done oracles initial path = initial :=
  rfl

@[simp]
theorem accessAfter_public (Moves : Type u) (rest : Moves → Oracle.TypeTree.{u})
    (oracles : OracleDecoration.{u, v} (.public Moves rest)) (initial : PFunctor.{v, u})
    (path : BranchPath (.public Moves rest)) :
    accessAfter (.public Moves rest) oracles initial path =
      accessAfter (rest path.1) (oracles.2 path.1) initial path.2 :=
  rfl

@[simp]
theorem accessAfter_oracle (Messages : Type u) (rest : PUnit.{u + 1} → Oracle.TypeTree.{u})
    (oracles : OracleDecoration.{u, v} (.oracle Messages rest)) (initial : PFunctor.{v, u})
    (path : BranchPath (.oracle Messages rest)) :
    accessAfter (.oracle Messages rest) oracles initial path =
      accessAfter (rest path.1) (oracles.2 path.1) (Access.extend initial oracles.1) path.2 :=
  rfl

/-- Equal public branch projections give identical available signatures. This says nothing about
equality of the concrete handlers: different hidden payloads can give different query answers. -/
theorem accessAfter_eq_of_toBranchPath_eq {tree : Oracle.TypeTree.{u}}
    (oracles : OracleDecoration.{u, v} tree) (initial : PFunctor.{v, u})
    {left right : ExecutionPath tree} (h : left.toBranchPath = right.toBranchPath) :
    accessAfter tree oracles initial left.toBranchPath =
      accessAfter tree oracles initial right.toBranchPath :=
  congrArg (accessAfter tree oracles initial) h

/-- Node-local presentation of accumulated access. The builder owns the growth rule. -/
@[reducible]
def AccessContext : Oracle.Position.{u} → Type (max (u + 1) (v + 1)) :=
  fun _ => PFunctor.{v, u}

/-- A node-local presentation, not by itself evidence of correctly scoped access. -/
abbrev AccessDecoration (tree : Oracle.TypeTree.{u}) :=
  Decoration (P := basePFunctor) (α := PUnit.{u + 1}) AccessContext.{u, v} tree

namespace AccessDecoration

/-- Build the canonical node-local presentation. Public nodes preserve access; oracle nodes expose
only the old signature at the send and extend it for the continuation. -/
def build :
    (tree : Oracle.TypeTree.{u}) → OracleDecoration.{u, v} tree →
    {ι : Type v} → OracleSpec.{v, u} ι → AccessDecoration.{u, v} tree
  | .done, _, _, _ => ⟨⟩
  | .public _ rest, oracles, _, access =>
      ⟨access.toPFunctor, fun move => build (rest move) (oracles.2 move) access⟩
  | .oracle _ rest, oracles, _, access =>
      ⟨access.toPFunctor, fun marker =>
        build (rest marker) (oracles.2 marker) (access + @OracleInterface.spec _ oracles.1)⟩

/-- Restrict a presentation using PolyFun's canonical displayed restriction. -/
abbrev restrict {tree : Oracle.TypeTree.{u}} (cursor : PFunctor.FreeM.Cursor tree)
    (access : AccessDecoration.{u, v} tree) : AccessDecoration.{u, v} cursor.residual :=
  Decoration.restrict cursor access

@[simp]
theorem restrict_root (tree : Oracle.TypeTree.{u}) (access : AccessDecoration.{u, v} tree) :
    restrict (PFunctor.FreeM.Cursor.root tree) access = access :=
  rfl

@[simp]
theorem restrict_down {position : Oracle.Position.{u}}
    {next : position.Branch → Oracle.TypeTree.{u}} (branch : position.Branch)
    (tail : PFunctor.FreeM.Cursor (next branch))
    (access : AccessDecoration.{u, v} (PFunctor.FreeM.liftBind position next)) :
    restrict (PFunctor.FreeM.Cursor.down branch tail) access = restrict tail (access.2 branch) :=
  rfl

/-- Restriction composes without introducing another cursor representation. -/
theorem restrict_comp {tree : Oracle.TypeTree.{u}} (first : PFunctor.FreeM.Cursor tree)
    (second : PFunctor.FreeM.Cursor first.residual) (access : AccessDecoration.{u, v} tree) :
    restrict (first.comp second) access = restrict second (restrict first access) :=
  Decoration.restrict_comp first second access

/-- Restricting a built presentation equals rebuilding at the residual with the accumulated access.
This connects the node presentation to the canonical prefix API, rather than merely proving laws
about arbitrary decorations. -/
theorem restrict_build_spine :
    {tree residual : Oracle.TypeTree.{u}} →
    (spine : PFunctor.FreeM.Cursor.Spine tree residual) →
    (oracles : OracleDecoration.{u, v} tree) → (initial : PFunctor.{v, u}) →
    restrict ⟨residual, spine⟩ (build tree oracles (OracleSpec.ofPFunctor initial)) =
      build residual (OracleDecoration.restrict ⟨residual, spine⟩ oracles)
        (OracleSpec.ofPFunctor (accessAlong spine oracles initial))
  | _, _, .root _, _, _ => rfl
  | _, _, .down (a := Oracle.Position.public _) move tail, oracles, initial =>
      restrict_build_spine tail (oracles.2 move) initial
  | _, _, .down (a := Oracle.Position.oracle _) marker tail, oracles, initial =>
      restrict_build_spine tail (oracles.2 marker) (Access.extend initial oracles.1)

/-- Cursor-facing canonical restriction/rebuild law. -/
theorem restrict_build {tree : Oracle.TypeTree.{u}} (cursor : PFunctor.FreeM.Cursor tree)
    (oracles : OracleDecoration.{u, v} tree) (initial : PFunctor.{v, u}) :
    restrict cursor (build tree oracles (OracleSpec.ofPFunctor initial)) =
      build cursor.residual (OracleDecoration.restrict cursor oracles)
        (OracleSpec.ofPFunctor (accessAt cursor oracles initial)) :=
  restrict_build_spine cursor.spine oracles initial

end AccessDecoration
end TypeTree
end Interaction.Oracle
