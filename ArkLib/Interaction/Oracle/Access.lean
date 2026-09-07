/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Protocol
import VCVio.OracleComp.SimSemantics.Append

/-!
# Accumulated oracle access

This file is the AR-3A access layer for typed oracle interactions. It records, at every node of an
`Oracle.TypeTree`, exactly the oracle resources that are queryable before the next message is sent.

Public values remain ordinary structural data: they select the dependent continuation and are not
re-encoded as oracle queries. Oracle access grows only after an oracle-backed prover message. In
particular, the access stored at an oracle node deliberately excludes that node's message; only the
continuation receives the extended specification. Future-message access is therefore absent by
construction.

Execution is intentionally out of scope. AR-3B will package prover/verifier strategies whose node
computations use the capabilities described here.
-/

universe u v

open OracleComp OracleSpec

namespace Interaction.Oracle

/-- A packed oracle specification. Packing the query-index type lets the available query space grow
as earlier prover oracle messages become available. -/
abbrev AccessSpec := Σ ι : Type v, OracleSpec.{v, u} ι

namespace AccessSpec

/-- Package an ordinary oracle specification as an access specification. -/
def ofSpec {ι : Type v} (spec : OracleSpec.{v, u} ι) : AccessSpec.{u, v} :=
  ⟨ι, spec⟩

/-- Extend an accumulated access specification with one newly available prover oracle message. -/
def extend {Messages : Type u} (access : AccessSpec.{u, v})
    (interface : OracleInterface.{u, v} Messages) : AccessSpec.{u, v} :=
  ⟨access.1 ⊕ interface.Query, access.2 + @OracleInterface.spec _ interface⟩

/-- Extend a concrete implementation of the prior access with a concrete prover oracle message. -/
def extendImpl {Messages : Type u} (access : AccessSpec.{u, v})
    (interface : OracleInterface.{u, v} Messages)
    (prior : QueryImpl access.2 Id) (message : Messages) :
    QueryImpl (access.extend interface).2 Id :=
  prior + fun q => @OracleInterface.answer _ interface message q

@[simp]
theorem extendImpl_prior {Messages : Type u} (access : AccessSpec.{u, v})
    (interface : OracleInterface.{u, v} Messages)
    (prior : QueryImpl access.2 Id) (message : Messages) (q : access.1) :
    access.extendImpl interface prior message (.inl q) = prior q :=
  rfl

@[simp]
theorem extendImpl_latest {Messages : Type u} (access : AccessSpec.{u, v})
    (interface : OracleInterface.{u, v} Messages)
    (prior : QueryImpl access.2 Id) (message : Messages) (q : interface.Query) :
    access.extendImpl interface prior message (.inr q) =
      @OracleInterface.answer _ interface message q :=
  rfl

end AccessSpec

namespace TypeTree

open PFunctor.FreeM.Displayed (Decoration)

/-- Node-local accumulated access. The recursive builder controls where this capability grows. -/
@[reducible]
def AccessContext : Oracle.Position.{u} → Type (max (u + 1) (v + 1)) :=
  fun _ => AccessSpec.{u, v}

/-- The accumulated oracle resources available immediately before every node in an oracle tree. -/
abbrev AccessDecoration (tree : Oracle.TypeTree.{u}) :=
  Decoration (P := basePFunctor) (α := PUnit.{u + 1}) AccessContext.{u, v} tree

namespace AccessDecoration

/-- Build node-local accumulated access from an initial source specification and the oracle
interfaces decorating the protocol tree.

A public node keeps the same access while its public value chooses the child. An oracle node also
stores the old access at the node itself, but appends that node's interface before constructing its
continuation. -/
def build :
    (tree : Oracle.TypeTree.{u}) →
    OracleDecoration.{u, v} tree →
    {ι : Type v} → OracleSpec.{v, u} ι →
    AccessDecoration.{u, v} tree
  | .done, _, _, _ => ⟨⟩
  | .public _ rest, oracles, _, access =>
      ⟨AccessSpec.ofSpec access, fun move => build (rest move) (oracles.2 move) access⟩
  | .oracle _ rest, oracles, _, access =>
      ⟨AccessSpec.ofSpec access, fun marker =>
        build (rest marker) (oracles.2 marker)
          (access + @OracleInterface.spec _ oracles.1)⟩

/-- Restrict accumulated access to the residual tree selected by a structural cursor. -/
abbrev restrict {tree : Oracle.TypeTree.{u}} (cursor : PFunctor.FreeM.Cursor tree)
    (access : AccessDecoration.{u, v} tree) : AccessDecoration.{u, v} cursor.residual :=
  Decoration.restrict cursor access

@[simp]
theorem restrict_root (tree : Oracle.TypeTree.{u})
    (access : AccessDecoration.{u, v} tree) :
    restrict (PFunctor.FreeM.Cursor.root tree) access = access :=
  rfl

@[simp]
theorem restrict_down {position : Oracle.Position.{u}}
    {next : position.Branch → Oracle.TypeTree.{u}} (branch : position.Branch)
    (tail : PFunctor.FreeM.Cursor (next branch))
    (access : AccessDecoration.{u, v} (PFunctor.FreeM.liftBind position next)) :
    restrict (PFunctor.FreeM.Cursor.down branch tail) access =
      restrict tail (access.2 branch) :=
  rfl

/-- Cursor composition restricts accumulated access in two stages. -/
theorem restrict_comp {tree : Oracle.TypeTree.{u}} (first : PFunctor.FreeM.Cursor tree)
    (second : PFunctor.FreeM.Cursor first.residual)
    (access : AccessDecoration.{u, v} tree) :
    restrict (first.comp second) access = restrict second (restrict first access) :=
  Decoration.restrict_comp first second access

end AccessDecoration
end TypeTree
end Interaction.Oracle
