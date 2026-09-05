/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Protocol

/-!
# Mixed-tree decoration acceptance client

This file exercises AR-2B on a branch-dependent public/oracle tree. Real PolyFun cursors select the
two oracle subtrees and the later public subtrees; restricting the decorations must recover the
interface and role belonging to the selected branch.
-/

namespace Interaction.Oracle.TypeTree.DecorationExample

open Interaction.TwoParty

section UniverseCanary

universe uRole uOracle uQuery uProtocol

/-- Compile-time canary that role decorations follow the tree universe. -/
abbrev UniverseRoleDecoration (tree : Oracle.TypeTree.{uRole}) := tree.RoleDecoration

/-- Compile-time canary that tree and oracle-query universes remain independently selectable. -/
abbrev UniverseOracleDecoration (tree : Oracle.TypeTree.{uOracle}) :=
  tree.OracleDecoration.{uOracle, uQuery}

/-- Compile-time canary that the decorated bundle is not pinned to the default universe. -/
abbrev UniverseProtocol := Oracle.Protocol.{uProtocol}

end UniverseCanary

/-- Public future reached after the Boolean oracle branch. -/
def falseFuture : Oracle.TypeTree :=
  .public (Fin 2) fun _ => .done

/-- Public future reached after the `Fin 3` oracle branch. -/
def trueFuture : Oracle.TypeTree :=
  .public Bool fun _ => .done

/-- Oracle subtree selected by the false root branch. -/
def falseOracle : Oracle.TypeTree :=
  .oracle Bool fun _ => falseFuture

/-- Oracle subtree selected by the true root branch. -/
def trueOracle : Oracle.TypeTree :=
  .oracle (Fin 3) fun _ => trueFuture

/-- A public Boolean selects two different oracle messages and two different public futures. -/
def mixedTree : Oracle.TypeTree :=
  .public Bool fun
    | false => falseOracle
    | true => trueOracle

/-- The root is receiver-owned; the two future public nodes deliberately have opposite roles. -/
def mixedRoles : mixedTree.RoleDecoration :=
  ⟨.receiver, fun
    | false => ⟨PUnit.unit, fun _ => ⟨.sender, fun _ => ⟨⟩⟩⟩
    | true => ⟨PUnit.unit, fun _ => ⟨.receiver, fun _ => ⟨⟩⟩⟩⟩

/-- The two oracle branches carry interfaces for their distinct message types. -/
def mixedOracles : mixedTree.OracleDecoration :=
  ⟨PUnit.unit, fun
    | false => ⟨OracleInterface.instDefault, fun _ => ⟨PUnit.unit, fun _ => ⟨⟩⟩⟩
    | true => ⟨OracleInterface.instDefault, fun _ => ⟨PUnit.unit, fun _ => ⟨⟩⟩⟩⟩

/-- A branch-dependent decorated bundle built through the public protocol constructors. -/
def builtProtocol : Oracle.Protocol :=
  Oracle.Protocol.public .receiver Bool fun
    | false => Oracle.Protocol.oracleWith Bool OracleInterface.instDefault <|
        Oracle.Protocol.public .sender (Fin 2) fun _ => .done
    | true => Oracle.Protocol.oracleWith (Fin 3) OracleInterface.instDefault <|
        Oracle.Protocol.public .receiver Bool fun _ => .done

example : builtProtocol.roles.1 = Role.receiver :=
  rfl

example : ((builtProtocol.roles.2 false).2 PUnit.unit).1 = Role.sender :=
  rfl

example : ((builtProtocol.roles.2 true).2 PUnit.unit).1 = Role.receiver :=
  rfl

example : (builtProtocol.oracles.2 false).1.Query = Unit :=
  rfl

/-- Cursor selecting the Boolean oracle subtree. -/
def falseOracleCursor : PFunctor.FreeM.Cursor mixedTree :=
  PFunctor.FreeM.Cursor.down false (PFunctor.FreeM.Cursor.root falseOracle)

/-- Cursor selecting the `Fin 3` oracle subtree. -/
def trueOracleCursor : PFunctor.FreeM.Cursor mixedTree :=
  PFunctor.FreeM.Cursor.down true (PFunctor.FreeM.Cursor.root trueOracle)

/-- Cursor continuing through the Boolean oracle marker to its future public node. -/
def falseFutureCursor : PFunctor.FreeM.Cursor mixedTree :=
  PFunctor.FreeM.Cursor.down false <|
    PFunctor.FreeM.Cursor.down PUnit.unit (PFunctor.FreeM.Cursor.root falseFuture)

/-- Cursor continuing through the `Fin 3` oracle marker to its future public node. -/
def trueFutureCursor : PFunctor.FreeM.Cursor mixedTree :=
  PFunctor.FreeM.Cursor.down true <|
    PFunctor.FreeM.Cursor.down PUnit.unit (PFunctor.FreeM.Cursor.root trueFuture)

/-- Restriction to the false branch recovers the Boolean oracle interface and its future. -/
example : OracleDecoration.restrict falseOracleCursor mixedOracles =
    ⟨OracleInterface.instDefault, fun _ => ⟨PUnit.unit, fun _ => ⟨⟩⟩⟩ :=
  rfl

/-- Restriction to the true branch recovers the `Fin 3` oracle interface and its future. -/
example : OracleDecoration.restrict trueOracleCursor mixedOracles =
    ⟨OracleInterface.instDefault, fun _ => ⟨PUnit.unit, fun _ => ⟨⟩⟩⟩ :=
  rfl

/-- Continuing through the false oracle marker recovers its sender-owned public future. -/
example : RoleDecoration.restrict falseFutureCursor mixedRoles =
    ⟨.sender, fun _ => ⟨⟩⟩ :=
  rfl

/-- Continuing through the true oracle marker recovers its receiver-owned public future. -/
example : RoleDecoration.restrict trueFutureCursor mixedRoles =
    ⟨.receiver, fun _ => ⟨⟩⟩ :=
  rfl

/-- Runtime roles make the implicit sender ownership of an oracle node explicit. -/
example : ((RoleDecoration.toRuntimeRoles mixedRoles).2 false).1 = Role.sender :=
  rfl

/-- Erasing to a generic runtime tree preserves the implicit sender ownership. -/
example : ((RoleDecoration.toTypeTreeRoles mixedTree mixedRoles).2 false).1 = Role.sender :=
  rfl

end Interaction.Oracle.TypeTree.DecorationExample
