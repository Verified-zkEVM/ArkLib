/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.TypeTree
import ArkLib.OracleReduction.OracleInterface
import PolyFun.Interaction.TwoParty.Decoration
import PolyFun.PFunctor.Free.Displayed.Cursor

/-!
# Decorations on oracle interaction type trees

The oracle tree position already records whether a node is public or oracle-backed. The two
decorations in this file attach only the data appropriate to that position:

* `RoleDecoration` stores a sender/receiver role at public nodes and `PUnit` at oracle nodes;
* `OracleDecoration` stores `PUnit` at public nodes and an `OracleInterface` at oracle nodes.

Both are specializations of PolyFun's generic node decoration, so they inherit structural maps and
cursor restriction. Oracle nodes project to sender-owned runtime nodes.
-/

universe u v

namespace Interaction.Oracle.TypeTree

open Interaction.TwoParty
open PFunctor.FreeM.Displayed (Decoration)

/-! ## Node contexts -/

/-- Node-local role data. Oracle messages are always sender-owned, so their role is implicit. -/
@[reducible]
def RoleContext : Oracle.Position.{u} → Type
  | .public _ => Role
  | .oracle _ => PUnit

namespace RoleContext

/-- Expose every oracle-tree node as a runtime role, making oracle ownership explicitly sender. -/
def toRuntime : (position : Oracle.Position.{u}) → RoleContext position → Role
  | .public _, role => role
  | .oracle _, _ => .sender

@[simp]
theorem toRuntime_public (Moves : Type u) (role : Role) :
    toRuntime (.public Moves) role = role :=
  rfl

@[simp]
theorem toRuntime_oracle (Messages : Type u) (marker : PUnit) :
    toRuntime (.oracle Messages) marker = .sender :=
  rfl

end RoleContext

/-- Node-local oracle-interface data. Public nodes carry no oracle interface. -/
@[reducible]
def OracleInterfaceContext : Oracle.Position.{u} → Type (max (u + 1) (v + 1))
  | .public _ => PUnit
  | .oracle Messages => OracleInterface.{u, v} Messages

/-! ## Decorations -/

/-- Public-node roles over an oracle interaction tree. Oracle nodes carry the unique unit marker. -/
abbrev RoleDecoration (tree : Oracle.TypeTree.{u}) :=
  Decoration (P := basePFunctor) (α := PUnit.{u + 1}) RoleContext tree

/-- Oracle interfaces over an oracle interaction tree. Public nodes carry the unique unit marker. -/
abbrev OracleDecoration (tree : Oracle.TypeTree.{u}) : Type (max (u + 1) (v + 1)) :=
  Decoration (P := basePFunctor) (α := PUnit.{u + 1}) OracleInterfaceContext.{u, v} tree

namespace RoleDecoration

/-- Restrict roles to the residual tree selected by a structural cursor. -/
abbrev restrict {tree : Oracle.TypeTree.{u}} (cursor : PFunctor.FreeM.Cursor tree)
    (roles : RoleDecoration tree) : RoleDecoration cursor.residual :=
  Decoration.restrict cursor roles

@[simp]
theorem restrict_root (tree : Oracle.TypeTree.{u}) (roles : RoleDecoration tree) :
    restrict (PFunctor.FreeM.Cursor.root tree) roles = roles :=
  rfl

@[simp]
theorem restrict_down {position : Oracle.Position.{u}}
    {next : position.Branch → Oracle.TypeTree.{u}} (branch : position.Branch)
    (tail : PFunctor.FreeM.Cursor (next branch))
    (roles : RoleDecoration (PFunctor.FreeM.liftBind position next)) :
    restrict (PFunctor.FreeM.Cursor.down branch tail) roles =
      restrict tail (roles.2 branch) :=
  rfl

theorem restrict_comp {tree : Oracle.TypeTree.{u}} (first : PFunctor.FreeM.Cursor tree)
    (second : PFunctor.FreeM.Cursor first.residual) (roles : RoleDecoration tree) :
    restrict (first.comp second) roles = restrict second (restrict first roles) :=
  Decoration.restrict_comp first second roles

/-- Make the implicit sender role at oracle nodes explicit for lens-native runtime clients. -/
def toRuntimeRoles {tree : Oracle.TypeTree.{u}} (roles : RoleDecoration tree) :
    TwoParty.RoleDecorationOver (P := basePFunctor) tree :=
  Decoration.map (P := basePFunctor) (α := PUnit.{u + 1})
    RoleContext.toRuntime tree roles

@[simp]
theorem toRuntimeRoles_done (roles : RoleDecoration (Oracle.TypeTree.done : Oracle.TypeTree.{u})) :
    toRuntimeRoles roles = ⟨⟩ :=
  rfl

@[simp]
theorem toRuntimeRoles_public (Moves : Type u) (rest : Moves → Oracle.TypeTree.{u})
    (roles : RoleDecoration (Oracle.TypeTree.public Moves rest)) :
    toRuntimeRoles roles = ⟨roles.1, fun move => toRuntimeRoles (roles.2 move)⟩ :=
  rfl

@[simp]
theorem toRuntimeRoles_oracle (Messages : Type u)
    (rest : PUnit.{u + 1} → Oracle.TypeTree.{u})
    (roles : RoleDecoration (Oracle.TypeTree.oracle Messages rest)) :
    toRuntimeRoles roles =
      ⟨.sender, fun _ => toRuntimeRoles (roles.2 PUnit.unit)⟩ :=
  rfl

/-- Making oracle sender ownership explicit commutes with cursor restriction. -/
theorem toRuntimeRoles_restrict {tree : Oracle.TypeTree.{u}}
    (cursor : PFunctor.FreeM.Cursor tree) (roles : RoleDecoration tree) :
    toRuntimeRoles (restrict cursor roles) =
      Decoration.restrict cursor (toRuntimeRoles roles) :=
  by simpa only [toRuntimeRoles] using
    (Decoration.restrict_map RoleContext.toRuntime cursor roles).symm

/-- Project roles to the erased generic runtime type tree. -/
def toTypeTreeRoles : (tree : Oracle.TypeTree.{u}) → RoleDecoration tree →
    TwoParty.RoleDecoration tree.toTypeTree
  | .done, _ => ⟨⟩
  | .public _ rest, ⟨role, roles⟩ =>
      ⟨role, fun move => toTypeTreeRoles (rest move) (roles move)⟩
  | .oracle _ rest, ⟨_, roles⟩ =>
      ⟨.sender, fun _ => toTypeTreeRoles (rest PUnit.unit) (roles PUnit.unit)⟩

@[simp]
theorem toTypeTreeRoles_done
    (roles : RoleDecoration (Oracle.TypeTree.done : Oracle.TypeTree.{u})) :
    toTypeTreeRoles .done roles = ⟨⟩ :=
  rfl

@[simp]
theorem toTypeTreeRoles_public (Moves : Type u) (rest : Moves → Oracle.TypeTree.{u})
    (roles : RoleDecoration (Oracle.TypeTree.public Moves rest)) :
    toTypeTreeRoles (.public Moves rest) roles =
      ⟨roles.1, fun move => toTypeTreeRoles (rest move) (roles.2 move)⟩ :=
  rfl

@[simp]
theorem toTypeTreeRoles_oracle (Messages : Type u)
    (rest : PUnit.{u + 1} → Oracle.TypeTree.{u})
    (roles : RoleDecoration (Oracle.TypeTree.oracle Messages rest)) :
    toTypeTreeRoles (.oracle Messages rest) roles =
      ⟨.sender, fun _ => toTypeTreeRoles (rest PUnit.unit) (roles.2 PUnit.unit)⟩ :=
  rfl

end RoleDecoration

namespace OracleDecoration

/-- Restrict oracle interfaces to the residual tree selected by a structural cursor. -/
abbrev restrict {tree : Oracle.TypeTree.{u}} (cursor : PFunctor.FreeM.Cursor tree)
    (oracles : OracleDecoration.{u, v} tree) : OracleDecoration.{u, v} cursor.residual :=
  Decoration.restrict cursor oracles

@[simp]
theorem restrict_root (tree : Oracle.TypeTree.{u}) (oracles : OracleDecoration.{u, v} tree) :
    restrict (PFunctor.FreeM.Cursor.root tree) oracles = oracles :=
  rfl

@[simp]
theorem restrict_down {position : Oracle.Position.{u}}
    {next : position.Branch → Oracle.TypeTree.{u}} (branch : position.Branch)
    (tail : PFunctor.FreeM.Cursor (next branch))
    (oracles : OracleDecoration.{u, v} (PFunctor.FreeM.liftBind position next)) :
    restrict (PFunctor.FreeM.Cursor.down branch tail) oracles =
      restrict tail (oracles.2 branch) :=
  rfl

theorem restrict_comp {tree : Oracle.TypeTree.{u}} (first : PFunctor.FreeM.Cursor tree)
    (second : PFunctor.FreeM.Cursor first.residual)
    (oracles : OracleDecoration.{u, v} tree) :
    restrict (first.comp second) oracles = restrict second (restrict first oracles) :=
  Decoration.restrict_comp first second oracles

end OracleDecoration

end Interaction.Oracle.TypeTree
