/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.TypeTree.Decoration

/-!
# Decorated oracle protocols

`Oracle.Protocol` is the minimal authoring bundle for an oracle interaction tree: the tree, its
public-node roles, and its oracle-node interfaces. The bundle uses one ambient universe for message
and query data; the underlying `OracleDecoration` remains independently universe-polymorphic. The
smart constructors preserve by construction that public nodes carry roles while oracle nodes are
sender-owned and carry an interface.
-/

universe u

namespace Interaction.Oracle

open Interaction.TwoParty

/-- An oracle interaction tree together with its role and oracle-interface decorations. -/
abbrev Protocol :=
  Σ tree : Oracle.TypeTree.{u}, tree.RoleDecoration × tree.OracleDecoration.{u, u}

namespace Protocol

/-- The underlying public/oracle interaction tree. -/
abbrev tree (protocol : Protocol.{u}) : Oracle.TypeTree.{u} :=
  protocol.1

/-- Roles at public nodes; oracle nodes are implicitly sender-owned. -/
abbrev roles (protocol : Protocol.{u}) : protocol.tree.RoleDecoration :=
  protocol.2.1

/-- Interfaces at oracle nodes; public nodes carry no interface. -/
abbrev oracles (protocol : Protocol.{u}) : protocol.tree.OracleDecoration.{u, u} :=
  protocol.2.2

/-- Terminal decorated protocol. -/
def done : Protocol.{u} :=
  ⟨.done, ⟨⟩, ⟨⟩⟩

/-- Public move with an explicit sender/receiver role. -/
def «public» (role : Role) (Moves : Type u) (rest : Moves → Protocol.{u}) :
    Protocol.{u} :=
  ⟨.public Moves (fun move => (rest move).tree),
    ⟨role, fun move => (rest move).roles⟩,
    ⟨PUnit.unit, fun move => (rest move).oracles⟩⟩

/-- Oracle message with an explicit oracle interface. -/
def oracleWith (Messages : Type u) (interface : OracleInterface.{u, u} Messages)
    (rest : Protocol.{u}) : Protocol.{u} :=
  ⟨.oracle Messages (fun _ => rest.tree),
    ⟨PUnit.unit, fun _ => rest.roles⟩,
    ⟨interface, fun _ => rest.oracles⟩⟩

/-- Oracle message using typeclass synthesis for its interface. -/
def «oracle» (Messages : Type u) [OracleInterface.{u, u} Messages]
    (rest : Protocol.{u}) : Protocol.{u} :=
  oracleWith Messages inferInstance rest

@[simp]
theorem done_tree : (done : Protocol.{u}).tree = .done :=
  rfl

@[simp]
theorem done_roles : (done : Protocol.{u}).roles = ⟨⟩ :=
  rfl

@[simp]
theorem done_oracles : (done : Protocol.{u}).oracles = ⟨⟩ :=
  rfl

@[simp]
theorem public_tree (role : Role) (Moves : Type u) (rest : Moves → Protocol.{u}) :
    (Protocol.public role Moves rest).tree = .public Moves (fun move => (rest move).tree) :=
  rfl

@[simp]
theorem public_roles (role : Role) (Moves : Type u) (rest : Moves → Protocol.{u}) :
    (Protocol.public role Moves rest).roles = ⟨role, fun move => (rest move).roles⟩ :=
  rfl

@[simp]
theorem public_oracles (role : Role) (Moves : Type u) (rest : Moves → Protocol.{u}) :
    (Protocol.public role Moves rest).oracles =
      ⟨PUnit.unit, fun move => (rest move).oracles⟩ :=
  rfl

@[simp]
theorem oracleWith_tree (Messages : Type u) (interface : OracleInterface.{u, u} Messages)
    (rest : Protocol.{u}) :
    (oracleWith Messages interface rest).tree = .oracle Messages (fun _ => rest.tree) :=
  rfl

@[simp]
theorem oracleWith_roles (Messages : Type u) (interface : OracleInterface.{u, u} Messages)
    (rest : Protocol.{u}) :
    (oracleWith Messages interface rest).roles =
      ⟨PUnit.unit, fun _ => rest.roles⟩ :=
  rfl

@[simp]
theorem oracleWith_oracles (Messages : Type u) (interface : OracleInterface.{u, u} Messages)
    (rest : Protocol.{u}) :
    (oracleWith Messages interface rest).oracles = ⟨interface, fun _ => rest.oracles⟩ :=
  rfl

@[simp]
theorem oracle_tree (Messages : Type u) [OracleInterface.{u, u} Messages]
    (rest : Protocol.{u}) :
    (Protocol.oracle Messages rest).tree = .oracle Messages (fun _ => rest.tree) :=
  rfl

@[simp]
theorem oracle_roles (Messages : Type u) [OracleInterface.{u, u} Messages]
    (rest : Protocol.{u}) :
    (Protocol.oracle Messages rest).roles = ⟨PUnit.unit, fun _ => rest.roles⟩ :=
  rfl

@[simp]
theorem oracle_oracles (Messages : Type u) [OracleInterface.{u, u} Messages]
    (rest : Protocol.{u}) :
    (Protocol.oracle Messages rest).oracles =
      ⟨(inferInstance : OracleInterface.{u, u} Messages), fun _ => rest.oracles⟩ :=
  rfl

end Protocol
end Interaction.Oracle
