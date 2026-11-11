/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.OracleVerifier
import PolyFun.PFunctor.Free.Cursor

/-! Positions and owners on a branch-dependent oracle protocol. A public bit selects a `Bool`
oracle node or a `Fin 3` oracle node, each followed by its own public future. Each oracle node
carries its interface in its position, and its owner comes from the signature. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.TwoParty.Lens

namespace Interaction.Core.DecorationExampleTests

section UniverseCanary

universe uProtocol uQuery

/-- Oracle protocols quantify message and query universes independently. -/
abbrev UniverseProtocol (Leaf : Type uProtocol := PUnit) :=
  OracleProtocol.{uProtocol, uQuery} Leaf

/-- An arbitrary interface attaches to an oracle node without identifying its universes. -/
def universeNode (Message : Type uProtocol)
    (interface : OracleInterface.{uProtocol, uQuery} Message) :
    UniverseProtocol.{uProtocol, uQuery} :=
  .liftBind (.oracle Message interface) (fun _ => .pure ⟨⟩)

/-- A small protocol node accepts every interface whose queries lie in the next universe. -/
example (interface : OracleInterface.{0, 1} Nat) :
    Node.position (universeNode Nat interface) (.inl ⟨⟩) = .oracle Nat interface := rfl

/-- The actual node's path resources retain the interface's larger query type. -/
example (interface : OracleInterface.{0, 1} Nat) :
    @OracleInterface.Query Nat
      ((pathFamily (universeNode Nat interface) ⟨⟨⟩, ⟨⟩⟩).interface (.inl ⟨⟩)) =
      interface.Query := rfl

/-- The oracle interfaces that an arbitrary oracle tree carries along a path, with query universe
independent of the message universe. Oracle positions carry their interfaces, so the
interaction layer reads the decoration of a tree off the tree itself. -/
abbrev UniverseOracleDecoration (tree : UniverseProtocol.{uProtocol, uQuery}) (p : Path tree) :=
  pathFamily tree p

/-- On an arbitrary small tree, the decoration along any path is the tree's own path family, with
queries in the next universe. -/
example (tree : OracleProtocol.{0, 1}) (p : Path tree) :
    UniverseOracleDecoration.{0, 1} tree p = pathFamily tree p := rfl

end UniverseCanary

/-- The public future after the `Bool` oracle node. -/
def falseFuture : OracleProtocol :=
  .liftBind (.message (Fin 2)) (fun _ => .pure ⟨⟩)

/-- The receiver-owned public future after the `Fin 3` oracle node. -/
def trueFuture : OracleProtocol :=
  .liftBind (.challenge Bool) (fun _ => .pure ⟨⟩)

/-- The oracle subtree selected by `false`. -/
def falseOracle : OracleProtocol :=
  .liftBind (.oracle Bool OracleInterface.instDefault) (fun _ => falseFuture)

/-- The oracle subtree selected by `true`. -/
def trueOracle : OracleProtocol :=
  .liftBind (.oracle (Fin 3) OracleInterface.instDefault) (fun _ => trueFuture)

-- DecorationExample fixture: the frozen tree's receiver-owned root is re-authored as a prover
-- message, since challenges never select the shape.
/-- A public bit selects two different oracle nodes and two different public futures. -/
def mixedTree : OracleProtocol :=
  .liftBind (.message Bool) fun
    | false => falseOracle
    | true => trueOracle

/-- The oracle node selected by `false`. -/
def falseNode : Node mixedTree := .inr ⟨false, .inl ⟨⟩⟩

/-- The oracle node selected by `true`. -/
def trueNode : Node mixedTree := .inr ⟨true, .inl ⟨⟩⟩

/-- The shape path through the `false` branch. -/
def falsePath : Path mixedTree := ⟨false, ⟨⟩, ⟨(0 : Fin 2), ⟨⟩⟩⟩

-- DecorationExample 7, restated: the selector is a message, and the interface is read from the
-- oracle family of a completed path through the `false` branch.
/-- The `false` oracle node answers `Unit` queries. -/
example : @OracleInterface.Query Bool ((pathFamily mixedTree falsePath).interface (.inl ⟨⟩)) =
    Unit := rfl

-- DecorationExample 8, restated: decoration restriction is retired. The position at the `false`
-- oracle node carries the `Bool` interface, and the cursor through `false` selects the `Bool`
-- oracle subtree with its future.
/-- The `false` oracle node carries the `Bool` interface. -/
example : Node.position mixedTree falseNode = .oracle Bool OracleInterface.instDefault := rfl

/-- The cursor through `false` selects the `Bool` oracle subtree. -/
def falseOracleCursor : Cursor.Spine mixedTree falseOracle := .down false (.root _)

-- DecorationExample 9, restated as row 8.
/-- The `true` oracle node carries the `Fin 3` interface. -/
example : Node.position mixedTree trueNode = .oracle (Fin 3) OracleInterface.instDefault := rfl

/-- The cursor through `true` selects the `Fin 3` oracle subtree. -/
def trueOracleCursor : Cursor.Spine mixedTree trueOracle := .down true (.root _)

-- DecorationExample 12: the oracle node is sender-owned through the signature.
/-- Both oracle nodes are owned by the sender. -/
example : owner oracleSig (Node.position mixedTree falseNode) = .sender := rfl

example : owner oracleSig (Node.position mixedTree trueNode) = .sender := rfl

/-- The root is the sender's branch-selecting public message. -/
theorem root_owner : owner oracleSig (Node.position mixedTree (.inl ⟨⟩)) = .sender := rfl

/-- The public node reached through the Boolean oracle marker. -/
def falseFutureNode : Node mixedTree := .inr ⟨false, .inr ⟨⟨⟩, .inl ⟨⟩⟩⟩

/-- The public node reached through the `Fin 3` oracle marker. -/
def trueFutureNode : Node mixedTree := .inr ⟨true, .inr ⟨⟨⟩, .inl ⟨⟩⟩⟩

/-- The cursor crosses the Boolean oracle marker to the sender's public future. -/
def falseFutureCursor : Cursor.Spine mixedTree falseFuture :=
  .down false (.down ⟨⟩ (.root _))

/-- The cursor crosses the `Fin 3` oracle marker to the receiver's public future. -/
def trueFutureCursor : Cursor.Spine mixedTree trueFuture :=
  .down true (.down ⟨⟩ (.root _))

/-- The Boolean oracle is followed by a public `Fin 2` message. -/
theorem falseFuture_position :
    Node.position mixedTree falseFutureNode = .message (Fin 2) := rfl

/-- The `Fin 3` oracle is followed by a public Boolean challenge. -/
theorem trueFuture_position : Node.position mixedTree trueFutureNode = .challenge Bool := rfl

/-- Crossing the Boolean oracle marker reaches a sender-owned public future. -/
theorem falseFuture_owner :
    owner oracleSig (Node.position mixedTree falseFutureNode) = .sender := rfl

/-- Crossing the `Fin 3` oracle marker reaches a receiver-owned public future. -/
theorem trueFuture_owner :
    owner oracleSig (Node.position mixedTree trueFutureNode) = .receiver := rfl

/-- The two oracle markers lead to distinct public position constructors. -/
theorem future_positions_ne :
    Node.position mixedTree falseFutureNode ≠ Node.position mixedTree trueFutureNode := by
  intro equal
  cases equal

end Interaction.Core.DecorationExampleTests
