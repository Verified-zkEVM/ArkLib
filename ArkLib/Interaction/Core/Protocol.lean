/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Signature

/-!
# Protocol trees and observations

A protocol is a tree with trivial leaves. Shape paths contain public branch choices, while
runtime transcripts additionally record challenges and oracle payloads. The verifier view is
a fibre over the shape path. Node indices are structural and never contain erased moves.
-/

@[expose] public section

universe u q uA

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens

/-- A plain protocol is authored directly over the plain polynomial. -/
abbrev Protocol := FreeM PlainPoly.{u} PUnit.{u + 1}

/-- An oracle protocol is authored directly over the oracle polynomial. -/
abbrev OracleProtocol := FreeM OraclePoly.{u, q} PUnit.{u + 1}

/-- The oracle verifier's observation, over a specified shape path. -/
def View (s : OracleProtocol.{u, q}) (p : Path s) : Type u :=
  {v : PathAlong viewSig s // projectPathAlong viewSig s v = p}

/-- Erase oracle payloads from a completed run, retaining its exact shape path. -/
def toView (s : OracleProtocol.{u, q}) (tr : PathAlong oracleSig s) :
    View s (projectPathAlong oracleSig s tr) :=
  ⟨PathAlong.mapMoves eraseOracle s tr, projectPathAlong_mapMoves eraseOracle s tr⟩

/-- All plain moves are visible, including the challenges erased from the shape. -/
def PlainView (s : Protocol.{u}) (p : Path s) : Type u :=
  {tr : PathAlong plainSig s // projectPathAlong plainSig s tr = p}

/-- The full plain transcript with its shape certificate. -/
def toPlainView (s : Protocol.{u}) (tr : PathAlong plainSig s) :
    PlainView s (projectPathAlong plainSig s tr) := ⟨tr, rfl⟩

/-- A node occurrence selected by source branches, in the branch universe. -/
def Node {P : PFunctor.{uA, u}} : FreeM P PUnit.{u + 1} → Type u
  | .pure _ => PEmpty
  | .liftBind _ next => PUnit ⊕ ((b : _) × Node (next b))

/-- The source position at a node occurrence. -/
def Node.position {P : PFunctor.{uA, u}} :
    (s : FreeM P PUnit.{u + 1}) → Node s → P.A
  | .pure _, n => n.elim
  | .liftBind a _, .inl _ => a
  | .liftBind _ next, .inr ⟨b, n⟩ => Node.position (next b) n

/-- Challenge indices name receiver nodes using shape branches alone. -/
abbrev ChallengeNode {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    (s : FreeM P PUnit.{u + 1}) := {n : Node s // owner l (n.position s) = .receiver}

/-- Each challenge query returns the move at its indexed receiver node. -/
def challengeSpec {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    (s : FreeM P PUnit.{u + 1}) : OracleSpec (ChallengeNode l s) :=
  fun n => Move l (n.val.position s)

/-- Split a node occurrence of an appended protocol into a prefix node or a suffix node. -/
def Node.appendSplit {P : PFunctor.{uA, u}} :
    (s₁ : FreeM P PUnit.{u + 1}) → (s₂ : Path s₁ → FreeM P PUnit.{u + 1}) →
    Node (s₁.append s₂) → Node s₁ ⊕ (p : Path s₁) × Node (s₂ p)
  | .pure _, _, n => .inr ⟨⟨⟩, n⟩
  | .liftBind _ _, _, .inl u => .inl (.inl u)
  | .liftBind _ next, s₂, .inr ⟨b, m⟩ =>
    match Node.appendSplit (next b) (fun p => s₂ ⟨b, p⟩) m with
    | .inl m' => .inl (.inr ⟨b, m'⟩)
    | .inr ⟨p, m'⟩ => .inr ⟨⟨b, p⟩, m'⟩

/-- Embed a prefix node or a suffix node into the appended protocol. -/
def Node.appendJoin {P : PFunctor.{uA, u}} :
    (s₁ : FreeM P PUnit.{u + 1}) → (s₂ : Path s₁ → FreeM P PUnit.{u + 1}) →
    Node s₁ ⊕ (p : Path s₁) × Node (s₂ p) → Node (s₁.append s₂)
  | .pure _, _, .inl n => nomatch n
  | .pure _, _, .inr ⟨⟨⟩, n⟩ => n
  | .liftBind _ _, _, .inl (.inl u) => .inl u
  | .liftBind _ next, s₂, .inl (.inr ⟨b, m⟩) =>
    .inr ⟨b, Node.appendJoin (next b) (fun p => s₂ ⟨b, p⟩) (.inl m)⟩
  | .liftBind _ next, s₂, .inr ⟨⟨b, p⟩, m⟩ =>
    .inr ⟨b, Node.appendJoin (next b) (fun p => s₂ ⟨b, p⟩) (.inr ⟨p, m⟩)⟩

/-- Joining a split node returns it. -/
theorem Node.appendJoin_appendSplit {P : PFunctor.{uA, u}} :
    (s₁ : FreeM P PUnit.{u + 1}) → (s₂ : Path s₁ → FreeM P PUnit.{u + 1}) →
    (n : Node (s₁.append s₂)) → Node.appendJoin s₁ s₂ (Node.appendSplit s₁ s₂ n) = n
  | .pure _, _, _ => rfl
  | .liftBind _ _, _, .inl _ => rfl
  | .liftBind _ next, s₂, .inr ⟨b, m⟩ => by
    have ih := Node.appendJoin_appendSplit (next b) (fun p => s₂ ⟨b, p⟩) m
    simp only [Node.appendSplit]
    split <;> rename_i h <;> rw [h] at ih <;> simp only [Node.appendJoin, ih] <;> rfl

/-- Splitting a joined node returns it. -/
theorem Node.appendSplit_appendJoin {P : PFunctor.{uA, u}} :
    (s₁ : FreeM P PUnit.{u + 1}) → (s₂ : Path s₁ → FreeM P PUnit.{u + 1}) →
    (x : Node s₁ ⊕ (p : Path s₁) × Node (s₂ p)) →
      Node.appendSplit s₁ s₂ (Node.appendJoin s₁ s₂ x) = x
  | .pure _, _, .inl n => nomatch n
  | .pure _, _, .inr ⟨⟨⟩, _⟩ => rfl
  | .liftBind _ _, _, .inl (.inl _) => rfl
  | .liftBind _ next, s₂, .inl (.inr ⟨b, m⟩) => by
    simp only [Node.appendJoin, Node.appendSplit,
      Node.appendSplit_appendJoin (next b) (fun p => s₂ ⟨b, p⟩) (.inl m)]
  | .liftBind _ next, s₂, .inr ⟨⟨b, p⟩, m⟩ => by
    simp only [Node.appendJoin, Node.appendSplit,
      Node.appendSplit_appendJoin (next b) (fun p => s₂ ⟨b, p⟩) (.inr ⟨p, m⟩)]

/-- Node occurrences of an appended protocol are those of the prefix and those of the suffix
fibres. This is generic in the polynomial and is a candidate for PolyFun. -/
def Node.appendEquiv {P : PFunctor.{uA, u}} (s₁ : FreeM P PUnit.{u + 1})
    (s₂ : Path s₁ → FreeM P PUnit.{u + 1}) :
    Node (s₁.append s₂) ≃ Node s₁ ⊕ (p : Path s₁) × Node (s₂ p) where
  toFun := Node.appendSplit s₁ s₂
  invFun := Node.appendJoin s₁ s₂
  left_inv := Node.appendJoin_appendSplit s₁ s₂
  right_inv := Node.appendSplit_appendJoin s₁ s₂

/-- A split node has the position of the node it came from. -/
theorem Node.position_appendSplit {P : PFunctor.{uA, u}} :
    (s₁ : FreeM P PUnit.{u + 1}) → (s₂ : Path s₁ → FreeM P PUnit.{u + 1}) →
    (n : Node (s₁.append s₂)) →
    Node.position (s₁.append s₂) n = Sum.elim (Node.position s₁)
      (fun x => Node.position (s₂ x.1) x.2) (Node.appendSplit s₁ s₂ n)
  | .pure _, _, _ => rfl
  | .liftBind _ _, _, .inl _ => rfl
  | .liftBind _ next, s₂, .inr ⟨b, m⟩ => by
    have ih := Node.position_appendSplit (next b) (fun p => s₂ ⟨b, p⟩) m
    simp only [Node.appendSplit]
    split <;> rename_i h <;> rw [h] at ih <;> exact ih

/-- The node splitting preserves positions. -/
theorem Node.position_appendEquiv {P : PFunctor.{uA, u}} (s₁ : FreeM P PUnit.{u + 1})
    (s₂ : Path s₁ → FreeM P PUnit.{u + 1}) (n : Node (s₁.append s₂)) :
    Node.position (s₁.append s₂) n = Sum.elim (Node.position s₁)
      (fun x => Node.position (s₂ x.1) x.2) (Node.appendEquiv s₁ s₂ n) :=
  Node.position_appendSplit s₁ s₂ n

/-- Challenge nodes of an appended protocol are those of the prefix and those of the suffix
fibres. This is generic in the polynomial and the lens and is a candidate for PolyFun. -/
def ChallengeNode.appendEquiv {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    (s₁ : FreeM P PUnit.{u + 1}) (s₂ : Path s₁ → FreeM P PUnit.{u + 1}) :
    ChallengeNode l (s₁.append s₂) ≃
      ChallengeNode l s₁ ⊕ (p : Path s₁) × ChallengeNode l (s₂ p) :=
  (Equiv.subtypeEquiv (q := Sum.elim (fun m : Node s₁ => owner l (m.position s₁) = .receiver)
      (fun x : (p : Path s₁) × Node (s₂ p) => owner l (x.2.position (s₂ x.1)) = .receiver))
    (Node.appendEquiv s₁ s₂) fun n => by
      rw [Node.position_appendEquiv]
      rcases Node.appendEquiv s₁ s₂ n with m | x <;> rfl).trans
  (Equiv.subtypeSum.trans (Equiv.sumCongr (Equiv.refl _)
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }))

/-- A challenge value changes the transcript but not the projected branch. -/
theorem plain_challenge_shape (C : Type u) (s : Protocol.{u})
    (x y : C) (tr : PathAlong plainSig s) :
    projectPathAlong plainSig (.liftBind (.challenge C) (fun _ => s)) ⟨x, tr⟩ =
      projectPathAlong plainSig (.liftBind (.challenge C) (fun _ => s)) ⟨y, tr⟩ := rfl

/-- An oracle payload likewise changes no branch of the source path. -/
theorem oracle_payload_shape (X : Type u) (I : OracleInterface.{u, q} X)
    (s : OracleProtocol.{u, q}) (x y : X) (tr : PathAlong oracleSig s) :
    projectPathAlong oracleSig (.liftBind (.oracle X I) (fun _ => s)) ⟨x, tr⟩ =
      projectPathAlong oracleSig (.liftBind (.oracle X I) (fun _ => s)) ⟨y, tr⟩ := rfl

end Interaction.Core
