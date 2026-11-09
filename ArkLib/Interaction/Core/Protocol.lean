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

universe u uA

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens

/-- A plain protocol is authored directly over the plain polynomial. -/
abbrev Protocol := FreeM PlainPoly.{u} PUnit.{u + 1}

/-- An oracle protocol is authored directly over the oracle polynomial. -/
abbrev OracleProtocol := FreeM OraclePoly.{u} PUnit.{u + 1}

/-- The oracle verifier's observation, over a specified shape path. -/
def View (s : OracleProtocol.{u}) (p : Path s) : Type u :=
  {v : PathAlong viewSig s // projectPathAlong viewSig s v = p}

/-- Erase oracle payloads from a completed run, retaining its exact shape path. -/
def toView (s : OracleProtocol.{u}) (tr : PathAlong oracleSig s) :
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

/-- A challenge value changes the transcript but not the projected branch. -/
theorem plain_challenge_shape (C : Type u) (s : Protocol.{u})
    (x y : C) (tr : PathAlong plainSig s) :
    projectPathAlong plainSig (.liftBind (.challenge C) (fun _ => s)) ⟨x, tr⟩ =
      projectPathAlong plainSig (.liftBind (.challenge C) (fun _ => s)) ⟨y, tr⟩ := rfl

/-- An oracle payload likewise changes no branch of the source path. -/
theorem oracle_payload_shape (X : Type u) (I : OracleInterface.{u, u} X)
    (s : OracleProtocol.{u}) (x y : X) (tr : PathAlong oracleSig s) :
    projectPathAlong oracleSig (.liftBind (.oracle X I) (fun _ => s)) ⟨x, tr⟩ =
      projectPathAlong oracleSig (.liftBind (.oracle X I) (fun _ => s)) ⟨y, tr⟩ := rfl

end Interaction.Core
