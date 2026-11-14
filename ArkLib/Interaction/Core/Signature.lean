/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Relation.Basic
public import PolyFun.Interaction.TwoParty.Lens.PublicCoin
public import PolyFun.PFunctor.Free.Path.MapMoves

/-!
# Plain and oracle interaction signatures

Public messages select branches. Challenges and oracle payloads have a single branch, while
remaining recorded in the full transcript. Oracle positions carry their query interface.
Ownership is determined by the signature into PolyFun's role polynomial.
-/

@[expose] public section

universe u q

namespace Interaction.Core
open PFunctor
open TwoParty.Lens

/-- Positions of a plain public-coin protocol. -/
inductive PlainPos : Type (u + 1) where
  | message (X : Type u)
  | challenge (C : Type u)

/-- Only public messages select the next subtree. -/
@[implicit_reducible]
def PlainPoly : PFunctor.{u + 1, u} :=
  ⟨PlainPos, fun | .message X => X | .challenge _ => PUnit⟩

/-- Plain messages belong to the prover; challenges belong to the sampler. -/
@[implicit_reducible]
def plainSig : PFunctor.Lens PlainPoly rolePoly.{u} where
  toFunA | .message X => (.sender, X) | .challenge C => (.receiver, C)
  toFunB | .message _ => id | .challenge _ => fun _ => ⟨⟩

/-- Oracle protocols additionally permit payloads with an explicit query interface. The query
universe `q` is independent of the payload and response universe `u`. -/
inductive OraclePos : Type (max (u + 1) (q + 1)) where
  | message (X : Type u)
  | challenge (C : Type u)
  | oracle (X : Type u) (interface : OracleInterface.{u, q} X)

/-- Oracle payloads, like challenges, cannot select a subtree. -/
@[implicit_reducible]
def OraclePoly : PFunctor.{max (u + 1) (q + 1), u} :=
  ⟨OraclePos.{u, q}, fun | .message X => X | .challenge _ | .oracle _ _ => PUnit⟩

/-- The oracle signature records all moves and erases private payloads from branching. -/
@[implicit_reducible]
def oracleSig : PFunctor.Lens OraclePoly.{u, q} rolePoly.{u} where
  toFunA
    | .message X | .oracle X _ => (.sender, X)
    | .challenge C => (.receiver, C)
  toFunB
    | .message _ => id
    | .challenge _ | .oracle _ _ => fun _ => ⟨⟩

/-- The verifier sees public messages and challenges, and a marker for each oracle payload. -/
@[implicit_reducible]
def viewSig : PFunctor.Lens OraclePoly.{u, q} rolePoly.{u} where
  toFunA
    | .message X => (.sender, X)
    | .challenge C => (.receiver, C)
    | .oracle _ _ => (.sender, PUnit)
  toFunB
    | .message _ => id
    | .challenge _ | .oracle _ _ => fun _ => ⟨⟩

/-- Forget oracle payloads without changing the underlying tree or shape path. -/
def eraseOracle : FreeM.PathAlong.MoveMap oracleSig.{u, q} viewSig where
  map
    | .message _, x => x
    | .challenge _, x => x
    | .oracle _ _, _ => ⟨⟩
  branch a _ := by cases a <;> rfl

@[simp] theorem owner_plain_message (X : Type u) :
    owner plainSig (.message X) = .sender := rfl

@[simp] theorem owner_plain_challenge (C : Type u) :
    owner plainSig (.challenge C) = .receiver := rfl

@[simp] theorem owner_oracle_message (X : Type u) :
    owner oracleSig.{u, q} (.message X) = .sender := rfl

@[simp] theorem owner_oracle_challenge (C : Type u) :
    owner oracleSig.{u, q} (.challenge C) = .receiver := rfl

@[simp] theorem owner_oracle_payload (X : Type u) (I : OracleInterface.{u, q} X) :
    owner oracleSig (.oracle X I) = .sender := rfl

end Interaction.Core
