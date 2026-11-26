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

namespace Interaction
open PFunctor
open TwoParty.Lens

/-- Positions of a plain public-coin protocol. -/
inductive PlainPos : Type 1 where
  | message (X : Type)
  | challenge (C : Type)

/-- Only public messages select the next subtree. -/
@[implicit_reducible]
def PlainPoly : PFunctor.{1, 0} :=
  ⟨PlainPos, fun | .message X => X | .challenge _ => Unit⟩

/-- PolyFun's role polynomial `rolePoly` at `Type`. A lens `PFunctor.Lens P Q` has independent
universes for `P` and `Q`. No argument therefore determines the universe of `rolePoly` in a
signature's type. This alias has no universe parameters. -/
abbrev rolePoly0 : PFunctor.{1, 0} := rolePoly.{0}

/-- Plain messages belong to the prover; challenges belong to the sampler. -/
@[implicit_reducible]
def plainSig : PFunctor.Lens PlainPoly rolePoly0 where
  toFunA | .message X => (.sender, X) | .challenge C => (.receiver, C)
  toFunB | .message _ => id | .challenge _ => fun _ => ⟨⟩

/-- Oracle protocols additionally permit payloads with an explicit query interface. -/
inductive OraclePos : Type 1 where
  | message (X : Type)
  | challenge (C : Type)
  | oracle (X : Type) (interface : OracleInterface X)

/-- Oracle payloads, like challenges, cannot select a subtree. -/
@[implicit_reducible]
def OraclePoly : PFunctor.{1, 0} :=
  ⟨OraclePos, fun | .message X => X | .challenge _ | .oracle _ _ => Unit⟩

/-- The oracle signature records all moves and erases private payloads from branching. -/
@[implicit_reducible]
def oracleSig : PFunctor.Lens OraclePoly rolePoly0 where
  toFunA
    | .message X | .oracle X _ => (.sender, X)
    | .challenge C => (.receiver, C)
  toFunB
    | .message _ => id
    | .challenge _ | .oracle _ _ => fun _ => ⟨⟩

/-- The verifier sees public messages and challenges, and a marker for each oracle payload. -/
@[implicit_reducible]
def viewSig : PFunctor.Lens OraclePoly rolePoly0 where
  toFunA
    | .message X => (.sender, X)
    | .challenge C => (.receiver, C)
    | .oracle _ _ => (.sender, Unit)
  toFunB
    | .message _ => id
    | .challenge _ | .oracle _ _ => fun _ => ⟨⟩

/-- Forget oracle payloads without changing the underlying tree or shape path. -/
def eraseOracle : FreeM.PathAlong.MoveMap oracleSig viewSig where
  map
    | .message _, x => x
    | .challenge _, x => x
    | .oracle _ _, _ => ⟨⟩
  branch a _ := by cases a <;> rfl

@[simp] theorem owner_plain_message (X : Type) :
    owner plainSig (.message X) = .sender := rfl

@[simp] theorem owner_plain_challenge (C : Type) :
    owner plainSig (.challenge C) = .receiver := rfl

@[simp] theorem owner_oracle_message (X : Type) :
    owner oracleSig (.message X) = .sender := rfl

@[simp] theorem owner_oracle_challenge (C : Type) :
    owner oracleSig (.challenge C) = .receiver := rfl

@[simp] theorem owner_oracle_payload (X : Type) (I : OracleInterface X) :
    owner oracleSig (.oracle X I) = .sender := rfl

end Interaction
