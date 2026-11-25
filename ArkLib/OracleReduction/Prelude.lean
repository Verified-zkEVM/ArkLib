/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Relation.Prelude

/-!
  # Prelude for the legacy layer

  This file contains the preliminary definitions that only the legacy layer uses: the direction
  `Direction` of a round in a `ProtocolSpec`, and the accept/reject relation
  `acceptRejectOracleRel`, whose statement carries the legacy layer's empty family of oracle
  statements. The generic preliminaries live in `ArkLib.Relation.Prelude`.
-/

@[expose] public section

/-- Enum type for the direction of a round in a protocol specification. It is either `.P_to_V`
(the prover sends a message to the verifier) or `.V_to_P` (the verifier sends a challenge to the
prover). -/
inductive Direction where
  | P_to_V  -- Message
  | V_to_P -- Challenge
deriving DecidableEq, Inhabited, Repr

namespace Direction

/-- Equivalence between `Direction` and `Fin 2`, sending `V_to_P` to `0` and `P_to_V` to `1`
(the choice is essentially arbitrary). -/
def equivFin2 : Direction ≃ Fin 2 where
  toFun := fun dir => match dir with | .V_to_P => ⟨0, by decide⟩ | .P_to_V => ⟨1, by decide⟩
  invFun := fun n => match n with | ⟨0, _⟩ => .V_to_P | ⟨1, _⟩ => .P_to_V
  left_inv := fun dir => match dir with | .P_to_V => rfl | .V_to_P => rfl
  right_inv := fun n => match n with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl

/-- Equivalence between `Direction` and `Bool`, sending `V_to_P` to `false` and `P_to_V` to `true`
(the choice is essentially arbitrary). -/
def equivBool : Direction ≃ Bool where
  toFun := fun dir => match dir with | .V_to_P => false | .P_to_V => true
  invFun := fun b => match b with | false => .V_to_P | true => .P_to_V
  left_inv := fun dir => match dir with | .P_to_V => rfl | .V_to_P => rfl
  right_inv := fun b => match b with | false => rfl | true => rfl

/-- This allows us to write `0` for `.V_to_P` and `1` for `.P_to_V`. -/
instance : Coe (Fin 2) Direction := ⟨equivFin2.invFun⟩

instance : Coe Bool Direction := ⟨equivBool.invFun⟩

lemma not_P_to_V_eq_V_to_P {x : Direction} (h : x ≠ .V_to_P) : x = .P_to_V := by
  cases x <;> simp_all

lemma not_V_to_P_eq_P_to_V {x : Direction} (h : x ≠ .P_to_V) : x = .V_to_P := by
  cases x <;> simp_all

end Direction

section Relation

/-- The trivial relation on Boolean statement, no oracle statements, and unit witness. -/
def acceptRejectOracleRel : Set ((Bool × (∀ _ : Empty, Unit)) × Unit) :=
  { ((true, isEmptyElim), ()) }

@[simp]
theorem acceptRejectOracleRel_language :
    acceptRejectOracleRel.language = { (true, isEmptyElim) } := by
  unfold Set.language acceptRejectOracleRel; simp

end Relation
