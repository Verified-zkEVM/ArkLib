/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Batteries.Data.Vector.Lemmas
import VCVio.OracleComp.Constructions.SampleableType

/-!
  # Prelude for Interactive (Oracle) Reductions

  This file contains preliminary definitions and instances that is used in defining I(O)Rs.
-/

open OracleComp

-- -- Notation for sums (maybe not needed?)
-- @[inherit_doc] postfix:max "↪ₗ" => Sum.inl
-- @[inherit_doc] postfix:max "↪ᵣ" => Sum.inr

/-- `⊕ᵥ` is notation for `Sum.rec`, the dependent elimination of `Sum.

This sends `(a : α) → γ (.inl a)` and `(b : β) → γ (.inr b)` to `(a : α ⊕ β) → γ a`. -/
infixr:35 " ⊕ᵥ " => Sum.rec

-- Figure out where to put this instance
instance instDecidableEqOption {α : Type*} [DecidableEq α] :
    DecidableEq (Option α) := inferInstance

/-- `VCVCompabible` is a type class for types that are finite, inhabited, and have decidable
  equality. These instances are needed when the type is used as the range of some `OracleSpec`. -/
class VCVCompatible (α : Type*) extends Fintype α, Inhabited α where
  [type_decidableEq' : DecidableEq α]

instance {α : Type*} [VCVCompatible α] : DecidableEq α := VCVCompatible.type_decidableEq'

@[simp]
theorem Vector.ofFn_get {α : Type*} {n : ℕ} (v : Vector α n) : Vector.ofFn (Vector.get v) = v := by
  ext
  simp [getElem]

def Equiv.rootVectorEquivFin {α : Type*} {n : ℕ} : Vector α n ≃ (Fin n → α) :=
  ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext <| Vector.get_ofFn f⟩

instance Vector.instFintype {α : Type*} {n : ℕ} [VCVCompatible α] : Fintype (Vector α n) :=
  Fintype.ofEquiv _ (Equiv.rootVectorEquivFin).symm

instance {α : Type*} {n : ℕ} [VCVCompatible α] : VCVCompatible (Fin n → α) where

instance {α : Type*} {n : ℕ} [VCVCompatible α] : VCVCompatible (Vector α n) where

instance {α β : Type*} [VCVCompatible α] [VCVCompatible β] : VCVCompatible (α × β) where

/-- `Sampleable` extends `VCVCompabible` with `SampleableType` -/
class Sampleable (α : Type) extends VCVCompatible α, SampleableType α

instance {α : Type} [Sampleable α] : DecidableEq α := inferInstance

/-!
## FinEnum bridge instances

These four instances form a chain that lets typeclass synthesis derive
`SampleableType (OracleFamily spec)` and `SampleableType (Equiv.Perm α)`
from granular `[VCVCompatible _]` hypotheses alone, without requiring verbose
`[SampleableType (OracleFamily (...))]` assumptions at call sites.

Chain: `VCVCompatible α` → `FinEnum α`
  → `FinEnum (Vector α n)` (via `Equiv.rootVectorEquivFin`)
  → `FinEnum (Equiv.Perm α)` (via `Fintype.equivFin`)
  → `SampleableType _` (via `FinEnum.SampleableType`)
-/

/-- `VCVCompatible` implies `FinEnum` (noncomputable, via `Fintype.equivFin`).
Low priority so explicit `FinEnum` instances on specific types take precedence. -/
noncomputable instance (priority := 50) VCVCompatible.instFinEnum
    {α : Type*} [VCVCompatible α] : FinEnum α where
  card := Fintype.card α
  equiv := Fintype.equivFin α
  decEq := inferInstance

/-- `FinEnum α` implies `FinEnum (Vector α n)` via `Equiv.rootVectorEquivFin`. -/
noncomputable instance Vector.instFinEnum
    {α : Type*} {n : ℕ} [FinEnum α] : FinEnum (Vector α n) :=
  FinEnum.ofEquiv _ Equiv.rootVectorEquivFin

/-- `Equiv.Perm α` is always nonempty (contains `Equiv.refl α`). -/
instance instNonemptyEquivPerm {α : Type*} : Nonempty (Equiv.Perm α) := ⟨Equiv.refl _⟩

/-- `FinEnum α` implies `FinEnum (Equiv.Perm α)` noncomputably. -/
noncomputable instance instFinEnumEquivPerm
    {α : Type*} [FinEnum α] : FinEnum (Equiv.Perm α) where
  card := Fintype.card (Equiv.Perm α)
  equiv := Fintype.equivFin _
  decEq := inferInstance

/-- `VCVCompatible α` implies `SampleableType α`.

Direct bridge: `VCVCompatible` → `FinEnum` → `SampleableType`, without relying on
multi-step typeclass synthesis that may fail at priority 50. -/
noncomputable instance VCVCompatible.instSampleableType
    {α : Type} [VCVCompatible α] : SampleableType α :=
  letI : FinEnum α := VCVCompatible.instFinEnum
  inferInstance

/-- `VCVCompatible α` implies `SampleableType (Equiv.Perm α)`.

Consolidates the chain: `VCVCompatible` → `FinEnum` → `FinEnum (Perm)` → `SampleableType`. -/
noncomputable instance instSampleableTypeEquivPermVCV
    {α : Type} [VCVCompatible α] : SampleableType (Equiv.Perm α) := by
  letI : FinEnum α := VCVCompatible.instFinEnum
  letI : Nonempty (Equiv.Perm α) := ⟨Equiv.refl _⟩
  infer_instance

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

@[simp]
lemma not_P_to_V_eq_V_to_P {x : Direction} (h : x ≠ .V_to_P) : x = .P_to_V := by
  cases x <;> simp_all

@[simp]
lemma not_V_to_P_eq_P_to_V {x : Direction} (h : x ≠ .P_to_V) : x = .V_to_P := by
  cases x <;> simp_all

end Direction

section Relation

-- TODO: use mathlib's `Rel` which will be `Set`-based in the next update

/-- The associated language `Set α` for a relation `Set (α × β)`. -/
@[reducible]
def Set.language {α β} (rel : Set (α × β)) : Set α :=
  Prod.fst '' rel

@[simp]
theorem Set.mem_language_iff {α β} (rel : Set (α × β)) (stmt : α) :
    stmt ∈ rel.language ↔ ∃ wit, (stmt, wit) ∈ rel := by
  simp [language]

@[simp]
theorem Set.not_mem_language_iff {α β} (rel : Set (α × β)) (stmt : α) :
    stmt ∉ rel.language ↔ ∀ wit, (stmt, wit) ∉ rel := by
  simp [language]

/-- The trivial relation on Boolean statement and unit witness, which outputs the Boolean (i.e.
  accepts or rejects). -/
def acceptRejectRel : Set (Bool × Unit) :=
  { (true, ()) }

/-- The trivial relation on Boolean statement, no oracle statements, and unit witness. -/
def acceptRejectOracleRel : Set ((Bool × (∀ _ : Empty, Unit)) × Unit) :=
  { ((true, isEmptyElim), ()) }

@[simp]
theorem acceptRejectRel_language : acceptRejectRel.language = { true } := by
  unfold Set.language acceptRejectRel; simp

@[simp]
theorem acceptRejectOracleRel_language :
    acceptRejectOracleRel.language = { (true, isEmptyElim) } := by
  unfold Set.language acceptRejectOracleRel; simp

end Relation
