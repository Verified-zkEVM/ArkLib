/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Batteries.Data.Vector.Lemmas
public import VCVio.OracleComp.Constructions.SampleableType

/-!
  # Prelude for Interactive (Oracle) Reductions

  This file contains preliminary definitions and instances that are used in defining I(O)Rs:
  type classes for the types of oracle responses and challenges, and the language of a relation
  given as a set of statement-witness pairs. None of them depends on a protocol layer. The legacy
  layer's own preliminaries are in `ArkLib.OracleReduction.Prelude`.
-/

@[expose] public section

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

-- TODO: port first to batteries, second to mathlib

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

/-- `Sampleable` extends `VCVCompabible` with `SampleableType` -/
class Sampleable (α : Type) extends VCVCompatible α, SampleableType α

instance {α : Type} [Sampleable α] : DecidableEq α := inferInstance

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

/-- The classical witness selector for a relation: some witness of `stmt` when one exists, and
`none` otherwise. -/
noncomputable def Set.chooseWitness {α β} (rel : Set (α × β)) (stmt : α) : Option β :=
  open Classical in if h : ∃ wit, (stmt, wit) ∈ rel then some h.choose else none

/-- The selected witness is invalid exactly when the statement is outside the language. -/
theorem Set.forall_mem_chooseWitness_notMem_iff {α β} (rel : Set (α × β)) (stmt : α) :
    (∀ wit ∈ rel.chooseWitness stmt, (stmt, wit) ∉ rel) ↔ stmt ∉ rel.language := by
  unfold Set.chooseWitness
  split_ifs with h
  · simp only [Option.mem_def, Option.some.injEq, forall_eq', Set.not_mem_language_iff]
    exact iff_of_false (· h.choose_spec) (· _ h.choose_spec)
  · simpa using h

/-- The trivial relation on Boolean statement and unit witness, which outputs the Boolean (i.e.
  accepts or rejects). -/
def acceptRejectRel : Set (Bool × Unit) :=
  { (true, ()) }

@[simp]
theorem acceptRejectRel_language : acceptRejectRel.language = { true } := by
  unfold Set.language acceptRejectRel; simp

end Relation
