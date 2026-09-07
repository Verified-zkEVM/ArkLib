/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Resource
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Resource-schema acceptance clients

These clients distinguish identity from answer equality, test explicit sharing against disjoint
allocation, and connect a reified bound to the actual refined object serving each query. The
renaming client changes both a query's resource and its dependent backing-object type.
-/

universe i q a e o p d s h

namespace Interaction.Oracle.ResourceExample

/-- Equal query interfaces can belong to different, differently bounded resources. -/
def catalog : ResourceCatalog Bool (fun _ => Bool) (fun r => Fin (if r then 5 else 3))
    Nat (Bool × Nat) (fun _ => Nat) where
  source := fun r =>
    { spec := Bool →ₒ Nat
      impl := fun (query : Bool) (obj : Fin (if r then 5 else 3)) =>
        (obj.val + (if query then 1 else 0) : Nat) }
  owner := fun r => if r then 20 else 10
  origin := fun r => (r, 7)
  meaning := fun _ bound obj => obj.val < bound
  required := fun r bound => bound = if r then 5 else 3
  valid := by
    intro r bound h obj
    subst bound
    exact obj.isLt

/-- An unused identity may have an empty descriptor language.

The allocated `false` resource selects a unit guarantee; constructing the catalog does not require
manufacturing a descriptor for the unallocated `true` identity. -/
def sparseCatalog : ResourceCatalog Bool (fun _ => PUnit) (fun _ => PUnit)
    PUnit PUnit (fun r => if r then PEmpty else PUnit) where
  source := fun _ =>
    { spec := PUnit →ₒ PUnit
      impl := fun _ _ => PUnit.unit }
  owner := fun _ => PUnit.unit
  origin := fun _ => PUnit.unit
  meaning := fun _ _ _ => True
  required := fun _ _ => True
  valid := fun _ _ _ _ => True.intro

example : sparseCatalog.Guarantee false := ⟨PUnit.unit, True.intro⟩

example (guarantee : sparseCatalog.Guarantee true) : False :=
  PEmpty.elim guarantee.val

/-- The first allocation has a three-valued backing type. -/
def left := ResourceSchema.single false

/-- The second allocation has a five-valued backing type. -/
def right := ResourceSchema.single true

/-- Tensoring these allocations is justified by distinct identities, not their answers. -/
theorem separate : left.Disjoint right := by
  intro x y
  change false ≠ true
  decide

/-- Two independent allocated objects. -/
def pair := left.tensor right separate

/-- A concrete object in the three-valued backing type. -/
def smallObject : Fin 3 := ⟨2, by decide⟩

/-- A concrete object in the five-valued backing type. -/
def largeObject : Fin 5 := ⟨4, by decide⟩

/-- Neither side's backing data is constant or interchangeable with the other's type. -/
def pairEnv : (x : pair.Slot) → Fin (if pair.key x then 5 else 3)
  | .inl _ => smallObject
  | .inr _ => largeObject

/-- Query both allocations, distinguishing both the resource and primitive-query routing. -/
def readPair : OracleComp (pair.asSource catalog).spec (Nat × Nat) := do
  let x : Nat ← liftM ((pair.asSource catalog).spec.query ⟨.inl ⟨⟩, true⟩)
  let y : Nat ← liftM ((pair.asSource catalog).spec.query ⟨.inr ⟨⟩, false⟩)
  return (x, y)

example : (pair.asSource catalog).eval pairEnv readPair = (3, 4) := rfl

example : ¬ left.Disjoint left := left.not_disjoint_self ⟨⟩

/-- Two public names, but only one allocated object and one backing environment entry. -/
def aliases : ResourceView left :=
  (ResourceView.full left).reindex (fun _ : Bool => PUnit.unit)

/-- Both names issue their primitive query against the same object. -/
def readAliases : OracleComp (aliases.asSource catalog).spec (Nat × Nat) := do
  let x : Nat ← liftM ((aliases.asSource catalog).spec.query ⟨false, false⟩)
  let y : Nat ← liftM ((aliases.asSource catalog).spec.query ⟨true, false⟩)
  return (x, y)

example : (aliases.asSource catalog).eval (fun _ => smallObject) readAliases = (2, 2) :=
  rfl

example : aliases.key false = aliases.key true := rfl
example : (false : aliases.Handle) ≠ true := by decide

/-- The guarantee is about the actual object observed through an alias. -/
example (env : (x : left.Slot) → Fin (if left.key x then 5 else 3)) :
    (env (aliases.resolve true)).val < 3 :=
  aliases.asSource_guarantee catalog env true ⟨3, rfl⟩

/-- The same descriptor language can express a false promise; it is not automatically granted. -/
example : ¬ catalog.meaning false 0 (⟨0, by decide⟩ : Fin 3) := by
  change ¬ (0 < (0 : Nat))
  decide

/-- A client cannot strengthen the real three-valued resource to the impossible bound zero. -/
example (h : ∀ obj : Fin 3, catalog.meaning false 0 obj) : False := by
  have hzero := h ⟨0, by decide⟩
  exact (Nat.not_lt_zero 0) hzero

/-- Zero objects give equal answers without erasing the resources' distinct identities. -/
def zeroObject (r : Bool) : Fin (if r then 5 else 3) :=
  ⟨0, by cases r <;> decide⟩

example : (catalog.source false).handler (zeroObject false) =
    (catalog.source true).handler (zeroObject true) := rfl

example : left.key ⟨⟩ ≠ right.key ⟨⟩ := by decide
example : catalog.owner false ≠ catalog.owner true := by decide

/-- Equal signatures, even with equal realized answers, do not create an identity-preserving map. -/
example : ¬ Nonempty (SchemaHom left right) := by
  rintro ⟨f⟩
  have h := f.key_eq PUnit.unit
  change true = false at h
  cases h

/-- Allocate all two identities, under their own names. -/
def both : ResourceSchema Bool where
  Slot := Bool
  key := ⟨fun x => x, fun _ _ h => h⟩

/-- A genuinely nontrivial injective renaming. -/
def flip : Bool ↪ Bool where
  toFun := Bool.not
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

/-- The renamed false slot now denotes the five-valued resource. -/
def renamed := both.reindex flip

/-- Actual resource-preserving routing, with dependent object transport. -/
def inclusion := SchemaHom.fromReindex both flip

/-- Distinct objects selected by stable identity. -/
def bothEnv : (r : Bool) → Fin (if r then 5 else 3)
  | false => smallObject
  | true => largeObject

example : (inclusion.toSourceHom catalog).onEnv bothEnv false =
    (largeObject : Fin 5) := rfl

/-- Read in handle order, which is different from the original allocation order. -/
def readRenamed : OracleComp (renamed.asSource catalog).spec (Nat × Nat) := do
  let x : Nat ← liftM ((renamed.asSource catalog).spec.query ⟨false, false⟩)
  let y : Nat ← liftM ((renamed.asSource catalog).spec.query ⟨true, true⟩)
  return (x, y)

example : (both.asSource catalog).eval bothEnv
    ((inclusion.toSourceHom catalog).mapProgram readRenamed) = (4, 3) := rfl

/-- No unused catalog entry needs to be inhabited to realize an empty allocation. -/
example : (x : (ResourceSchema.empty : ResourceSchema.{0, 0} Bool).Slot) →
    Fin (if (ResourceSchema.empty : ResourceSchema.{0, 0} Bool).key x then 5 else 3) :=
  fun x => PEmpty.elim x

/-- Tensor forgetting routes both resources to their matching product environments. -/
example : ((left.asSource catalog).tensor (right.asSource catalog)).eval
    ((fun _ => smallObject), (fun _ => largeObject))
    ((ResourceSchema.tensorSourceEquiv left right separate catalog).toHom.mapProgram readPair) =
      (3, 4) := rfl

/-- Combining views of one allocation is sharing, not a second allocation. -/
def shared := (ResourceView.full left).share aliases

/-- Different handles and primitive queries still use exactly one backing object. -/
def readShared : OracleComp (shared.asSource catalog).spec (Nat × Nat) := do
  let x : Nat ← liftM ((shared.asSource catalog).spec.query ⟨.inl ⟨⟩, true⟩)
  let y : Nat ← liftM ((shared.asSource catalog).spec.query ⟨.inr true, false⟩)
  return (x, y)

example : (left.asSource catalog).eval (fun _ => smallObject)
    ((shared.toSourceHom catalog).mapProgram readShared) = (3, 2) := rfl

/-- Both the primitive-query and response types vary with resource identity. -/
def mixedCatalog : ResourceCatalog Bool (fun r => if r then Fin 2 else Bool)
    (fun r => Fin (if r then 5 else 3)) Nat Nat (fun _ => Nat) where
  source := fun r => match r with
    | false =>
      { spec := Bool →ₒ Nat
        impl := fun _ (obj : Fin 3) => obj.val }
    | true =>
      { spec := Fin 2 →ₒ Bool
        impl := fun (query : Fin 2) (obj : Fin 5) => decide (query.val < obj.val) }
  owner := fun _ => 0
  origin := fun _ => 7
  meaning := fun _ bound obj => obj.val < bound
  required := fun r bound => bound = if r then 5 else 3
  valid := by
    intro r bound h obj
    subst bound
    exact obj.isLt

/-- After renaming, the false handle has a `Fin 2` query and a `Bool` response. -/
def readMixed : OracleComp (renamed.asSource mixedCatalog).spec (Bool × Nat) := do
  let bit : Bool ← liftM ((renamed.asSource mixedCatalog).spec.query
    ⟨false, (⟨1, by decide⟩ : Fin 2)⟩)
  let value : Nat ← liftM ((renamed.asSource mixedCatalog).spec.query ⟨true, false⟩)
  return (bit, value)

example : (both.asSource mixedCatalog).eval bothEnv
    ((inclusion.toSourceHom mixedCatalog).mapProgram readMixed) = (true, 2) := rfl

/-- A reified degree promise is witnessed by the actual polynomial used for evaluation.

The polynomial stays in the backing environment; the query interface only exposes evaluation.
This client uses Mathlib's refined mathematical objects, not an arbitrary function tagged as
low-degree. -/
noncomputable def polynomialCatalog : ResourceCatalog Unit (fun _ => Nat)
    (fun _ => {p : Polynomial Nat // p.natDegree < 2}) Unit Nat (fun _ => Nat) where
  source := fun _ =>
    { spec := Nat →ₒ Nat
      impl := fun query (obj : {p : Polynomial Nat // p.natDegree < 2}) => obj.val.eval query }
  owner := fun _ => ()
  origin := fun _ => 7
  meaning := fun _ bound obj => obj.val.natDegree < bound
  required := fun _ bound => bound = 2
  valid := by
    intro _ bound h obj
    subst bound
    exact obj.property

/-- A nonconstant polynomial whose refined type certifies its advertised degree bound. -/
noncomputable def linearObject : {p : Polynomial Nat // p.natDegree < 2} :=
  ⟨Polynomial.X, by simp⟩

example : (polynomialCatalog.source ()).handler linearObject 3 = (3 : Nat) := by
  change (Polynomial.X : Polynomial Nat).eval 3 = 3
  simp

example : (polynomialCatalog.source ()).handler linearObject 7 = (7 : Nat) := by
  change (Polynomial.X : Polynomial Nat).eval 7 = 7
  simp

example : polynomialCatalog.meaning () 2 linearObject :=
  polynomialCatalog.realizes () ⟨2, rfl⟩ linearObject

/-- The descriptor zero cannot be substituted for the actual degree promise. -/
example : ¬ polynomialCatalog.meaning () 0 linearObject := by
  change ¬ (Polynomial.X : Polynomial Nat).natDegree < 0
  exact Nat.not_lt_zero _

example : ¬ polynomialCatalog.required () 0 := by
  change ¬ (0 = 2)
  decide

section Universes

variable {Id : Type i} {Query : Id → Type q} {Object : Id → Type a}
  {Owner : Type o} {Origin : Type p} {Descriptor : Id → Type d}

example (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor)
    (S : ResourceSchema.{i, s} Id) :
    SourceCtx.{max s q, e, max s a}
      ((x : S.Slot) × Query (S.key x)) ((x : S.Slot) → Object (S.key x)) :=
  S.asSource C

example (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor)
    (S : ResourceSchema.{i, s} Id) (view : ResourceView.{i, s, h} S) :
    SourceCtx.{max h q, e, max s a}
      ((x : view.Handle) × Query (view.key x)) ((x : S.Slot) → Object (S.key x)) :=
  view.asSource C

end Universes

end Interaction.Oracle.ResourceExample
