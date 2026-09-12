/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Resource
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Named-context acceptance clients

These clients distinguish oracle names from answer equality, test aliased views against disjoint
contexts, and connect a reified property to the refined realization interpreting each query. The
reindexing client changes both an oracle name and its dependent realization type.
-/

universe i q a e o p d s h

namespace Interaction.Oracle.ResourceExample

/-- Equal query interfaces can have different names and differently bounded realizations. -/
def model : OracleModel Bool (fun _ => Bool) (fun r => Fin (if r then 5 else 3))
    Nat (Bool × Nat) (fun _ => Nat) where
  source := fun r =>
    { spec := Bool →ₒ Nat
      impl := fun (query : Bool) (obj : Fin (if r then 5 else 3)) =>
        (obj.val + (if query then 1 else 0) : Nat) }
  owner := fun r => if r then 20 else 10
  origin := fun r => (r, 7)
  satisfies := fun _ bound obj => obj.val < bound
  promised := fun r bound => bound = if r then 5 else 3
  satisfies_promises := by
    intro r bound h obj
    subst bound
    exact obj.isLt

/-- An oracle name may have an empty property-symbol language.

The `false` name promises a unit guarantee; constructing the model does not require manufacturing
a property symbol for the `true` name. -/
def sparseModel : OracleModel Bool (fun _ => PUnit) (fun _ => PUnit)
    PUnit PUnit (fun r => if r then PEmpty else PUnit) where
  source := fun _ =>
    { spec := PUnit →ₒ PUnit
      impl := fun _ _ => PUnit.unit }
  owner := fun _ => PUnit.unit
  origin := fun _ => PUnit.unit
  satisfies := fun _ _ _ => True
  promised := fun _ _ => True
  satisfies_promises := fun _ _ _ _ => True.intro

example : sparseModel.Guarantee false := ⟨PUnit.unit, True.intro⟩

example (guarantee : sparseModel.Guarantee true) : False :=
  PEmpty.elim guarantee.val

/-- The first named context has a three-valued realization type. -/
def left := NamedContext.single false

/-- The second named context has a five-valued realization type. -/
def right := NamedContext.single true

/-- These contexts have disjoint names, independently of their answers. -/
theorem separate : left.Disjoint right := by
  intro x y
  change false ≠ true
  decide

/-- The disjoint union of the two named contexts. -/
def pair := left.disjointUnion right separate

/-- A concrete realization in the three-valued type. -/
def smallRealization : Fin 3 := ⟨2, by decide⟩

/-- A concrete realization in the five-valued type. -/
def largeRealization : Fin 5 := ⟨4, by decide⟩

/-- The two names have distinct dependent realization types. -/
def pairEnv : (x : pair.Index) → Fin (if pair.name x then 5 else 3)
  | .inl _ => smallRealization
  | .inr _ => largeRealization

/-- Query both sides, distinguishing the oracle name and primitive-query routing. -/
def readPair : OracleComp (pair.asSource model).spec (Nat × Nat) := do
  let x : Nat ← liftM ((pair.asSource model).spec.query ⟨.inl ⟨⟩, true⟩)
  let y : Nat ← liftM ((pair.asSource model).spec.query ⟨.inr ⟨⟩, false⟩)
  return (x, y)

example : (pair.asSource model).eval pairEnv readPair = (3, 4) := rfl

example : ¬ left.Disjoint left := left.not_disjoint_self ⟨⟩

/-- Two view indices reference the same named-context index and realization. -/
def aliases : NamedContext.View left :=
  (NamedContext.View.full left).reindex (fun _ : Bool => PUnit.unit)

/-- Both view indices issue their primitive query against the same realization. -/
def readAliases : OracleComp (aliases.asSource model).spec (Nat × Nat) := do
  let x : Nat ← liftM ((aliases.asSource model).spec.query ⟨false, false⟩)
  let y : Nat ← liftM ((aliases.asSource model).spec.query ⟨true, false⟩)
  return (x, y)

example : (aliases.asSource model).eval (fun _ => smallRealization) readAliases = (2, 2) :=
  rfl

example : aliases.name false = aliases.name true := rfl
example : (false : aliases.Index) ≠ true := by decide

/-- The guarantee applies to the realization referenced through an alias. -/
example (env : (x : left.Index) → Fin (if left.name x then 5 else 3)) :
    (env (aliases.toIndex true)).val < 3 :=
  aliases.asSource_guarantee model env true ⟨3, rfl⟩

/-- The same property-symbol language can express a false property that is not promised. -/
example : ¬ model.satisfies false 0 (⟨0, by decide⟩ : Fin 3) := by
  change ¬ (0 < (0 : Nat))
  decide

/-- A client cannot strengthen the three-valued realization to the impossible bound zero. -/
example (h : ∀ obj : Fin 3, model.satisfies false 0 obj) : False := by
  have hzero := h ⟨0, by decide⟩
  exact (Nat.not_lt_zero 0) hzero

/-- Zero realizations give equal answers without erasing the distinct oracle names. -/
def zeroRealization (r : Bool) : Fin (if r then 5 else 3) :=
  ⟨0, by cases r <;> decide⟩

example : (model.source false).handler (zeroRealization false) =
    (model.source true).handler (zeroRealization true) := rfl

example : left.name ⟨⟩ ≠ right.name ⟨⟩ := by decide
example : model.owner false ≠ model.owner true := by decide

/-- Equal signatures and answers do not create a name-preserving inclusion. -/
example : ¬ Nonempty (NamedContext.Inclusion left right) := by
  rintro ⟨f⟩
  have h := f.name_eq PUnit.unit
  change true = false at h
  cases h

/-- The named context containing both oracle names. -/
def both : NamedContext Bool where
  Index := Bool
  name := ⟨fun x => x, fun _ _ h => h⟩

/-- A genuinely nontrivial injective renaming. -/
def flip : Bool ↪ Bool where
  toFun := Bool.not
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

/-- The reindexed `false` index now denotes the five-valued oracle name. -/
def renamed := both.reindex flip

/-- Name-preserving inclusion with dependent realization transport. -/
def inclusion := NamedContext.Inclusion.fromReindex both flip

/-- Distinct realizations selected by oracle name. -/
def bothEnv : (r : Bool) → Fin (if r then 5 else 3)
  | false => smallRealization
  | true => largeRealization

example : (inclusion.toSourceHom model).pullEnv bothEnv false =
    (largeRealization : Fin 5) := rfl

/-- Read in the reindexed order, which differs from the original context order. -/
def readRenamed : OracleComp (renamed.asSource model).spec (Nat × Nat) := do
  let x : Nat ← liftM ((renamed.asSource model).spec.query ⟨false, false⟩)
  let y : Nat ← liftM ((renamed.asSource model).spec.query ⟨true, true⟩)
  return (x, y)

example : (both.asSource model).eval bothEnv
    ((inclusion.toSourceHom model).mapProgram readRenamed) = (4, 3) := rfl

/-- Interpreting an empty named context requires no realization of an unused model entry. -/
example : (x : (NamedContext.empty : NamedContext.{0, 0} Bool).Index) →
    Fin (if (NamedContext.empty : NamedContext.{0, 0} Bool).name x then 5 else 3) :=
  fun x => PEmpty.elim x

/-- A disjoint union of contexts corresponds to the sum of their interpreted sources. -/
example : ((left.asSource model).sum (right.asSource model)).eval
    ((fun _ => smallRealization), (fun _ => largeRealization))
    ((NamedContext.disjointUnionSourceEquiv left right separate model).toHom.mapProgram readPair) =
      (3, 4) := rfl

/-- Combining two views shares their one underlying named context. -/
def shared := (NamedContext.View.full left).share aliases

/-- Different view indices and primitive queries still use one realization. -/
def readShared : OracleComp (shared.asSource model).spec (Nat × Nat) := do
  let x : Nat ← liftM ((shared.asSource model).spec.query ⟨.inl ⟨⟩, true⟩)
  let y : Nat ← liftM ((shared.asSource model).spec.query ⟨.inr true, false⟩)
  return (x, y)

example : (left.asSource model).eval (fun _ => smallRealization)
    ((shared.toSourceHom model).mapProgram readShared) = (3, 2) := rfl

/-- Both the primitive-query and response types vary with the oracle name. -/
def mixedModel : OracleModel Bool (fun r => if r then Fin 2 else Bool)
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
  satisfies := fun _ bound obj => obj.val < bound
  promised := fun r bound => bound = if r then 5 else 3
  satisfies_promises := by
    intro r bound h obj
    subst bound
    exact obj.isLt

/-- After reindexing, the `false` context index has a `Fin 2` query and a `Bool` response. -/
def readMixed : OracleComp (renamed.asSource mixedModel).spec (Bool × Nat) := do
  let bit : Bool ← liftM ((renamed.asSource mixedModel).spec.query
    ⟨false, (⟨1, by decide⟩ : Fin 2)⟩)
  let value : Nat ← liftM ((renamed.asSource mixedModel).spec.query ⟨true, false⟩)
  return (bit, value)

example : (both.asSource mixedModel).eval bothEnv
    ((inclusion.toSourceHom mixedModel).mapProgram readMixed) = (true, 2) := rfl

/-- A reified degree promise is witnessed by the actual polynomial used for evaluation.

The polynomial stays in the realization family; the query interface only exposes evaluation.
This client uses Mathlib's refined polynomial type rather than an arbitrary function tagged as
low degree. -/
noncomputable def polynomialModel : OracleModel Unit (fun _ => Nat)
    (fun _ => {p : Polynomial Nat // p.natDegree < 2}) Unit Nat (fun _ => Nat) where
  source := fun _ =>
    { spec := Nat →ₒ Nat
      impl := fun query (obj : {p : Polynomial Nat // p.natDegree < 2}) => obj.val.eval query }
  owner := fun _ => ()
  origin := fun _ => 7
  satisfies := fun _ bound obj => obj.val.natDegree < bound
  promised := fun _ bound => bound = 2
  satisfies_promises := by
    intro _ bound h obj
    subst bound
    exact obj.property

/-- A nonconstant polynomial whose refined type certifies its advertised degree bound. -/
noncomputable def linearRealization : {p : Polynomial Nat // p.natDegree < 2} :=
  ⟨Polynomial.X, by simp⟩

example : (polynomialModel.source ()).handler linearRealization 3 = (3 : Nat) := by
  change (Polynomial.X : Polynomial Nat).eval 3 = 3
  simp

example : (polynomialModel.source ()).handler linearRealization 7 = (7 : Nat) := by
  change (Polynomial.X : Polynomial Nat).eval 7 = 7
  simp

example : polynomialModel.satisfies () 2 linearRealization :=
  polynomialModel.satisfies_guarantee () ⟨2, rfl⟩ linearRealization

/-- The property symbol zero cannot be substituted for the promised degree bound. -/
example : ¬ polynomialModel.satisfies () 0 linearRealization := by
  change ¬ (Polynomial.X : Polynomial Nat).natDegree < 0
  exact Nat.not_lt_zero _

example : ¬ polynomialModel.promised () 0 := by
  change ¬ (0 = 2)
  decide

section Universes

variable {Id : Type i} {Query : Id → Type q} {Realization : Id → Type a}
  {Owner : Type o} {Origin : Type p} {PropertySymbol : Id → Type d}

example (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol)
    (S : NamedContext.{i, s} Id) :
    SourceCtx.{max s q, e, max s a}
      ((x : S.Index) × Query (S.name x)) ((x : S.Index) → Realization (S.name x)) :=
  S.asSource C

example (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol)
    (S : NamedContext.{i, s} Id) (view : NamedContext.View.{i, s, h} S) :
    SourceCtx.{max h q, e, max s a}
      ((x : view.Index) × Query (view.name x)) ((x : S.Index) → Realization (S.name x)) :=
  view.asSource C

end Universes

end Interaction.Oracle.ResourceExample
