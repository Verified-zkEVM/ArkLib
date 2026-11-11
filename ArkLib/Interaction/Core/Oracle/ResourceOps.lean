/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.OracleVerifier
public import PolyFun.PFunctor.Lens.Basic

/-!
# Tensor products and response lifting of oracle resources

A tensor query asks both component queries and receives both answers. Its query, response and
backing-data universes are independent. Response lifting changes only the response carrier.

Raw resource maps use polynomial lenses and coherent maps of backing data. Their response
universes may differ: these maps pull back pure answers without interpreting an oracle program.
Response lifting has inverse raw maps that preserve every query, answer and backing datum.
-/

@[expose] public section

universe v u w v' u' w' v'' u'' w''

namespace Interaction.Core

/-- Pair queries, answers and backing data, keeping both components' universes independent. -/
def Resources.tensor (R : Resources.{v, u, w}) (S : Resources.{v', u', w'}) :
    Resources.{max v v', max u u', max w w'} where
  Index := R.Index × S.Index
  spec := OracleSpec.ofPFunctor (PFunctor.tensor R.spec.toPFunctor S.spec.toPFunctor)
  Data := R.Data × S.Data
  answer data query := (R.answer data.1 query.1, S.answer data.2 query.2)

/-- A tensor query returns the pair of answers from its two backing data components. -/
@[simp]
theorem Resources.tensor_answer (R : Resources.{v, u, w}) (S : Resources.{v', u', w'})
    (data : R.Data × S.Data) (query : R.Index × S.Index) :
    (R.tensor S).answer data query = (R.answer data.1 query.1, S.answer data.2 query.2) := rfl

/-- Lift response types while preserving the query carrier and the backing data. -/
def Resources.liftResponse (R : Resources.{v, u, w}) : Resources.{max v v', u, w} where
  Index := R.Index
  spec query := ULift.{v'} (R.spec query)
  Data := R.Data
  answer data query := ⟨R.answer data query⟩

/-- A lifted answer contains exactly the original answer. -/
@[simp]
theorem Resources.liftResponse_answer (R : Resources.{v, u, w})
    (data : R.Data) (query : R.Index) :
    (R.liftResponse.{v, u, w, v'}).answer data query = ULift.up (R.answer data query) := rfl

/-- A pure query route whose backward data map realizes the backward response map. -/
structure ResourceHom (R : Resources.{v, u, w}) (S : Resources.{v', u', w'}) where
  /-- Send queries forward and pull their responses back through a polynomial lens. -/
  route : PFunctor.Lens R.spec.toPFunctor S.spec.toPFunctor
  /-- Recover source backing data from target backing data. -/
  pullData : S.Data → R.Data
  /-- Routing an interpreted answer agrees with interpreting the recovered data. -/
  commutes : ∀ data query,
    R.answer (pullData data) query = route.toFunB query (S.answer data (route.toFunA query))

namespace ResourceHom

variable {R : Resources.{v, u, w}} {S : Resources.{v', u', w'}}
    {T : Resources.{v'', u'', w''}}

/-- Pull back arbitrary pure answers, including answers not represented by backing data. -/
def pull (f : ResourceHom R S) (answer : QueryImpl S.spec Id) : QueryImpl R.spec Id :=
  fun query => f.route.toFunB query (answer (f.route.toFunA query))

/-- Identity routing preserves queries, responses and backing data. -/
def id (R : Resources.{v, u, w}) : ResourceHom R R where
  route := PFunctor.Lens.id R.spec.toPFunctor
  pullData data := data
  commutes _ _ := rfl

/-- Compose query routes forward and backing-data maps backward. -/
def comp (g : ResourceHom S T) (f : ResourceHom R S) : ResourceHom R T where
  route := PFunctor.Lens.comp g.route f.route
  pullData := f.pullData ∘ g.pullData
  commutes data query := by
    change R.answer (f.pullData (g.pullData data)) query =
      f.route.toFunB query
        (g.route.toFunB (f.route.toFunA query)
          (T.answer data (g.route.toFunA (f.route.toFunA query))))
    rw [f.commutes, g.commutes]

/-- Pulling answers along the identity route preserves them. -/
@[simp]
theorem pull_id (answer : QueryImpl R.spec Id) : (id R).pull answer = answer := rfl

/-- Pulling answers through a composite is successive pullback through its two routes. -/
theorem pull_comp (g : ResourceHom S T) (f : ResourceHom R S)
    (answer : QueryImpl T.spec Id) : (g.comp f).pull answer = f.pull (g.pull answer) := rfl

/-- Pulling interpreted answers agrees with interpreting the pulled backing data. -/
@[simp]
theorem pull_answer (f : ResourceHom R S) (data : S.Data) :
    f.pull (S.answer data) = R.answer (f.pullData data) := by
  funext query
  exact (f.commutes data query).symm

/-- Route into lifted responses, unwrapping each answer and preserving the backing data. -/
def toLiftResponse (R : Resources.{v, u, w}) :
    ResourceHom R (R.liftResponse.{v, u, w, v'}) where
  route := ⟨fun query => query, fun _ answer => answer.down⟩
  pullData data := data
  commutes _ _ := rfl

/-- Route out of lifted responses, wrapping each answer and preserving the backing data. -/
def fromLiftResponse (R : Resources.{v, u, w}) :
    ResourceHom (R.liftResponse.{v, u, w, v'}) R where
  route := ⟨fun query => query, fun _ answer => ⟨answer⟩⟩
  pullData data := data
  commutes _ _ := rfl

end ResourceHom

/-- Inverse coherent routes preserve both polynomial query behavior and backing data. -/
structure ResourceEquiv (R : Resources.{v, u, w}) (S : Resources.{v', u', w'}) where
  /-- The forward raw resource map. -/
  toHom : ResourceHom R S
  /-- The inverse raw resource map. -/
  invHom : ResourceHom S R
  /-- The source round trip is the identity on routing and backing data. -/
  left_inv : invHom.comp toHom = ResourceHom.id R
  /-- The target round trip is the identity on routing and backing data. -/
  right_inv : toHom.comp invHom = ResourceHom.id S

namespace ResourceEquiv

variable {R : Resources.{v, u, w}} {S : Resources.{v', u', w'}}

/-- Pulling source answers through both inverse routes recovers the original answers. -/
@[simp]
theorem pull_inv (e : ResourceEquiv R S) (answer : QueryImpl R.spec Id) :
    e.toHom.pull (e.invHom.pull answer) = answer := by
  rw [← ResourceHom.pull_comp, e.left_inv, ResourceHom.pull_id]

/-- Pulling target answers through both inverse routes recovers the original answers. -/
@[simp]
theorem inv_pull (e : ResourceEquiv R S) (answer : QueryImpl S.spec Id) :
    e.invHom.pull (e.toHom.pull answer) = answer := by
  rw [← ResourceHom.pull_comp, e.right_inv, ResourceHom.pull_id]

/-- Response lifting is reversible on queries, responses and backing data. -/
def liftResponse (R : Resources.{v, u, w}) :
    ResourceEquiv R (R.liftResponse.{v, u, w, v'}) where
  toHom := ResourceHom.toLiftResponse R
  invHom := ResourceHom.fromLiftResponse R
  left_inv := rfl
  right_inv := rfl

end ResourceEquiv

end Interaction.Core
