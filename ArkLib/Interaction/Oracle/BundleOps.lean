/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.OracleVerifier
public import PolyFun.PFunctor.Lens.Basic

/-!
# Tensor products and response lifting of oracle bundles

A tensor query asks both component queries and receives both answers. Its query, response and
backing-data universes are independent. Response lifting changes only the response carrier.

A bundle lens pairs a polynomial lens with a coherent map of backing data. Its two bundles may
have different response universes: the lens pulls back pure answers without interpreting an
oracle program. Response lifting has inverse bundle lenses that preserve every query, answer and
backing datum.
-/

@[expose] public section

universe v u w v' u' w' v'' u'' w''

namespace Interaction

/-- Realize a specification by any pure handler, without a representability requirement. -/
def OracleBundle.ofSpec {I : Type u} (spec : OracleSpec.{u, v} I) :
    OracleBundle.{v, u, max u v} where
  Index := I
  spec := spec
  Data := QueryImpl spec Id
  answer data := data

/-- A query program defines output behavior by interpreting it in the supplied bundle. -/
def OracleMap.ofImpl (R : OracleBundle.{v, u, w}) {J : Type u'}
    (spec : OracleSpec.{u', v} J) (query : QueryImpl spec (OracleComp R.spec)) :
    OracleMap R (OracleBundle.ofSpec spec) where
  f data q := simulateQ (R.answer data) (query q)
  impl := query
  law _ _ := rfl

/-- Pair queries, answers and backing data, keeping both components' universes independent. -/
def OracleBundle.tensor (R : OracleBundle.{v, u, w}) (S : OracleBundle.{v', u', w'}) :
    OracleBundle.{max v v', max u u', max w w'} where
  Index := R.Index × S.Index
  spec := OracleSpec.ofPFunctor (PFunctor.tensor R.spec.toPFunctor S.spec.toPFunctor)
  Data := R.Data × S.Data
  answer data query := (R.answer data.1 query.1, S.answer data.2 query.2)

/-- A tensor query returns the pair of answers from its two backing data components. -/
@[simp]
theorem OracleBundle.tensor_answer (R : OracleBundle.{v, u, w}) (S : OracleBundle.{v', u', w'})
    (data : R.Data × S.Data) (query : R.Index × S.Index) :
    (R.tensor S).answer data query = (R.answer data.1 query.1, S.answer data.2 query.2) := rfl

/-- Lift response types while preserving the query carrier and the backing data. -/
def OracleBundle.liftResponse (R : OracleBundle.{v, u, w}) : OracleBundle.{max v v', u, w} where
  Index := R.Index
  spec query := ULift.{v'} (R.spec query)
  Data := R.Data
  answer data query := ⟨R.answer data query⟩

/-- A lifted answer contains exactly the original answer. -/
@[simp]
theorem OracleBundle.liftResponse_answer (R : OracleBundle.{v, u, w})
    (data : R.Data) (query : R.Index) :
    (R.liftResponse.{v, u, w, v'}).answer data query = ULift.up (R.answer data query) := rfl

/-- A pure query route whose backward data map realizes the backward response map. -/
structure OracleBundle.Lens (R : OracleBundle.{v, u, w}) (S : OracleBundle.{v', u', w'}) where
  /-- Send queries forward and pull their responses back through a polynomial lens. -/
  route : PFunctor.Lens R.spec.toPFunctor S.spec.toPFunctor
  /-- Recover source backing data from target backing data. -/
  pullData : S.Data → R.Data
  /-- Routing an interpreted answer agrees with interpreting the recovered data. -/
  commutes : ∀ data query,
    R.answer (pullData data) query = route.toFunB query (S.answer data (route.toFunA query))

namespace OracleBundle.Lens

variable {R : OracleBundle.{v, u, w}} {S : OracleBundle.{v', u', w'}}
    {T : OracleBundle.{v'', u'', w''}}

/-- Pull back arbitrary pure answers, including answers not represented by backing data. -/
def pullAnswer (f : OracleBundle.Lens R S) (answer : QueryImpl S.spec Id) : QueryImpl R.spec Id :=
  fun query => f.route.toFunB query (answer (f.route.toFunA query))

/-- Identity routing preserves queries, responses and backing data. -/
def id (R : OracleBundle.{v, u, w}) : OracleBundle.Lens R R where
  route := PFunctor.Lens.id R.spec.toPFunctor
  pullData data := data
  commutes _ _ := rfl

/-- Compose query routes forward and backing-data maps backward. -/
def comp (g : OracleBundle.Lens S T) (f : OracleBundle.Lens R S) : OracleBundle.Lens R T where
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
theorem pullAnswer_id (answer : QueryImpl R.spec Id) : (id R).pullAnswer answer = answer := rfl

/-- Pulling answers through a composite is successive pullback through its two routes. -/
theorem pullAnswer_comp (g : OracleBundle.Lens S T) (f : OracleBundle.Lens R S)
    (answer : QueryImpl T.spec Id) :
    (g.comp f).pullAnswer answer = f.pullAnswer (g.pullAnswer answer) := rfl

/-- Pulling interpreted answers agrees with interpreting the pulled backing data. -/
@[simp]
theorem pullAnswer_answer (f : OracleBundle.Lens R S) (data : S.Data) :
    f.pullAnswer (S.answer data) = R.answer (f.pullData data) := by
  funext query
  exact (f.commutes data query).symm

/-- Route into lifted responses, unwrapping each answer and preserving the backing data. -/
def toLiftResponse (R : OracleBundle.{v, u, w}) :
    OracleBundle.Lens R (R.liftResponse.{v, u, w, v'}) where
  route := ⟨fun query => query, fun _ answer => answer.down⟩
  pullData data := data
  commutes _ _ := rfl

/-- Route out of lifted responses, wrapping each answer and preserving the backing data. -/
def fromLiftResponse (R : OracleBundle.{v, u, w}) :
    OracleBundle.Lens (R.liftResponse.{v, u, w, v'}) R where
  route := ⟨fun query => query, fun _ answer => ⟨answer⟩⟩
  pullData data := data
  commutes _ _ := rfl

end OracleBundle.Lens

/-- Inverse coherent routes preserve both polynomial query behavior and backing data. -/
structure OracleBundle.Equiv (R : OracleBundle.{v, u, w}) (S : OracleBundle.{v', u', w'}) where
  /-- The forward bundle lens. -/
  toLens : OracleBundle.Lens R S
  /-- The inverse bundle lens. -/
  invLens : OracleBundle.Lens S R
  /-- The source round trip is the identity on routing and backing data. -/
  left_inv : invLens.comp toLens = OracleBundle.Lens.id R
  /-- The target round trip is the identity on routing and backing data. -/
  right_inv : toLens.comp invLens = OracleBundle.Lens.id S

namespace OracleBundle.Equiv

variable {R : OracleBundle.{v, u, w}} {S : OracleBundle.{v', u', w'}}

/-- Pulling source answers through both inverse routes recovers the original answers. -/
@[simp]
theorem pullAnswer_inv (e : OracleBundle.Equiv R S) (answer : QueryImpl R.spec Id) :
    e.toLens.pullAnswer (e.invLens.pullAnswer answer) = answer := by
  rw [← OracleBundle.Lens.pullAnswer_comp, e.left_inv, OracleBundle.Lens.pullAnswer_id]

/-- Pulling target answers through both inverse routes recovers the original answers. -/
@[simp]
theorem inv_pullAnswer (e : OracleBundle.Equiv R S) (answer : QueryImpl S.spec Id) :
    e.invLens.pullAnswer (e.toLens.pullAnswer answer) = answer := by
  rw [← OracleBundle.Lens.pullAnswer_comp, e.right_inv, OracleBundle.Lens.pullAnswer_id]

/-- Response lifting is reversible on queries, responses and backing data. -/
def liftResponse (R : OracleBundle.{v, u, w}) :
    OracleBundle.Equiv R (R.liftResponse.{v, u, w, v'}) where
  toLens := OracleBundle.Lens.toLiftResponse R
  invLens := OracleBundle.Lens.fromLiftResponse R
  left_inv := rfl
  right_inv := rfl

end OracleBundle.Equiv

end Interaction
