/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Relation.Basic
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import PolyFun.PFunctor.Basic

/-!
# Oracle bundles and oracle maps

An `OracleBundle` pairs a query specification with concrete data that answers it. An `OracleMap`
between two bundles maps the data of the first to the data of the second, and simulates each query
of the second bundle by queries to the first, so that both agree on every input.

This file defines the bundle constructors (`of`, `ofInst`, `empty`, `sum`, `tensor`, `ofSpec`,
`indexed`, `ofIndexed`), the bundle of an `OracleFamily`, and the oracle maps that compose,
project, regroup and rename bundles. None of them depends on a protocol tree or on execution.

The combinators `of`, `ofInst`, `empty`, `sum`, `tensor`, `indexed` and `ofIndexed` are
`@[reducible]`, so a bundle built from them unfolds to its four fields during unification and
instance search.
-/

@[expose] public section

namespace Interaction
open OracleComp Oracle

/-- A query specification and the concrete data that answers it, all in `Type`.

For fixed `Query` and `Data`, the specification and answer function are equivalent to VCVio's
`OracleContext Query (fun α => Data → α)`. -/
structure OracleBundle : Type 1 where
  /-- The query type. -/
  Query : Type
  /-- The queries and their response types. -/
  spec : OracleSpec.{0, 0} Query
  /-- The concrete data. -/
  Data : Type
  /-- How concrete data answers each query. -/
  answer : Data → QueryImpl spec Id

namespace OracleBundle

/-- Arbitrary deterministic answers to the queries of a bundle, without a representability
assumption. -/
abbrev Behavior (B : OracleBundle) : Type := QueryImpl B.spec Id

/-- The query interface of a bundle as an `OracleInterface` on its data.

This is not an instance: a global instance concluding `OracleInterface ?B.Data` would make
instance search try every bundle whose data type unifies with the goal. -/
@[reducible]
def toInterface (B : OracleBundle) : OracleInterface B.Data where
  Query := B.Query
  spec := B.spec
  answer := B.answer

/-- Package a data type and an explicit interface for it as an oracle bundle. -/
@[reducible]
def of (Data : Type) (I : OracleInterface.{0, 0} Data) : OracleBundle where
  Query := I.Query
  spec := I.spec
  Data := Data
  answer := I.answer

/-- Package a data type with the interface that instance search finds for it. -/
@[reducible]
def ofInst (Data : Type) [I : OracleInterface Data] : OracleBundle := of Data I

/-- The empty bundle: no queries, and `Unit` data. -/
@[reducible]
def empty : OracleBundle where
  Query := Empty
  spec := fun q => q.elim
  Data := Unit
  answer _ q := q.elim

/-- A sum bundle: each query goes to one side and is answered from that side's data.
Their data stays a pair. -/
@[reducible] def sum (R : OracleBundle) (R' : OracleBundle) :
    OracleBundle where
  Query := R.Query ⊕ R'.Query
  spec := R.spec + R'.spec
  Data := R.Data × R'.Data
  answer x := R.answer x.1 + R'.answer x.2

/-- Pair queries, answers and backing data. -/
@[reducible]
def tensor (R : OracleBundle) (S : OracleBundle) :
    OracleBundle where
  Query := R.Query × S.Query
  spec := OracleSpec.ofPFunctor (PFunctor.tensor R.spec.toPFunctor S.spec.toPFunctor)
  Data := R.Data × S.Data
  answer data query := (R.answer data.1 query.1, S.answer data.2 query.2)

/-- A tensor query returns the pair of answers from its two backing data components. -/
@[simp]
theorem tensor_answer (R : OracleBundle) (S : OracleBundle)
    (data : R.Data × S.Data) (query : R.Query × S.Query) :
    (R.tensor S).answer data query = (R.answer data.1 query.1, S.answer data.2 query.2) := rfl

/-- Realize a specification by any pure handler, without a representability requirement. -/
def ofSpec {I : Type} (spec : OracleSpec.{0, 0} I) :
    OracleBundle where
  Query := I
  spec := spec
  Data := QueryImpl spec Id
  answer data := data

/-- Combine an indexed collection of bundles into one bundle. A query names an index and a query
of the bundle at that index. The data is a dependent function giving each bundle's data. -/
@[reducible]
def indexed {I : Type} (F : I → OracleBundle) : OracleBundle where
  Query := (i : I) × (F i).Query
  spec := fun q => (F q.1).spec q.2
  Data := ∀ i, (F i).Data
  answer data q := (F q.1).answer (data q.1) q.2

/-- The indexed bundle of a type family with an explicit interface at each index. -/
@[reducible]
def ofIndexed {I : Type} (A : I → Type) (O : ∀ i, OracleInterface (A i)) :
    OracleBundle :=
  indexed fun i => of (A i) (O i)

end OracleBundle

/-- The oracle bundle of an oracle family: queries through its interfaces, answered from concrete
realizations in `Type`.
-/
@[reducible] def OracleBundle.ofFamily {I : Type} {A : I → Type}
    (F : OracleFamily.{0, 0, 0} I A) : OracleBundle where
  Query := (i : I) × (F.interface i).Query
  spec := F.spec
  Data := ∀ i, A i
  answer := F.behaviorOfRealizations

attribute [coe] OracleBundle.ofFamily

/-- An oracle family is used as an oracle bundle through its interfaces. -/
instance {I : Type} {A : I → Type} :
    CoeOut (OracleFamily.{0, 0, 0} I A) OracleBundle :=
  ⟨OracleBundle.ofFamily⟩

/-- A concrete oracle map and its query-by-query implementation agree on all input data. -/
structure OracleMap (In : OracleBundle) (Out : OracleBundle) where
  /-- Concrete output data, available to a subsequent honest prover. -/
  f : In.Data → Out.Data
  /-- Output queries are simulated using only input oracle queries. -/
  impl : QueryImpl Out.spec (OracleComp In.spec)
  /-- Simulation answers exactly as the materialized output data. -/
  law : ∀ x q, simulateQ (In.answer x) (impl q) = Out.answer (f x) q

namespace OracleMap

section OracleBundle
variable {In : OracleBundle} {Mid : OracleBundle}
  {Out : OracleBundle} {Other : OracleBundle}

/-- Compose concrete data maps and substitute query implementations. -/
def comp (g : OracleMap Mid Out) (h : OracleMap In Mid) : OracleMap In Out where
  f := g.f ∘ h.f
  impl := QueryImpl.compose h.impl g.impl
  law x q := by
    rw [QueryImpl.apply_compose, ← QueryImpl.simulateQ_compose]
    have he : QueryImpl.compose (In.answer x) h.impl = Mid.answer (h.f x) := funext (h.law x)
    rw [he]
    exact g.law (h.f x) q

/-- Routing every query through a map agrees with materializing its output first. -/
theorem simulate_eq (h : OracleMap In Out) (x : In.Data)
    {α : Type} (program : OracleComp Out.spec α) :
    simulateQ (In.answer x) (simulateQ h.impl program) =
      simulateQ (Out.answer (h.f x)) program :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (h.law x) program

/-- The identity map of an oracle bundle. -/
def id (R : OracleBundle) : OracleMap R R where
  f x := x
  impl q := liftM (R.spec.query q)
  law _ _ := rfl

/-- Keep the left side of a sum bundle. Inlining erases the unused bundle interpreters when a
computable verifier specializes this projection to a mathematical oracle family. -/
@[macro_inline]
def fst (R : OracleBundle) (R' : OracleBundle) :
    OracleMap (R.sum R') R where
  f x := x.1
  impl q := liftM ((R.spec + R'.spec).query (.inl q))
  law _ _ := rfl

/-- Keep the right side of a sum bundle. -/
def snd (R : OracleBundle) (R' : OracleBundle) :
    OracleMap (R.sum R') R' where
  f x := x.2
  impl q := liftM ((R.spec + R'.spec).query (.inr q))
  law _ _ := rfl

/-- Add the empty bundle on the left of a bundle. The map pairs the data with `()` and forwards
every query of the right side unchanged. -/
def emptyLeft (R : OracleBundle) : OracleMap R (OracleBundle.empty.sum R) where
  f x := ((), x)
  impl
    | .inl e => e.elim
    | .inr q => liftM (R.spec.query q)
  law _ q := by
    rcases q with e | q
    · exact e.elim
    · rfl

/-- Apply two oracle maps to the two sides of a sum bundle. -/
def par (h : OracleMap In Mid) (g : OracleMap Out Other) :
    OracleMap (In.sum Out) (Mid.sum Other) where
  f x := (h.f x.1, g.f x.2)
  impl
    | .inl q => simulateQ (fst In Out).impl (h.impl q)
    | .inr q => simulateQ (snd In Out).impl (g.impl q)
  law x q := by
    cases q with
    | inl q =>
      exact (QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := In.answer x.1)
        (fun _ => rfl) (h.impl q)).trans (h.law _ _)
    | inr q =>
      exact (QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := Out.answer x.2)
        (fun _ => rfl) (g.impl q)).trans (g.law _ _)

/-- Regroup a sum bundle to the left without changing its data or answers. -/
def sumAssocSymm (R₁ : OracleBundle) (R₂ : OracleBundle)
    (R₃ : OracleBundle) : OracleMap (R₁.sum (R₂.sum R₃)) ((R₁.sum R₂).sum R₃) where
  f x := ((x.1, x.2.1), x.2.2)
  impl
    | .inl (.inl q) => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inl q))
    | .inl (.inr q) => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inr (.inl q)))
    | .inr q => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inr (.inr q)))
  law x q := by rcases q with (q | q) | q <;> rfl

/-- Regroup a sum bundle to the right without changing its data or answers. -/
def sumAssoc (R₁ : OracleBundle) (R₂ : OracleBundle)
    (R₃ : OracleBundle) : OracleMap ((R₁.sum R₂).sum R₃) (R₁.sum (R₂.sum R₃)) where
  f x := (x.1.1, (x.1.2, x.2))
  impl
    | .inl q => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inl (.inl q)))
    | .inr (.inl q) => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inl (.inr q)))
    | .inr (.inr q) => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inr q))
  law x q := by rcases q with q | (q | q) <;> rfl

/-- Retain, project or alias the slots of an indexed bundle. Output slot `j` reads input slot
`rename j`, so a non-injective `rename` gives several output slots the same data. -/
def reindex {I J : Type} (F : I → OracleBundle) (rename : J → I) :
    OracleMap (OracleBundle.indexed F) (OracleBundle.indexed (F ∘ rename)) where
  f x j := x (rename j)
  impl q := liftM ((OracleBundle.indexed F).spec.query ⟨rename q.1, q.2⟩)
  law _ _ := rfl

/-- A query program defines output behavior by interpreting it in the supplied bundle. -/
def ofImpl (R : OracleBundle) {J : Type}
    (spec : OracleSpec.{0, 0} J) (query : QueryImpl spec (OracleComp R.spec)) :
    OracleMap R (OracleBundle.ofSpec spec) where
  f data q := simulateQ (R.answer data) (query q)
  impl := query
  law _ _ := rfl

end OracleBundle

section Families
variable {I : Type} {J : Type} {A : I → Type}

/-- Embeddings are oracle maps that retain or rename existing input slots. -/
def embedding (In : OracleFamily.{0, 0, 0} I A) (rename : J → I) :
    OracleMap In (In.reindex rename) where
  f x j := x (rename j)
  impl q := liftM (In.spec.query ⟨rename q.1, q.2⟩)
  law _ _ := rfl

end Families

end OracleMap

end Interaction
