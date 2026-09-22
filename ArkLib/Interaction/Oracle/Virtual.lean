/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Source
public import ArkLib.OracleReduction.OracleInterface

/-!
# Virtual oracle programs

Virtual oracles are query implementations in the existing free oracle monad. Their meaning is
interpretation, with no separately stored denotation or coherence proof. Semantic equivalence
quantifies over every deterministic handler, not only handlers realized by selected backing data.
`OracleInterface` fixes responses to its realization universe; `OracleComp` further requires
source responses and output responses to share a universe. Query indices remain independent.
-/

@[expose] public section

universe u v w u' w' u'' w'' t a b

namespace Interaction.Oracle

/-- An indexed family of realization types with explicitly selected oracle interfaces. -/
structure OracleFamily (Index : Type u) (Realization : Index → Type v) where
  /-- Observable interface, supplied as data rather than inferred. -/
  interface : ∀ i, OracleInterface.{v, w} (Realization i)

namespace OracleFamily

variable {I : Type u} {Data : I → Type v}

/-- Index carrier of the interface family. -/
abbrev Index (_ : OracleFamily.{u, v, w} I Data) := I

/-- The admissible realization type at each index. -/
abbrev Realization (O : OracleFamily.{u, v, w} I Data) : O.Index → Type v := Data

/-- The dependent query signature of the explicit interfaces. -/
abbrev spec (O : OracleFamily.{u, v, w} I Data) := [O.Realization]ₒ' O.interface

/-- Arbitrary deterministic answers, without a representability assumption. -/
abbrev Behavior (O : OracleFamily.{u, v, w} I Data) := QueryImpl O.spec Id

/-- Interpret a family of admissible realizations through its declared interfaces. -/
def behaviorOfRealizations (O : OracleFamily.{u, v, w} I Data)
    (data : ∀ i, O.Realization i) : O.Behavior :=
  fun q => (O.interface q.1).answer (data q.1) q.2

/-- The source whose environments are arbitrary behaviors, including unrepresentable ones. -/
def asBehaviorSource (O : OracleFamily.{u, v, w} I Data) := SourceCtx.ofSpec O.spec

/-- Pull back the indexed interface family along an arbitrary map.

Repeated indices copy interface types; they do not force independently supplied realizations or
behaviors to agree. Use a named-context view when aliases must share a realization. -/
def reindex (O : OracleFamily.{u, v, w} I Data) {J : Type u'} (f : J → O.Index) :
    OracleFamily J (O.Realization ∘ f) := ⟨fun j => O.interface (f j)⟩

end OracleFamily

/-- A derived oracle is precisely a program for each output query. -/
structure VirtualOracle {I : Type u} (srcSpec : OracleSpec.{u, v} I)
    {OutIdx : Type u'} {OutRealization : OutIdx → Type v}
    (Out : OracleFamily.{u', v, w} OutIdx OutRealization) where
  /-- The query program, interpreted by the upstream interpreter. -/
  query : QueryImpl Out.spec (OracleComp srcSpec)

namespace VirtualOracle

variable {I : Type u} {J : Type u'} {K : Type u''}
  {srcSpec : OracleSpec.{u, v} I}
  {AI : Type a} {AO : AI → Type v} {BI : Type b} {BO : BI → Type v}
  {A : OracleFamily.{a, v, w} AI AO} {B : OracleFamily.{b, v, w'} BI BO}

/-- Expose an existing query implementation as a virtual oracle. -/
def ofQuery (query : QueryImpl A.spec (OracleComp srcSpec)) : VirtualOracle srcSpec A :=
  ⟨query⟩

/-- Evaluate each query using a deterministic source handler. -/
def eval (a : VirtualOracle srcSpec A) (impl : QueryImpl srcSpec Id) : A.Behavior :=
  QueryImpl.compose impl a.query

/-- Equality of answers for every deterministic handler. This does not assert trace equality. -/
def SemEquiv (a b : VirtualOracle srcSpec A) : Prop := ∀ impl, a.eval impl = b.eval impl

/-- Identity view exports the source interface unchanged. -/
def id (A : OracleFamily.{a, v, w} AI AO) : VirtualOracle A.spec A :=
  ⟨QueryImpl.id' A.spec⟩

@[simp]
theorem eval_id (impl : A.Behavior) : (id A).eval impl = impl := by
  funext q
  simp [eval, id, QueryImpl.compose, QueryImpl.id']

/-- Substitute query programs for every source query. -/
def substSource (a : VirtualOracle srcSpec A)
    {L : Type t} {targetSpec : OracleSpec.{t, v} L}
    (route : QueryImpl srcSpec (OracleComp targetSpec)) : VirtualOracle targetSpec A :=
  ⟨QueryImpl.compose route a.query⟩

@[simp]
theorem eval_substSource (a : VirtualOracle srcSpec A)
    {L : Type t} {targetSpec : OracleSpec.{t, v} L}
    (route : QueryImpl srcSpec (OracleComp targetSpec)) (impl : QueryImpl targetSpec Id) :
    (a.substSource route).eval impl = a.eval (QueryImpl.compose impl route) := by
  funext q
  exact (QueryImpl.simulateQ_compose impl route (a.query q)).symm

/-- Reindex output interfaces by reusing their query programs. -/
def reindex (a : VirtualOracle srcSpec A) (f : K → A.Index) :
    VirtualOracle srcSpec (A.reindex f) := ⟨fun q => a.query ⟨f q.1, q.2⟩⟩

@[simp]
theorem eval_reindex (a : VirtualOracle srcSpec A) (f : K → A.Index)
    (impl : QueryImpl srcSpec Id) (q : (A.reindex f).spec.Domain) :
    (a.reindex f).eval impl q = a.eval impl ⟨f q.1, q.2⟩ := rfl

/-- Map the source along a coherent polynomial source morphism. -/
def mapSource {E : Type w'} {F : Type w''}
    {S : SourceCtx.{u, v, w'} I E} {T : SourceCtx.{u', v, w''} J F}
    (a : VirtualOracle S.spec A) (f : SourceHom S T) : VirtualOracle T.spec A :=
  a.substSource f.toQueryImpl

@[simp]
theorem eval_mapSource {E : Type w'} {F : Type w''}
    {S : SourceCtx.{u, v, w'} I E} {T : SourceCtx.{u', v, w''} J F}
    (a : VirtualOracle S.spec A) (f : SourceHom S T) (impl : QueryImpl T.spec Id) :
    (a.mapSource f).eval impl = a.eval (f.pull impl) := by
  rw [mapSource, eval_substSource]
  congr 1


/-- Add unused sources on the right. -/
def sumWeaken (a : VirtualOracle srcSpec A) {L : Type t} (extra : OracleSpec.{t, v} L) :
    VirtualOracle (srcSpec + extra) A :=
  a.substSource (fun q => liftM ((srcSpec + extra).query (.inl q)))

@[simp]
theorem eval_sumWeaken (a : VirtualOracle srcSpec A) {L : Type t} (extra : OracleSpec.{t, v} L)
    (impl : QueryImpl srcSpec Id) (other : QueryImpl extra Id) :
    (a.sumWeaken extra).eval (QueryImpl.add impl other) = a.eval impl := by
  rw [sumWeaken, eval_substSource]
  congr 1

/-- Compose a derived interface with a downstream view of that interface. -/
def subst (a : VirtualOracle srcSpec A) (b : VirtualOracle A.spec B) :
    VirtualOracle srcSpec B := b.substSource a.query

@[simp]
theorem eval_subst (a : VirtualOracle srcSpec A) (b : VirtualOracle A.spec B)
    (impl : QueryImpl srcSpec Id) : (a.subst b).eval impl = b.eval (a.eval impl) :=
  eval_substSource b a.query impl

/-- Substitution preserves observational equality on both sides. -/
theorem subst_congr {a a' : VirtualOracle srcSpec A} {b b' : VirtualOracle A.spec B}
    (ha : SemEquiv a a') (hb : SemEquiv b b') : SemEquiv (a.subst b) (a'.subst b') := by
  intro impl
  simp only [eval_subst, ha impl]
  exact hb _

/-- Substitution with additional downstream sources kept available. -/
def substWithSuffix (a : VirtualOracle srcSpec A) (extra : OracleSpec.{u'', v} K)
    (b : VirtualOracle (A.spec + extra) B) : VirtualOracle (srcSpec + extra) B :=
  b.substSource (QueryImpl.add (a.sumWeaken extra).query
    (fun q => liftM ((srcSpec + extra).query (.inr q))))

@[simp]
theorem eval_substWithSuffix (a : VirtualOracle srcSpec A) (extra : OracleSpec.{u'', v} K)
    (b : VirtualOracle (A.spec + extra) B)
    (impl : QueryImpl srcSpec Id) (other : QueryImpl extra Id) :
    (a.substWithSuffix extra b).eval (QueryImpl.add impl other) =
      b.eval (QueryImpl.add (a.eval impl) other) := by
  rw [substWithSuffix, eval_substSource]
  congr 1
  funext q
  cases q with
  | inl q => exact congrFun (eval_sumWeaken a extra impl other) q
  | inr q => simp [QueryImpl.compose, QueryImpl.add]

/-- Identity substitution preserves all deterministic behavior. -/
theorem subst_id (a : VirtualOracle srcSpec A) : SemEquiv (a.subst (id A)) a := by
  intro impl
  simp

/-- An identity upstream interface preserves all deterministic behavior. -/
theorem id_subst (b : VirtualOracle A.spec B) : SemEquiv ((id A).subst b) b := by
  intro impl
  simp

/-- The semantic relation is reflexive. -/
theorem SemEquiv.refl (a : VirtualOracle srcSpec A) : SemEquiv a a := fun _ => rfl

/-- The semantic relation is symmetric. -/
theorem SemEquiv.symm {a b : VirtualOracle srcSpec A} (h : SemEquiv a b) :
    SemEquiv b a := fun impl => (h impl).symm

/-- The semantic relation is transitive. -/
theorem SemEquiv.trans {a b c : VirtualOracle srcSpec A}
    (h : SemEquiv a b) (h' : SemEquiv b c) : SemEquiv a c :=
  fun impl => (h impl).trans (h' impl)

/-- Successive substitutions agree under every handler. -/
theorem subst_assoc {CI : Type t} {CO : CI → Type v}
    {C : OracleFamily.{t, v, w''} CI CO} (a : VirtualOracle srcSpec A)
    (b : VirtualOracle A.spec B) (c : VirtualOracle B.spec C) :
    SemEquiv ((a.subst b).subst c) (a.subst (b.subst c)) := by
  intro impl
  simp

end VirtualOracle

end Interaction.Oracle
