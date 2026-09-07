/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Source
import ArkLib.OracleReduction.OracleInterface

/-!
# Virtual oracle programs

Virtual oracles are query implementations in the existing free oracle monad. Their meaning is
interpretation, with no separately stored denotation or coherence proof. Semantic equivalence
quantifies over every deterministic handler, not only handlers realized by selected backing data.
`OracleInterface` fixes responses to its object universe; `OracleComp` further requires the source
responses and output responses to share a universe. Query indices remain independent.
-/

universe u v w u' w' u'' w'' t a b

namespace Interaction.Oracle

/-- An indexed family of objects with explicitly selected interfaces. -/
structure OracleFamily (ι : Type u) (Obj : ι → Type v) where
  /-- Observable interface, supplied as data rather than inferred. -/
  oracle : ∀ i, OracleInterface.{v, w} (Obj i)

namespace OracleFamily

variable {I : Type u} {Data : I → Type v}

/-- Slot carrier of a family. -/
abbrev ι (_ : OracleFamily.{u, v, w} I Data) := I

/-- Concrete representation carrier of a family. -/
abbrev Obj (O : OracleFamily.{u, v, w} I Data) : O.ι → Type v := Data

/-- The dependent query signature of the explicit interfaces. -/
abbrev spec (O : OracleFamily.{u, v, w} I Data) := [O.Obj]ₒ' O.oracle

/-- Arbitrary deterministic answers, without a representability assumption. -/
abbrev Behavior (O : OracleFamily.{u, v, w} I Data) := QueryImpl O.spec Id

/-- Interpret concrete data through the declared interfaces. -/
def answerData (O : OracleFamily.{u, v, w} I Data) (data : ∀ i, O.Obj i) : O.Behavior :=
  fun q => (O.oracle q.1).answer (data q.1) q.2

/-- The source whose environments are all behaviors of this family. -/
def asSource (O : OracleFamily.{u, v, w} I Data) := SourceCtx.ofSpec O.spec

/-- Rename or select slots, including repeated selection of the same slot. -/
def reindex (O : OracleFamily.{u, v, w} I Data) {J : Type u'} (f : J → O.ι) :
    OracleFamily J (O.Obj ∘ f) := ⟨fun j => O.oracle (f j)⟩

end OracleFamily

/-- A derived oracle is precisely a program for each output query. -/
structure VirtualOracle {I : Type u} (srcSpec : OracleSpec.{u, v} I)
    {OutIdx : Type u'} {OutObj : OutIdx → Type v}
    (Out : OracleFamily.{u', v, w} OutIdx OutObj) where
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
def mapSource (a : VirtualOracle srcSpec A)
    {L : Type t} {targetSpec : OracleSpec.{t, v} L}
    (route : QueryImpl srcSpec (OracleComp targetSpec)) : VirtualOracle targetSpec A :=
  ⟨QueryImpl.compose route a.query⟩

@[simp]
theorem eval_mapSource (a : VirtualOracle srcSpec A)
    {L : Type t} {targetSpec : OracleSpec.{t, v} L}
    (route : QueryImpl srcSpec (OracleComp targetSpec)) (impl : QueryImpl targetSpec Id) :
    (a.mapSource route).eval impl = a.eval (QueryImpl.compose impl route) := by
  funext q
  exact (QueryImpl.simulateQ_compose impl route (a.query q)).symm

/-- Select output slots without changing their query programs. -/
def reindex (a : VirtualOracle srcSpec A) (f : K → A.ι) :
    VirtualOracle srcSpec (A.reindex f) := ⟨fun q => a.query ⟨f q.1, q.2⟩⟩

@[simp]
theorem eval_reindex (a : VirtualOracle srcSpec A) (f : K → A.ι)
    (impl : QueryImpl srcSpec Id) (q : (A.reindex f).spec.Domain) :
    (a.reindex f).eval impl q = a.eval impl ⟨f q.1, q.2⟩ := rfl

/-- Route the backing source using its existing coherent polynomial morphism. -/
def rebase {E : Type w'} {F : Type w''}
    {S : SourceCtx.{u, v, w'} I E} {T : SourceCtx.{u', v, w''} J F}
    (a : VirtualOracle S.spec A) (f : SourceHom S T) : VirtualOracle T.spec A :=
  a.mapSource f.toQueryImpl

@[simp]
theorem eval_rebase {E : Type w'} {F : Type w''}
    {S : SourceCtx.{u, v, w'} I E} {T : SourceCtx.{u', v, w''} J F}
    (a : VirtualOracle S.spec A) (f : SourceHom S T) (impl : QueryImpl T.spec Id) :
    (a.rebase f).eval impl = a.eval (f.pull impl) := by
  rw [rebase, eval_mapSource]
  congr 1


/-- Add unused sources on the right. -/
def tensorWeaken (a : VirtualOracle srcSpec A) {L : Type t} (extra : OracleSpec.{t, v} L) :
    VirtualOracle (srcSpec + extra) A :=
  a.mapSource (fun q => liftM ((srcSpec + extra).query (.inl q)))

@[simp]
theorem eval_tensorWeaken (a : VirtualOracle srcSpec A) {L : Type t} (extra : OracleSpec.{t, v} L)
    (impl : QueryImpl srcSpec Id) (other : QueryImpl extra Id) :
    (a.tensorWeaken extra).eval (QueryImpl.add impl other) = a.eval impl := by
  rw [tensorWeaken, eval_mapSource]
  congr 1

/-- Compose a derived interface with a downstream view of that interface. -/
def subst (a : VirtualOracle srcSpec A) (b : VirtualOracle A.spec B) :
    VirtualOracle srcSpec B := b.mapSource a.query

@[simp]
theorem eval_subst (a : VirtualOracle srcSpec A) (b : VirtualOracle A.spec B)
    (impl : QueryImpl srcSpec Id) : (a.subst b).eval impl = b.eval (a.eval impl) :=
  eval_mapSource b a.query impl

/-- Substitution preserves observational equality on both sides. -/
theorem subst_congr {a a' : VirtualOracle srcSpec A} {b b' : VirtualOracle A.spec B}
    (ha : SemEquiv a a') (hb : SemEquiv b b') : SemEquiv (a.subst b) (a'.subst b') := by
  intro impl
  simp only [eval_subst, ha impl]
  exact hb _

/-- Substitution with additional downstream sources kept available. -/
def substWith (a : VirtualOracle srcSpec A) (extra : OracleSpec.{u'', v} K)
    (b : VirtualOracle (A.spec + extra) B) : VirtualOracle (srcSpec + extra) B :=
  b.mapSource (QueryImpl.add (a.tensorWeaken extra).query
    (fun q => liftM ((srcSpec + extra).query (.inr q))))

@[simp]
theorem eval_substWith (a : VirtualOracle srcSpec A) (extra : OracleSpec.{u'', v} K)
    (b : VirtualOracle (A.spec + extra) B)
    (impl : QueryImpl srcSpec Id) (other : QueryImpl extra Id) :
    (a.substWith extra b).eval (QueryImpl.add impl other) =
      b.eval (QueryImpl.add (a.eval impl) other) := by
  rw [substWith, eval_mapSource]
  congr 1
  funext q
  cases q with
  | inl q => exact congrFun (eval_tensorWeaken a extra impl other) q
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
