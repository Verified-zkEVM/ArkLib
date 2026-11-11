/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Execution
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose

/-!
# Passive oracle verification

Completed shape paths determine the available oracle family. Its concrete data comes from the
same full transcript, while the decision sees only the verifier view and query access. Output
oracles are one map containing concrete data, query simulation and their agreement law.
-/

@[expose] public section

universe u q dI uι uS uI uJ uK uL uX uY uZ uW dX dY dZ dW w wI wJ

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle

-- Reduce the shape projection when the payload family descends to a child.
attribute [local implicit_reducible] projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun

/-- The oracle nodes on a completed shape path. -/
@[implicit_reducible]
def oracleIdx : (s : OracleProtocol.{u, q}) → Path s → Type u
  | .pure _, _ => PEmpty
  | .liftBind (.message _) next, ⟨x, p⟩ => oracleIdx (next x) p
  | .liftBind (.challenge _) next, ⟨x, p⟩ => oracleIdx (next x) p
  | .liftBind (.oracle _ _) next, ⟨x, p⟩ => PUnit ⊕ oracleIdx (next x) p

/-- Concrete data carriers of the oracle nodes on a completed path. -/
@[implicit_reducible]
def OracleData : (s : OracleProtocol.{u, q}) → (p : Path s) → oracleIdx s p → Type u
  | .pure _, _ => fun i => i.elim
  | .liftBind (.message _) next, ⟨x, p⟩ => OracleData (next x) p
  | .liftBind (.challenge _) next, ⟨x, p⟩ => OracleData (next x) p
  | .liftBind (.oracle X _) next, ⟨x, p⟩ =>
    Sum.elim (fun _ => X) (OracleData (next x) p)

/-- Independent families of concrete data, with disjoint query access. -/
@[implicit_reducible]
def sumFamily {I : Type uI} {J : Type uJ} {A : I → Type u} {B : J → Type u}
    (a : OracleFamily.{uI, u, w} I A) (b : OracleFamily.{uJ, u, w} J B) :
    OracleFamily (I ⊕ J) (Sum.elim A B) :=
  ⟨fun | .inl i => a.interface i | .inr j => b.interface j⟩

/-- The family consisting of one oracle payload. -/
@[implicit_reducible]
def singletonFamily {X : Type u} (I : OracleInterface.{u, q} X) :
    OracleFamily.{u, u, q} PUnit (fun _ => X) := ⟨fun _ => I⟩

/-- The concrete oracle family at a completed path. -/
@[implicit_reducible]
def pathFamily : (s : OracleProtocol.{u, q}) → (p : Path s) →
    OracleFamily (oracleIdx s p) (OracleData s p)
  | .pure _, _ => ⟨fun i => i.elim⟩
  | .liftBind (.message _) next, ⟨x, p⟩ => pathFamily (next x) p
  | .liftBind (.challenge _) next, ⟨x, p⟩ => pathFamily (next x) p
  | .liftBind (.oracle _ I) next, ⟨x, p⟩ =>
    sumFamily (singletonFamily I) (pathFamily (next x) p)

/-- Queries to the oracle nodes on a completed path. -/
abbrev oracles (s : OracleProtocol.{u, q}) (p : Path s) := (pathFamily s p).spec

/-- Read the concrete payloads from exactly the full transcript that produced this shape. -/
def payloads : (s : OracleProtocol.{u, q}) → (tr : PathAlong oracleSig s) →
    (i : oracleIdx s (projectPathAlong oracleSig s tr)) →
      OracleData s (projectPathAlong oracleSig s tr) i
  | .pure _, _, i => i.elim
  | .liftBind (.message _) next, ⟨x, tr⟩, i => payloads (next x) tr i
  | .liftBind (.challenge _) next, ⟨_, tr⟩, i => payloads (next ⟨⟩) tr i
  | .liftBind (.oracle _ _) _, ⟨x, _⟩, .inl _ => x
  | .liftBind (.oracle _ _) next, ⟨_, tr⟩, .inr i => payloads (next ⟨⟩) tr i

/-- The sole payload handler used by execution answers from the completed run. -/
def payloadImpl (s : OracleProtocol.{u, q}) (tr : PathAlong oracleSig s) :
    QueryImpl (oracles s (projectPathAlong oracleSig s tr)) Id :=
  (pathFamily s (projectPathAlong oracleSig s tr)).behaviorOfRealizations (payloads s tr)

/-- Pair the data of two disjoint families. -/
def sumData {I : Type uI} {J : Type uJ} {A : I → Type u} {B : J → Type u}
    (a : ∀ i, A i) (b : ∀ j, B j) : ∀ k, Sum.elim A B k
  | .inl i => a i
  | .inr j => b j

/-- Reassembling disjoint data from its two restrictions is the identity. -/
theorem sumData_eta {I : Type uI} {J : Type uJ} {A : I → Type u} {B : J → Type u}
    (x : ∀ k, Sum.elim A B k) :
    sumData (fun i => x (.inl i)) (fun j => x (.inr j)) = x := by
  funext k
  cases k <;> rfl

/-- Oracle resources: a query specification and the concrete data that answers it. The query
indices and the data may lie in any universe; only the responses lie in `Type u`, the universe of
the computations that receive them. The universe parameters of `Resources.{u, uX, dX}` are those of
the responses, the query indices and the data, in this order. -/
structure Resources : Type (max (uX + 1) (u + 1) (dX + 1)) where
  /-- The query indices. -/
  Index : Type uX
  /-- The queries and their response types. -/
  spec : OracleSpec.{uX, u} Index
  /-- The concrete data. -/
  Data : Type dX
  /-- How concrete data answers each query. -/
  answer : Data → QueryImpl spec Id

/-- The resources of an oracle family: queries through its interfaces, answered from concrete
realizations. The query universe `wI` of the interfaces is independent of the response universe.
-/
@[reducible] def Resources.ofFamily {I : Type uI} {A : I → Type u}
    (F : OracleFamily.{uI, u, wI} I A) : Resources.{u, max uI wI, max uI u} where
  Index := (i : I) × (F.interface i).Query
  spec := F.spec
  Data := ∀ i, A i
  answer := F.behaviorOfRealizations

attribute [coe] Resources.ofFamily

/-- An oracle family is used as resources through its interfaces. -/
instance {I : Type uI} {A : I → Type u} :
    CoeOut (OracleFamily.{uI, u, wI} I A) Resources.{u, max uI wI, max uI u} :=
  ⟨Resources.ofFamily⟩

/-- Disjoint resources: each query goes to one side and is answered from that side's data. The
two sides keep their own index and data universes, and their data stays a pair. -/
@[reducible] def Resources.sum (R : Resources.{u, uX, dX}) (R' : Resources.{u, uY, dY}) :
    Resources.{u, max uX uY, max dX dY} where
  Index := R.Index ⊕ R'.Index
  spec := R.spec + R'.spec
  Data := R.Data × R'.Data
  answer x := R.answer x.1 + R'.answer x.2

/-- A concrete oracle map and its query-by-query implementation agree on all input data. -/
structure OracleMap (In : Resources.{u, uX, dX}) (Out : Resources.{u, uY, dY}) where
  /-- Concrete output data, available to a subsequent honest prover. -/
  f : In.Data → Out.Data
  /-- Output queries are simulated using only input oracle queries. -/
  impl : QueryImpl Out.spec (OracleComp In.spec)
  /-- Simulation answers exactly as the materialized output data. -/
  law : ∀ x q, simulateQ (In.answer x) (impl q) = Out.answer (f x) q

namespace OracleMap

section Resources
variable {In : Resources.{u, uX, dX}} {Mid : Resources.{u, uY, dY}}
  {Out : Resources.{u, uZ, dZ}} {Other : Resources.{u, uW, dW}}

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
    {α : Type u} (program : OracleComp Out.spec α) :
    simulateQ (In.answer x) (simulateQ h.impl program) =
      simulateQ (Out.answer (h.f x)) program :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (h.law x) program

/-- The identity map of resources. -/
def id (R : Resources.{u, uX, dX}) : OracleMap R R where
  f x := x
  impl q := liftM (R.spec.query q)
  law _ _ := rfl

/-- Keep the left side of disjoint resources. -/
def fst (R : Resources.{u, uX, dX}) (R' : Resources.{u, uY, dY}) : OracleMap (R.sum R') R where
  f x := x.1
  impl q := liftM ((R.spec + R'.spec).query (.inl q))
  law _ _ := rfl

/-- Keep the right side of disjoint resources. -/
def snd (R : Resources.{u, uX, dX}) (R' : Resources.{u, uY, dY}) : OracleMap (R.sum R') R' where
  f x := x.2
  impl q := liftM ((R.spec + R'.spec).query (.inr q))
  law _ _ := rfl

/-- Apply two oracle maps to disjoint resources. -/
def par (h : OracleMap In Mid) (g : OracleMap Out Other) :
    OracleMap (In.sum Out) (Mid.sum Other) where
  f x := (h.f x.1, g.f x.2)
  impl
    | .inl q => simulateQ (fun r => liftM ((In.spec + Out.spec).query (.inl r))) (h.impl q)
    | .inr q => simulateQ (fun r => liftM ((In.spec + Out.spec).query (.inr r))) (g.impl q)
  law x q := by
    cases q with
    | inl q =>
      exact (QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := In.answer x.1)
        (fun _ => rfl) (h.impl q)).trans (h.law _ _)
    | inr q =>
      exact (QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := Out.answer x.2)
        (fun _ => rfl) (g.impl q)).trans (g.law _ _)

/-- Regroup disjoint resources to the left without changing their data or answers. -/
def reassoc (R₁ : Resources.{u, uX, dX}) (R₂ : Resources.{u, uY, dY})
    (R₃ : Resources.{u, uZ, dZ}) : OracleMap (R₁.sum (R₂.sum R₃)) ((R₁.sum R₂).sum R₃) where
  f x := ((x.1, x.2.1), x.2.2)
  impl
    | .inl (.inl q) => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inl q))
    | .inl (.inr q) => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inr (.inl q)))
    | .inr q => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inr (.inr q)))
  law x q := by rcases q with (q | q) | q <;> rfl

/-- Regroup disjoint resources to the right without changing their data or answers. -/
def unreassoc (R₁ : Resources.{u, uX, dX}) (R₂ : Resources.{u, uY, dY})
    (R₃ : Resources.{u, uZ, dZ}) : OracleMap ((R₁.sum R₂).sum R₃) (R₁.sum (R₂.sum R₃)) where
  f x := (x.1.1, (x.1.2, x.2))
  impl
    | .inl q => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inl (.inl q)))
    | .inr (.inl q) => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inl (.inr q)))
    | .inr (.inr q) => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inr q))
  law x q := by rcases q with q | (q | q) <;> rfl

end Resources

section Families
variable {I : Type uI} {J : Type uJ} {K : Type uK} {A : I → Type u} {B : J → Type u}
  {C : K → Type u}

/-- Embeddings are oracle maps that retain or rename existing input slots. -/
def embedding (In : OracleFamily.{uI, u, wI} I A) (rename : J → I) :
    OracleMap In (In.reindex rename) where
  f x j := x (rename j)
  impl q := liftM (In.spec.query ⟨rename q.1, q.2⟩)
  law _ _ := rfl

/-- View a family of disjoint data as disjoint resources, with its data split into a pair. -/
def ofSumFamily (a : OracleFamily.{uI, u, w} I A) (b : OracleFamily.{uJ, u, w} J B) :
    OracleMap (sumFamily a b) (Resources.sum a b) where
  f x := (fun i => x (.inl i), fun j => x (.inr j))
  impl
    | .inl q => liftM ((sumFamily a b).spec.query ⟨.inl q.1, q.2⟩)
    | .inr q => liftM ((sumFamily a b).spec.query ⟨.inr q.1, q.2⟩)
  law x q := by rcases q with q | q <;> rfl

/-- Combine disjoint resources into a family, the inverse representation of `ofSumFamily`. -/
def toSumFamily (a : OracleFamily.{uI, u, w} I A) (b : OracleFamily.{uJ, u, w} J B) :
    OracleMap (Resources.sum a b) (sumFamily a b) where
  f x := sumData x.1 x.2
  impl
    | ⟨.inl i, q⟩ => liftM ((Resources.sum a b).spec.query (.inl ⟨i, q⟩))
    | ⟨.inr j, q⟩ => liftM ((Resources.sum a b).spec.query (.inr ⟨j, q⟩))
  law x q := by rcases q with ⟨i | j, q⟩ <;> rfl

/-- Splitting and recombining a family recovers its concrete data. -/
theorem toSumFamily_ofSumFamily (a : OracleFamily.{uI, u, w} I A)
    (b : OracleFamily.{uJ, u, w} J B) (x : (Resources.ofFamily (sumFamily a b)).Data) :
    (toSumFamily a b).f ((ofSumFamily a b).f x) = x := sumData_eta x

/-- Combining and splitting disjoint resources recovers both data components. -/
theorem ofSumFamily_toSumFamily (a : OracleFamily.{uI, u, w} I A)
    (b : OracleFamily.{uJ, u, w} J B) (x : (Resources.sum a b).Data) :
    (ofSumFamily a b).f ((toSumFamily a b).f x) = x := rfl

variable {L : Type uL} {D : L → Type u} {In : OracleFamily.{uI, u, w} I A}
  {Mid : OracleFamily.{uJ, u, wJ} J B} {Out : OracleFamily.{uK, u, w} K C}
  {Other : OracleFamily.{uL, u, wJ} L D}

/-- Apply two oracle maps to the two parts of a family of disjoint data. -/
def sum (h : OracleMap In Mid) (g : OracleMap Out Other) :
    OracleMap (sumFamily In Out) (sumFamily Mid Other) :=
  (toSumFamily Mid Other).comp ((h.par g).comp (ofSumFamily In Out))

/-- Reassociate family data through the resource reassociation and representation bridges. -/
def assoc (In : OracleFamily.{uI, u, w} I A) (Mid : OracleFamily.{uJ, u, w} J B)
    (Out : OracleFamily.{uK, u, w} K C) :
    OracleMap (sumFamily (sumFamily In Mid) Out) (sumFamily In (sumFamily Mid Out)) :=
  (toSumFamily In (sumFamily Mid Out)).comp
    (((OracleMap.id In).par (toSumFamily Mid Out)).comp
      ((unreassoc In Mid Out).comp
        (((ofSumFamily In Mid).par (OracleMap.id Out)).comp
          (ofSumFamily (sumFamily In Mid) Out))))

/-- Inverse family reassociation through the resource reassociation and representation bridges. -/
def unassoc (In : OracleFamily.{uI, u, w} I A) (Mid : OracleFamily.{uJ, u, w} J B)
    (Out : OracleFamily.{uK, u, w} K C) :
    OracleMap (sumFamily In (sumFamily Mid Out)) (sumFamily (sumFamily In Mid) Out) :=
  (toSumFamily (sumFamily In Mid) Out).comp
    (((toSumFamily In Mid).par (OracleMap.id Out)).comp
      ((reassoc In Mid Out).comp
        (((OracleMap.id In).par (ofSumFamily Mid Out)).comp
          (ofSumFamily In (sumFamily Mid Out)))))

end Families

end OracleMap

/-- Route the oracles of an appended path into its two completed component paths. -/
def oracles_append : (s₁ : OracleProtocol.{u, q}) → (s₂ : Path s₁ → OracleProtocol.{u, q}) →
    (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    OracleMap (sumFamily (pathFamily s₁ p₁) (pathFamily (s₂ p₁) p₂))
      (pathFamily (s₁.append s₂) (Path.append s₁ s₂ p₁ p₂))
  | .pure _, s₂, ⟨⟩, p₂ =>
    OracleMap.embedding (sumFamily (pathFamily (.pure PUnit.unit) ⟨⟩)
      (pathFamily (s₂ ⟨⟩) p₂)) Sum.inr
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracles_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracles_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.oracle _ I) next, s₂, ⟨x, p₁⟩, p₂ =>
    ((OracleMap.embedding (singletonFamily I) id).sum
      (oracles_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂)).comp
      (OracleMap.assoc (singletonFamily I) (pathFamily (next x) p₁)
        (pathFamily (s₂ ⟨x, p₁⟩) p₂))

/-- Route either component's oracle queries into the completed appended path. -/
def oracles_split : (s₁ : OracleProtocol.{u, q}) → (s₂ : Path s₁ → OracleProtocol.{u, q}) →
    (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    OracleMap (pathFamily (s₁.append s₂) (Path.append s₁ s₂ p₁ p₂))
      (sumFamily (pathFamily s₁ p₁) (pathFamily (s₂ p₁) p₂))
  | .pure _, s₂, ⟨⟩, p₂ =>
    { f := fun x => sumData (fun i => i.elim) x
      impl := fun
        | ⟨.inl i, _⟩ => i.elim
        | ⟨.inr i, q⟩ => (liftM ((pathFamily (s₂ ⟨⟩) p₂).spec.query ⟨i, q⟩) :
        OracleComp (pathFamily (s₂ ⟨⟩) p₂).spec _)
      law := fun _ q => by
        rcases q with ⟨i | i, q⟩
        · exact i.elim
        · rfl }
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracles_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracles_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.oracle _ I) next, s₂, ⟨x, p₁⟩, p₂ =>
    (OracleMap.unassoc (singletonFamily I) (pathFamily (next x) p₁)
      (pathFamily (s₂ ⟨x, p₁⟩) p₂)).comp
      ((OracleMap.embedding (singletonFamily I) id).sum
        (oracles_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂))

/-- Materializing the append route and then splitting it recovers both component families. -/
theorem oracles_split_append : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    (x : ∀ i, (sumFamily (pathFamily s₁ p₁) (pathFamily (s₂ p₁) p₂)).Realization i) →
    (oracles_split s₁ s₂ p₁ p₂).f ((oracles_append s₁ s₂ p₁ p₂).f x) = x
  | .pure _, _, ⟨⟩, _, _ => by
    funext i
    rcases i with i | i
    · exact i.elim
    · rfl
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracles_split_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracles_split_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.oracle _ _) next, s₂, ⟨x, p₁⟩, p₂, data => by
    have ih := oracles_split_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
      (sumData (fun i => data (.inl (.inr i))) (fun i => data (.inr i)))
    funext i
    rcases i with (i | i) | i
    · rfl
    · exact congrFun ih (.inl i)
    · exact congrFun ih (.inr i)

/-- Splitting and recombining an appended family preserves every concrete payload. -/
theorem oracles_append_split : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    (x : ∀ i, OracleData (s₁.append s₂) (Path.append s₁ s₂ p₁ p₂) i) →
    (oracles_append s₁ s₂ p₁ p₂).f ((oracles_split s₁ s₂ p₁ p₂).f x) = x
  | .pure _, _, ⟨⟩, _, _ => rfl
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracles_append_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracles_append_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.oracle _ _) next, s₂, ⟨x, p₁⟩, p₂, data => by
    have ih := oracles_append_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
      (fun i => data (.inr i))
    funext i
    cases i with
    | inl i => rfl
    | inr i =>
      change (oracles_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f
        (sumData
          (fun j => (oracles_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f
            (fun k => data (.inr k)) (.inl j))
          (fun j => (oracles_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f
            (fun k => data (.inr k)) (.inr j))) i = data (.inr i)
      exact (congrArg (fun d =>
        (oracles_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f d i)
        (sumData_eta ((oracles_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f
          (fun k => data (.inr k))))).trans (congrFun ih i)

/-- A completed shape paired with the concrete payloads at its oracle nodes. -/
abbrev PathData (s : OracleProtocol.{u, q}) := (p : Path s) × (∀ i, OracleData s p i)

/-- Prepend one full move to a materialized path. -/
def PathData.prepend : (a : OraclePos.{u, q}) → (next : OraclePoly.B a → OracleProtocol) →
    (x : Move oracleSig a) → PathData (next (oracleSig.toFunB a x)) →
      PathData (.liftBind a next)
  | .message _, _, x, ⟨p, data⟩ => ⟨⟨x, p⟩, data⟩
  | .challenge _, _, _, ⟨p, data⟩ => ⟨⟨⟨⟩, p⟩, data⟩
  | .oracle _ _, _, x, ⟨p, data⟩ => ⟨⟨⟨⟩, p⟩, sumData (fun _ => x) data⟩

/-- Appending full transcripts materializes exactly the two routed payload families. -/
theorem payloads_append : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (tr₁ : PathAlong oracleSig s₁) →
    (tr₂ : PathAlong oracleSig (s₂ (projectPathAlong oracleSig s₁ tr₁))) →
    (⟨projectPathAlong oracleSig (s₁.append s₂) (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂),
      payloads (s₁.append s₂) (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂)⟩ :
        PathData (s₁.append s₂)) =
      ⟨Path.append s₁ s₂ (projectPathAlong oracleSig s₁ tr₁)
          (projectPathAlong oracleSig _ tr₂),
        (oracles_append s₁ s₂ (projectPathAlong oracleSig s₁ tr₁)
          (projectPathAlong oracleSig _ tr₂)).f
          (sumData (payloads s₁ tr₁) (payloads _ tr₂))⟩
  | .pure _, _, ⟨⟩, _ => rfl
  | .liftBind (.message _) next, s₂, ⟨x, tr₁⟩, tr₂ =>
    congrArg (PathData.prepend (.message _) (fun b =>
      (next b).append (fun p => s₂ ⟨b, p⟩)) x)
      (payloads_append (next x) (fun p => s₂ ⟨x, p⟩) tr₁ tr₂)
  | .liftBind (.challenge _) next, s₂, ⟨x, tr₁⟩, tr₂ =>
    congrArg (PathData.prepend (.challenge _) (fun b =>
      (next b).append (fun p => s₂ ⟨b, p⟩)) x)
      (payloads_append (next ⟨⟩) (fun p => s₂ ⟨⟨⟩, p⟩) tr₁ tr₂)
  | .liftBind (.oracle _ I) next, s₂, ⟨x, tr₁⟩, tr₂ => by
    have h := congrArg (PathData.prepend (.oracle _ I) (fun b =>
      (next b).append (fun p => s₂ ⟨b, p⟩)) x)
      (payloads_append (next ⟨⟩) (fun p => s₂ ⟨⟨⟩, p⟩) tr₁ tr₂)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      funext i
      cases i <;> rfl
    · rfl

/-- The appended transcript's handler agrees with routing into its component handlers. -/
theorem payloadImpl_append (s₁ : OracleProtocol.{u, q})
    (s₂ : Path s₁ → OracleProtocol.{u, q}) (tr₁ : PathAlong oracleSig s₁)
    (tr₂ : PathAlong oracleSig (s₂ (projectPathAlong oracleSig s₁ tr₁))) :
    (⟨projectPathAlong oracleSig (s₁.append s₂) (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂),
      payloadImpl (s₁.append s₂) (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂)⟩ :
      (p : Path (s₁.append s₂)) × QueryImpl (oracles (s₁.append s₂) p) Id) =
    ⟨Path.append s₁ s₂ (projectPathAlong oracleSig s₁ tr₁)
        (projectPathAlong oracleSig _ tr₂),
      QueryImpl.compose
        ((sumFamily (pathFamily s₁ (projectPathAlong oracleSig s₁ tr₁))
          (pathFamily _ (projectPathAlong oracleSig _ tr₂))).behaviorOfRealizations
            (sumData (payloads s₁ tr₁) (payloads _ tr₂)))
        (oracles_append s₁ s₂ (projectPathAlong oracleSig s₁ tr₁)
          (projectPathAlong oracleSig _ tr₂)).impl⟩ := by
  have h := congrArg
    (fun d : PathData (s₁.append s₂) =>
      (⟨d.1, (pathFamily (s₁.append s₂) d.1).behaviorOfRealizations d.2⟩ :
        (p : Path (s₁.append s₂)) × QueryImpl (oracles (s₁.append s₂) p) Id))
    (payloads_append s₁ s₂ tr₁ tr₂)
  refine h.trans ?_
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact (funext ((oracles_append s₁ s₂ _ _).law _)).symm

/-- The resources a decision at path `p` may query: the input resources and the path
payloads. Input data may lie in a universe independent of responses and moves. Input queries
and oracle-node queries also have independent universes. -/
abbrev pathResources (inputs : Resources.{u, uI, dI})
    (s : OracleProtocol.{u, q}) (p : Path s) :=
  Resources.sum inputs (Resources.ofFamily (pathFamily s p))

/-- A passive oracle verifier. The output statement type `T p` and the output oracle family
`outputs p` are indexed by the public shape path `p` of the run, so a public message may change
both. A verifier with one output type and family uses constant families. -/
structure OracleVerifier {ι : Type uι} (ambient : OracleSpec.{uι, u} ι)
    (s : OracleProtocol.{u, q}) (S : Type uS) (T : Path s → Type u)
    {J : Path s → Type uJ} {B : (p : Path s) → J p → Type u}
    (inputs : Resources.{u, uI, dI})
    (outputs : (p : Path s) → OracleFamily.{uJ, u, wJ} (J p) (B p)) where
  /-- The decision has query access to inputs and path payloads, never their raw values. -/
  decide : S → (p : Path s) → View s p →
    OptionT (OracleComp (ambient + (pathResources inputs s p).spec)) (T p)
  /-- The output interface may use the public statement and verifier view. -/
  outputMap : S → (p : Path s) → View s p →
    OracleMap (pathResources inputs s p) (Resources.ofFamily (outputs p))

/-- The output statement paired with the concrete output oracle data, at each shape path. -/
abbrev OracleVerifier.Output {s : OracleProtocol.{u, q}} (T : Path s → Type u)
    {J : Path s → Type u} (B : (p : Path s) → J p → Type u) (p : Path s) : Type u :=
  T p × (∀ j, B p j)

/-- The decision with resource queries answered from concrete data; ambient queries remain.

Its possible results, with every ambient answer allowed, are the statements the decision can
return on that data and view.
-/
def OracleVerifier.decideWith {ι : Type uι} {ambient : OracleSpec.{uι, u} ι}
    {s : OracleProtocol.{u, q}} {S : Type uS} {T : Path s → Type u}
    {J : Path s → Type uJ} {B : (p : Path s) → J p → Type u}
    {inputs : Resources.{u, uI, dI}}
    {outputs : (p : Path s) → OracleFamily.{uJ, u, wJ} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (p : Path s) (v : View s p)
    (data : (pathResources inputs s p).Data) :
    OracleComp ambient (Option (T p)) :=
  simulateQ (QueryImpl.addLift (QueryImpl.id' ambient)
    ((pathResources inputs s p).answer data)) (V.decide stmt p v).run

/-- Interpret the decision's resource queries using the input and the actual run's payloads. -/
def OracleVerifier.run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : OracleProtocol.{u, q}} {S : Type uS} {T : Path s → Type u}
    {J : Path s → Type u} {B : (p : Path s) → J p → Type u}
    {inputs : Resources.{u, uI, dI}}
    {outputs : (p : Path s) → OracleFamily.{u, u, wJ} (J p) (B p)}
    {Out : PathAlong oracleSig s → Type u}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s)
      (Observation oracleSig s Out (OracleVerifier.Output T B)) := do
  let ⟨tr, out, _⟩ ← TwoParty.Lens.run s
    (prover.simulate (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))))
    (sampler oracleSig s (fun c =>
      liftM ((ambient + challengeSpec oracleSig s).query (.inr c))))
  let p := projectPathAlong oracleSig s tr
  let view := toView s tr
  let resources : (pathResources inputs s p).Data := (data, payloads s tr)
  let verdict ← simulateQ
    (QueryImpl.addLift
      ((fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) :
        QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)))
      ((pathResources inputs s p).answer resources))
    (V.decide stmt p view).run
  pure ⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f resources)⟩

end Interaction.Core
