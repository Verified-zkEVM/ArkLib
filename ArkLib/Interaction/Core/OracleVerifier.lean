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

-- Reduce the shape projection when the oracle message family descends to a child.
attribute [local implicit_reducible] projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun

/-- The indices of the oracle messages on a completed shape path, one per oracle node. -/
@[implicit_reducible]
def OracleMessageIndex : (s : OracleProtocol.{u, q}) → Path s → Type u
  | .pure _, _ => PEmpty
  | .liftBind (.message _) next, ⟨x, p⟩ => OracleMessageIndex (next x) p
  | .liftBind (.challenge _) next, ⟨x, p⟩ => OracleMessageIndex (next x) p
  | .liftBind (.oracle _ _) next, ⟨x, p⟩ => PUnit ⊕ OracleMessageIndex (next x) p

/-- The type of the oracle message at each oracle node of a completed path. -/
@[implicit_reducible]
def OracleMessage : (s : OracleProtocol.{u, q}) → (p : Path s) → OracleMessageIndex s p → Type u
  | .pure _, _ => fun i => i.elim
  | .liftBind (.message _) next, ⟨x, p⟩ => OracleMessage (next x) p
  | .liftBind (.challenge _) next, ⟨x, p⟩ => OracleMessage (next x) p
  | .liftBind (.oracle X _) next, ⟨x, p⟩ =>
    Sum.elim (fun _ => X) (OracleMessage (next x) p)

/-- Independent families of concrete data, with disjoint query access. -/
@[implicit_reducible]
def sumFamily {I : Type uI} {J : Type uJ} {A : I → Type u} {B : J → Type u}
    (a : OracleFamily.{uI, u, w} I A) (b : OracleFamily.{uJ, u, w} J B) :
    OracleFamily (I ⊕ J) (Sum.elim A B) :=
  ⟨fun | .inl i => a.interface i | .inr j => b.interface j⟩

/-- The family consisting of one oracle message. -/
@[implicit_reducible]
def singletonFamily {X : Type u} (I : OracleInterface.{u, q} X) :
    OracleFamily.{u, u, q} PUnit (fun _ => X) := ⟨fun _ => I⟩

/-- The family of oracle messages at a completed path, with their query interfaces. -/
@[implicit_reducible]
def oracleMessageFamily : (s : OracleProtocol.{u, q}) → (p : Path s) →
    OracleFamily (OracleMessageIndex s p) (OracleMessage s p)
  | .pure _, _ => ⟨fun i => i.elim⟩
  | .liftBind (.message _) next, ⟨x, p⟩ => oracleMessageFamily (next x) p
  | .liftBind (.challenge _) next, ⟨x, p⟩ => oracleMessageFamily (next x) p
  | .liftBind (.oracle _ I) next, ⟨x, p⟩ =>
    sumFamily (singletonFamily I) (oracleMessageFamily (next x) p)

/-- The query specification of the oracle messages on a completed path. -/
abbrev oracleMessageSpec (s : OracleProtocol.{u, q}) (p : Path s) := (oracleMessageFamily s p).spec

/-- Read the oracle messages from exactly the full transcript that produced this shape. -/
def oracleMessages : (s : OracleProtocol.{u, q}) → (tr : Transcript oracleSig s) →
    (i : OracleMessageIndex s tr.path) → OracleMessage s tr.path i
  | .pure _, _, i => i.elim
  | .liftBind (.message _) next, ⟨x, tr⟩, i => oracleMessages (next x) tr i
  | .liftBind (.challenge _) next, ⟨_, tr⟩, i => oracleMessages (next ⟨⟩) tr i
  | .liftBind (.oracle _ _) _, ⟨x, _⟩, .inl _ => x
  | .liftBind (.oracle _ _) next, ⟨_, tr⟩, .inr i => oracleMessages (next ⟨⟩) tr i

/-- The sole oracle message handler used by execution; it answers from the completed run. -/
def oracleMessageImpl (s : OracleProtocol.{u, q}) (tr : Transcript oracleSig s) :
    QueryImpl (oracleMessageSpec s tr.path) Id :=
  (oracleMessageFamily s tr.path).behaviorOfRealizations (oracleMessages s tr)

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
def sumAssocSymm (R₁ : Resources.{u, uX, dX}) (R₂ : Resources.{u, uY, dY})
    (R₃ : Resources.{u, uZ, dZ}) : OracleMap (R₁.sum (R₂.sum R₃)) ((R₁.sum R₂).sum R₃) where
  f x := ((x.1, x.2.1), x.2.2)
  impl
    | .inl (.inl q) => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inl q))
    | .inl (.inr q) => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inr (.inl q)))
    | .inr q => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inr (.inr q)))
  law x q := by rcases q with (q | q) | q <;> rfl

/-- Regroup disjoint resources to the right without changing their data or answers. -/
def sumAssoc (R₁ : Resources.{u, uX, dX}) (R₂ : Resources.{u, uY, dY})
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
def familySumAssoc (In : OracleFamily.{uI, u, w} I A) (Mid : OracleFamily.{uJ, u, w} J B)
    (Out : OracleFamily.{uK, u, w} K C) :
    OracleMap (sumFamily (sumFamily In Mid) Out) (sumFamily In (sumFamily Mid Out)) :=
  (toSumFamily In (sumFamily Mid Out)).comp
    (((OracleMap.id In).par (toSumFamily Mid Out)).comp
      ((sumAssoc In Mid Out).comp
        (((ofSumFamily In Mid).par (OracleMap.id Out)).comp
          (ofSumFamily (sumFamily In Mid) Out))))

/-- Inverse family reassociation through the resource reassociation and representation bridges. -/
def familySumAssocSymm (In : OracleFamily.{uI, u, w} I A) (Mid : OracleFamily.{uJ, u, w} J B)
    (Out : OracleFamily.{uK, u, w} K C) :
    OracleMap (sumFamily In (sumFamily Mid Out)) (sumFamily (sumFamily In Mid) Out) :=
  (toSumFamily (sumFamily In Mid) Out).comp
    (((toSumFamily In Mid).par (OracleMap.id Out)).comp
      ((sumAssocSymm In Mid Out).comp
        (((OracleMap.id In).par (ofSumFamily Mid Out)).comp
          (ofSumFamily In (sumFamily Mid Out)))))

end Families

end OracleMap

/-- Route the oracle messages of an appended path into its two completed component paths. -/
def oracleMessageFamily_append : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) →
    (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    OracleMap (sumFamily (oracleMessageFamily s₁ p₁) (oracleMessageFamily (s₂ p₁) p₂))
      (oracleMessageFamily (s₁.append s₂) (Path.append s₁ s₂ p₁ p₂))
  | .pure _, s₂, ⟨⟩, p₂ =>
    OracleMap.embedding (sumFamily (oracleMessageFamily (.pure PUnit.unit) ⟨⟩)
      (oracleMessageFamily (s₂ ⟨⟩) p₂)) Sum.inr
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracleMessageFamily_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracleMessageFamily_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.oracle _ I) next, s₂, ⟨x, p₁⟩, p₂ =>
    ((OracleMap.embedding (singletonFamily I) id).sum
      (oracleMessageFamily_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂)).comp
      (OracleMap.familySumAssoc (singletonFamily I) (oracleMessageFamily (next x) p₁)
        (oracleMessageFamily (s₂ ⟨x, p₁⟩) p₂))

/-- Route either component's oracle queries into the completed appended path. -/
def oracleMessageFamily_split : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) →
    (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    OracleMap (oracleMessageFamily (s₁.append s₂) (Path.append s₁ s₂ p₁ p₂))
      (sumFamily (oracleMessageFamily s₁ p₁) (oracleMessageFamily (s₂ p₁) p₂))
  | .pure _, s₂, ⟨⟩, p₂ =>
    { f := fun x => sumData (fun i => i.elim) x
      impl := fun
        | ⟨.inl i, _⟩ => i.elim
        | ⟨.inr i, q⟩ => (liftM ((oracleMessageFamily (s₂ ⟨⟩) p₂).spec.query ⟨i, q⟩) :
        OracleComp (oracleMessageFamily (s₂ ⟨⟩) p₂).spec _)
      law := fun _ q => by
        rcases q with ⟨i | i, q⟩
        · exact i.elim
        · rfl }
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracleMessageFamily_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracleMessageFamily_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.oracle _ I) next, s₂, ⟨x, p₁⟩, p₂ =>
    (OracleMap.familySumAssocSymm (singletonFamily I) (oracleMessageFamily (next x) p₁)
      (oracleMessageFamily (s₂ ⟨x, p₁⟩) p₂)).comp
      ((OracleMap.embedding (singletonFamily I) id).sum
        (oracleMessageFamily_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂))

/-- Materializing the append route and then splitting it recovers both component families. -/
theorem oracleMessageFamily_split_append : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    (x : ∀ i,
      (sumFamily (oracleMessageFamily s₁ p₁) (oracleMessageFamily (s₂ p₁) p₂)).Realization i) →
    (oracleMessageFamily_split s₁ s₂ p₁ p₂).f ((oracleMessageFamily_append s₁ s₂ p₁ p₂).f x) = x
  | .pure _, _, ⟨⟩, _, _ => by
    funext i
    rcases i with i | i
    · exact i.elim
    · rfl
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracleMessageFamily_split_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracleMessageFamily_split_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.oracle _ _) next, s₂, ⟨x, p₁⟩, p₂, data => by
    have ih := oracleMessageFamily_split_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
      (sumData (fun i => data (.inl (.inr i))) (fun i => data (.inr i)))
    funext i
    rcases i with (i | i) | i
    · rfl
    · exact congrFun ih (.inl i)
    · exact congrFun ih (.inr i)

/-- Splitting and recombining an appended family preserves every concrete oracle message. -/
theorem oracleMessageFamily_append_split : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    (x : ∀ i, OracleMessage (s₁.append s₂) (Path.append s₁ s₂ p₁ p₂) i) →
    (oracleMessageFamily_append s₁ s₂ p₁ p₂).f ((oracleMessageFamily_split s₁ s₂ p₁ p₂).f x) = x
  | .pure _, _, ⟨⟩, _, _ => rfl
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracleMessageFamily_append_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracleMessageFamily_append_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.oracle _ _) next, s₂, ⟨x, p₁⟩, p₂, data => by
    have ih := oracleMessageFamily_append_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
      (fun i => data (.inr i))
    funext i
    cases i with
    | inl i => rfl
    | inr i =>
      change (oracleMessageFamily_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f
        (sumData
          (fun j => (oracleMessageFamily_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f
            (fun k => data (.inr k)) (.inl j))
          (fun j => (oracleMessageFamily_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f
            (fun k => data (.inr k)) (.inr j))) i = data (.inr i)
      exact (congrArg (fun d =>
        (oracleMessageFamily_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f d i)
        (sumData_eta ((oracleMessageFamily_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f
          (fun k => data (.inr k))))).trans (congrFun ih i)

/-- A completed shape paired with the oracle messages at its oracle nodes. -/
abbrev PathWithOracleMessages (s : OracleProtocol.{u, q}) :=
  (p : Path s) × (∀ i, OracleMessage s p i)

/-- Prepend one full move to a materialized path. -/
def PathWithOracleMessages.prepend : (a : OraclePos.{u, q}) →
    (next : OraclePoly.B a → OracleProtocol) →
    (x : Move oracleSig a) → PathWithOracleMessages (next (oracleSig.toFunB a x)) →
      PathWithOracleMessages (.liftBind a next)
  | .message _, _, x, ⟨p, data⟩ => ⟨⟨x, p⟩, data⟩
  | .challenge _, _, _, ⟨p, data⟩ => ⟨⟨⟨⟩, p⟩, data⟩
  | .oracle _ _, _, x, ⟨p, data⟩ => ⟨⟨⟨⟩, p⟩, sumData (fun _ => x) data⟩

/-- Appending full transcripts materializes exactly the two routed oracle message families. -/
theorem oracleMessages_append : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (tr₁ : Transcript oracleSig s₁) →
    (tr₂ : Transcript oracleSig (s₂ tr₁.path)) →
    (⟨Transcript.path (Transcript.append s₁ s₂ tr₁ tr₂),
      oracleMessages (s₁.append s₂) (Transcript.append s₁ s₂ tr₁ tr₂)⟩ :
        PathWithOracleMessages (s₁.append s₂)) =
      ⟨Path.append s₁ s₂ tr₁.path tr₂.path,
        (oracleMessageFamily_append s₁ s₂ tr₁.path tr₂.path).f
          (sumData (oracleMessages s₁ tr₁) (oracleMessages _ tr₂))⟩
  | .pure _, _, ⟨⟩, _ => rfl
  | .liftBind (.message _) next, s₂, ⟨x, tr₁⟩, tr₂ =>
    congrArg (PathWithOracleMessages.prepend (.message _) (fun b =>
      (next b).append (fun p => s₂ ⟨b, p⟩)) x)
      (oracleMessages_append (next x) (fun p => s₂ ⟨x, p⟩) tr₁ tr₂)
  | .liftBind (.challenge _) next, s₂, ⟨x, tr₁⟩, tr₂ =>
    congrArg (PathWithOracleMessages.prepend (.challenge _) (fun b =>
      (next b).append (fun p => s₂ ⟨b, p⟩)) x)
      (oracleMessages_append (next ⟨⟩) (fun p => s₂ ⟨⟨⟩, p⟩) tr₁ tr₂)
  | .liftBind (.oracle _ I) next, s₂, ⟨x, tr₁⟩, tr₂ => by
    have h := congrArg (PathWithOracleMessages.prepend (.oracle _ I) (fun b =>
      (next b).append (fun p => s₂ ⟨b, p⟩)) x)
      (oracleMessages_append (next ⟨⟩) (fun p => s₂ ⟨⟨⟩, p⟩) tr₁ tr₂)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Sigma.ext (by rfl) ?_
      apply heq_of_eq
      funext i
      cases i <;> rfl
    · rfl

/-- The appended transcript's handler agrees with routing into its component handlers. -/
theorem oracleMessageImpl_append (s₁ : OracleProtocol.{u, q})
    (s₂ : Path s₁ → OracleProtocol.{u, q}) (tr₁ : Transcript oracleSig s₁)
    (tr₂ : Transcript oracleSig (s₂ tr₁.path)) :
    (⟨Transcript.path (Transcript.append s₁ s₂ tr₁ tr₂),
      oracleMessageImpl (s₁.append s₂) (Transcript.append s₁ s₂ tr₁ tr₂)⟩ :
      (p : Path (s₁.append s₂)) × QueryImpl (oracleMessageSpec (s₁.append s₂) p) Id) =
    ⟨Path.append s₁ s₂ tr₁.path tr₂.path,
      QueryImpl.compose
        ((sumFamily (oracleMessageFamily s₁ tr₁.path)
          (oracleMessageFamily _ tr₂.path)).behaviorOfRealizations
            (sumData (oracleMessages s₁ tr₁) (oracleMessages _ tr₂)))
        (oracleMessageFamily_append s₁ s₂ tr₁.path tr₂.path).impl⟩ := by
  have h := congrArg
    (fun d : PathWithOracleMessages (s₁.append s₂) =>
      (⟨d.1, (oracleMessageFamily (s₁.append s₂) d.1).behaviorOfRealizations d.2⟩ :
        (p : Path (s₁.append s₂)) × QueryImpl (oracleMessageSpec (s₁.append s₂) p) Id))
    (oracleMessages_append s₁ s₂ tr₁ tr₂)
  refine h.trans ?_
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact (funext ((oracleMessageFamily_append s₁ s₂ _ _).law _)).symm

/-- The resources a decision at path `p` may query: the input resources and the path
oracle messages. Input data may lie in a universe independent of responses and moves. Input queries
and oracle-node queries also have independent universes. -/
abbrev pathResources (inputs : Resources.{u, uI, dI})
    (s : OracleProtocol.{u, q}) (p : Path s) :=
  Resources.sum inputs (Resources.ofFamily (oracleMessageFamily s p))

/-- A passive oracle verifier. The output statement type `T p` and the output oracle family
`outputs p` are indexed by the public shape path `p` of the run, so a public message may change
both. A verifier with one output type and family uses constant families. -/
structure OracleVerifier {ι : Type uι} (ambient : OracleSpec.{uι, u} ι)
    (s : OracleProtocol.{u, q}) (S : Type uS) (T : Path s → Type u)
    {J : Path s → Type uJ} {B : (p : Path s) → J p → Type u}
    (inputs : Resources.{u, uI, dI})
    (outputs : (p : Path s) → OracleFamily.{uJ, u, wJ} (J p) (B p)) where
  /-- The decision has query access to inputs and path oracle messages, never their raw values. -/
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

/-- Interpret the decision's resource queries using the input and the oracle messages of the
actual run. -/
def OracleVerifier.run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : OracleProtocol.{u, q}} {S : Type uS} {T : Path s → Type u}
    {J : Path s → Type u} {B : (p : Path s) → J p → Type u}
    {inputs : Resources.{u, uI, dI}}
    {outputs : (p : Path s) → OracleFamily.{u, u, wJ} (J p) (B p)}
    {Out : Transcript oracleSig s → Type u}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s)
      (Outcome oracleSig s Out (OracleVerifier.Output T B)) := do
  let ⟨tr, out, _⟩ ← TwoParty.Lens.run s
    (prover.simulate (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))))
    (sampler oracleSig s (fun c =>
      liftM ((ambient + challengeSpec oracleSig s).query (.inr c))))
  let p := Transcript.path tr
  let view := toView s tr
  let resources : (pathResources inputs s p).Data := (data, oracleMessages s tr)
  let verdict ← simulateQ
    (QueryImpl.addLift
      ((fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) :
        QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)))
      ((pathResources inputs s p).answer resources))
    (V.decide stmt p view).run
  pure ⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f resources)⟩

end Interaction.Core
