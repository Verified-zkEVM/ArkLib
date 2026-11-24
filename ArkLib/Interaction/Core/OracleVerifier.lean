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

universe v v' uκ uρ

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

/-- An oracle bundle: a query specification and the concrete data that answers it. The query
indices and the data may lie in any universe; only the responses lie in `Type u`, the universe of
the computations that receive them. The universe parameters of `OracleBundle.{u, uX, dX}` are
those of the responses, the query indices and the data, in this order. -/
structure OracleBundle : Type (max (uX + 1) (u + 1) (dX + 1)) where
  /-- The query indices. -/
  Index : Type uX
  /-- The queries and their response types. -/
  spec : OracleSpec.{uX, u} Index
  /-- The concrete data. -/
  Data : Type dX
  /-- How concrete data answers each query. -/
  answer : Data → QueryImpl spec Id

/-- The oracle bundle of an oracle family: queries through its interfaces, answered from concrete
realizations. The query universe `wI` of the interfaces is independent of the response universe.
-/
@[reducible] def OracleBundle.ofFamily {I : Type uI} {A : I → Type u}
    (F : OracleFamily.{uI, u, wI} I A) : OracleBundle.{u, max uI wI, max uI u} where
  Index := (i : I) × (F.interface i).Query
  spec := F.spec
  Data := ∀ i, A i
  answer := F.behaviorOfRealizations

attribute [coe] OracleBundle.ofFamily

/-- An oracle family is used as an oracle bundle through its interfaces. -/
instance {I : Type uI} {A : I → Type u} :
    CoeOut (OracleFamily.{uI, u, wI} I A) OracleBundle.{u, max uI wI, max uI u} :=
  ⟨OracleBundle.ofFamily⟩

/-- A sum bundle: each query goes to one side and is answered from that side's data. The
two sides keep their own index and data universes, and their data stays a pair. -/
@[reducible] def OracleBundle.sum (R : OracleBundle.{u, uX, dX}) (R' : OracleBundle.{u, uY, dY}) :
    OracleBundle.{u, max uX uY, max dX dY} where
  Index := R.Index ⊕ R'.Index
  spec := R.spec + R'.spec
  Data := R.Data × R'.Data
  answer x := R.answer x.1 + R'.answer x.2

/-- A concrete oracle map and its query-by-query implementation agree on all input data. -/
structure OracleMap (In : OracleBundle.{u, uX, dX}) (Out : OracleBundle.{u, uY, dY}) where
  /-- Concrete output data, available to a subsequent honest prover. -/
  f : In.Data → Out.Data
  /-- Output queries are simulated using only input oracle queries. -/
  impl : QueryImpl Out.spec (OracleComp In.spec)
  /-- Simulation answers exactly as the materialized output data. -/
  law : ∀ x q, simulateQ (In.answer x) (impl q) = Out.answer (f x) q

namespace OracleMap

section OracleBundle
variable {In : OracleBundle.{u, uX, dX}} {Mid : OracleBundle.{u, uY, dY}}
  {Out : OracleBundle.{u, uZ, dZ}} {Other : OracleBundle.{u, uW, dW}}

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

/-- The identity map of an oracle bundle. -/
def id (R : OracleBundle.{u, uX, dX}) : OracleMap R R where
  f x := x
  impl q := liftM (R.spec.query q)
  law _ _ := rfl

/-- Keep the left side of a sum bundle. -/
def fst (R : OracleBundle.{u, uX, dX}) (R' : OracleBundle.{u, uY, dY}) :
    OracleMap (R.sum R') R where
  f x := x.1
  impl q := liftM ((R.spec + R'.spec).query (.inl q))
  law _ _ := rfl

/-- Keep the right side of a sum bundle. -/
def snd (R : OracleBundle.{u, uX, dX}) (R' : OracleBundle.{u, uY, dY}) :
    OracleMap (R.sum R') R' where
  f x := x.2
  impl q := liftM ((R.spec + R'.spec).query (.inr q))
  law _ _ := rfl

/-- Apply two oracle maps to the two sides of a sum bundle. -/
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

/-- Regroup a sum bundle to the left without changing its data or answers. -/
def sumAssocSymm (R₁ : OracleBundle.{u, uX, dX}) (R₂ : OracleBundle.{u, uY, dY})
    (R₃ : OracleBundle.{u, uZ, dZ}) : OracleMap (R₁.sum (R₂.sum R₃)) ((R₁.sum R₂).sum R₃) where
  f x := ((x.1, x.2.1), x.2.2)
  impl
    | .inl (.inl q) => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inl q))
    | .inl (.inr q) => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inr (.inl q)))
    | .inr q => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inr (.inr q)))
  law x q := by rcases q with (q | q) | q <;> rfl

/-- Regroup a sum bundle to the right without changing its data or answers. -/
def sumAssoc (R₁ : OracleBundle.{u, uX, dX}) (R₂ : OracleBundle.{u, uY, dY})
    (R₃ : OracleBundle.{u, uZ, dZ}) : OracleMap ((R₁.sum R₂).sum R₃) (R₁.sum (R₂.sum R₃)) where
  f x := (x.1.1, (x.1.2, x.2))
  impl
    | .inl q => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inl (.inl q)))
    | .inr (.inl q) => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inl (.inr q)))
    | .inr (.inr q) => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inr q))
  law x q := by rcases q with q | (q | q) <;> rfl

end OracleBundle

section Families
variable {I : Type uI} {J : Type uJ} {K : Type uK} {A : I → Type u} {B : J → Type u}
  {C : K → Type u}

/-- Embeddings are oracle maps that retain or rename existing input slots. -/
def embedding (In : OracleFamily.{uI, u, wI} I A) (rename : J → I) :
    OracleMap In (In.reindex rename) where
  f x j := x (rename j)
  impl q := liftM (In.spec.query ⟨rename q.1, q.2⟩)
  law _ _ := rfl

/-- View a family of disjoint data as a sum bundle, with its data split into a pair. -/
def ofSumFamily (a : OracleFamily.{uI, u, w} I A) (b : OracleFamily.{uJ, u, w} J B) :
    OracleMap (sumFamily a b) (OracleBundle.sum a b) where
  f x := (fun i => x (.inl i), fun j => x (.inr j))
  impl
    | .inl q => liftM ((sumFamily a b).spec.query ⟨.inl q.1, q.2⟩)
    | .inr q => liftM ((sumFamily a b).spec.query ⟨.inr q.1, q.2⟩)
  law x q := by rcases q with q | q <;> rfl

/-- Combine a sum bundle into a family, the inverse representation of `ofSumFamily`. -/
def toSumFamily (a : OracleFamily.{uI, u, w} I A) (b : OracleFamily.{uJ, u, w} J B) :
    OracleMap (OracleBundle.sum a b) (sumFamily a b) where
  f x := sumData x.1 x.2
  impl
    | ⟨.inl i, q⟩ => liftM ((OracleBundle.sum a b).spec.query (.inl ⟨i, q⟩))
    | ⟨.inr j, q⟩ => liftM ((OracleBundle.sum a b).spec.query (.inr ⟨j, q⟩))
  law x q := by rcases q with ⟨i | j, q⟩ <;> rfl

/-- Splitting and recombining a family recovers its concrete data. -/
theorem toSumFamily_ofSumFamily (a : OracleFamily.{uI, u, w} I A)
    (b : OracleFamily.{uJ, u, w} J B) (x : (OracleBundle.ofFamily (sumFamily a b)).Data) :
    (toSumFamily a b).f ((ofSumFamily a b).f x) = x := sumData_eta x

/-- Combining and splitting a sum bundle recovers both data components. -/
theorem ofSumFamily_toSumFamily (a : OracleFamily.{uI, u, w} I A)
    (b : OracleFamily.{uJ, u, w} J B) (x : (OracleBundle.sum a b).Data) :
    (ofSumFamily a b).f ((toSumFamily a b).f x) = x := rfl

variable {L : Type uL} {D : L → Type u} {In : OracleFamily.{uI, u, w} I A}
  {Mid : OracleFamily.{uJ, u, wJ} J B} {Out : OracleFamily.{uK, u, w} K C}
  {Other : OracleFamily.{uL, u, wJ} L D}

/-- Apply two oracle maps to the two parts of a family of disjoint data. -/
def sum (h : OracleMap In Mid) (g : OracleMap Out Other) :
    OracleMap (sumFamily In Out) (sumFamily Mid Other) :=
  (toSumFamily Mid Other).comp ((h.par g).comp (ofSumFamily In Out))

/-- A left-family query follows its component map and retains the left source occurrence. -/
theorem sum_impl_inl (h : OracleMap In Mid) (g : OracleMap Out Other)
    (j : J) (q : (Mid.interface j).Query) :
    (h.sum g).impl ⟨.inl j, q⟩ = simulateQ
      (fun r => liftM ((sumFamily In Out).spec.query ⟨.inl r.1, r.2⟩)) (h.impl ⟨j, q⟩) := by
  simp only [sum, comp, QueryImpl.apply_compose, toSumFamily, par]
  erw [simulateQ_spec_query]
  simp only [QueryImpl.apply_compose]
  exact QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) _

/-- A right-family query follows its component map and retains the right source occurrence. -/
theorem sum_impl_inr (h : OracleMap In Mid) (g : OracleMap Out Other)
    (j : L) (q : (Other.interface j).Query) :
    (h.sum g).impl ⟨.inr j, q⟩ = simulateQ
      (fun r => liftM ((sumFamily In Out).spec.query ⟨.inr r.1, r.2⟩)) (g.impl ⟨j, q⟩) := by
  simp only [sum, comp, QueryImpl.apply_compose, toSumFamily, par]
  erw [simulateQ_spec_query]
  simp only [QueryImpl.apply_compose]
  exact QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) _

/-- Reassociate family data through the bundle reassociation and representation bridges. -/
def familySumAssoc (In : OracleFamily.{uI, u, w} I A) (Mid : OracleFamily.{uJ, u, w} J B)
    (Out : OracleFamily.{uK, u, w} K C) :
    OracleMap (sumFamily (sumFamily In Mid) Out) (sumFamily In (sumFamily Mid Out)) :=
  (toSumFamily In (sumFamily Mid Out)).comp
    (((OracleMap.id In).par (toSumFamily Mid Out)).comp
      ((sumAssoc In Mid Out).comp
        (((ofSumFamily In Mid).par (OracleMap.id Out)).comp
          (ofSumFamily (sumFamily In Mid) Out))))

/-- Inverse family reassociation through the bundle reassociation and representation bridges. -/
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

/-- The bundle a decision at path `p` may query: the input bundle and the path
oracle messages. Input data may lie in a universe independent of responses and moves. Input queries
and oracle-node queries also have independent universes. -/
abbrev pathBundle (inputs : OracleBundle.{u, uI, dI})
    (s : OracleProtocol.{u, q}) (p : Path s) :=
  OracleBundle.sum inputs (OracleBundle.ofFamily (oracleMessageFamily s p))

/-- A passive oracle verifier. The output statement type `T p` and the output oracle family
`outputs p` are indexed by the public shape path `p` of the run, so a public message may change
both. A verifier with one output type and family uses constant families. -/
structure OracleVerifier {ι : Type uι} (ambient : OracleSpec.{uι, u} ι)
    (s : OracleProtocol.{u, q}) (S : Type uS) (T : Path s → Type u)
    {J : Path s → Type uJ} {B : (p : Path s) → J p → Type u}
    (inputs : OracleBundle.{u, uI, dI})
    (outputs : (p : Path s) → OracleFamily.{uJ, u, wJ} (J p) (B p)) where
  /-- The decision has query access to inputs and path oracle messages, never their raw values. -/
  decide : S → (p : Path s) → View s p →
    OptionT (OracleComp (ambient + (pathBundle inputs s p).spec)) (T p)
  /-- The output interface may use the public statement and verifier view. -/
  outputMap : S → (p : Path s) → View s p →
    OracleMap (pathBundle inputs s p) (OracleBundle.ofFamily (outputs p))

/-- The output statement paired with the concrete output oracle data, at each shape path. -/
abbrev OracleVerifier.Output {s : OracleProtocol.{u, q}} (T : Path s → Type u)
    {J : Path s → Type u} (B : (p : Path s) → J p → Type u) (p : Path s) : Type u :=
  T p × (∀ j, B p j)

/-- Lift the queries to the oracle nodes of a completed path into the query interface of a
decision on that path. Compiler inlining keeps the input family, which only fixes the query
interface, out of execution. -/
@[macro_inline]
def pathLift {ι : Type uι} {I : Type uI} (ambient : OracleSpec.{uι, u} ι) {A : I → Type u}
    (inputs : OracleFamily.{uI, u, wI} I A) {s : OracleProtocol.{u}} (p : Path s) :
    QueryImpl (oracleMessageSpec s p) (OracleComp (ambient + (pathBundle inputs s p).spec)) :=
  fun q => liftM ((ambient + (pathBundle inputs s p).spec).query
    (.inr (.inr q)))

/-- Lifted path-oracle queries, answered from input data and path oracle messages with ambient
queries answered in any lawful monad, are a pure computation of the path oracle messages: they
make no ambient query. -/
theorem simulateQ_pathLift {ι : Type uι} {I : Type uI}
    {ambient : OracleSpec.{uι, u} ι} {A : I → Type u}
    {inputs : OracleFamily.{uI, u, wI} I A} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (amb : QueryImpl ambient m) {s : OracleProtocol.{u}} (p : Path s) (x : ∀ i, A i)
    (pl : ∀ i, OracleMessage s p i) {α : Type u} (oa : OracleComp (oracleMessageSpec s p) α) :
    simulateQ (QueryImpl.addLift amb ((pathBundle inputs s p).answer (x, pl)))
        (simulateQ (pathLift ambient inputs p) oa) =
      (pure (simulateQ ((oracleMessageFamily s p).behaviorOfRealizations pl) oa) : m α) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := ((oracleMessageFamily s p).behaviorOfRealizations pl).liftTarget m)
    (fun t => ?_) oa).trans ?_
  · simp only [QueryImpl.addLift_def]
    exact QueryImpl.simulateQ_add_query_right _ _ _
  · rw [simulateQ_liftTarget]
    rfl

/-- The decision with bundle queries answered from concrete data; ambient queries remain.

Its possible results, with every ambient answer allowed, are the statements the decision can
return on that data and view.
-/
def OracleVerifier.decideWith {ι : Type uι} {ambient : OracleSpec.{uι, u} ι}
    {s : OracleProtocol.{u, q}} {S : Type uS} {T : Path s → Type u}
    {J : Path s → Type uJ} {B : (p : Path s) → J p → Type u}
    {inputs : OracleBundle.{u, uI, dI}}
    {outputs : (p : Path s) → OracleFamily.{uJ, u, wJ} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (p : Path s) (v : View s p)
    (data : (pathBundle inputs s p).Data) :
    OracleComp ambient (Option (T p)) :=
  simulateQ (QueryImpl.addLift (QueryImpl.id' ambient)
    ((pathBundle inputs s p).answer data)) (V.decide stmt p v).run

/-- Interpreting ambient queries after closing bundle queries agrees with closing them
together under the ambient handler. -/
theorem OracleVerifier.simulateQ_decideWith {ι : Type uι}
    {ambient : OracleSpec.{uι, u} ι} {s : OracleProtocol.{u, q}} {S : Type uS}
    {T : Path s → Type u}
    {J : Path s → Type uJ} {B : (p : Path s) → J p → Type u}
    {inputs : OracleBundle.{u, uI, dI}}
    {outputs : (p : Path s) → OracleFamily.{uJ, u, wJ} (J p) (B p)}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (V : OracleVerifier ambient s S T inputs outputs) (impl : QueryImpl ambient m)
    (stmt : S) (p : Path s) (v : View s p)
    (data : (pathBundle inputs s p).Data) :
    simulateQ impl (V.decideWith stmt p v data) =
      simulateQ (QueryImpl.addLift impl
        ((pathBundle inputs s p).answer data))
        (V.decide stmt p v).run := by
  unfold OracleVerifier.decideWith
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun q => ?_) _
  rcases q with q | q
  · simp [QueryImpl.addLift_def]
  · simp only [QueryImpl.addLift_def]
    change simulateQ impl (pure _) = pure _
    simp

/-- The shared execution mechanism: run PolyFun's interaction once through the supplied monad
layer, then interpret the final decision and close its output from the same transcript. -/
def OracleVerifier.executeWith {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : OracleProtocol.{u, q}} {S : Type uS} {T : Path s → Type u}
    {J : Path s → Type u} {B : (p : Path s) → J p → Type u}
    {inputs : OracleBundle.{u, uI, dI}}
    {outputs : (p : Path s) → OracleFamily.{u, u, wJ} (J p) (B p)}
    {Out : Transcript oracleSig s → Type u} {m : Type u → Type u} [Monad m]
    {ITrace : Type u} {DTrace : Path s → Type u}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (interpret : {A : Type u} → m A →
      OracleComp (ambient + challengeSpec oracleSig s) (A × ITrace))
    (prover : Focal oracleSig m s Out) (coins : Counterpart oracleSig m s (fun _ => PUnit))
    (decision : (p : Path s) → View s p → (pathBundle inputs s p).Data →
      OracleComp (ambient + challengeSpec oracleSig s) (Option (T p) × DTrace p)) :
    OracleComp (ambient + challengeSpec oracleSig s)
      ((obs : Outcome oracleSig s Out (OracleVerifier.Output T B)) ×
        ITrace × DTrace (Transcript.path obs.1)) := do
  let ⟨⟨tr, out, _⟩, trace⟩ ← interpret (TwoParty.Lens.run s prover coins)
  let p := Transcript.path tr
  let view := toView s tr
  let pathData : (pathBundle inputs s p).Data := (data, oracleMessages s tr)
  let (verdict, decisionTrace) ← decision p view pathData
  pure ⟨⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f pathData)⟩,
    trace, decisionTrace⟩

/-- Interpret the decision's bundle queries using the input and the oracle messages of the
actual run. -/
def OracleVerifier.run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : OracleProtocol.{u, q}} {S : Type uS} {T : Path s → Type u}
    {J : Path s → Type u} {B : (p : Path s) → J p → Type u}
    {inputs : OracleBundle.{u, uI, dI}}
    {outputs : (p : Path s) → OracleFamily.{u, u, wJ} (J p) (B p)}
    {Out : Transcript oracleSig s → Type u}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s)
      (Outcome oracleSig s Out (OracleVerifier.Output T B)) :=
  Sigma.fst <$> V.executeWith stmt data
    (ITrace := PUnit) (DTrace := fun _ => PUnit)
    (fun action => (fun result => (result, PUnit.unit)) <$> action)
    (prover.simulate (fun r => liftM ((ambient + challengeSpec oracleSig s).query (.inl r))))
    (sampler oracleSig s (fun c =>
      liftM ((ambient + challengeSpec oracleSig s).query (.inr c))))
    (fun p view pathData => (fun verdict => (verdict, PUnit.unit)) <$>
      simulateQ (QueryImpl.addLift
        ((fun r => liftM ((ambient + challengeSpec oracleSig s).query (.inl r))) :
          QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)))
        ((pathBundle inputs s p).answer pathData)) (V.decide stmt p view).run)

/-- The ordinary specialization exposes the familiar unlogged execution equation using only
functor and monad laws of the shared mechanism. -/
theorem OracleVerifier.run_eq {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : OracleProtocol.{u, q}} {S : Type uS} {T : Path s → Type u}
    {J : Path s → Type u} {B : (p : Path s) → J p → Type u}
    {inputs : OracleBundle.{u, uI, dI}}
    {outputs : (p : Path s) → OracleFamily.{u, u, wJ} (J p) (B p)}
    {Out : Transcript oracleSig s → Type u}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    V.run stmt data prover = (do
  let ⟨tr, out, _⟩ ← TwoParty.Lens.run s
    (prover.simulate (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))))
    (sampler oracleSig s (fun c =>
      liftM ((ambient + challengeSpec oracleSig s).query (.inr c))))
  let p := Transcript.path tr
  let view := toView s tr
  let pathData : (pathBundle inputs s p).Data := (data, oracleMessages s tr)
  let verdict ← simulateQ
    (QueryImpl.addLift
      ((fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) :
        QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)))
      ((pathBundle inputs s p).answer pathData))
    (V.decide stmt p view).run
  pure ⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f pathData)⟩
) := by
  simp [OracleVerifier.run, OracleVerifier.executeWith, _root_.map_bind, bind_map_left]

/-- A run is the interaction, then the decision answered from the input and the run's oracle
messages, with its ambient queries sent to the ambient part of the run's oracle. -/
theorem OracleVerifier.run_eq_decideWith {ι : Type u} {I : Type uI} {ambient : OracleSpec.{u, u} ι}
    {s : OracleProtocol.{u}} {S : Type uS} {T : Path s → Type u} {A : I → Type u}
    {J : Path s → Type u} {B : (p : Path s) → J p → Type u}
    {inputs : OracleFamily.{uI, u, wI} I A}
    {outputs : (p : Path s) → OracleFamily.{u, u, wJ} (J p) (B p)}
    {Out : Transcript oracleSig s → Type u}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (x : ∀ i, A i)
    (prover : Prover oracleSig ambient s Out) :
    V.run stmt x prover = (do
      let ⟨tr, out, _⟩ ← TwoParty.Lens.run s
        (prover.simulate fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q)))
        (sampler oracleSig s fun c => liftM ((ambient + challengeSpec oracleSig s).query (.inr c)))
      let verdict ← simulateQ
        (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q)) :
          QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)))
        (V.decideWith stmt _ (toView s tr) (x, oracleMessages s tr))
      pure ⟨tr, out, verdict.map fun t =>
        (t, (V.outputMap stmt _ (toView s tr)).f (x, oracleMessages s tr))⟩) := by
  rw [OracleVerifier.run_eq]
  refine bind_congr fun y => ?_
  obtain ⟨tr, o, ⟨⟩⟩ := y
  dsimp only
  exact congrArg (fun d => d >>= _)
    (OracleVerifier.simulateQ_decideWith V _ stmt _ (toView s tr)
      (x, oracleMessages s tr)).symm

section BundleAnswers

variable {ι : Type uι} {κ : Type uκ} {ρ : Type uρ} {α : Type u}
  {ambient : OracleSpec.{uι, u} ι} {chal : OracleSpec.{uκ, u} κ}
  {bundle : OracleSpec.{uρ, u} ρ}

/-- Answering bundle queries before interpretation agrees with interpreting them beside the
restricted ambient handler, for any lawful target monad. -/
theorem simulateQ_bundleAnswer {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (H : QueryImpl (ambient + chal) m) (answer : QueryImpl bundle Id)
    (program : OracleComp (ambient + bundle) α) :
    simulateQ H (simulateQ (QueryImpl.addLift
      ((fun q => liftM ((ambient + chal).query (.inl q))) :
        QueryImpl ambient (OracleComp (ambient + chal))) answer) program) =
      simulateQ (QueryImpl.addLift (fun q => H (.inl q)) answer) program := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun q => ?_) program
  rcases q with q | q
  · simp
  · exact simulateQ_pure _ _

/-- Deterministic bundle answers commute with adjoining any lifted challenge handler. -/
theorem simulateQ_addLift_bundleAnswer {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {n : Type u → Type v'} [MonadLiftT n m]
    (impl : QueryImpl ambient m) (draw : QueryImpl chal n) (answer : QueryImpl bundle Id)
    (program : OracleComp (ambient + bundle) α) :
    simulateQ (impl.addLift draw : QueryImpl (ambient + chal) m)
      (simulateQ (QueryImpl.addLift
        ((fun q => liftM ((ambient + chal).query (.inl q))) :
          QueryImpl ambient (OracleComp (ambient + chal))) answer) program) =
      simulateQ (impl.addLift answer : QueryImpl (ambient + bundle) m) program := by
  simpa using simulateQ_bundleAnswer (impl.addLift draw : QueryImpl (ambient + chal) m)
    answer program

end BundleAnswers

end Interaction.Core
