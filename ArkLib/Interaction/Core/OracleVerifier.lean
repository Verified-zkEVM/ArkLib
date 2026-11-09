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

universe u

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle

-- Reduce the shape projection when the payload family descends to a child.
attribute [local implicit_reducible] projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun

/-- The oracle nodes on a completed shape path. -/
@[implicit_reducible]
def oracleIdx : (s : OracleProtocol.{u}) → Path s → Type u
  | .pure _, _ => PEmpty
  | .liftBind (.message _) next, ⟨x, p⟩ => oracleIdx (next x) p
  | .liftBind (.challenge _) next, ⟨x, p⟩ => oracleIdx (next x) p
  | .liftBind (.oracle _ _) next, ⟨x, p⟩ => PUnit ⊕ oracleIdx (next x) p

/-- Concrete data carriers of the oracle nodes on a completed path. -/
@[implicit_reducible]
def OracleData : (s : OracleProtocol.{u}) → (p : Path s) → oracleIdx s p → Type u
  | .pure _, _ => fun i => i.elim
  | .liftBind (.message _) next, ⟨x, p⟩ => OracleData (next x) p
  | .liftBind (.challenge _) next, ⟨x, p⟩ => OracleData (next x) p
  | .liftBind (.oracle X _) next, ⟨x, p⟩ =>
    Sum.elim (fun _ => X) (OracleData (next x) p)

/-- Independent families of concrete data, with disjoint query access. -/
@[implicit_reducible]
def sumFamily {I J : Type u} {A : I → Type u} {B : J → Type u}
    (a : OracleFamily.{u, u, u} I A) (b : OracleFamily.{u, u, u} J B) :
    OracleFamily (I ⊕ J) (Sum.elim A B) :=
  ⟨fun | .inl i => a.interface i | .inr j => b.interface j⟩

/-- The family consisting of one oracle payload. -/
@[implicit_reducible]
def singletonFamily {X : Type u} (I : OracleInterface.{u, u} X) :
    OracleFamily.{u, u, u} PUnit (fun _ => X) := ⟨fun _ => I⟩

/-- The concrete oracle family at a completed path. -/
@[implicit_reducible]
def pathFamily : (s : OracleProtocol.{u}) → (p : Path s) →
    OracleFamily (oracleIdx s p) (OracleData s p)
  | .pure _, _ => ⟨fun i => i.elim⟩
  | .liftBind (.message _) next, ⟨x, p⟩ => pathFamily (next x) p
  | .liftBind (.challenge _) next, ⟨x, p⟩ => pathFamily (next x) p
  | .liftBind (.oracle _ I) next, ⟨x, p⟩ =>
    sumFamily (singletonFamily I) (pathFamily (next x) p)

/-- Queries to the oracle nodes on a completed path. -/
abbrev oracles (s : OracleProtocol.{u}) (p : Path s) := (pathFamily s p).spec

/-- Read the concrete payloads from exactly the full transcript that produced this shape. -/
def payloads : (s : OracleProtocol.{u}) → (tr : PathAlong oracleSig s) →
    (i : oracleIdx s (projectPathAlong oracleSig s tr)) →
      OracleData s (projectPathAlong oracleSig s tr) i
  | .pure _, _, i => i.elim
  | .liftBind (.message _) next, ⟨x, tr⟩, i => payloads (next x) tr i
  | .liftBind (.challenge _) next, ⟨_, tr⟩, i => payloads (next ⟨⟩) tr i
  | .liftBind (.oracle _ _) _, ⟨x, _⟩, .inl _ => x
  | .liftBind (.oracle _ _) next, ⟨_, tr⟩, .inr i => payloads (next ⟨⟩) tr i

/-- The sole payload handler used by execution answers from the completed run. -/
def payloadImpl (s : OracleProtocol.{u}) (tr : PathAlong oracleSig s) :
    QueryImpl (oracles s (projectPathAlong oracleSig s tr)) Id :=
  (pathFamily s (projectPathAlong oracleSig s tr)).behaviorOfRealizations (payloads s tr)

/-- Pair the data of two disjoint families. -/
def sumData {I J : Type u} {A : I → Type u} {B : J → Type u}
    (a : ∀ i, A i) (b : ∀ j, B j) : ∀ k, Sum.elim A B k
  | .inl i => a i
  | .inr j => b j

/-- Reassembling disjoint data from its two restrictions is the identity. -/
theorem sumData_eta {I J : Type u} {A : I → Type u} {B : J → Type u}
    (x : ∀ k, Sum.elim A B k) :
    sumData (fun i => x (.inl i)) (fun j => x (.inr j)) = x := by
  funext k
  cases k <;> rfl

/-- A concrete oracle map and its query-by-query implementation agree on all input data. -/
structure OracleMap {I J : Type u} {A : I → Type u} {B : J → Type u}
    (In : OracleFamily.{u, u, u} I A) (Out : OracleFamily.{u, u, u} J B) where
  /-- Concrete output data, available to a subsequent honest prover. -/
  f : (∀ i, A i) → (∀ j, B j)
  /-- Output queries are simulated using only input oracle queries. -/
  impl : QueryImpl Out.spec (OracleComp In.spec)
  /-- Simulation answers exactly as the materialized output data. -/
  law : ∀ x q, simulateQ (In.behaviorOfRealizations x) (impl q) =
    Out.behaviorOfRealizations (f x) q

namespace OracleMap
variable {I J K : Type u} {A : I → Type u} {B : J → Type u} {C : K → Type u}
  {In : OracleFamily.{u, u, u} I A} {Mid : OracleFamily.{u, u, u} J B}
  {Out : OracleFamily.{u, u, u} K C}

/-- Embeddings are oracle maps that retain or rename existing input slots. -/
def embedding (In : OracleFamily.{u, u, u} I A) (rename : J → I) :
    OracleMap In (In.reindex rename) where
  f x j := x (rename j)
  impl q := liftM (In.spec.query ⟨rename q.1, q.2⟩)
  law _ _ := rfl

/-- Compose concrete data maps and substitute query implementations. -/
def comp (g : OracleMap Mid Out) (h : OracleMap In Mid) : OracleMap In Out where
  f := g.f ∘ h.f
  impl := QueryImpl.compose h.impl g.impl
  law x q := by
    rw [QueryImpl.apply_compose, ← QueryImpl.simulateQ_compose]
    have he : QueryImpl.compose (In.behaviorOfRealizations x) h.impl =
        Mid.behaviorOfRealizations (h.f x) := funext (h.law x)
    rw [he]
    exact g.law (h.f x) q

/-- Routing every query through a map agrees with materializing its output first. -/
theorem simulate_eq (h : OracleMap In Out) (x : ∀ i, A i)
    {α : Type u} (program : OracleComp Out.spec α) :
    simulateQ (In.behaviorOfRealizations x) (simulateQ h.impl program) =
      simulateQ (Out.behaviorOfRealizations (h.f x)) program :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (h.law x) program

/-- Apply two oracle maps to disjoint resources. -/
def sum {L : Type u} {D : L → Type u} {Other : OracleFamily.{u, u, u} L D}
    (h : OracleMap In Mid) (g : OracleMap Out Other) :
    OracleMap (sumFamily In Out) (sumFamily Mid Other) where
  f x := sumData (h.f (fun i => x (.inl i))) (g.f (fun j => x (.inr j)))
  impl
    | ⟨.inl j, q⟩ => simulateQ
      (fun r => liftM ((sumFamily In Out).spec.query ⟨.inl r.1, r.2⟩)) (h.impl ⟨j, q⟩)
    | ⟨.inr j, q⟩ => simulateQ
      (fun r => liftM ((sumFamily In Out).spec.query ⟨.inr r.1, r.2⟩)) (g.impl ⟨j, q⟩)
  law x q := by
    rcases q with ⟨j, q⟩
    cases j with
    | inl j =>
      exact (QueryImpl.simulateQ_simulateQ_eq_of_apply
        (impl := In.behaviorOfRealizations (fun i => x (.inl i)))
        (fun _ => rfl) (h.impl ⟨j, q⟩)).trans (h.law _ _)
    | inr j =>
      exact (QueryImpl.simulateQ_simulateQ_eq_of_apply
        (impl := Out.behaviorOfRealizations (fun i => x (.inr i)))
        (fun _ => rfl) (g.impl ⟨j, q⟩)).trans (g.law _ _)

/-- Reassociate disjoint resources without changing their data or answers. -/
def assoc (In : OracleFamily.{u, u, u} I A) (Mid : OracleFamily.{u, u, u} J B)
    (Out : OracleFamily.{u, u, u} K C) :
    OracleMap (sumFamily (sumFamily In Mid) Out) (sumFamily In (sumFamily Mid Out)) where
  f x := sumData (fun i => x (.inl (.inl i)))
    (sumData (fun j => x (.inl (.inr j))) (fun k => x (.inr k)))
  impl
    | ⟨.inl i, q⟩ => liftM ((sumFamily (sumFamily In Mid) Out).spec.query ⟨.inl (.inl i), q⟩)
    | ⟨.inr (.inl j), q⟩ =>
      liftM ((sumFamily (sumFamily In Mid) Out).spec.query ⟨.inl (.inr j), q⟩)
    | ⟨.inr (.inr k), q⟩ =>
      liftM ((sumFamily (sumFamily In Mid) Out).spec.query ⟨.inr k, q⟩)
  law x q := by rcases q with ⟨i | (j | k), q⟩ <;> rfl

/-- The inverse reassociation of disjoint resources. -/
def unassoc (In : OracleFamily.{u, u, u} I A) (Mid : OracleFamily.{u, u, u} J B)
    (Out : OracleFamily.{u, u, u} K C) :
    OracleMap (sumFamily In (sumFamily Mid Out)) (sumFamily (sumFamily In Mid) Out) where
  f x := sumData (sumData (fun i => x (.inl i)) (fun j => x (.inr (.inl j))))
    (fun k => x (.inr (.inr k)))
  impl
    | ⟨.inl (.inl i), q⟩ =>
      liftM ((sumFamily In (sumFamily Mid Out)).spec.query ⟨.inl i, q⟩)
    | ⟨.inl (.inr j), q⟩ =>
      liftM ((sumFamily In (sumFamily Mid Out)).spec.query ⟨.inr (.inl j), q⟩)
    | ⟨.inr k, q⟩ =>
      liftM ((sumFamily In (sumFamily Mid Out)).spec.query ⟨.inr (.inr k), q⟩)
  law x q := by rcases q with ⟨(i | j) | k, q⟩ <;> rfl

end OracleMap

/-- Route the oracles of an appended path into its two completed component paths. -/
def oracles_append : (s₁ : OracleProtocol.{u}) → (s₂ : Path s₁ → OracleProtocol.{u}) →
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
def oracles_split : (s₁ : OracleProtocol.{u}) → (s₂ : Path s₁ → OracleProtocol.{u}) →
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
theorem oracles_split_append : (s₁ : OracleProtocol.{u}) →
    (s₂ : Path s₁ → OracleProtocol.{u}) → (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
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
theorem oracles_append_split : (s₁ : OracleProtocol.{u}) →
    (s₂ : Path s₁ → OracleProtocol.{u}) → (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
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
abbrev PathData (s : OracleProtocol.{u}) := (p : Path s) × (∀ i, OracleData s p i)

/-- Prepend one full move to a materialized path. -/
def PathData.prepend : (a : OraclePos.{u}) → (next : OraclePoly.B a → OracleProtocol) →
    (x : Move oracleSig a) → PathData (next (oracleSig.toFunB a x)) →
      PathData (.liftBind a next)
  | .message _, _, x, ⟨p, data⟩ => ⟨⟨x, p⟩, data⟩
  | .challenge _, _, _, ⟨p, data⟩ => ⟨⟨⟨⟩, p⟩, data⟩
  | .oracle _ _, _, x, ⟨p, data⟩ => ⟨⟨⟨⟩, p⟩, sumData (fun _ => x) data⟩

/-- Appending full transcripts materializes exactly the two routed payload families. -/
theorem payloads_append : (s₁ : OracleProtocol.{u}) →
    (s₂ : Path s₁ → OracleProtocol.{u}) → (tr₁ : PathAlong oracleSig s₁) →
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
theorem payloadImpl_append (s₁ : OracleProtocol.{u})
    (s₂ : Path s₁ → OracleProtocol.{u}) (tr₁ : PathAlong oracleSig s₁)
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

/-- A passive oracle verifier with one fixed output oracle family. -/
structure OracleVerifier {ι I J : Type u} (ambient : OracleSpec.{u, u} ι)
    (s : OracleProtocol.{u}) (S T : Type u) {A : I → Type u} {B : J → Type u}
    (inputs : OracleFamily.{u, u, u} I A) (outputs : OracleFamily.{u, u, u} J B) where
  /-- The decision has query access to inputs and path payloads, never their raw values. -/
  decide : S → (p : Path s) → View s p →
    OptionT (OracleComp (ambient + (sumFamily inputs (pathFamily s p)).spec)) T
  /-- The output interface may use the public statement and verifier view. -/
  outputMap : S → (p : Path s) → View s p →
    OracleMap (sumFamily inputs (pathFamily s p)) outputs

/-- Interpret the decision's resource queries using the input and the actual run's payloads. -/
def OracleVerifier.run {ι I J : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : OracleProtocol.{u}} {S T : Type u} {A : I → Type u} {B : J → Type u}
    {inputs : OracleFamily.{u, u, u} I A} {outputs : OracleFamily.{u, u, u} J B}
    {Out : PathAlong oracleSig s → Type u}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : ∀ i, A i)
    (prover : Prover oracleSig ambient s Out) :
    OracleComp (ambient + challengeSpec oracleSig s)
      (Observation oracleSig s Out (T × (∀ j, B j))) := do
  let ⟨tr, out, _⟩ ← TwoParty.Lens.run s
    (prover.simulate (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))))
    (sampler oracleSig s (fun c =>
      liftM ((ambient + challengeSpec oracleSig s).query (.inr c))))
  let p := projectPathAlong oracleSig s tr
  let view := toView s tr
  let resources := sumData data (payloads s tr)
  let verdict ← simulateQ
    (QueryImpl.addLift
      ((fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) :
        QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)))
      ((sumFamily inputs (pathFamily s p)).behaviorOfRealizations resources))
    (V.decide stmt p view).run
  pure ⟨tr, out, verdict.map fun t => (t, (V.outputMap stmt p view).f resources)⟩

end Interaction.Core
