/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Relation.OracleInterface
import ArkLib.Relation.Basic
import ArkLib.Interaction.OracleVerifier
import ArkLib.Interaction.Oracle.BundleOps
import ArkLib.Interaction.Composition
import Mathlib.Data.ZMod.Basic

/-!
# Oracle consolidation prototype

Companion to `docs/design/interaction-layer/oracle-consolidation.md`.

- Part 1 defines the recommended consolidated API (Design D) in namespace `Consolidated`, at
  `Type` / `Type 1` with zero universe parameters per the post-step-5 universe policy.
- Part 2 checks the exact relationships (equivalences, `rfl` equalities, proof-only equalities,
  and failures recorded via `#guard_msgs`) between `Consolidated` and the current types
  (`OracleInterface`, `OracleContext`, `OracleFamily`, `OracleBundle`).
- Part 3 checks reducibility, typeclass synthesis, `toOracleSpec` semireducibility, Lean 4.28
  `.implicit` transparency (why `OracleInterface.answer` avoids `Id` and why `OracleBundle` keeps
  four flat fields), and `@[macro_inline]` compiler erasure for noncomputable input bundles.
- Part 4 elaborates realistic end-to-end examples (sums, tensors, indexed families, reindexing,
  derived behavior-only outputs, and two-stage passive verifier routing) with zero universe pins.

Check with `lake env lean docs/design/interaction-layer/prototypes/OracleConsolidation.lean`.
-/

set_option linter.dupNamespace false

/-! ## Part 1. Recommended design (Design D) at `Type` / `Type 1` -/

namespace Consolidated

open OracleComp OracleSpec PFunctor FreeM

/-- Policy alias for VCVio's empty oracle specification at `Type` (zero universe parameters). -/
abbrev emptySpec0 : OracleSpec.{0, 0} PEmpty.{1} := emptySpec.{0, 0}

/-- Typeclass providing a pure query interface for concrete oracle data in `Type`.
Flattens `OracleInterface` by dropping the `OracleContext` / `ReaderM` indirection.
Uses `(q : Query) → spec q` rather than `QueryImpl spec Id` so the non-reducible `Id` wrapper
never blocks typeclass synthesis in instance bodies (see Part 3). -/
@[ext]
class OracleInterface (Message : Type) : Type 1 where
  Query : Type
  spec : OracleSpec Query
  answer : Message → (q : Query) → spec q

namespace OracleInterface

/-- The response type at a query `q`. -/
abbrev Response {Message : Type} [O : OracleInterface Message] (q : O.Query) : Type :=
  O.spec q

/-- View `O.answer m` as a pure VCVio `QueryImpl` (holds by `rfl`). -/
@[reducible]
def answerImpl {Message : Type} [O : OracleInterface Message] (m : Message) :
    QueryImpl O.spec Id :=
  O.answer m

/-- Pointwise decidable response equality induces decidable answer equality. -/
instance instDecidablePredAnswerEq {Message : Type} [O : OracleInterface Message]
    [∀ q, DecidableEq (O.spec q)] (a b : Message) :
    DecidablePred (fun q => O.answer a q = O.answer b q) := fun q =>
  (inferInstance : DecidableEq (O.spec q)) (O.answer a q) (O.answer b q)

/-- Default trivial interface returning the whole message on `Unit`. Not registered as an
instance. -/
@[reducible]
def instDefault {Message : Type} : OracleInterface Message where
  Query := Unit
  spec := Unit →ₒ Message
  answer m _ := m

instance {Message : Type} : Inhabited (OracleInterface Message) := ⟨instDefault⟩

/-- Semireducible specification of an indexed family of interfaces (matches `[v]ₒ`). -/
def toOracleSpec {ι : Type} (v : ι → Type) [O : ∀ i, OracleInterface (v i)] :
    OracleSpec ((i : ι) × (O i).Query) :=
  fun q => (O q.1).Response q.2

/-- Canonical function interface. -/
@[reducible, inline]
instance instFunction {α β : Type} : OracleInterface (α → β) where
  Query := α
  spec := α →ₒ β
  answer f q := f q

/-- Disjoint-sum interface on products. Uses `QueryImpl.add` directly without `addReaderT`. -/
@[reducible, inline]
instance instProd {α β : Type} [Oα : OracleInterface α] [Oβ : OracleInterface β] :
    OracleInterface (α × β) where
  Query := Oα.Query ⊕ Oβ.Query
  spec := Oα.spec + Oβ.spec
  answer x := (Oα.answerImpl x.1 + Oβ.answerImpl x.2)

/-- Tensor interface on products (low priority). -/
@[reducible, inline]
instance (priority := low) instTensorProd {α β : Type}
    [Oα : OracleInterface α] [Oβ : OracleInterface β] : OracleInterface (α × β) where
  Query := Oα.Query × Oβ.Query
  spec := fun q => Oα.Response q.1 × Oβ.Response q.2
  answer x q := (Oα.answer x.1 q.1, Oβ.answer x.2 q.2)

/-- Disjoint-sum interface on dependent families. -/
@[reducible, inline]
instance instProdForall {ι : Type} (v : ι → Type) [O : ∀ i, OracleInterface (v i)] :
    OracleInterface (∀ i, v i) where
  Query := (i : ι) × (O i).Query
  spec := fun q => (O q.1).spec q.2
  answer x q := (O q.1).answer (x q.1) q.2

/-- Univariate polynomial evaluation oracle. -/
@[reducible, inline]
instance instPolynomial (R : Type) [CommSemiring R] : OracleInterface (Polynomial R) where
  Query := R
  spec := R →ₒ R
  answer p point := p.eval point

/-- Multivariate polynomial evaluation oracle (noncomputable via Mathlib `MvPolynomial.eval`). -/
noncomputable instance instMvPolynomial (R : Type) [CommSemiring R] (σ : Type) :
    OracleInterface (MvPolynomial σ R) where
  Query := σ → R
  spec := (σ → R) →ₒ R
  answer p points := MvPolynomial.eval points p

/-- Pure simulation handler for an indexed family of interfaces. -/
def simOracle0 {ι : Type} (T : ι → Type) [O : ∀ i, OracleInterface (T i)]
    (t : ∀ i, T i) : QueryImpl (toOracleSpec T) Id :=
  fun q => (O q.1).answer (t q.1) q.2

/-- Combined simulation handler matching legacy `simOracle2`. -/
def simOracle2 {ι : Type} (oSpec : OracleSpec ι)
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) :
    QueryImpl (oSpec + (toOracleSpec T₁ + toOracleSpec T₂)) (OracleComp oSpec) :=
  QueryImpl.addLift (QueryImpl.id oSpec)
    (QueryImpl.add (simOracle0 T₁ t₁) (simOracle0 T₂ t₂))

/-- Queries on which two messages agree. -/
def agreementQueries {Message : Type} (O : OracleInterface Message)
    [Fintype O.Query] [∀ q, DecidableEq (O.spec q)] (a b : Message) : Finset O.Query :=
  Finset.univ.filter fun q => O.answer a q = O.answer b q

/-- Oracle distance bound. -/
def distanceLE {Message : Type} (O : OracleInterface Message)
    [Fintype O.Query] [∀ q, DecidableEq (O.spec q)] (d : ℕ) : Prop :=
  ∀ a b : Message, a ≠ b → (O.agreementQueries a b).card ≤ d

end OracleInterface

/-- A bundled oracle: concrete backing data paired with its explicit query specification and
pure answer map. Keeps four flat fields so `B.Query`, `B.spec`, and `B.answer` never route
through semireducible class projections (see Part 3), while remaining definitionally equivalent
(`rfl` both ways) to `(Data : Type) × OracleInterface Data`. -/
structure OracleBundle : Type 1 where
  /-- The query index type. -/
  Query : Type
  /-- The query specification. -/
  spec : OracleSpec Query
  /-- The concrete data backing the oracle. -/
  Data : Type
  /-- How concrete data answers each query. -/
  answer : Data → QueryImpl spec Id

namespace OracleBundle

/-- Arbitrary deterministic answers, without a representability assumption. -/
abbrev Behavior (B : OracleBundle) : Type := QueryImpl B.spec Id

/-- View a bundle's query interface as an `OracleInterface B.Data`. Not registered as an instance
(a global instance concluding `OracleInterface ?B.Data` would trigger runaway synthesis). -/
@[reducible]
def toInterface (B : OracleBundle) : OracleInterface B.Data where
  Query := B.Query
  spec := B.spec
  answer := B.answer

/-- Package a data type and an explicit interface as an oracle bundle. -/
@[reducible]
def of (Data : Type) (I : OracleInterface Data) : OracleBundle where
  Query := I.Query
  spec := I.spec
  Data := Data
  answer := I.answer

/-- Package a data type using typeclass inference for its interface. -/
@[reducible]
def ofInst (Data : Type) [I : OracleInterface Data] : OracleBundle := of Data I

/-- The empty oracle bundle: `Unit` data and `Empty` queries. -/
@[reducible]
def empty : OracleBundle where
  Query := Empty
  spec := fun q => q.elim
  Data := Unit
  answer _ q := q.elim

/-- Disjoint sum of two oracle bundles. -/
@[reducible]
def sum (R S : OracleBundle) : OracleBundle where
  Query := R.Query ⊕ S.Query
  spec := R.spec + S.spec
  Data := R.Data × S.Data
  answer x := R.answer x.1 + S.answer x.2

/-- Tensor product of two oracle bundles: asks both queries and returns both answers. -/
@[reducible]
def tensor (R S : OracleBundle) : OracleBundle where
  Query := R.Query × S.Query
  spec := OracleSpec.ofPFunctor (PFunctor.tensor R.spec.toPFunctor S.spec.toPFunctor)
  Data := R.Data × S.Data
  answer x q := (R.answer x.1 q.1, S.answer x.2 q.2)

/-- Realize a specification by any pure handler, with no representability assumption. -/
@[reducible]
def ofSpec {I : Type} (spec : OracleSpec I) : OracleBundle where
  Query := I
  spec := spec
  Data := QueryImpl spec Id
  answer data := data

/-- Combine an indexed collection of oracle bundles into one bundle.
Replaces `OracleBundle.ofFamily` without needing a separate `OracleFamily` structure. -/
@[reducible]
def indexed {I : Type} (F : I → OracleBundle) : OracleBundle where
  Query := (i : I) × (F i).Query
  spec := fun q => (F q.1).spec q.2
  Data := ∀ i, (F i).Data
  answer data q := (F q.1).answer (data q.1) q.2

/-- Build an indexed bundle from a type family and per-slot interfaces (matches legacy `[A]ₒ`). -/
@[reducible]
def ofIndexed {I : Type} (A : I → Type) (O : ∀ i, OracleInterface (A i)) : OracleBundle :=
  indexed fun i => of (A i) (O i)

end OracleBundle

/-- A concrete data map paired with a query-by-query simulation and their agreement law. -/
structure OracleMap (In Out : OracleBundle) : Type where
  f : In.Data → Out.Data
  impl : QueryImpl Out.spec (OracleComp In.spec)
  law : ∀ x q, simulateQ (In.answer x) (impl q) = Out.answer (f x) q

namespace OracleMap

def comp {In Mid Out : OracleBundle} (g : OracleMap Mid Out) (h : OracleMap In Mid) :
    OracleMap In Out where
  f := g.f ∘ h.f
  impl := QueryImpl.compose h.impl g.impl
  law x q := by
    rw [QueryImpl.apply_compose, ← QueryImpl.simulateQ_compose]
    have he : QueryImpl.compose (In.answer x) h.impl = Mid.answer (h.f x) := funext (h.law x)
    rw [he]
    exact g.law (h.f x) q

theorem simulate_eq {In Out : OracleBundle} (h : OracleMap In Out) (x : In.Data)
    {α : Type} (program : OracleComp Out.spec α) :
    simulateQ (In.answer x) (simulateQ h.impl program) =
      simulateQ (Out.answer (h.f x)) program :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (h.law x) program

def id (R : OracleBundle) : OracleMap R R where
  f x := x
  impl q := liftM (R.spec.query q)
  law _ _ := rfl

@[macro_inline]
def fst (R S : OracleBundle) : OracleMap (R.sum S) R where
  f x := x.1
  impl q := liftM ((R.spec + S.spec).query (.inl q))
  law _ _ := rfl

def snd (R S : OracleBundle) : OracleMap (R.sum S) S where
  f x := x.2
  impl q := liftM ((R.spec + S.spec).query (.inr q))
  law _ _ := rfl

def emptyLeft (R : OracleBundle) : OracleMap R (OracleBundle.empty.sum R) where
  f x := ((), x)
  impl
    | .inl e => e.elim
    | .inr q => liftM (R.spec.query q)
  law _ q := by
    rcases q with e | q
    · exact e.elim
    · rfl

def par {In Mid Out Other : OracleBundle} (h : OracleMap In Mid) (g : OracleMap Out Other) :
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

def sumAssoc (R₁ R₂ R₃ : OracleBundle) :
    OracleMap ((R₁.sum R₂).sum R₃) (R₁.sum (R₂.sum R₃)) where
  f x := (x.1.1, (x.1.2, x.2))
  impl
    | .inl q => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inl (.inl q)))
    | .inr (.inl q) => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inl (.inr q)))
    | .inr (.inr q) => liftM (((R₁.spec + R₂.spec) + R₃.spec).query (.inr q))
  law _ q := by rcases q with q | (q | q) <;> rfl

def sumAssocSymm (R₁ R₂ R₃ : OracleBundle) :
    OracleMap (R₁.sum (R₂.sum R₃)) ((R₁.sum R₂).sum R₃) where
  f x := ((x.1, x.2.1), x.2.2)
  impl
    | .inl (.inl q) => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inl q))
    | .inl (.inr q) => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inr (.inl q)))
    | .inr q => liftM ((R₁.spec + (R₂.spec + R₃.spec)).query (.inr (.inr q)))
  law _ q := by rcases q with (q | q) | q <;> rfl

/-- Retain, project, or alias slots of an indexed bundle. Replaces `OracleMap.embedding`. -/
def reindex {I J : Type} (F : I → OracleBundle) (rename : J → I) :
    OracleMap (OracleBundle.indexed F) (OracleBundle.indexed (F ∘ rename)) where
  f x j := x (rename j)
  impl q := liftM ((OracleBundle.indexed F).spec.query ⟨rename q.1, q.2⟩)
  law _ _ := rfl

/-- A query program defines a behavior-only output bundle. -/
def ofImpl (R : OracleBundle) {J : Type} (spec : OracleSpec J)
    (query : QueryImpl spec (OracleComp R.spec)) :
    OracleMap R (OracleBundle.ofSpec spec) where
  f data q := simulateQ (R.answer data) (query q)
  impl := query
  law _ _ := rfl

/-- Preserve ambient queries while routing bundle queries through an oracle map. -/
def withAmbient {ι : Type} (ambient : OracleSpec ι) {In Out : OracleBundle}
    (route : OracleMap In Out) : QueryImpl (ambient + Out.spec) (OracleComp (ambient + In.spec))
  | .inl q => liftM ((ambient + In.spec).query (.inl q))
  | .inr q => simulateQ (fun r => liftM ((ambient + In.spec).query (.inr r))) (route.impl q)

theorem simulate_withAmbient {ι : Type} {ambient : OracleSpec ι} {In Out : OracleBundle}
    (route : OracleMap In Out) (x : In.Data) {α : Type}
    (program : OracleComp (ambient + Out.spec) α) :
    simulateQ (QueryImpl.addLift (QueryImpl.id' ambient) (In.answer x) :
        QueryImpl (ambient + In.spec) (OracleComp ambient))
        (simulateQ (route.withAmbient ambient) program) =
      simulateQ (QueryImpl.addLift (QueryImpl.id' ambient) (Out.answer (route.f x)) :
        QueryImpl (ambient + Out.spec) (OracleComp ambient)) program := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun q => ?_) program
  rcases q with q | q
  · simp [withAmbient]
  · simp only [withAmbient, QueryImpl.addLift_def]
    rw [QueryImpl.simulateQ_simulateQ_eq_of_apply
      (impl := (In.answer x).liftTarget (OracleComp ambient))
      (fun r => QueryImpl.simulateQ_add_query_right _ _ r), simulateQ_liftTarget, route.law]
    rfl

end OracleMap

/-! ### Minimal oracle protocol tree, path bundle, and passive verifier (all at `Type` / `Type 1`) -/

open Interaction.TwoParty.Lens

/-- Oracle positions at `Type 1`: carries `OracleInterface X` directly on the position (answers
D1's open point with empty `Γ`). -/
inductive OraclePos : Type 1 where
  | message (X : Type)
  | challenge (C : Type)
  | oracle (X : Type) (interface : OracleInterface X)

@[implicit_reducible]
def OraclePoly : PFunctor.{1, 0} :=
  ⟨OraclePos, fun | .message X => X | .challenge _ | .oracle _ _ => Unit⟩

@[implicit_reducible]
def oracleSig : PFunctor.Lens OraclePoly rolePoly.{0} where
  toFunA
    | .message X | .oracle X _ => (.sender, X)
    | .challenge C => (.receiver, C)
  toFunB
    | .message _ => id
    | .challenge _ | .oracle _ _ => fun _ => ()

@[implicit_reducible]
def viewSig : PFunctor.Lens OraclePoly rolePoly.{0} where
  toFunA
    | .message X => (.sender, X)
    | .challenge C => (.receiver, C)
    | .oracle _ _ => (.sender, Unit)
  toFunB
    | .message _ => id
    | .challenge _ | .oracle _ _ => fun _ => ()

abbrev OracleProtocol : Type 1 := FreeM OraclePoly Unit
abbrev Path (s : OracleProtocol) : Type := PFunctor.FreeM.Path s
abbrev View (s : OracleProtocol) (p : Path s) : Type :=
  Interaction.TranscriptAt viewSig s p

/-- The bundle of oracle messages on a completed path, built directly with `empty` and `sum`.
Avoids `singletonFamily`, `sumFamily`, `ofSumFamily`, `toSumFamily`, and `sumData`. -/
@[implicit_reducible]
def oracleMessageBundle : (s : OracleProtocol) → Path s → OracleBundle
  | .pure _, _ => OracleBundle.empty
  | .liftBind (.message _) next, ⟨x, p⟩ => oracleMessageBundle (next x) p
  | .liftBind (.challenge _) next, ⟨x, p⟩ => oracleMessageBundle (next x) p
  | .liftBind (.oracle X I) next, ⟨x, p⟩ =>
    (OracleBundle.of X I).sum (oracleMessageBundle (next x) p)

abbrev oracleMessageSpec (s : OracleProtocol) (p : Path s) := (oracleMessageBundle s p).spec

/-- Read the concrete oracle messages from a completed transcript as a nested product. -/
def oracleMessages : (s : OracleProtocol) → (tr : Interaction.Transcript oracleSig s) →
    (oracleMessageBundle s tr.path).Data
  | .pure _, _ => ()
  | .liftBind (.message _) next, ⟨x, tr⟩ => oracleMessages (next x) tr
  | .liftBind (.challenge _) next, ⟨_, tr⟩ => oracleMessages (next ()) tr
  | .liftBind (.oracle _ _) next, ⟨x, tr⟩ => (x, oracleMessages (next ()) tr)

/-- Route the appended path's oracle messages into its two component bundles directly via `par`
and `sumAssoc` (no `ofSumFamily` / `toSumFamily` / `familySumAssoc`). -/
def oracleMessageBundle_append : (s₁ : OracleProtocol) → (s₂ : Path s₁ → OracleProtocol) →
    (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    OracleMap ((oracleMessageBundle s₁ p₁).sum (oracleMessageBundle (s₂ p₁) p₂))
      (oracleMessageBundle (s₁.append s₂) (FreeM.Path.append s₁ s₂ p₁ p₂))
  | .pure _, _, ⟨⟩, _ => OracleMap.snd OracleBundle.empty _
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracleMessageBundle_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracleMessageBundle_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.oracle X I) next, s₂, ⟨x, p₁⟩, p₂ =>
    ((OracleMap.id (OracleBundle.of X I)).par
      (oracleMessageBundle_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂)).comp
      (OracleMap.sumAssoc (OracleBundle.of X I)
        (oracleMessageBundle (next x) p₁) (oracleMessageBundle (s₂ ⟨x, p₁⟩) p₂))

/-- Split an appended path's oracle messages into the pair of component bundles. -/
def oracleMessageBundle_split : (s₁ : OracleProtocol) → (s₂ : Path s₁ → OracleProtocol) →
    (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    OracleMap (oracleMessageBundle (s₁.append s₂) (FreeM.Path.append s₁ s₂ p₁ p₂))
      ((oracleMessageBundle s₁ p₁).sum (oracleMessageBundle (s₂ p₁) p₂))
  | .pure _, _, ⟨⟩, _ => OracleMap.emptyLeft _
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracleMessageBundle_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂ =>
    oracleMessageBundle_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂
  | .liftBind (.oracle X I) next, s₂, ⟨x, p₁⟩, p₂ =>
    (OracleMap.sumAssocSymm (OracleBundle.of X I)
      (oracleMessageBundle (next x) p₁) (oracleMessageBundle (s₂ ⟨x, p₁⟩) p₂)).comp
      ((OracleMap.id (OracleBundle.of X I)).par
        (oracleMessageBundle_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂))

/-- Round-trip law without `funext`, `sumData`, or `sumData_eta`. -/
theorem oracleMessageBundle_append_split : (s₁ : OracleProtocol) →
    (s₂ : Path s₁ → OracleProtocol) → (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    (x : (oracleMessageBundle (s₁.append s₂) (FreeM.Path.append s₁ s₂ p₁ p₂)).Data) →
    (oracleMessageBundle_append s₁ s₂ p₁ p₂).f ((oracleMessageBundle_split s₁ s₂ p₁ p₂).f x) = x
  | .pure _, _, ⟨⟩, _, _ => rfl
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracleMessageBundle_append_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracleMessageBundle_append_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.oracle _ _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    Prod.ext rfl (oracleMessageBundle_append_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data.2)

/-- Inverse round-trip law without `funext` or `sumData_eta`. -/
theorem oracleMessageBundle_split_append : (s₁ : OracleProtocol) →
    (s₂ : Path s₁ → OracleProtocol) → (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    (x : ((oracleMessageBundle s₁ p₁).sum (oracleMessageBundle (s₂ p₁) p₂)).Data) →
    (oracleMessageBundle_split s₁ s₂ p₁ p₂).f ((oracleMessageBundle_append s₁ s₂ p₁ p₂).f x) = x
  | .pure _, _, ⟨⟩, _, ⟨⟨⟩, _⟩ => rfl
  | .liftBind (.message _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracleMessageBundle_split_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.challenge _) next, s₂, ⟨x, p₁⟩, p₂, data =>
    oracleMessageBundle_split_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ data
  | .liftBind (.oracle _ _) next, s₂, ⟨x, p₁⟩, p₂, ⟨⟨a, b⟩, c⟩ => by
    have ih := oracleMessageBundle_split_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂ (b, c)
    change ((a, ((oracleMessageBundle_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f
        ((oracleMessageBundle_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f (b, c))).1),
      ((oracleMessageBundle_split (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f
        ((oracleMessageBundle_append (next x) (fun p => s₂ ⟨x, p⟩) p₁ p₂).f (b, c))).2) =
      ((a, b), c)
    rw [ih]

/-- Split the oracle messages of an arbitrary appended path. -/
def splitOracleMessages : (s₁ : OracleProtocol) → (s₂ : Path s₁ → OracleProtocol) →
    (p : Path (s₁.append s₂)) →
    OracleMap (oracleMessageBundle (s₁.append s₂) p)
      ((oracleMessageBundle s₁ (FreeM.Path.split s₁ s₂ p).1).sum
        (oracleMessageBundle (s₂ (FreeM.Path.split s₁ s₂ p).1) (FreeM.Path.split s₁ s₂ p).2))
  | .pure _, s₂, p => oracleMessageBundle_split (.pure ()) s₂ ⟨⟩ p
  | .liftBind (.message _) next, s₂, ⟨x, p⟩ =>
    splitOracleMessages (next x) (fun q => s₂ ⟨x, q⟩) p
  | .liftBind (.challenge _) next, s₂, ⟨x, p⟩ =>
    splitOracleMessages (next x) (fun q => s₂ ⟨x, q⟩) p
  | .liftBind (.oracle X I) next, s₂, ⟨x, p⟩ =>
    (OracleMap.sumAssocSymm (OracleBundle.of X I)
      (oracleMessageBundle (next x) (FreeM.Path.split (next x) (fun q => s₂ ⟨x, q⟩) p).1)
      (oracleMessageBundle _ (FreeM.Path.split (next x) (fun q => s₂ ⟨x, q⟩) p).2)).comp
      ((OracleMap.id (OracleBundle.of X I)).par
        (splitOracleMessages (next x) (fun q => s₂ ⟨x, q⟩) p))

/-- Bundle queried by a passive verifier's decision. -/
abbrev pathBundle (inputs : OracleBundle) (s : OracleProtocol) (p : Path s) : OracleBundle :=
  inputs.sum (oracleMessageBundle s p)

/-- Lift path-oracle queries into the decision's specification. `@[macro_inline]` erases
noncomputable input bundles before code generation. -/
@[macro_inline]
def pathLift {ι : Type} (ambient : OracleSpec ι) (inputs : OracleBundle)
    {s : OracleProtocol} (p : Path s) :
    QueryImpl (oracleMessageSpec s p) (OracleComp (ambient + (pathBundle inputs s p).spec)) :=
  fun q => liftM ((ambient + (pathBundle inputs s p).spec).query (.inr (.inr q)))

/-- Passive oracle verifier with symmetric `OracleBundle` inputs and path-indexed `OracleBundle`
outputs. Drops `{J}` and `{B}` parameters and `OracleBundle.ofFamily` coercions. -/
structure OracleVerifier {ι : Type} (ambient : OracleSpec ι)
    (s : OracleProtocol) (S : Type) (T : Path s → Type)
    (inputs : OracleBundle) (outputs : Path s → OracleBundle) : Type where
  decide : S → (p : Path s) → View s p →
    OptionT (OracleComp (ambient + (pathBundle inputs s p).spec)) (T p)
  outputMap : S → (p : Path s) → View s p →
    OracleMap (pathBundle inputs s p) (outputs p)

namespace OracleVerifier

def decideWith {ι : Type} {ambient : OracleSpec ι} {s : OracleProtocol} {S : Type}
    {T : Path s → Type} {inputs : OracleBundle} {outputs : Path s → OracleBundle}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (p : Path s) (v : View s p)
    (data : (pathBundle inputs s p).Data) : OracleComp ambient (Option (T p)) :=
  simulateQ (QueryImpl.addLift (QueryImpl.id' ambient) ((pathBundle inputs s p).answer data))
    (V.decide stmt p v).run

/-- Reassociate inputs and appended oracle messages into prefix bundle and suffix messages,
without `ofSumFamily`. -/
def splitPathBundle {inputs : OracleBundle} {s₁ : OracleProtocol}
    {s₂ : Path s₁ → OracleProtocol} (p : Path (s₁.append s₂)) :
    OracleMap (pathBundle inputs (s₁.append s₂) p)
      ((pathBundle inputs s₁ (FreeM.Path.split s₁ s₂ p).1).sum
        (oracleMessageBundle (s₂ (FreeM.Path.split s₁ s₂ p).1) (FreeM.Path.split s₁ s₂ p).2)) :=
  (OracleMap.sumAssocSymm inputs
    (oracleMessageBundle s₁ (FreeM.Path.split s₁ s₂ p).1)
    (oracleMessageBundle _ (FreeM.Path.split s₁ s₂ p).2)).comp
    ((OracleMap.id inputs).par (splitOracleMessages s₁ s₂ p))

def prefixRoute {inputs : OracleBundle} {s₁ : OracleProtocol}
    {s₂ : Path s₁ → OracleProtocol} (p : Path (s₁.append s₂)) :
    OracleMap (pathBundle inputs (s₁.append s₂) p)
      (pathBundle inputs s₁ (FreeM.Path.split s₁ s₂ p).1) :=
  (OracleMap.fst _ _).comp (splitPathBundle (inputs := inputs) p)

def suffixRoute {ι : Type} {ambient : OracleSpec ι} {inputs : OracleBundle}
    {s₁ : OracleProtocol} {s₂ : Path s₁ → OracleProtocol} {S : Type}
    {T : Path s₁ → Type} {middle : Path s₁ → OracleBundle}
    (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (stmt : S) (p : Path (s₁.append s₂)) (v : View (s₁.append s₂) p) :
    OracleMap (pathBundle inputs (s₁.append s₂) p)
      (pathBundle (middle (FreeM.Path.split s₁ s₂ p).1) _ (FreeM.Path.split s₁ s₂ p).2) :=
  ((V₁.outputMap stmt (FreeM.Path.split s₁ s₂ p).1
      (Interaction.TranscriptAt.split viewSig s₁ s₂ p v).1).par
    (OracleMap.id (oracleMessageBundle _ (FreeM.Path.split s₁ s₂ p).2))).comp
      (splitPathBundle (inputs := inputs) p)

abbrev splitOutputs {s₁ : OracleProtocol} {s₂ : Path s₁ → OracleProtocol}
    (outputs : (p₁ : Path s₁) → Path (s₂ p₁) → OracleBundle)
    (p : Path (s₁.append s₂)) : OracleBundle :=
  outputs (FreeM.Path.split s₁ s₂ p).1 (FreeM.Path.split s₁ s₂ p).2

/-- Sequential composition of passive oracle verifiers (statement-free output map for brevity). -/
def appendSimple {ι : Type} {ambient : OracleSpec ι} {inputs : OracleBundle}
    {s₁ : OracleProtocol} {s₂ : Path s₁ → OracleProtocol} {S : Type}
    {T : Path s₁ → Type} {U : (p₁ : Path s₁) → Path (s₂ p₁) → Type}
    {middle : Path s₁ → OracleBundle}
    {outputs : (p₁ : Path s₁) → Path (s₂ p₁) → OracleBundle}
    (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p₁ : Path s₁) → OracleVerifier ambient (s₂ p₁) (T p₁) (U p₁) (middle p₁) (outputs p₁))
    (midStmt : S → (p : Path (s₁.append s₂)) → View (s₁.append s₂) p →
      T (FreeM.Path.split s₁ s₂ p).1) :
    OracleVerifier ambient (s₁.append s₂) S
      (fun p => U (FreeM.Path.split s₁ s₂ p).1 (FreeM.Path.split s₁ s₂ p).2)
      inputs (splitOutputs outputs) where
  decide stmt p v := OptionT.mk do
    let z := FreeM.Path.split s₁ s₂ p
    let views := Interaction.TranscriptAt.split viewSig s₁ s₂ p v
    let mid ← simulateQ ((prefixRoute (inputs := inputs) p).withAmbient ambient)
      (V₁.decide stmt z.1 views.1).run
    match mid with
    | none => pure none
    | some mid =>
      simulateQ ((suffixRoute V₁ stmt p v).withAmbient ambient)
        ((V₂ z.1).decide mid z.2 views.2).run
  outputMap stmt p v :=
    let z := FreeM.Path.split s₁ s₂ p
    let views := Interaction.TranscriptAt.split viewSig s₁ s₂ p v
    ((V₂ z.1).outputMap (midStmt stmt p v) z.2 views.2).comp (suffixRoute V₁ stmt p v)

theorem appendSimple_decideWith {ι : Type} {ambient : OracleSpec ι} {inputs : OracleBundle}
    {s₁ : OracleProtocol} {s₂ : Path s₁ → OracleProtocol} {S : Type}
    {T : Path s₁ → Type} {U : (p₁ : Path s₁) → Path (s₂ p₁) → Type}
    {middle : Path s₁ → OracleBundle}
    {outputs : (p₁ : Path s₁) → Path (s₂ p₁) → OracleBundle}
    (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p₁ : Path s₁) → OracleVerifier ambient (s₂ p₁) (T p₁) (U p₁) (middle p₁) (outputs p₁))
    (midStmt : S → (p : Path (s₁.append s₂)) → View (s₁.append s₂) p →
      T (FreeM.Path.split s₁ s₂ p).1)
    (stmt : S) (p : Path (s₁.append s₂)) (v : View (s₁.append s₂) p)
    (data : (pathBundle inputs (s₁.append s₂) p).Data) :
    (V₁.appendSimple V₂ midStmt).decideWith stmt p v data =
      V₁.decideWith stmt (FreeM.Path.split s₁ s₂ p).1
          (Interaction.TranscriptAt.split viewSig s₁ s₂ p v).1
          ((prefixRoute (inputs := inputs) p).f data) >>= fun
        | none => pure none
        | some mid => (V₂ (FreeM.Path.split s₁ s₂ p).1).decideWith mid
            (FreeM.Path.split s₁ s₂ p).2
            (Interaction.TranscriptAt.split viewSig s₁ s₂ p v).2
            ((suffixRoute V₁ stmt p v).f data) := by
  simp only [decideWith, appendSimple, OptionT.run_mk, simulateQ_bind]
  congr 1
  · exact OracleMap.simulate_withAmbient (prefixRoute (inputs := inputs) p) data _
  · funext mid
    cases mid with
    | none => simp
    | some mid => exact OracleMap.simulate_withAmbient (suffixRoute V₁ stmt p v) data _

end OracleVerifier
end Consolidated

/-! ## Part 2. Exact relationships with current ArkLib and VCVio types -/

section Relationships

open OracleSpec OracleComp

/-- 2.1: `Consolidated.OracleInterface X` is equivalent to `(Query : Type) × OracleContext Query (ReaderM X)`.
Both round-trips hold by `rfl` because `ReaderM`, `Id`, and `QueryImpl` reduce. -/
def interfaceEquivOracleContext (X : Type) :
    Consolidated.OracleInterface X ≃
      (Query : Type) × OracleContext.{0, 0, 0} Query (ReaderM X) where
  toFun O := ⟨O.Query, ⟨O.spec, fun q => ReaderT.mk fun m => O.answer m q⟩⟩
  invFun p := ⟨p.1, p.2.spec, fun m q => (p.2.impl q).run m⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- 2.2: `Consolidated.OracleBundle` is definitionally equivalent (`rfl` both ways) to the sigma
type `(Data : Type) × Consolidated.OracleInterface Data`. -/
def bundleEquivSigma :
    Consolidated.OracleBundle ≃ (Data : Type) × Consolidated.OracleInterface Data where
  toFun B := ⟨B.Data, B.toInterface⟩
  invFun p := Consolidated.OracleBundle.of p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- 2.3: Current `OracleInterface.{0, 0} X` is equivalent (`rfl` both ways) to
`Consolidated.OracleInterface X`. -/
def currentInterfaceEquivConsolidated (X : Type) :
    _root_.OracleInterface.{0, 0} X ≃ Consolidated.OracleInterface X where
  toFun O := ⟨O.Query, O.toOC.spec, fun m q => (O.toOC.impl q).run m⟩
  invFun O := ⟨O.Query, ⟨O.spec, fun q => ReaderT.mk fun m => O.answer m q⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- 2.4: Current `Interaction.OracleBundle.{0, 0, 0}` is equivalent (`rfl` both ways) to
`Consolidated.OracleBundle`. -/
def currentBundleEquivConsolidated :
    Interaction.OracleBundle.{0, 0, 0} ≃ Consolidated.OracleBundle where
  toFun B := ⟨B.Index, B.spec, B.Data, B.answer⟩
  invFun B := ⟨B.Query, B.spec, B.Data, B.answer⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- 2.5: Current `OracleFamily.{0, 0, 0} I A` is equivalent (`rfl` both ways) to
`(i : I) → Consolidated.OracleInterface (A i)`. -/
def currentFamilyEquivPi (I : Type) (A : I → Type) :
    Interaction.Oracle.OracleFamily.{0, 0, 0} I A ≃
      ((i : I) → Consolidated.OracleInterface (A i)) where
  toFun F i := (currentInterfaceEquivConsolidated (A i)) (F.interface i)
  invFun G := ⟨fun i => (currentInterfaceEquivConsolidated (A i)).symm (G i)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- 2.6: The total space of `OracleFamily` is equivalent (`rfl` both ways) to the total space of
`I → Consolidated.OracleBundle`. -/
def currentFamilySigmaEquivIndexedBundle :
    ((I : Type) × (A : I → Type) × Interaction.Oracle.OracleFamily.{0, 0, 0} I A) ≃
      ((I : Type) × (I → Consolidated.OracleBundle)) where
  toFun x := ⟨x.1, fun i => Consolidated.OracleBundle.of (x.2.1 i)
    ((currentInterfaceEquivConsolidated (x.2.1 i)) (x.2.2.interface i))⟩
  invFun y := ⟨y.1, fun i => (y.2 i).Data,
    ⟨fun i => (currentInterfaceEquivConsolidated (y.2 i).Data).symm (y.2 i).toInterface⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### 2.7 Key definitional equalities that hold by `rfl` in Design D -/
section RflChecks

example (R S : Consolidated.OracleBundle) (x : R.Data × S.Data) :
    (R.sum S).answer x = R.answer x.1 + S.answer x.2 := rfl

example {α β : Type} (Oα : Consolidated.OracleInterface α) (Oβ : Consolidated.OracleInterface β) :
    Consolidated.OracleBundle.of (α × β) (@Consolidated.OracleInterface.instProd α β Oα Oβ) =
      (Consolidated.OracleBundle.of α Oα).sum (Consolidated.OracleBundle.of β Oβ) := rfl

example {I : Type} (A : I → Type) (O : ∀ i, Consolidated.OracleInterface (A i)) :
    Consolidated.OracleBundle.ofIndexed A O =
      Consolidated.OracleBundle.of (∀ i, A i) (@Consolidated.OracleInterface.instProdForall I A O) :=
  rfl

example {I : Type} (A : I → Type) (O : ∀ i, Consolidated.OracleInterface (A i)) :
    (Consolidated.OracleBundle.ofIndexed A O).spec =
      @Consolidated.OracleInterface.toOracleSpec I A O := rfl

example {I : Type} (spec : OracleSpec I) :
    (Consolidated.OracleBundle.ofSpec spec).answer = id := rfl

end RflChecks

/-! ### 2.8 Failures and non-definitional equalities recorded via `#guard_msgs` -/
section ExpectedFailures

-- Failure 1 (Design B blocker): `OracleContext.add` cannot combine two `ReaderM` contexts with
-- different data types `Data₁` and `Data₂`.
/--
error: Application type mismatch: The argument
  C₂
has type
  OracleContext Query₂ (ReaderM Data₂)
but is expected to have type
  OracleContext (?m.7 C₁ C₂) (ReaderM Data₁)
in the application
  C₁.add C₂
-/
#guard_msgs in
def oracleContextAddDiffData {Query₁ Query₂ Data₁ Data₂ : Type}
    (C₁ : OracleContext Query₁ (ReaderM Data₁))
    (C₂ : OracleContext Query₂ (ReaderM Data₂)) :=
  C₁.add C₂

-- Failure 2 (Design B blocker): `QueryImpl.addReaderT` does not reduce definitionally to
-- `QueryImpl.add` after `.run (x₁, x₂)` (requires `funext`/`cases`).
/--
error: Type mismatch
  rfl
has type
  ?m.38 = ?m.38
but is expected to have type
  (fun q => (C₁.impl.addReaderT C₂.impl q).run x) =
    (fun q => ReaderT.run (C₁.impl q) x.1) + fun q => ReaderT.run (C₂.impl q) x.2
-/
#guard_msgs in
example {Query₁ Query₂ Data₁ Data₂ : Type}
    (C₁ : OracleContext.{0, 0, 0} Query₁ (ReaderM Data₁))
    (C₂ : OracleContext.{0, 0, 0} Query₂ (ReaderM Data₂))
    (x : Data₁ × Data₂) :
    (fun q => (QueryImpl.addReaderT C₁.impl C₂.impl q).run x) =
      ((fun q => (C₁.impl q).run x.1) + (fun q => (C₂.impl q).run x.2)) :=
  rfl

-- Proof succeeds via `funext` and `cases`:
example {Query₁ Query₂ Data₁ Data₂ : Type}
    (C₁ : OracleContext.{0, 0, 0} Query₁ (ReaderM Data₁))
    (C₂ : OracleContext.{0, 0, 0} Query₂ (ReaderM Data₂))
    (x : Data₁ × Data₂) :
    (fun q => (QueryImpl.addReaderT C₁.impl C₂.impl q).run x) =
      ((fun q => (C₁.impl q).run x.1) + (fun q => (C₂.impl q).run x.2)) := by
  funext q
  cases q <;> rfl

-- Failure 3 (Sigma-type ergonomics): replacing `structure OracleBundle` with an `abbrev` for a
-- Sigma type breaks dot notation (`B.spec`, `B.sum`, etc.).
abbrev SigmaBundle : Type 1 := (Data : Type) × Consolidated.OracleInterface Data

/--
error: Invalid field `spec`: The environment does not contain `Sigma.spec`, so it is not possible to project the field `spec` from an expression
  B
of type
  (Data : Type) × Consolidated.OracleInterface Data
-/
#guard_msgs in
def sigmaDotFails (B : SigmaBundle) := B.spec

-- Failure 4 (Family sum vs bundle sum): `(indexed F).sum (indexed G)` is not definitionally equal
-- to `indexed (Sum.elim F G)`. The two data types are equivalent, as `sumData_eta` shows for the
-- current families, and Design D adds no isomorphism structure for them.
/--
error: Type mismatch
  rfl
has type
  ?m.9 = ?m.9
but is expected to have type
  ((Consolidated.OracleBundle.indexed F).sum (Consolidated.OracleBundle.indexed G)).Data =
    (Consolidated.OracleBundle.indexed (Sum.elim F G)).Data
-/
#guard_msgs in
example {I J : Type} (F : I → Consolidated.OracleBundle) (G : J → Consolidated.OracleBundle) :
    ((Consolidated.OracleBundle.indexed F).sum (Consolidated.OracleBundle.indexed G)).Data =
      (Consolidated.OracleBundle.indexed (Sum.elim F G)).Data :=
  rfl

-- Failure 5 (single-query lenses vs `OracleMap`): an `OracleMap` can make 0 or ≥ 2 queries per
-- routed query, so a single-query lens (the shape of VCVio's `SubSpec`) cannot express it.
def doubleQueryMap (R : Consolidated.OracleBundle) :
    Consolidated.OracleMap R
      (Consolidated.OracleBundle.ofSpec
        (OracleSpec.ofPFunctor (PFunctor.tensor R.spec.toPFunctor R.spec.toPFunctor))) :=
  Consolidated.OracleMap.ofImpl R
    (OracleSpec.ofPFunctor (PFunctor.tensor R.spec.toPFunctor R.spec.toPFunctor)) fun q => do
    let a ← liftM (R.spec.query q.1)
    let b ← liftM (R.spec.query q.2)
    pure (a, b)

end ExpectedFailures

end Relationships

/-! ## Part 3. Reducibility, instance search, transparency, and `@[macro_inline]` computability -/

section Invariants

open OracleSpec OracleComp Consolidated

-- 3.1: Why `OracleInterface.answer` uses `(q : Query) → spec q` rather than `QueryImpl spec Id`:
-- `Id` is semireducible in Lean 4, so `QueryImpl spec Id` puts `Id` in the expected return type
-- of `answer` and breaks `Semiring` synthesis on `Polynomial.eval`.
namespace AnswerWithIdFails
class BadInterface (Message : Type) : Type 1 where
  Query : Type
  spec : OracleSpec Query
  answer : Message → QueryImpl spec Id

/--
error: failed to synthesize instance of type class
  Semiring (Id ((ofFn fun x => R).Range point))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
instance (R : Type) [CommSemiring R] : BadInterface (Polynomial R) where
  Query := R
  spec := R →ₒ R
  answer p point := p.eval point
end AnswerWithIdFails

-- 3.2: Why `OracleBundle` keeps four flat fields rather than nesting `interface : OracleInterface Data`:
-- `OracleInterface.Query` is a semireducible class projection, so unfolding `In.spec` in a `simp`
-- step exposes primitive projection `In.interface.2 : OracleSpec In.interface.1` against
-- `OracleSpec (OracleInterface.Query In.Data)`, which fails `rw`'s `.implicit` transparency check.
namespace NestedBundleFails
structure NestedBundle : Type 1 where
  Data : Type
  interface : Consolidated.OracleInterface Data

abbrev NestedBundle.Query (B : NestedBundle) : Type := B.interface.Query
abbrev NestedBundle.spec (B : NestedBundle) : OracleSpec B.Query := B.interface.spec
abbrev NestedBundle.answer (B : NestedBundle) (x : B.Data) : QueryImpl B.spec Id :=
  B.interface.answer x

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  simulateQ (?m.97 + QueryImpl.liftTarget (OracleComp ambient) (In.answer x))
    (simulateQ (fun r => liftM (OracleSpec.query (Sum.inr r))) ?oa)
in the target expression
  simulateQ
      (QueryImpl.liftTarget (OracleComp ambient) (QueryImpl.id' ambient) +
        QueryImpl.liftTarget (OracleComp ambient) (In.answer x))
      (simulateQ (fun r => liftM (OracleSpec.query (Sum.inr r))) oa) =
    (QueryImpl.liftTarget (OracleComp ambient) (QueryImpl.id' ambient) +
        QueryImpl.liftTarget (OracleComp ambient) (In.answer x))
      (Sum.inr q)

ι : Type
ambient : OracleSpec ι
In : NestedBundle
x : In.Data
q : In.Query
oa : OracleComp In.spec (In.spec q)
h : simulateQ (In.answer x) oa = In.answer x q
⊢ simulateQ
      (QueryImpl.liftTarget (OracleComp ambient) (QueryImpl.id' ambient) +
        QueryImpl.liftTarget (OracleComp ambient) (In.answer x))
      (simulateQ (fun r => liftM (OracleSpec.query (Sum.inr r))) oa) =
    (QueryImpl.liftTarget (OracleComp ambient) (QueryImpl.id' ambient) +
        QueryImpl.liftTarget (OracleComp ambient) (In.answer x))
      (Sum.inr q)

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    In.interface.2
  has type
    OracleSpec In.interface.1
  but is expected to have type
    OracleSpec (Consolidated.OracleInterface.Query In.Data)
  in the application
    @simulateQ (Consolidated.OracleInterface.Query In.Data) In.interface.2
-/
#guard_msgs in
example {ι : Type} {ambient : OracleSpec ι} {In : NestedBundle} (x : In.Data)
    (q : In.Query) (oa : OracleComp In.spec (In.spec q))
    (h : simulateQ (In.answer x) oa = In.answer x q) :
    simulateQ (QueryImpl.addLift (QueryImpl.id' ambient) (In.answer x) :
        QueryImpl (ambient + In.spec) (OracleComp ambient))
        (simulateQ (fun r => liftM ((ambient + In.spec).query (.inr r))) oa) =
      (QueryImpl.addLift (QueryImpl.id' ambient) (In.answer x) :
        QueryImpl (ambient + In.spec) (OracleComp ambient)) (.inr q) := by
  simp only [QueryImpl.addLift_def]
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := (In.answer x).liftTarget (OracleComp ambient))
    (fun r => QueryImpl.simulateQ_add_query_right _ _ r), simulateQ_liftTarget, h]
  rfl
end NestedBundleFails

-- 3.3: Lean 4 class projections (`OracleInterface.Query`) are not unfolded during `synthInstance`
-- (true on BOTH current and consolidated `OracleInterface`, which is why `OracleInterface.lean:311`
-- supplies explicit `Fintype` instances). Direct flat bundles (e.g. `ofSpec`) unfold directly.
/--
error: failed to synthesize instance of type class
  Fintype (Consolidated.OracleInterface.Query (Polynomial (ZMod 7)))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Fintype (Consolidated.OracleInterface.Query (Polynomial (ZMod 7))) := inferInstance

example : Fintype ((OracleBundle.ofSpec (ZMod 7 →ₒ ZMod 7)).Query) := inferInstance
example (q : (OracleBundle.ofSpec (ZMod 7 →ₒ ZMod 7)).Query) :
    DecidableEq ((OracleBundle.ofSpec (ZMod 7 →ₒ ZMod 7)).spec q) := inferInstance

-- 3.4: `toOracleSpec` remains semireducible, preserving single-step `rfl` simulation matching
-- `ArkLib/Relation/OracleInterface.lean:238` and `ArkLib/OracleReduction/Basic.lean:515`.
theorem simulateQ_simOracle2_liftM_query_snd {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, Consolidated.OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, Consolidated.OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) (j : ι₂) (q : Consolidated.OracleInterface.Query (T₂ j)) :
    simulateQ (Consolidated.OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM ((Consolidated.OracleInterface.toOracleSpec T₂).query ⟨j, q⟩) :
        OracleComp (oSpec + (Consolidated.OracleInterface.toOracleSpec T₁ +
          Consolidated.OracleInterface.toOracleSpec T₂)) _) =
      pure (Consolidated.OracleInterface.answer (t₂ j) q) :=
  rfl

-- 3.5: Compiler erasure (`@[macro_inline]`): a verifier parameterized by a `noncomputable`
-- `OracleBundle` stays computable (no `noncomputable` modifier!) because `pathLift` and
-- `OracleMap.fst` inline away the unused bundle interpreter before codegen.
noncomputable def mathMvPolyBundle (n : ℕ) : OracleBundle :=
  OracleBundle.ofInst (MvPolynomial (Fin n) (ZMod 7))

def oneOracleProto : OracleProtocol :=
  .liftBind (.oracle (ZMod 7 → ZMod 7) inferInstance) fun _ =>
    .liftBind (.challenge (ZMod 7)) fun _ => .pure ()

@[macro_inline]
def computableVerifierOn (inputs : OracleBundle) :
    OracleVerifier emptySpec0 oneOracleProto (ZMod 7) (fun _ => ZMod 7) inputs (fun _ => inputs) where
  decide target p v := OptionT.mk do
    let r : ZMod 7 := v.1.2.1
    let val : ZMod 7 ← simulateQ (pathLift emptySpec0 inputs p)
      (liftM ((oracleMessageSpec oneOracleProto p).query (.inl r)))
    if val = target then pure (some r) else pure none
  outputMap _ _ _ := OracleMap.fst _ _

/-- Compiles WITHOUT `noncomputable` even though `mathMvPolyBundle n` is `noncomputable`. -/
def computableMvPolyVerifier (n : ℕ) :
    OracleVerifier emptySpec0 oneOracleProto (ZMod 7) (fun _ => ZMod 7)
      (mathMvPolyBundle n) (fun _ => mathMvPolyBundle n) :=
  computableVerifierOn (mathMvPolyBundle n)

end Invariants

/-! ## Part 4. Realistic examples with zero universe pins -/

section Examples

set_option pp.universes true

open OracleSpec OracleComp Consolidated

/-- 4.1: Single-oracle bundle (no dummy `Unit` index) and sums/tensors without universe pins. -/
def fnBundle : OracleBundle := OracleBundle.ofInst (ZMod 7 → ZMod 7)
def pairBundle : OracleBundle := fnBundle.sum fnBundle
def tensorBundle : OracleBundle := fnBundle.tensor fnBundle

/--
info: fnBundle : OracleBundle
-/
#guard_msgs in
#check @fnBundle

/--
info: pairBundle : OracleBundle
-/
#guard_msgs in
#check @pairBundle

/--
info: tensorBundle : OracleBundle
-/
#guard_msgs in
#check @tensorBundle

/-- 4.2: Indexed family of bundles converted via `OracleBundle.indexed` and reindexed/aliased
via `OracleMap.reindex`. -/
def twoSlotFamily : Bool → OracleBundle
  | false => OracleBundle.ofInst (ZMod 7 → ZMod 7)
  | true => OracleBundle.of (ZMod 7) Consolidated.OracleInterface.instDefault

def twoSlotBundle : OracleBundle := OracleBundle.indexed twoSlotFamily

/-- Alias slot `false` into both positions of `Fin 2`. -/
def duplicateFirstSlot : OracleMap twoSlotBundle
    (OracleBundle.indexed (twoSlotFamily ∘ fun (_ : Fin 2) => false)) :=
  OracleMap.reindex twoSlotFamily (fun (_ : Fin 2) => false)

/--
info: duplicateFirstSlot : OracleMap twoSlotBundle
  (OracleBundle.indexed (Function.comp.{1, 1, 2} twoSlotFamily fun x => false))
-/
#guard_msgs in
#check @duplicateFirstSlot

example (f : ZMod 7 → ZMod 7) (c : ZMod 7) (i : Fin 2) (x : ZMod 7) :
    let data : twoSlotBundle.Data := fun | false => f | true => c
    (OracleBundle.indexed (twoSlotFamily ∘ fun (_ : Fin 2) => false)).answer
      (duplicateFirstSlot.f data) ⟨i, x⟩ = f x := rfl

/-- 4.3: Derived behavior-only output (`OracleBundle.ofSpec`) as a first-class `OracleVerifier`
output (not expressible when `OracleVerifier.outputs` required `OracleFamily`). -/
def shiftedSpec : OracleSpec (ZMod 7) := ZMod 7 →ₒ ZMod 7

def shiftedVerifier :
    OracleVerifier emptySpec0 oneOracleProto (ZMod 7) (fun _ => ZMod 7)
      fnBundle (fun _ => OracleBundle.ofSpec shiftedSpec) where
  decide target p v := OptionT.mk do
    let r : ZMod 7 := v.1.2.1
    let a : ZMod 7 ← liftM ((emptySpec0 + (pathBundle fnBundle oneOracleProto p).spec).query
      (.inr (.inl r)))
    let b : ZMod 7 ← liftM ((emptySpec0 + (pathBundle fnBundle oneOracleProto p).spec).query
      (.inr (.inr (.inl r))))
    if a + b = target then pure (some (r + 1)) else pure none
  outputMap _ p _ :=
    OracleMap.ofImpl (pathBundle fnBundle oneOracleProto p) shiftedSpec fun q => do
      let a : ZMod 7 ← liftM ((pathBundle fnBundle oneOracleProto p).spec.query (.inl q))
      let b : ZMod 7 ← liftM ((pathBundle fnBundle oneOracleProto p).spec.query (.inr (.inl q)))
      pure (a + b)

/--
info: shiftedVerifier : OracleVerifier emptySpec0 oneOracleProto (ZMod 7) (fun x => ZMod 7) fnBundle fun x =>
  OracleBundle.ofSpec shiftedSpec
-/
#guard_msgs in
#check @shiftedVerifier

/-- 4.4: Two-stage passive verifier composition and routing theorem with zero universe pins and
no `ofSumFamily`/`sumData_eta`. -/
def stage2Verifier :
    OracleVerifier emptySpec0 oneOracleProto (ZMod 7) (fun _ => ZMod 7)
      (OracleBundle.ofSpec shiftedSpec) (fun _ => OracleBundle.ofSpec shiftedSpec) where
  decide target p v := OptionT.mk do
    let r : ZMod 7 := v.1.2.1
    let a : ZMod 7 ← liftM ((emptySpec0 +
      (pathBundle (OracleBundle.ofSpec shiftedSpec) oneOracleProto p).spec).query (.inr (.inl r)))
    if a = target then pure (some r) else pure none
  outputMap _ _ _ := OracleMap.fst _ _

def composedMidStmt : ZMod 7 →
    (p : Path (oneOracleProto.append fun _ => oneOracleProto)) →
    View (oneOracleProto.append fun _ => oneOracleProto) p → ZMod 7 :=
  fun _ p v =>
    let r : ZMod 7 :=
      (Interaction.TranscriptAt.split viewSig oneOracleProto (fun _ => oneOracleProto) p v).1.1.2.1
    r + 1

def composedVerifier :=
  shiftedVerifier.appendSimple (fun _ => stage2Verifier) composedMidStmt

/--
info: composedVerifier : OracleVerifier emptySpec0 (PFunctor.FreeM.append.{0, 0, 1, 0} oneOracleProto fun x => oneOracleProto)
  (ZMod 7) (fun p => ZMod 7) fnBundle (OracleVerifier.splitOutputs fun x x_1 => OracleBundle.ofSpec shiftedSpec)
-/
#guard_msgs in
#check @composedVerifier

/-- Routing check on the composed verifier: elaborates with zero universe annotations. -/
theorem composedVerifier_decideWith
    (stmt : ZMod 7) (p : Path (oneOracleProto.append fun _ => oneOracleProto))
    (v : View (oneOracleProto.append fun _ => oneOracleProto) p)
    (data : (pathBundle fnBundle (oneOracleProto.append fun _ => oneOracleProto) p).Data) :
    composedVerifier.decideWith stmt p v data =
      shiftedVerifier.decideWith stmt
          (PFunctor.FreeM.Path.split oneOracleProto (fun _ => oneOracleProto) p).1
          (Interaction.TranscriptAt.split viewSig oneOracleProto (fun _ => oneOracleProto) p v).1
          ((OracleVerifier.prefixRoute (inputs := fnBundle) p).f data) >>= fun
        | none => pure none
        | some mid => stage2Verifier.decideWith mid
            (PFunctor.FreeM.Path.split oneOracleProto (fun _ => oneOracleProto) p).2
            (Interaction.TranscriptAt.split viewSig oneOracleProto (fun _ => oneOracleProto) p v).2
            ((OracleVerifier.suffixRoute shiftedVerifier stmt p v).f data) :=
  by
    unfold composedVerifier
    rw [OracleVerifier.appendSimple_decideWith]
    congr 1
    funext mid
    cases mid <;> rfl

/--
info: composedVerifier_decideWith : ∀ (stmt : ZMod 7)
  (p : Consolidated.Path (PFunctor.FreeM.append.{0, 0, 1, 0} oneOracleProto fun x => oneOracleProto))
  (v : View (PFunctor.FreeM.append.{0, 0, 1, 0} oneOracleProto fun x => oneOracleProto) p)
  (data : (pathBundle fnBundle (PFunctor.FreeM.append.{0, 0, 1, 0} oneOracleProto fun x => oneOracleProto) p).Data),
  Eq.{1} (composedVerifier.decideWith stmt p v data) do
    let x ←
      shiftedVerifier.decideWith stmt
          (Sigma.fst.{0, 0} (PFunctor.FreeM.Path.split.{0, 0, 1, 0} oneOracleProto (fun x => oneOracleProto) p))
          (Interaction.TranscriptAt.split.{0, 1} viewSig oneOracleProto (fun x => oneOracleProto) p v).1
          ((OracleVerifier.prefixRoute p).f data)
    match x with
      | none.{0} => pure.{0, 0} none.{0}
      | some.{0} mid =>
        stage2Verifier.decideWith mid
          (Sigma.snd.{0, 0} (PFunctor.FreeM.Path.split.{0, 0, 1, 0} oneOracleProto (fun x => oneOracleProto) p))
          (Interaction.TranscriptAt.split.{0, 1} viewSig oneOracleProto (fun x => oneOracleProto) p v).2
          ((shiftedVerifier.suffixRoute stmt p v).f data)
-/
#guard_msgs in
#check @composedVerifier_decideWith

end Examples
