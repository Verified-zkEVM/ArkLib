/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.OracleVerifier
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Named bundles and oracle families with dependent carriers

Oracle family indices name the oracles. A sum bundle of two families keeps two same-interface
oracles with different carrier types apart. An embedding along a non-injective renaming makes two
output indices share one realization; an embedding along `Bool.not` transports a carrier to the
renamed index. Query and response types may vary with the index, and a carrier subtype states a
degree bound that holds of every realization.

Named bundles keep distinct response and realization carriers in `Type`. A view restricts the
visible queries while retaining the whole context's data. Both forms are used directly as verifier
inputs.

The polynomial fixture is noncomputable because Mathlib's `Polynomial` is; it is used only for
the evaluation and degree proofs.
-/

open Interaction Interaction.Oracle OracleComp

namespace Interaction.BundleFamiliesTests


/-- The carrier at index `r`: three values for `false`, five for `true`. -/
abbrev Carrier (r : Bool) : Type := Fin (if r then 5 else 3)

/-- A `Bool` query reads the realization's value, plus one when the query is `true`. -/
@[reducible] def countInterface (r : Bool) : OracleInterface (Carrier r) where
  Query := Bool
  spec := fun _ => Nat
  answer m query := m.val + (if query then 1 else 0)

/-- Both indices have the same query interface and different carrier types. -/
def model : OracleFamily Bool Carrier := ⟨countInterface⟩

/-- The family holding only index `false`. -/
abbrev left := model.reindex (fun _ : PUnit => false)

/-- The family holding only index `true`. -/
abbrev right := model.reindex (fun _ : PUnit => true)

/-- The sum bundle of the two single-index families. -/
abbrev pair := (OracleBundle.ofFamily left).sum (OracleBundle.ofFamily right)

/-- A concrete realization in the three-valued carrier. -/
def smallRealization : Fin 3 := ⟨2, by decide⟩

/-- A concrete realization in the five-valued carrier. -/
def largeRealization : Fin 5 := ⟨4, by decide⟩

/-- Data for the sum, of a different carrier type on each side. -/
def pairEnv : pair.Data :=
  (fun _ => smallRealization, fun _ => largeRealization)

/-- Query both sides. -/
def readPair : OracleComp pair.spec (Nat × Nat) := do
  let x : Nat ← liftM (pair.spec.query (.inl ⟨⟨⟩, true⟩))
  let y : Nat ← liftM (pair.spec.query (.inr ⟨⟨⟩, false⟩))
  return (x, y)

-- ResourceExample R4, restated: the old-layer disjoint union of two named contexts becomes the
-- `OracleBundle.sum` of two single-index families with carriers `Fin 3` and `Fin 5`, queried by
-- side. Not weaker.
example : simulateQ (pair.answer pairEnv) readPair = (3, 4) := rfl

/-- Two output indices, both reading the one realization of `left`. -/
def aliases := OracleMap.embedding left (fun _ : Bool => PUnit.unit)

/-- Both output indices issue their query. -/
def readAliases : OracleComp (left.reindex (fun _ : Bool => PUnit.unit)).spec (Nat × Nat) := do
  let x : Nat ← liftM ((left.reindex (fun _ : Bool => PUnit.unit)).spec.query ⟨false, false⟩)
  let y : Nat ← liftM ((left.reindex (fun _ : Bool => PUnit.unit)).spec.query ⟨true, false⟩)
  return (x, y)

-- ResourceExample R6, restated: the old-layer aliasing view becomes the embedding along a constant
-- renaming; both output indices answer from the single realization. Not weaker.
example : simulateQ (left.behaviorOfRealizations (fun _ => smallRealization))
    (simulateQ aliases.impl readAliases) = (2, 2) := rfl

-- ResourceExample R7, restated: names are family indices, so "both aliases carry the same name"
-- becomes: both output indices make the same input query and read the same input datum.
example (q : Bool) : aliases.impl ⟨false, q⟩ = aliases.impl ⟨true, q⟩ := rfl
example (x : ∀ i, left.Realization i) : aliases.f x false = aliases.f x true := rfl

-- ResourceExample R8, restated: the output indices of the embedding are distinct, so R6 and R7
-- are not vacuous.
example : (false : (left.reindex (fun _ : Bool => PUnit.unit)).Index) ≠ true := by decide

/-- Realizations selected by index. -/
def bothEnv : ∀ r, Carrier r
  | false => smallRealization
  | true => largeRealization

/-- The embedding along `Bool.not`: output index `false` denotes input index `true`. -/
def inclusion := OracleMap.embedding model Bool.not

-- ResourceExample R16, restated: the old-layer inclusion from a reindex becomes the embedding along
-- `Bool.not`; its data map transports the five-valued realization to output index `false`. Not
-- weaker.
example : inclusion.f bothEnv false = (largeRealization : Fin 5) := rfl

/-- Read in the renamed order. -/
def readRenamed : OracleComp (model.reindex Bool.not).spec (Nat × Nat) := do
  let x : Nat ← liftM ((model.reindex Bool.not).spec.query ⟨false, false⟩)
  let y : Nat ← liftM ((model.reindex Bool.not).spec.query ⟨true, true⟩)
  return (x, y)

-- ResourceExample R17, restated: the old-layer program routed through the inclusion becomes the
-- program simulated through the embedding's `impl`, then answered from the original data. The
-- same answers follow from the transported data by `OracleMap.simulate_eq`. Not weaker.
example : simulateQ (model.behaviorOfRealizations bothEnv)
    (simulateQ inclusion.impl readRenamed) = (4, 3) := rfl

example : simulateQ ((model.reindex Bool.not).behaviorOfRealizations (inclusion.f bothEnv))
    readRenamed = (4, 3) :=
  (OracleMap.simulate_eq inclusion bothEnv readRenamed).symm.trans rfl

-- ResourceExample R18, restated: data for the empty family exists without a realization of any
-- model index.
example : ∀ i, (model.reindex (fun i : PEmpty => i.elim)).Realization i := fun i => i.elim

/-- Apply the identity embedding to each side of the sum. -/
def sumOfSides := (OracleMap.embedding left id).par (OracleMap.embedding right id)

-- ResourceExample R19, restated: the old-layer correspondence between a disjoint union and the
-- sum of its interpreted sources becomes the sum of the two side maps. Routing `readPair` through
-- it keeps R4's answers. Reassociating with the empty family on the right does too.
example : simulateQ (pair.answer pairEnv)
    (simulateQ sumOfSides.impl readPair) = (3, 4) := rfl

/-- The empty family. -/
abbrev noIndices := model.reindex (fun i : PEmpty => i.elim)

example : simulateQ ((pair.sum noIndices).answer (pairEnv, fun i => i.elim))
    (simulateQ (OracleMap.sumAssoc left right noIndices).impl
      (simulateQ (OracleMap.sumAssocSymm left right noIndices).impl
        (simulateQ (OracleMap.fst pair noIndices).impl readPair))) = (3, 4) := rfl

/-- One output index for `left` itself and two aliases of it. -/
def shared := OracleMap.embedding left (Sum.elim id (fun _ : Bool => PUnit.unit))

/-- Different output indices and queries, one realization. -/
def readShared : OracleComp
    (left.reindex (Sum.elim id (fun _ : Bool => PUnit.unit))).spec (Nat × Nat) := do
  let x : Nat ← liftM
    ((left.reindex (Sum.elim id (fun _ : Bool => PUnit.unit))).spec.query ⟨.inl ⟨⟩, true⟩)
  let y : Nat ← liftM
    ((left.reindex (Sum.elim id (fun _ : Bool => PUnit.unit))).spec.query ⟨.inr true, false⟩)
  return (x, y)

-- ResourceExample R20, restated: `View.share` becomes the embedding along
-- `Sum.elim id (fun _ => ⟨⟩)`. Not weaker.
example : simulateQ (left.behaviorOfRealizations (fun _ => smallRealization))
    (simulateQ shared.impl readShared) = (3, 2) := rfl

/-- Index `false` takes a `Bool` query and answers a `Nat`; index `true` takes a `Fin 2` query
and answers a `Bool`. -/
@[reducible] def mixedInterface : (r : Bool) → OracleInterface (Carrier r)
  | false =>
    { Query := Bool
      spec := fun _ => Nat
      answer m _ := m.val }
  | true =>
    { Query := Fin 2
      spec := fun _ => Bool
      answer m query := decide (query.val < m.val) }

/-- Query and response types vary with the index. -/
def mixedModel : OracleFamily Bool Carrier := ⟨mixedInterface⟩

/-- After renaming, output index `false` takes a `Fin 2` query and answers a `Bool`. -/
def readMixed : OracleComp (mixedModel.reindex Bool.not).spec (Bool × Nat) := do
  let bit : Bool ← liftM ((mixedModel.reindex Bool.not).spec.query ⟨false, (1 : Fin 2)⟩)
  let value : Nat ← liftM ((mixedModel.reindex Bool.not).spec.query ⟨true, false⟩)
  return (bit, value)

-- ResourceExample R21, restated: the old-layer model with name-dependent query and response types
-- becomes an oracle family with per-index interfaces, renamed by the embedding along `Bool.not`.
-- Not weaker.
example : simulateQ (mixedModel.behaviorOfRealizations bothEnv)
    (simulateQ (OracleMap.embedding mixedModel Bool.not).impl readMixed) = (true, 2) := rfl

/-- Polynomials of degree below two, as a carrier subtype. -/
abbrev LowDegree := {p : Polynomial Nat // p.natDegree < 2}

/-- Evaluation is the only query. -/
@[reducible] def evaluation : OracleInterface LowDegree where
  Query := Nat
  spec := fun _ => Nat
  answer m point := m.val.eval point

/-- One polynomial oracle. -/
def polynomials : OracleFamily Unit (fun _ => LowDegree) :=
  ⟨fun _ => evaluation⟩

/-- The polynomial `X`, whose carrier certifies its degree bound. -/
noncomputable def linearRealization : LowDegree := ⟨Polynomial.X, by simp⟩

-- ResourceExample R22 (two examples), restated: the old-layer polynomial model becomes a family
-- with carrier `{p // natDegree < 2}` and an evaluation interface. Not weaker.
example :
    polynomials.behaviorOfRealizations (fun _ => linearRealization) ⟨(), (3 : Nat)⟩ =
      (3 : Nat) := by
  change (Polynomial.X : Polynomial Nat).eval 3 = 3
  simp

example :
    polynomials.behaviorOfRealizations (fun _ => linearRealization) ⟨(), (7 : Nat)⟩ =
      (7 : Nat) := by
  change (Polynomial.X : Polynomial Nat).eval 7 = 7
  simp

-- ResourceExample R23, restated: the old-layer reified guarantee becomes the carrier subtype.
-- The degree bound holds of every realization of the family, in particular of
-- `linearRealization`.
example (x : ∀ i, polynomials.Realization i) (i : Unit) : (x i).val.natDegree < 2 :=
  (x i).property

example : linearRealization.val.natDegree < 2 := linearRealization.property

-- ResourceExample R9: the alias reads the original three-valued carrier, including its bound.
/-- Every aliased realization satisfies its carrier's bound. -/
example (data : ∀ i, left.Realization i) : (aliases.f data true).val < 3 :=
  (data PUnit.unit).isLt

-- ResourceExample R10 and R11: the numerical false property remains expressible without symbols.
/-- The zero realization does not satisfy a strict bound of zero. -/
example : ¬ (0 : Carrier false).val < 0 := Nat.not_lt_zero _

/-- No family of proofs can impose the impossible bound zero on every three-valued object. -/
example (h : ∀ obj : Carrier false, obj.val < 0) : False := Nat.not_lt_zero _ (h 0)

/-- The zero object in each of the two independently indexed carriers. -/
def zeroRealization (index : Bool) : Carrier index :=
  ⟨0, by cases index <;> decide⟩

-- ResourceExample R12 and R13: equal answers do not identify the two family indices.
/-- The two zero objects have equal query behavior. -/
example : (fun query : Bool => model.behaviorOfRealizations zeroRealization ⟨false, query⟩) =
    (fun query : Bool => model.behaviorOfRealizations zeroRealization ⟨true, query⟩) := rfl

/-- The indices of the two equal-behavior objects are still distinct. -/
example : (false : model.Index) ≠ true := by decide

-- ResourceExample R24: the false degree property is a numerical fact about the same polynomial.
/-- The polynomial cannot have natural degree strictly below zero. -/
example : ¬ linearRealization.val.natDegree < 0 := Nat.not_lt_zero _

/-! ### R26 and R27 named and visible contexts at `Type` -/

section IndependentRealizations


variable {Name : Type} {Query : Name → Type} {Realization : Name → Type}
  {Response : (n : Name) → Query n → Type}

/-- A view bundle queries selected named oracles while retaining the whole context's data (R27). -/
def viewBundle (answer : ∀ n, Realization n → (q : Query n) → Response n q)
    {Index : Type} (name : Index → Name) {Visible : Type} (select : Visible → Index) :
    OracleBundle where
  Query := (x : Visible) × Query (name (select x))
  spec query := Response (name (select query.1)) query.2
  Data := (x : Index) → Realization (name x)
  answer data query := answer _ (data (select query.1)) query.2

/-- The whole named context is the identity view (R26). -/
abbrev namedBundle (answer : ∀ n, Realization n → (q : Query n) → Response n q)
    {Index : Type} (name : Index → Name) : OracleBundle :=
  viewBundle answer name id

/-- R26 keeps its exact query and data carriers. -/
example (answer : ∀ n, Realization n → (q : Query n) → Response n q)
    {Index : Type} (name : Index → Name) :
    (namedBundle answer name).Query = ((x : Index) × Query (name x)) ∧
      (namedBundle answer name).Data = ((x : Index) → Realization (name x)) := ⟨rfl, rfl⟩

/-- R27 keeps the original context's data when the visible index has a distinct carrier. -/
example (answer : ∀ n, Realization n → (q : Query n) → Response n q)
    {Index : Type} (name : Index → Name) {Visible : Type} (select : Visible → Index) :
    (viewBundle answer name select).Query = ((x : Visible) × Query (name (select x))) ∧
      (viewBundle answer name select).Data = ((x : Index) → Realization (name x)) :=
  ⟨rfl, rfl⟩

/-- No output oracles are needed to test the verifier's input-bundle boundary. -/
def noOutputs : OracleFamily PEmpty (fun _ => PUnit) := ⟨fun x => x.elim⟩

/-- A verifier consumes an R27-shaped view at `Type`.
Its decision reads the selected query from the whole
context's unencoded data. -/
def viewVerifier {Response : (n : Name) → Query n → Type}
    (answer : ∀ n, Realization n → (q : Query n) → Response n q)
    {Index : Type} (name : Index → Name) {Visible : Type} (select : Visible → Index)
    (x : Visible) (query : Query (name (select x))) :
    OracleVerifier (PEmpty →ₒ PUnit) (.pure ⟨⟩ : OracleProtocol)
      PUnit (fun _ => Response (name (select x)) query)
      (viewBundle answer name select) (fun _ => noOutputs) where
  decide _ p _ := liftM
    (((PEmpty →ₒ PUnit) +
      (pathBundle (viewBundle answer name select)
        (.pure ⟨⟩ : OracleProtocol) p).spec).query (.inr (.inl ⟨x, query⟩)))
  outputMap _ _ _ :=
    { f := fun _ x => x.elim
      impl := fun query => query.1.elim
      law := fun _ query => query.1.elim }

/-- The R26 verifier is the identity-view specialization of the R27 verifier. -/
abbrev namedVerifier {Response : (n : Name) → Query n → Type}
    (answer : ∀ n, Realization n → (q : Query n) → Response n q)
    {Index : Type} (name : Index → Name) (x : Index) (query : Query (name x)) :
    OracleVerifier (PEmpty →ₒ PUnit) (.pure ⟨⟩ : OracleProtocol)
      PUnit (fun _ => Response (name x) query) (namedBundle answer name)
      (fun _ => noOutputs) :=
  viewVerifier answer name id x query

/-- The run also accepts the unencoded realization family at `Type`. -/
example {Response : (n : Name) → Query n → Type}
    (answer : ∀ n, Realization n → (q : Query n) → Response n q)
    {Index : Type} (name : Index → Name) (x : Index) (query : Query (name x))
    (data : (x : Index) → Realization (name x)) :=
  (namedVerifier answer name x query).run (Out := fun _ => PUnit) ⟨⟩ data (pure ⟨⟩)

/-- Both R26 and R27 are verifier inputs with the same original realization family. The view
changes only which queries are visible, without encoding or restricting the backing data. -/
example {Response : (n : Name) → Query n → Type}
    (answer : ∀ n, Realization n → (q : Query n) → Response n q)
    {Index : Type} (name : Index → Name) {Visible : Type} (select : Visible → Index)
    (x : Visible) (query : Query (name (select x)))
    (data : (x : Index) → Realization (name x)) :=
  ((namedVerifier answer name (select x) query).run
      (Out := fun _ => PUnit) ⟨⟩ data (pure ⟨⟩),
    (viewVerifier answer name select x query).run
      (Out := fun _ => PUnit) ⟨⟩ data (pure ⟨⟩))

end IndependentRealizations

section Universes

variable {Name : Type} {Realization : Name → Type} {Index : Type} {View : Type}

-- OracleFamily specializes the bundle contracts through OracleBundle.ofFamily.
/-- A bundle of selected oracles keeps the context, query and data-index carriers at `Type`. -/
example (C : OracleFamily Name Realization) (name : Index → Name) :
    OracleBundle := OracleBundle.ofFamily (C.reindex name)

/-- Selecting interfaces preserves the context's query indices. -/
example (C : OracleFamily Name Realization) (name : Index → Name) :
    OracleSpec.{0, 0} ((x : Index) × (C.interface (name x)).Query) :=
  (C.reindex name).spec

/-- Context data answers all selected queries. -/
example (C : OracleFamily Name Realization) (name : Index → Name) :
    (∀ x, Realization (name x)) → QueryImpl (C.reindex name).spec Id :=
  (C.reindex name).behaviorOfRealizations

-- The family specialization keeps the original context when routing through a view.
/-- An arbitrary view changes query indices without changing the original context data. -/
example (C : OracleFamily Name Realization) (name : Index → Name)
    (view : View → Index) (data : ∀ x, Realization (name x)) :
    QueryImpl (C.reindex (name ∘ view)).spec Id :=
  (C.reindex (name ∘ view)).behaviorOfRealizations
    ((OracleMap.embedding (C.reindex name) view).f data)

/-- View queries keep the selected name's dependent query carrier. -/
example (C : OracleFamily Name Realization) (name : Index → Name)
    (view : View → Index) :
    OracleSpec.{0, 0} ((x : View) × (C.interface (name (view x))).Query) :=
  (C.reindex (name ∘ view)).spec

/-- Routing through a view answers from the original context at the selected index. -/
example (C : OracleFamily Name Realization) (name : Index → Name)
    (view : View → Index) (data : ∀ x, Realization (name x))
    (x : View) (query : (C.interface (name (view x))).Query) :
    (C.reindex (name ∘ view)).behaviorOfRealizations
        ((OracleMap.embedding (C.reindex name) view).f data) ⟨x, query⟩ =
      (C.reindex name).behaviorOfRealizations data ⟨view x, query⟩ := rfl

end Universes

end Interaction.BundleFamiliesTests
