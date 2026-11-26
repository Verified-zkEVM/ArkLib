/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.OracleVerifier
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Named bundles and indexed bundles with dependent carriers

The indices of an indexed bundle name its oracles. A sum of two indexed bundles keeps two
same-interface oracles with different carrier types apart. Reindexing along a non-injective
renaming makes two output indices share one realization; reindexing along `Bool.not` transports a
carrier to the renamed index. Query and response types may vary with the index, and a carrier
subtype states a degree bound that holds of every realization.

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
  toOC.spec := fun _ => Nat
  toOC.impl query := do return (← read).val + (if query then 1 else 0)

/-- The oracle at index `r`: the shared query interface on the carrier at `r`. -/
abbrev slot (r : Bool) : OracleBundle := OracleBundle.of (Carrier r) (countInterface r)

/-- Both indices have the same query interface and different carrier types. -/
def model : OracleBundle := OracleBundle.ofIndexed Carrier countInterface

/-- The oracle of index `false`, as the only index of its bundle. -/
abbrev leftSlots := slot ∘ fun _ : Unit => false

/-- The oracle of index `true`, as the only index of its bundle. -/
abbrev rightSlots := slot ∘ fun _ : Unit => true

/-- The bundle holding only index `false`. -/
abbrev left := OracleBundle.indexed leftSlots

/-- The bundle holding only index `true`. -/
abbrev right := OracleBundle.indexed rightSlots

/-- The sum bundle of the two single-index bundles. -/
abbrev pair := left.sum right

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
-- `OracleBundle.sum` of two single-index bundles with carriers `Fin 3` and `Fin 5`, queried by
-- side. Not weaker.
example : simulateQ (pair.answer pairEnv) readPair = (3, 4) := rfl

/-- Two output indices, both reading the one realization of `left`. -/
def aliases := OracleMap.reindex leftSlots (fun _ : Bool => ())

/-- The bundle of the two aliases. -/
abbrev aliased := OracleBundle.indexed (leftSlots ∘ fun _ : Bool => ())

/-- Both output indices issue their query. -/
def readAliases : OracleComp aliased.spec (Nat × Nat) := do
  let x : Nat ← liftM (aliased.spec.query ⟨false, false⟩)
  let y : Nat ← liftM (aliased.spec.query ⟨true, false⟩)
  return (x, y)

-- ResourceExample R6, restated: the old-layer aliasing view becomes reindexing along a constant
-- renaming; both output indices answer from the single realization. Not weaker.
example : simulateQ (left.answer (fun _ => smallRealization))
    (simulateQ aliases.impl readAliases) = (2, 2) := rfl

-- ResourceExample R7, restated: names are bundle indices, so "both aliases carry the same name"
-- becomes: both output indices make the same input query and read the same input datum.
example (q : Bool) : aliases.impl ⟨false, q⟩ = aliases.impl ⟨true, q⟩ := rfl
example (x : left.Data) : aliases.f x false = aliases.f x true := rfl

-- ResourceExample R8, restated: the output indices of the reindexing are distinct, so R6 and R7
-- are not vacuous.
example : (⟨false, false⟩ : aliased.Query) ≠ ⟨true, false⟩ :=
  fun h => Bool.false_ne_true (congrArg Sigma.fst h)

/-- Realizations selected by index. -/
def bothEnv : ∀ r, Carrier r
  | false => smallRealization
  | true => largeRealization

/-- Reindexing along `Bool.not`: output index `false` denotes input index `true`. -/
def inclusion := OracleMap.reindex slot Bool.not

/-- The renamed bundle. -/
abbrev renamed := OracleBundle.indexed (slot ∘ Bool.not)

-- ResourceExample R16, restated: the old-layer inclusion from a reindex becomes reindexing along
-- `Bool.not`; its data map transports the five-valued realization to output index `false`. Not
-- weaker.
example : inclusion.f bothEnv false = (largeRealization : Fin 5) := rfl

/-- Read in the renamed order. -/
def readRenamed : OracleComp renamed.spec (Nat × Nat) := do
  let x : Nat ← liftM (renamed.spec.query ⟨false, false⟩)
  let y : Nat ← liftM (renamed.spec.query ⟨true, true⟩)
  return (x, y)

-- ResourceExample R17, restated: the old-layer program routed through the inclusion becomes the
-- program simulated through the reindexing map's `impl`, then answered from the original data. The
-- same answers follow from the transported data by `OracleMap.simulate_eq`. Not weaker.
example : simulateQ (model.answer bothEnv)
    (simulateQ inclusion.impl readRenamed) = (4, 3) := rfl

example : simulateQ (renamed.answer (inclusion.f bothEnv))
    readRenamed = (4, 3) :=
  (OracleMap.simulate_eq inclusion bothEnv readRenamed).symm.trans rfl

-- ResourceExample R18, restated: data for the empty indexed bundle exists without a realization
-- of any model index.
example : (OracleBundle.indexed (slot ∘ fun i : PEmpty => i.elim)).Data := fun i => i.elim

/-- Apply the identity reindexing to each side of the sum. -/
def sumOfSides := (OracleMap.reindex leftSlots id).par (OracleMap.reindex rightSlots id)

-- ResourceExample R19, restated: the old-layer correspondence between a disjoint union and the
-- sum of its interpreted sources becomes the sum of the two side maps. Routing `readPair` through
-- it keeps R4's answers. Reassociating with the empty indexed bundle on the right does too.
example : simulateQ (pair.answer pairEnv)
    (simulateQ sumOfSides.impl readPair) = (3, 4) := rfl

/-- The indexed bundle with no indices. -/
abbrev noIndices := OracleBundle.indexed (slot ∘ fun i : PEmpty => i.elim)

example : simulateQ ((pair.sum noIndices).answer (pairEnv, fun i => i.elim))
    (simulateQ (OracleMap.sumAssoc left right noIndices).impl
      (simulateQ (OracleMap.sumAssocSymm left right noIndices).impl
        (simulateQ (OracleMap.fst pair noIndices).impl readPair))) = (3, 4) := rfl

/-- One output index for `left` itself and two aliases of it. -/
def shared := OracleMap.reindex leftSlots (Sum.elim id (fun _ : Bool => ()))

/-- The bundle of `left` and its two aliases. -/
abbrev sharedBundle := OracleBundle.indexed (leftSlots ∘ Sum.elim id (fun _ : Bool => ()))

/-- Different output indices and queries, one realization. -/
def readShared : OracleComp sharedBundle.spec (Nat × Nat) := do
  let x : Nat ← liftM (sharedBundle.spec.query ⟨.inl ⟨⟩, true⟩)
  let y : Nat ← liftM (sharedBundle.spec.query ⟨.inr true, false⟩)
  return (x, y)

-- ResourceExample R20, restated: `View.share` becomes reindexing along
-- `Sum.elim id (fun _ => ⟨⟩)`. Not weaker.
example : simulateQ (left.answer (fun _ => smallRealization))
    (simulateQ shared.impl readShared) = (3, 2) := rfl

/-- Index `false` takes a `Bool` query and answers a `Nat`; index `true` takes a `Fin 2` query
and answers a `Bool`. -/
@[reducible] def mixedInterface : (r : Bool) → OracleInterface (Carrier r)
  | false =>
    { Query := Bool
      toOC.spec := fun _ => Nat
      toOC.impl _ := do return (← read).val }
  | true =>
    { Query := Fin 2
      toOC.spec := fun _ => Bool
      toOC.impl query := do return decide (query.val < (← read).val) }

/-- The oracle at index `r` with the index-dependent interface. -/
abbrev mixedSlot (r : Bool) : OracleBundle := OracleBundle.of (Carrier r) (mixedInterface r)

/-- Query and response types vary with the index. -/
def mixedModel : OracleBundle := OracleBundle.ofIndexed Carrier mixedInterface

/-- The renamed bundle with index-dependent interfaces. -/
abbrev mixedRenamed := OracleBundle.indexed (mixedSlot ∘ Bool.not)

/-- After renaming, output index `false` takes a `Fin 2` query and answers a `Bool`. -/
def readMixed : OracleComp mixedRenamed.spec (Bool × Nat) := do
  let bit : Bool ← liftM (mixedRenamed.spec.query ⟨false, (1 : Fin 2)⟩)
  let value : Nat ← liftM (mixedRenamed.spec.query ⟨true, false⟩)
  return (bit, value)

-- ResourceExample R21, restated: the old-layer model with name-dependent query and response types
-- becomes an indexed bundle with per-index interfaces, renamed by reindexing along `Bool.not`.
-- Not weaker.
example : simulateQ (mixedModel.answer bothEnv)
    (simulateQ (OracleMap.reindex mixedSlot Bool.not).impl readMixed) = (true, 2) := rfl

/-- Polynomials of degree below two, as a carrier subtype. -/
abbrev LowDegree := {p : Polynomial Nat // p.natDegree < 2}

/-- Evaluation is the only query. -/
@[reducible] def evaluation : OracleInterface LowDegree where
  Query := Nat
  toOC.spec := fun _ => Nat
  toOC.impl point := do return (← read).val.eval point

/-- One polynomial oracle. -/
def polynomials : OracleBundle :=
  OracleBundle.ofIndexed (fun _ : Unit => LowDegree) fun _ => evaluation

/-- The polynomial `X`, whose carrier certifies its degree bound. -/
noncomputable def linearRealization : LowDegree := ⟨Polynomial.X, by simp⟩

-- ResourceExample R22 (two examples), restated: the old-layer polynomial model becomes an indexed
-- bundle with carrier `{p // natDegree < 2}` and an evaluation interface. Not weaker.
example :
    polynomials.answer (fun _ => linearRealization) ⟨(), (3 : Nat)⟩ =
      (3 : Nat) := by
  change (Polynomial.X : Polynomial Nat).eval 3 = 3
  simp

example :
    polynomials.answer (fun _ => linearRealization) ⟨(), (7 : Nat)⟩ =
      (7 : Nat) := by
  change (Polynomial.X : Polynomial Nat).eval 7 = 7
  simp

-- ResourceExample R23, restated: the old-layer reified guarantee becomes the carrier subtype.
-- The degree bound holds of every realization of the bundle, in particular of
-- `linearRealization`.
example (x : polynomials.Data) (i : Unit) : (x i).val.natDegree < 2 :=
  (x i).property

example : linearRealization.val.natDegree < 2 := linearRealization.property

-- ResourceExample R9: the alias reads the original three-valued carrier, including its bound.
/-- Every aliased realization satisfies its carrier's bound. -/
example (data : left.Data) : (aliases.f data true).val < 3 :=
  (data ()).isLt

-- ResourceExample R10 and R11: the numerical false property remains expressible without symbols.
/-- The zero realization does not satisfy a strict bound of zero. -/
example : ¬ (0 : Carrier false).val < 0 := Nat.not_lt_zero _

/-- No family of proofs can impose the impossible bound zero on every three-valued object. -/
example (h : ∀ obj : Carrier false, obj.val < 0) : False := Nat.not_lt_zero _ (h 0)

/-- The zero object in each of the two independently indexed carriers. -/
def zeroRealization (index : Bool) : Carrier index :=
  ⟨0, by cases index <;> decide⟩

-- ResourceExample R12 and R13: equal answers do not identify the two bundle indices.
/-- The two zero objects have equal query behavior. -/
example : (fun query : Bool => model.answer zeroRealization ⟨false, query⟩) =
    (fun query : Bool => model.answer zeroRealization ⟨true, query⟩) := rfl

/-- The indices of the two equal-behavior objects are still distinct. -/
example (query : Bool) : (⟨false, query⟩ : model.Query) ≠ ⟨true, query⟩ :=
  fun h => Bool.false_ne_true (congrArg Sigma.fst h)

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
def noOutputs : OracleBundle := OracleBundle.ofIndexed (fun _ : PEmpty => PUnit) fun x => x.elim

/-- A verifier consumes an R27-shaped view at `Type`.
Its decision reads the selected query from the whole
context's unencoded data. -/
def viewVerifier {Response : (n : Name) → Query n → Type}
    (answer : ∀ n, Realization n → (q : Query n) → Response n q)
    {Index : Type} (name : Index → Name) {Visible : Type} (select : Visible → Index)
    (x : Visible) (query : Query (name (select x))) :
    OracleVerifier (PEmpty →ₒ PUnit) (.pure ⟨⟩ : OracleProtocol.{0, 0})
      PUnit (fun _ => Response (name (select x)) query)
      (viewBundle answer name select) (fun _ => noOutputs) where
  decide _ p _ := liftM
    (((PEmpty →ₒ PUnit) +
      (pathBundle (viewBundle answer name select)
        (.pure ⟨⟩ : OracleProtocol.{0, 0}) p).spec).query (.inr (.inl ⟨x, query⟩)))
  outputMap _ _ _ :=
    { f := fun _ x => x.elim
      impl := fun query => query.1.elim
      law := fun _ query => query.1.elim }

/-- The R26 verifier is the identity-view specialization of the R27 verifier. -/
abbrev namedVerifier {Response : (n : Name) → Query n → Type}
    (answer : ∀ n, Realization n → (q : Query n) → Response n q)
    {Index : Type} (name : Index → Name) (x : Index) (query : Query (name x)) :
    OracleVerifier (PEmpty →ₒ PUnit) (.pure ⟨⟩ : OracleProtocol.{0, 0})
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

/-- The bundle of each named oracle, with its explicit interface. -/
abbrev namedSlot (O : ∀ n, OracleInterface.{0, 0} (Realization n)) (n : Name) : OracleBundle :=
  OracleBundle.of (Realization n) (O n)

-- Indexed bundles specialize the bundle contracts.
/-- A bundle of selected oracles keeps the context, query and data-index carriers at `Type`. -/
example (O : ∀ n, OracleInterface.{0, 0} (Realization n)) (name : Index → Name) :
    OracleBundle := OracleBundle.indexed (namedSlot O ∘ name)

/-- Selecting interfaces preserves the context's query indices. -/
example (O : ∀ n, OracleInterface.{0, 0} (Realization n)) (name : Index → Name) :
    OracleSpec.{0, 0} ((x : Index) × (O (name x)).Query) :=
  (OracleBundle.indexed (namedSlot O ∘ name)).spec

/-- Context data answers all selected queries. -/
example (O : ∀ n, OracleInterface.{0, 0} (Realization n)) (name : Index → Name) :
    (∀ x, Realization (name x)) → QueryImpl (OracleBundle.indexed (namedSlot O ∘ name)).spec Id :=
  (OracleBundle.indexed (namedSlot O ∘ name)).answer

-- The indexed specialization keeps the original context when routing through a view.
/-- An arbitrary view changes query indices without changing the original context data. -/
example (O : ∀ n, OracleInterface.{0, 0} (Realization n)) (name : Index → Name)
    (view : View → Index) (data : ∀ x, Realization (name x)) :
    QueryImpl (OracleBundle.indexed (namedSlot O ∘ (name ∘ view))).spec Id :=
  (OracleBundle.indexed (namedSlot O ∘ (name ∘ view))).answer
    ((OracleMap.reindex (namedSlot O ∘ name) view).f data)

/-- View queries keep the selected name's dependent query carrier. -/
example (O : ∀ n, OracleInterface.{0, 0} (Realization n)) (name : Index → Name)
    (view : View → Index) :
    OracleSpec.{0, 0} ((x : View) × (O (name (view x))).Query) :=
  (OracleBundle.indexed (namedSlot O ∘ (name ∘ view))).spec

/-- Routing through a view answers from the original context at the selected index. -/
example (O : ∀ n, OracleInterface.{0, 0} (Realization n)) (name : Index → Name)
    (view : View → Index) (data : ∀ x, Realization (name x))
    (x : View) (query : (O (name (view x))).Query) :
    (OracleBundle.indexed (namedSlot O ∘ (name ∘ view))).answer
        ((OracleMap.reindex (namedSlot O ∘ name) view).f data) ⟨x, query⟩ =
      (OracleBundle.indexed (namedSlot O ∘ name)).answer data ⟨view x, query⟩ := rfl

end Universes

end Interaction.BundleFamiliesTests
