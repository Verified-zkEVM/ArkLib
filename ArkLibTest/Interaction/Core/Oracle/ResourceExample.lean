/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.OracleVerifier
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Oracle family indices: disjoint sums, aliases and renaming with dependent carriers

Oracle family indices name the oracles. A sum of families keeps two same-interface oracles with
different carrier types apart. An embedding along a non-injective renaming makes two output
indices share one realization; an embedding along `Bool.not` transports a carrier to the renamed
index. Query and response types may vary with the index, and a carrier subtype states a degree
bound that holds of every realization.

The polynomial fixture is noncomputable because Mathlib's `Polynomial` is; it is used only for
the evaluation and degree proofs.
-/

open Interaction.Core Interaction.Oracle OracleComp

namespace Interaction.Core.ResourceExampleTests

/-- The carrier at index `r`: three values for `false`, five for `true`. -/
abbrev Carrier (r : Bool) : Type := Fin (if r then 5 else 3)

/-- A `Bool` query reads the realization's value, plus one when the query is `true`. -/
@[reducible] def countInterface (r : Bool) : OracleInterface (Carrier r) where
  Query := Bool
  toOC.spec := fun _ => Nat
  toOC.impl query := do return (← read).val + (if query then 1 else 0)

/-- Both indices have the same query interface and different carrier types. -/
@[instance_reducible] def model : OracleFamily Bool Carrier := ⟨countInterface⟩

/-- The family holding only index `false`. -/
abbrev left := model.reindex (fun _ : PUnit => false)

/-- The family holding only index `true`. -/
abbrev right := model.reindex (fun _ : PUnit => true)

/-- The disjoint sum of the two single-index families. -/
abbrev pair := sumFamily left right

/-- A concrete realization in the three-valued carrier. -/
def smallRealization : Fin 3 := ⟨2, by decide⟩

/-- A concrete realization in the five-valued carrier. -/
def largeRealization : Fin 5 := ⟨4, by decide⟩

/-- Data for the disjoint sum, of a different carrier type on each side. -/
def pairEnv : ∀ k, pair.Realization k :=
  sumData (fun _ => smallRealization) (fun _ => largeRealization)

/-- Query both sides. -/
def readPair : OracleComp pair.spec (Nat × Nat) := do
  let x : Nat ← liftM (pair.spec.query ⟨.inl ⟨⟩, true⟩)
  let y : Nat ← liftM (pair.spec.query ⟨.inr ⟨⟩, false⟩)
  return (x, y)

-- ResourceExample R4, restated: the frozen disjoint union of two named contexts becomes
-- `sumFamily` of two single-index families with carriers `Fin 3` and `Fin 5`, queried by index.
-- Not weaker.
example : simulateQ (pair.behaviorOfRealizations pairEnv) readPair = (3, 4) := rfl

/-- Two output indices, both reading the one realization of `left`. -/
def aliases := OracleMap.embedding left (fun _ : Bool => PUnit.unit)

/-- Both output indices issue their query. -/
def readAliases : OracleComp (left.reindex (fun _ : Bool => PUnit.unit)).spec (Nat × Nat) := do
  let x : Nat ← liftM ((left.reindex (fun _ : Bool => PUnit.unit)).spec.query ⟨false, false⟩)
  let y : Nat ← liftM ((left.reindex (fun _ : Bool => PUnit.unit)).spec.query ⟨true, false⟩)
  return (x, y)

-- ResourceExample R6, restated: the frozen aliasing view becomes the embedding along a constant
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

-- ResourceExample R16, restated: the frozen inclusion from a reindex becomes the embedding along
-- `Bool.not`; its data map transports the five-valued realization to output index `false`. Not
-- weaker.
example : inclusion.f bothEnv false = (largeRealization : Fin 5) := rfl

/-- Read in the renamed order. -/
def readRenamed : OracleComp (model.reindex Bool.not).spec (Nat × Nat) := do
  let x : Nat ← liftM ((model.reindex Bool.not).spec.query ⟨false, false⟩)
  let y : Nat ← liftM ((model.reindex Bool.not).spec.query ⟨true, true⟩)
  return (x, y)

-- ResourceExample R17, restated: the frozen program routed through the inclusion becomes the
-- program simulated through the embedding's `impl`, then answered from the original data. The
-- same answers follow from the transported data by `OracleMap.simulate_eq`. Not weaker.
example : simulateQ (model.behaviorOfRealizations bothEnv)
    (simulateQ inclusion.impl readRenamed) = (4, 3) := rfl

example : simulateQ ((model.reindex Bool.not).behaviorOfRealizations (inclusion.f bothEnv))
    readRenamed = (4, 3) := by
  rw [← OracleMap.simulate_eq]
  rfl

-- ResourceExample R18, restated: data for the empty family exists without a realization of any
-- model index.
example : ∀ i, (model.reindex (fun i : PEmpty => i.elim)).Realization i := fun i => i.elim

/-- Apply the identity embedding to each side of the sum. -/
def sumOfSides := (OracleMap.embedding left id).sum (OracleMap.embedding right id)

-- ResourceExample R19, restated: the frozen correspondence between a disjoint union and the sum of
-- its interpreted sources becomes the sum of the two side maps; routing `readPair` through it
-- keeps R4's answers. Reassociating with the empty family on the right does too.
example : simulateQ (pair.behaviorOfRealizations pairEnv)
    (simulateQ sumOfSides.impl readPair) = (3, 4) := rfl

/-- The empty family. -/
abbrev noIndices := model.reindex (fun i : PEmpty => i.elim)

example : simulateQ ((sumFamily (sumFamily left right) noIndices).behaviorOfRealizations
      (sumData pairEnv (fun i => i.elim)))
    (simulateQ (OracleMap.assoc left right noIndices).impl
      (simulateQ (OracleMap.unassoc left right noIndices).impl
        (simulateQ (OracleMap.embedding (sumFamily (sumFamily left right) noIndices) Sum.inl).impl
          readPair))) = (3, 4) := rfl

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
      toOC.spec := fun _ => Nat
      toOC.impl _ := do return (← read).val }
  | true =>
    { Query := Fin 2
      toOC.spec := fun _ => Bool
      toOC.impl query := do return decide (query.val < (← read).val) }

/-- Query and response types vary with the index. -/
@[instance_reducible] def mixedModel : OracleFamily Bool Carrier := ⟨mixedInterface⟩

/-- After renaming, output index `false` takes a `Fin 2` query and answers a `Bool`. -/
def readMixed : OracleComp (mixedModel.reindex Bool.not).spec (Bool × Nat) := do
  let bit : Bool ← liftM ((mixedModel.reindex Bool.not).spec.query ⟨false, (1 : Fin 2)⟩)
  let value : Nat ← liftM ((mixedModel.reindex Bool.not).spec.query ⟨true, false⟩)
  return (bit, value)

-- ResourceExample R21, restated: the frozen model with name-dependent query and response types
-- becomes an oracle family with per-index interfaces, renamed by the embedding along `Bool.not`.
-- Not weaker.
example : simulateQ (mixedModel.behaviorOfRealizations bothEnv)
    (simulateQ (OracleMap.embedding mixedModel Bool.not).impl readMixed) = (true, 2) := rfl

/-- Polynomials of degree below two, as a carrier subtype. -/
abbrev LowDegree := {p : Polynomial Nat // p.natDegree < 2}

/-- Evaluation is the only query. -/
@[reducible] def evaluation : OracleInterface LowDegree where
  Query := Nat
  toOC.spec := fun _ => Nat
  toOC.impl point := do return (← read).val.eval point

/-- One polynomial oracle. -/
@[instance_reducible] def polynomials : OracleFamily Unit (fun _ => LowDegree) :=
  ⟨fun _ => evaluation⟩

/-- The polynomial `X`, whose carrier certifies its degree bound. -/
noncomputable def linearRealization : LowDegree := ⟨Polynomial.X, by simp⟩

-- ResourceExample R22 (two examples), restated: the frozen polynomial model becomes a family
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

-- ResourceExample R23, restated (OQ5): the frozen reified guarantee becomes the carrier subtype.
-- The degree bound holds of every realization of the family, in particular of
-- `linearRealization`.
example (x : ∀ i, polynomials.Realization i) (i : Unit) : (x i).val.natDegree < 2 :=
  (x i).property

example : linearRealization.val.natDegree < 2 := linearRealization.property

end Interaction.Core.ResourceExampleTests
