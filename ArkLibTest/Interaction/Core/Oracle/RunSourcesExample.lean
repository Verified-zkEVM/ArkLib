/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Composition

/-!
# Decision resources of a completed run: distinct slots and hidden coordinates

The resources of a completed run are the input family and the oracle nodes on its path, with data
read from the full transcript. Same-signature slots stay distinct, an unqueried coordinate of a
message is not observable, and a path through an uninhabited oracle node has no payload. For an
appended protocol whose suffix shape is selected by a prefix message, the appended run's resources
answer every component slot as the two component runs do.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp

namespace Interaction.Core.RunSourcesExampleTests

/-- Only the first coordinate of a sent pair can be queried. -/
@[reducible] def interface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := fun _ => Nat
  toOC.impl _ := do return (← read).1

/-- One scalar input slot. -/
@[instance_reducible] def inputs : OracleFamily PUnit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The input slot holds 7. -/
def inputData : ∀ i, inputs.Realization i := fun _ => 7

/-- A prover message `Bool`, then two oracle sends of equal signature. -/
@[instance_reducible] def tree : OracleProtocol :=
  .liftBind (.message Bool) fun _ =>
    .liftBind (.oracle (Nat × Nat) interface) fun _ =>
      .liftBind (.oracle (Nat × Nat) interface) fun _ => .pure ⟨⟩

/-- A run whose messages carry a private second coordinate. -/
def path (hidden : Nat) : PathAlong oracleSig tree :=
  ⟨true, (11, hidden), (19, hidden + 1), ⟨⟩⟩

/-- The decision resources on the shape path of `path`. -/
abbrev resources := sumFamily inputs (pathFamily tree ⟨true, ⟨⟩, ⟨⟩, ⟨⟩⟩)

/-- Read the input, first sent and last sent slots. -/
def readAll : OracleComp resources.spec (Nat × Nat × Nat) := do
  let old : Nat ← liftM (resources.spec.query ⟨.inl ⟨⟩, ()⟩)
  let first : Nat ← liftM (resources.spec.query ⟨.inr (.inl ⟨⟩), ()⟩)
  let last : Nat ← liftM (resources.spec.query ⟨.inr (.inr (.inl ⟨⟩)), ()⟩)
  return (old, first, last)

-- RunSourcesExample RS1, restated: the frozen closing handler becomes the resources of the
-- completed run, `sumFamily inputs (pathFamily tree p)` answered from the input data and the
-- payloads of the same transcript. The frozen public `Bool` is a prover message, and the frozen
-- behaviour-only input `fun _ => 7` is input data 7. Holds for every hidden value.
example (hidden : Nat) :
    simulateQ ((sumFamily inputs (pathFamily tree (projectPathAlong oracleSig tree (path hidden)))
      ).behaviorOfRealizations (sumData inputData (payloads tree (path hidden)))) readAll =
      (7, 11, 19) := rfl

-- RunSourcesExample RS2, restated: the resource handler of the run does not depend on the private
-- coordinate of either message.
example (hidden₁ hidden₂ : Nat) :
    (sumFamily inputs (pathFamily tree (projectPathAlong oracleSig tree (path hidden₁)))
      ).behaviorOfRealizations (sumData inputData (payloads tree (path hidden₁))) =
    (sumFamily inputs (pathFamily tree (projectPathAlong oracleSig tree (path hidden₂)))
      ).behaviorOfRealizations (sumData inputData (payloads tree (path hidden₂))) := by
  funext q
  rcases q with ⟨_ | (_ | (_ | i)), _⟩
  · rfl
  · rfl
  · rfl
  · exact i.elim

/-- An oracle node whose carrier is uninhabited. -/
@[instance_reducible] def impossible : OracleProtocol :=
  .liftBind (.oracle Empty OracleInterface.instDefault) fun _ => .pure ⟨⟩

-- RunSourcesExample RS3, restated: the shape path through an `Empty` oracle node exists, its
-- oracle index exists, and the payload at that index does not; no full transcript exists either.
example : IsEmpty (OracleData impossible ⟨⟨⟩, ⟨⟩⟩ (.inl ⟨⟩)) := by
  change IsEmpty Empty
  infer_instance

example : IsEmpty (PathAlong oracleSig impossible) :=
  ⟨fun tr => tr.1.elim⟩

/-! ## Dependent append with distinguishable slots

A prover message `Bool` selects the suffix shape: one oracle send, or a `Unit` message followed by
two sends. The messages keep private coordinates, and all same-signature slots stay distinct. -/

/-- A prover message `Bool`, then one oracle send. -/
@[instance_reducible] def firstTree : OracleProtocol :=
  .liftBind (.message Bool) fun _ =>
    .liftBind (.oracle (Nat × Nat) interface) fun _ => .pure ⟨⟩

/-- The suffix shape selected by the prefix message. -/
@[instance_reducible] def secondTree : Path firstTree → OracleProtocol
  | ⟨true, _⟩ => .liftBind (.oracle (Nat × Nat) interface) fun _ => .pure ⟨⟩
  | ⟨false, _⟩ => .liftBind (.message Unit) fun _ =>
      .liftBind (.oracle (Nat × Nat) interface) fun _ =>
        .liftBind (.oracle (Nat × Nat) interface) fun _ => .pure ⟨⟩

/-- The appended protocol. -/
abbrev combined := firstTree.append secondTree

/-- The prefix run. -/
def firstPath (branch : Bool) (hidden : Nat) : PathAlong oracleSig firstTree :=
  ⟨branch, (11, hidden), ⟨⟩⟩

/-- The suffix run selected by the prefix message. -/
def secondPath (branch : Bool) (hidden : Nat) :
    PathAlong oracleSig
      (secondTree (projectPathAlong oracleSig firstTree (firstPath branch hidden))) :=
  match branch with
  | true => ⟨(19, hidden + 1), ⟨⟩⟩
  | false => ⟨(), (23, hidden + 1), (29, hidden + 2), ⟨⟩⟩

/-- The appended run. -/
def combinedPath (branch : Bool) (hidden : Nat) : PathAlong oracleSig combined :=
  PathAlong.append oracleSig firstTree secondTree (firstPath branch hidden)
    (secondPath branch hidden)

-- RunSourcesExample RS8, restated: splitting the projected appended path selects the same
-- dependent suffix as projecting the two component runs; this is `project_split` with the
-- concrete `PathAlong.split` of an appended run. Holds for every branch and hidden value.
example (branch : Bool) (hidden : Nat) :
    Path.split firstTree secondTree
      (projectPathAlong oracleSig combined (combinedPath branch hidden)) =
      ⟨projectPathAlong oracleSig firstTree (firstPath branch hidden),
        projectPathAlong oracleSig _ (secondPath branch hidden)⟩ := by
  rw [← project_split, combinedPath, PathAlong.split_append]

/-- The component resources: the input, the prefix slots and the suffix slots. -/
abbrev splitResources (branch : Bool) (hidden : Nat) :=
  sumFamily inputs (sumFamily
    (pathFamily firstTree (projectPathAlong oracleSig firstTree (firstPath branch hidden)))
    (pathFamily _ (projectPathAlong oracleSig _ (secondPath branch hidden))))

/-- The component data of the two runs. -/
def splitData (branch : Bool) (hidden : Nat) : ∀ i, (splitResources branch hidden).Realization i :=
  sumData inputData (sumData (payloads firstTree (firstPath branch hidden))
    (payloads _ (secondPath branch hidden)))

/-- Query the input and each prefix and suffix slot, in slot order. -/
def readSplit (branch : Bool) (hidden : Nat) :
    OracleComp (splitResources branch hidden).spec (List Nat) :=
  match branch with
  | true => do
    let old : Nat ← liftM ((splitResources true hidden).spec.query ⟨.inl ⟨⟩, ()⟩)
    let first : Nat ← liftM ((splitResources true hidden).spec.query ⟨.inr (.inl (.inl ⟨⟩)), ()⟩)
    let last : Nat ← liftM ((splitResources true hidden).spec.query ⟨.inr (.inr (.inl ⟨⟩)), ()⟩)
    return [old, first, last]
  | false => do
    let old : Nat ← liftM ((splitResources false hidden).spec.query ⟨.inl ⟨⟩, ()⟩)
    let first : Nat ← liftM ((splitResources false hidden).spec.query ⟨.inr (.inl (.inl ⟨⟩)), ()⟩)
    let next : Nat ← liftM ((splitResources false hidden).spec.query ⟨.inr (.inr (.inl ⟨⟩)), ()⟩)
    let last : Nat ←
      liftM ((splitResources false hidden).spec.query ⟨.inr (.inr (.inr (.inl ⟨⟩))), ()⟩)
    return [old, first, next, last]

-- RunSourcesExample RS9, restated: the frozen prefix-then-suffix closing becomes the component
-- resources `sumFamily inputs (sumFamily (pathFamily …) (pathFamily …))` with the payloads of the
-- two component runs. Both suffix shapes answer each slot. Holds for every hidden value.
theorem readSplit_split (branch : Bool) (hidden : Nat) :
    simulateQ ((splitResources branch hidden).behaviorOfRealizations (splitData branch hidden))
      (readSplit branch hidden) = if branch then [7, 11, 19] else [7, 11, 23, 29] := by
  cases branch <;> rfl

/-- Route component queries into the appended run's resources: the input stays, and the oracle
slots go through `oracles_split`. -/
def splitRoute (branch : Bool) (hidden : Nat) :=
  (OracleMap.embedding inputs id).sum
    (oracles_split firstTree secondTree
      (projectPathAlong oracleSig firstTree (firstPath branch hidden))
      (projectPathAlong oracleSig _ (secondPath branch hidden)))

/-- The appended run's resources and data. -/
abbrev combinedResources (branch : Bool) (hidden : Nat) :=
  sumFamily inputs (pathFamily combined
    (projectPathAlong oracleSig combined (combinedPath branch hidden)))

def combinedData (branch : Bool) (hidden : Nat) :
    ∀ i, (combinedResources branch hidden).Realization i :=
  sumData inputData (payloads combined (combinedPath branch hidden))

/-- On this run, the appended path materializes exactly the routed component payloads. -/
theorem payloads_combined (branch : Bool) (hidden : Nat) :
    payloads combined (combinedPath branch hidden) =
      (oracles_append firstTree secondTree
        (projectPathAlong oracleSig firstTree (firstPath branch hidden))
        (projectPathAlong oracleSig _ (secondPath branch hidden))).f
        (sumData (payloads firstTree (firstPath branch hidden))
          (payloads _ (secondPath branch hidden))) :=
  eq_of_heq (Sigma.mk.inj (payloads_append firstTree secondTree (firstPath branch hidden)
    (secondPath branch hidden))).2

-- RunSourcesExample RS10, restated: the frozen append query law for closing handlers becomes the
-- appended run's resources answering the component program through `oracles_split`. The proof
-- uses the oracle map law (`OracleMap.simulate_eq`), the payload append law (`payloads_append`)
-- and `oracles_split_append`, then RS9. Holds for every branch and hidden value.
example (branch : Bool) (hidden : Nat) :
    simulateQ ((combinedResources branch hidden).behaviorOfRealizations
        (combinedData branch hidden))
      (simulateQ (splitRoute branch hidden).impl (readSplit branch hidden)) =
      if branch then [7, 11, 19] else [7, 11, 23, 29] := by
  refine (OracleMap.simulate_eq (splitRoute branch hidden) (combinedData branch hidden)
    (readSplit branch hidden)).trans ((congrArg (fun x => simulateQ
      ((splitResources branch hidden).behaviorOfRealizations x) (readSplit branch hidden))
      ?_).trans (readSplit_split branch hidden))
  funext i
  rcases i with i | i
  · rfl
  · exact (congrArg (fun d => (oracles_split firstTree secondTree _ _).f d i)
      (payloads_combined branch hidden)).trans
      (congrFun (oracles_split_append firstTree secondTree _ _ _) i)

-- RunSourcesExample RS11, restated: in both suffix shapes, the appended run's resource handler
-- does not depend on the private coordinates.
example (branch : Bool) (hidden₁ hidden₂ : Nat) :
    HEq ((combinedResources branch hidden₁).behaviorOfRealizations (combinedData branch hidden₁))
      ((combinedResources branch hidden₂).behaviorOfRealizations
        (combinedData branch hidden₂)) := by
  cases branch <;> apply heq_of_eq <;> funext q
  · rcases q with ⟨_ | _ | _ | _ | i, _⟩ <;> rfl
  · rcases q with ⟨_ | _ | _ | i, _⟩ <;> rfl

end Interaction.Core.RunSourcesExampleTests
