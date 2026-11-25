/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Composition

/-!
# The decision bundle of a completed run: distinct oracles and hidden coordinates

The bundle of a completed run consists of the input family and the oracle nodes on its path, with
data read from the full transcript. Same-signature oracles stay distinct, an unqueried coordinate
of a message is not observable, and a path through an uninhabited oracle node has no oracle
message. For an appended protocol whose suffix shape is selected by a prefix message, the appended
run's bundle answers every component oracle as the two component runs do.
-/

open PFunctor PFunctor.FreeM Interaction Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp

namespace Interaction.RunBundlesTests

/-- Only the first coordinate of a sent pair can be queried. -/
@[reducible] def interface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := fun _ => Nat
  toOC.impl _ := do return (← read).1

/-- One scalar input oracle. -/
def inputs : OracleFamily PUnit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The input oracle holds 7. -/
def inputData : ∀ i, inputs.Realization i := fun _ => 7

/-- A prover message `Bool`, then two oracle sends of equal signature. -/
def tree : OracleProtocol :=
  .liftBind (.message Bool) fun _ =>
    .liftBind (.oracle (Nat × Nat) interface) fun _ =>
      .liftBind (.oracle (Nat × Nat) interface) fun _ => .pure ⟨⟩

/-- A run whose messages carry a private second coordinate. -/
def path (hidden : Nat) : Transcript oracleSig tree :=
  ⟨true, (11, hidden), (19, hidden + 1), ⟨⟩⟩

/-- The decision bundle on the path of `path`. -/
abbrev pathData := sumFamily inputs (oracleMessageFamily tree ⟨true, ⟨⟩, ⟨⟩, ⟨⟩⟩)

/-- Read the input, first sent and last sent oracles. -/
def readAll : OracleComp pathData.spec (Nat × Nat × Nat) := do
  let old : Nat ← liftM (pathData.spec.query ⟨.inl ⟨⟩, ()⟩)
  let first : Nat ← liftM (pathData.spec.query ⟨.inr (.inl ⟨⟩), ()⟩)
  let last : Nat ← liftM (pathData.spec.query ⟨.inr (.inr (.inl ⟨⟩)), ()⟩)
  return (old, first, last)

-- RunSourcesExample RS1, restated: the old-layer closing handler becomes the bundle of the
-- completed run, `sumFamily inputs (oracleMessageFamily tree p)` answered from the input data and
-- the oracle messages of the same transcript. The old-layer public `Bool` is a prover message, and
-- the old-layer behaviour-only input `fun _ => 7` is input data 7. Holds for every hidden value.
example (hidden : Nat) :
    simulateQ ((sumFamily inputs (oracleMessageFamily tree (Transcript.path (path hidden)))
      ).behaviorOfRealizations (sumData inputData (oracleMessages tree (path hidden)))) readAll =
      (7, 11, 19) := rfl

-- RunSourcesExample RS2, restated: the bundle handler of the run does not depend on the private
-- coordinate of either message.
example (hidden₁ hidden₂ : Nat) :
    (sumFamily inputs (oracleMessageFamily tree (Transcript.path (path hidden₁)))
      ).behaviorOfRealizations (sumData inputData (oracleMessages tree (path hidden₁))) =
    (sumFamily inputs (oracleMessageFamily tree (Transcript.path (path hidden₂)))
      ).behaviorOfRealizations (sumData inputData (oracleMessages tree (path hidden₂))) := by
  funext q
  rcases q with ⟨_ | (_ | (_ | i)), _⟩
  · rfl
  · rfl
  · rfl
  · exact i.elim

/-- An oracle node whose carrier is uninhabited. -/
def impossible : OracleProtocol :=
  .liftBind (.oracle Empty OracleInterface.instDefault) fun _ => .pure ⟨⟩

-- RunSourcesExample RS3, restated: the path through an `Empty` oracle node and its oracle index
-- exist. The oracle message at that index does not, and no full transcript exists either.
example : IsEmpty (OracleMessage impossible ⟨⟨⟩, ⟨⟩⟩ (.inl ⟨⟩)) := by
  change IsEmpty Empty
  infer_instance

example : IsEmpty (Transcript oracleSig impossible) :=
  ⟨fun tr => tr.1.elim⟩

/-! ## Dependent append with distinguishable oracles

A prover message `Bool` selects the suffix shape: one oracle send, or a `Unit` message followed by
two sends. The messages keep private coordinates, and all same-signature oracles stay distinct. -/

/-- A prover message `Bool`, then one oracle send. -/
def firstTree : OracleProtocol :=
  .liftBind (.message Bool) fun _ =>
    .liftBind (.oracle (Nat × Nat) interface) fun _ => .pure ⟨⟩

/-- The suffix shape selected by the prefix message. -/
def secondTree : Path firstTree → OracleProtocol
  | ⟨true, _⟩ => .liftBind (.oracle (Nat × Nat) interface) fun _ => .pure ⟨⟩
  | ⟨false, _⟩ => .liftBind (.message Unit) fun _ =>
      .liftBind (.oracle (Nat × Nat) interface) fun _ =>
        .liftBind (.oracle (Nat × Nat) interface) fun _ => .pure ⟨⟩

/-- The appended protocol. -/
abbrev combined := firstTree.append secondTree

/-- The prefix run. -/
def firstPath (branch : Bool) (hidden : Nat) : Transcript oracleSig firstTree :=
  ⟨branch, (11, hidden), ⟨⟩⟩

/-- The suffix run selected by the prefix message. -/
def secondPath (branch : Bool) (hidden : Nat) :
    Transcript oracleSig
      (secondTree (Transcript.path (firstPath branch hidden))) :=
  match branch with
  | true => ⟨(19, hidden + 1), ⟨⟩⟩
  | false => ⟨(), (23, hidden + 1), (29, hidden + 2), ⟨⟩⟩

/-- The appended run. -/
def combinedPath (branch : Bool) (hidden : Nat) : Transcript oracleSig combined :=
  Transcript.append firstTree secondTree (firstPath branch hidden)
    (secondPath branch hidden)

-- RunSourcesExample RS4: tree conversion is absent; the dependent appended shape is explicit.
/-- Appending preserves the one-send and two-send suffix shapes selected by the message. -/
example : combined = .liftBind (.message Bool) (fun branch =>
    .liftBind (.oracle (Nat × Nat) interface) (fun _ => match branch with
      | true => .liftBind (.oracle (Nat × Nat) interface) (fun _ => .pure ⟨⟩)
      | false => .liftBind (.message Unit) (fun _ =>
          .liftBind (.oracle (Nat × Nat) interface) (fun _ =>
            .liftBind (.oracle (Nat × Nat) interface) (fun _ => .pure ⟨⟩))))) := by
  apply congrArg (FreeM.liftBind (P := OraclePoly) (OraclePos.message Bool))
  funext branch
  cases branch <;> rfl

-- RunSourcesExample RS7: the concrete transcript split keeps every sent and hidden coordinate.
/-- Splitting the appended transcript recovers both full component transcripts. -/
example (branch : Bool) (hidden : Nat) :
    Transcript.split firstTree secondTree (combinedPath branch hidden) =
      ⟨firstPath branch hidden, secondPath branch hidden⟩ :=
  Transcript.split_append firstTree secondTree (firstPath branch hidden)
    (secondPath branch hidden)

-- RunSourcesExample RS8, restated: splitting the projected appended path selects the same
-- dependent suffix as projecting the two component runs. This is `project_split` with the
-- concrete `PathAlong.split` of an appended run. Holds for every branch and hidden value.
example (branch : Bool) (hidden : Nat) :
    Path.split firstTree secondTree
      (Transcript.path (combinedPath branch hidden)) =
      ⟨Transcript.path (firstPath branch hidden),
        Transcript.path (secondPath branch hidden)⟩ := by
  rw [← project_split, combinedPath, Transcript.split_append]

/-- The component bundle: the input, the prefix oracles and the suffix oracles. -/
abbrev splitPathBundle (branch : Bool) (hidden : Nat) :=
  sumFamily inputs (sumFamily
    (oracleMessageFamily firstTree (Transcript.path (firstPath branch hidden)))
    (oracleMessageFamily _ (Transcript.path (secondPath branch hidden))))

/-- The component data of the two runs. -/
def splitData (branch : Bool) (hidden : Nat) : ∀ i, (splitPathBundle branch hidden).Realization i :=
  sumData inputData (sumData (oracleMessages firstTree (firstPath branch hidden))
    (oracleMessages _ (secondPath branch hidden)))

/-- Query the input and each prefix and suffix oracle, in oracle order. -/
def readSplit (branch : Bool) (hidden : Nat) :
    OracleComp (splitPathBundle branch hidden).spec (List Nat) :=
  match branch with
  | true => do
    let old : Nat ← liftM ((splitPathBundle true hidden).spec.query ⟨.inl ⟨⟩, ()⟩)
    let first : Nat ← liftM ((splitPathBundle true hidden).spec.query ⟨.inr (.inl (.inl ⟨⟩)), ()⟩)
    let last : Nat ← liftM ((splitPathBundle true hidden).spec.query ⟨.inr (.inr (.inl ⟨⟩)), ()⟩)
    return [old, first, last]
  | false => do
    let old : Nat ← liftM ((splitPathBundle false hidden).spec.query ⟨.inl ⟨⟩, ()⟩)
    let first : Nat ← liftM ((splitPathBundle false hidden).spec.query ⟨.inr (.inl (.inl ⟨⟩)), ()⟩)
    let next : Nat ← liftM ((splitPathBundle false hidden).spec.query ⟨.inr (.inr (.inl ⟨⟩)), ()⟩)
    let last : Nat ←
      liftM ((splitPathBundle false hidden).spec.query ⟨.inr (.inr (.inr (.inl ⟨⟩))), ()⟩)
    return [old, first, next, last]

-- RunSourcesExample RS9, restated: the old-layer prefix-then-suffix closing becomes the component
-- bundle `sumFamily inputs (sumFamily (oracleMessageFamily …) (oracleMessageFamily …))` with the
-- oracle messages of the two component runs. Both suffix shapes answer each oracle. Holds for every
-- hidden value.
/-- Closing the two component runs answers each queried oracle in the selected suffix shape. -/
theorem readSplit_split (branch : Bool) (hidden : Nat) :
    simulateQ ((splitPathBundle branch hidden).behaviorOfRealizations (splitData branch hidden))
      (readSplit branch hidden) = if branch then [7, 11, 19] else [7, 11, 23, 29] := by
  cases branch <;> rfl

/-- Route component queries into the appended run's bundle: the input stays, and the oracle
nodes go through `oracleMessageFamily_split`. -/
def splitRoute (branch : Bool) (hidden : Nat) :=
  (OracleMap.embedding inputs id).sum
    (oracleMessageFamily_split firstTree secondTree
      (Transcript.path (firstPath branch hidden))
      (Transcript.path (secondPath branch hidden)))

/-- The appended run's bundle and data. -/
abbrev combinedBundle (branch : Bool) (hidden : Nat) :=
  sumFamily inputs (oracleMessageFamily combined
    (Transcript.path (combinedPath branch hidden)))

/-- The input data and oracle messages of the appended transcript. -/
def combinedData (branch : Bool) (hidden : Nat) :
    ∀ i, (combinedBundle branch hidden).Realization i :=
  sumData inputData (oracleMessages combined (combinedPath branch hidden))

/-- On this run, the appended path materializes exactly the routed component oracle messages. -/
theorem payloads_combined (branch : Bool) (hidden : Nat) :
    oracleMessages combined (combinedPath branch hidden) =
      (oracleMessageFamily_append firstTree secondTree
        (Transcript.path (firstPath branch hidden))
        (Transcript.path (secondPath branch hidden))).f
        (sumData (oracleMessages firstTree (firstPath branch hidden))
          (oracleMessages _ (secondPath branch hidden))) :=
  eq_of_heq (Sigma.mk.inj (oracleMessages_append firstTree secondTree (firstPath branch hidden)
    (secondPath branch hidden))).2

-- RunSourcesExample RS10, restated: the old-layer append query law for closing handlers becomes the
-- appended run's bundle answering the component program through `oracleMessageFamily_split`. The
-- proof uses the oracle map law (`OracleMap.simulate_eq`), the append law for oracle messages
-- (`oracleMessages_append`) and `oracleMessageFamily_split_append`, then RS9. Holds for every
-- branch and hidden value.
example (branch : Bool) (hidden : Nat) :
    simulateQ ((combinedBundle branch hidden).behaviorOfRealizations
        (combinedData branch hidden))
      (simulateQ (splitRoute branch hidden).impl (readSplit branch hidden)) =
      if branch then [7, 11, 19] else [7, 11, 23, 29] := by
  refine (OracleMap.simulate_eq (splitRoute branch hidden) (combinedData branch hidden)
    (readSplit branch hidden)).trans ((congrArg (fun x => simulateQ
      ((splitPathBundle branch hidden).behaviorOfRealizations x) (readSplit branch hidden))
      ?_).trans (readSplit_split branch hidden))
  funext i
  rcases i with i | i
  · rfl
  · exact (congrArg (fun d => (oracleMessageFamily_split firstTree secondTree _ _).f d i)
      (payloads_combined branch hidden)).trans
      (congrFun (oracleMessageFamily_split_append firstTree secondTree _ _ _) i)

-- RunSourcesExample RS11, restated: in both suffix shapes, the appended run's bundle handler
-- does not depend on the private coordinates.
example (branch : Bool) (hidden₁ hidden₂ : Nat) :
    HEq ((combinedBundle branch hidden₁).behaviorOfRealizations (combinedData branch hidden₁))
      ((combinedBundle branch hidden₂).behaviorOfRealizations
        (combinedData branch hidden₂)) := by
  cases branch <;> apply heq_of_eq <;> funext q
  · rcases q with ⟨_ | _ | _ | _ | i, _⟩ <;> rfl
  · rcases q with ⟨_ | _ | _ | i, _⟩ <;> rfl

/-! ## Receiver-selected shapes in the general two-party signature

The general signature permits a receiver move to select a suffix shape. Ownership comes from
positions, without converting a separate role decoration. -/

/-- A receiver bit followed by one sender pair. -/
abbrev receiverPrefix : FreeM rolePoly.{0} PUnit.{1} :=
  .liftBind (.receiver, Bool) fun _ =>
    .liftBind (.sender, Nat × Nat) fun _ => .pure ⟨⟩

/-- One sender pair, or a sender unit followed by two sender pairs. -/
abbrev receiverSuffix : Path receiverPrefix → FreeM rolePoly.{0} PUnit.{1}
  | ⟨true, _, _⟩ => .liftBind (.sender, Nat × Nat) fun _ => .pure ⟨⟩
  | ⟨false, _, _⟩ => .liftBind (.sender, Unit) fun _ =>
      .liftBind (.sender, Nat × Nat) fun _ =>
        .liftBind (.sender, Nat × Nat) fun _ => .pure ⟨⟩

/-- The protocol whose receiver bit selects the suffix shape. -/
abbrev receiverCombined := receiverPrefix.append receiverSuffix

-- RunSourcesExample RS5: the generic position append law preserves the owner at every node.
/-- Appended ownership is the ownership of the corresponding prefix or suffix position. -/
example (node : Node receiverCombined) :
    owner (PFunctor.Lens.id rolePoly) (node.position receiverCombined) =
      Sum.elim (fun n => owner (PFunctor.Lens.id rolePoly) (n.position receiverPrefix))
        (fun x => owner (PFunctor.Lens.id rolePoly) (x.2.position (receiverSuffix x.1)))
        (Node.appendEquiv receiverPrefix receiverSuffix node) := by
  rw [Node.position_appendEquiv]
  cases Node.appendEquiv receiverPrefix receiverSuffix node <;> rfl

/-- The first sender node in either receiver-selected suffix. -/
abbrev receiverSuffixRoot : (path : Path receiverPrefix) → Node (receiverSuffix path)
  | ⟨true, _, _⟩ => .inl ⟨⟩
  | ⟨false, _, _⟩ => .inl ⟨⟩

-- RunSourcesExample RS6: the root is receiver-owned and each suffix root is sender-owned.
/-- The appended root belongs to the receiver who chooses the bit. -/
example : owner (PFunctor.Lens.id rolePoly)
    (Node.position receiverCombined (.inl ⟨⟩)) = .receiver := rfl

/-- Both suffix roots belong to the sender, for every prefix pair and receiver bit. -/
example (branch : Bool) (message : Nat × Nat) :
    owner (PFunctor.Lens.id rolePoly)
      (Node.position receiverCombined (Node.appendJoin receiverPrefix receiverSuffix
        (.inr ⟨⟨branch, message, ⟨⟩⟩, receiverSuffixRoot ⟨branch, message, ⟨⟩⟩⟩))) = .sender := by
  cases branch <;> rfl

end Interaction.RunBundlesTests
