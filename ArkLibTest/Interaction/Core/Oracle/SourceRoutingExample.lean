/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.Cost

/-!
# The input queries of one exported oracle query

A prefix output map exports `input 0 + sent.1` from two input slots and one sent pair oracle.
Answering one exported query makes exactly two queries to the prefix resources: input slot 0,
then the sent oracle. It never queries input slot 1, and never reads the private coordinate.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle OracleComp

namespace Interaction.Core.SourceRoutingExampleTests

/-- Two scalar input slots; slot 1 is never exported. -/
@[instance_reducible] def inputs : OracleFamily (Fin 2) (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- Slot 0 holds 7; slot 1 holds the hidden value. -/
def inputData (hidden : Nat) : ∀ _ : Fin 2, Nat := fun i => if i = 0 then 7 else hidden

/-- Only the first coordinate of a sent pair is observable. -/
@[reducible] def firstInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := fun _ => Nat
  toOC.impl _ := do return (← read).1

/-- The prefix sends one pair oracle. -/
@[instance_reducible] def firstProtocol : OracleProtocol :=
  .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ => .pure ⟨⟩)

/-- One exported scalar oracle. -/
@[instance_reducible] def exported : OracleFamily PUnit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The prefix resources on its only path. -/
abbrev prefixResources := sumFamily inputs (pathFamily firstProtocol ⟨⟨⟩, ⟨⟩⟩)

/-- Export input slot 0 plus the observable coordinate of the sent pair. -/
def exportMap : OracleMap prefixResources exported where
  f x _ := (show Nat from x (.inl 0)) + (show Nat × Nat from x (.inr (.inl ⟨⟩))).1
  impl _ := do
    let a : Nat ← liftM (prefixResources.spec.query ⟨.inl 0, ()⟩)
    let b : Nat ← liftM (prefixResources.spec.query ⟨.inr (.inl ⟨⟩), ()⟩)
    pure (a + b)
  law x q := by
    simp only [simulateQ_bind]
    rfl

/-- The run that sends `(11, secret)`. -/
def run (secret : Nat) : PathAlong oracleSig firstProtocol := ⟨(11, secret), ⟨⟩⟩

/-- Record the slot of each resource query (`i` for input slot `i`, 2 for the sent oracle) and
answer it from the input data and the payloads of the run. -/
def sourceLog (hidden secret : Nat) : QueryImpl prefixResources.spec (StateM (List Nat)) :=
  fun q => do
    modify (· ++ [match q.1 with
      | .inl i => i.val
      | .inr _ => 2])
    pure (prefixResources.behaviorOfRealizations
      (sumData (inputData hidden) (payloads firstProtocol (run secret))) q)

-- SourceRoutingExample SR2, restated: the frozen virtual-oracle export becomes the `impl` of the
-- prefix output map, run under a logging handler of `sumFamily inputs (pathFamily …)` whose
-- answers come from the input data and the run's payloads. For every hidden input and private
-- coordinate, one exported query makes the queries `[0, 2]` and answers 18. Not weaker.
example (hidden secret : Nat) :
    (simulateQ (sourceLog hidden secret) (exportMap.impl ⟨⟨⟩, ()⟩)).run [] = ((18 : Nat), [0, 2]) :=
  rfl

/-- Each query costs one unit. -/
def unitCost {ι : Type} (spec : OracleSpec ι) : CostModel spec Nat := ⟨fun _ => 1⟩

/-- Every query to the exported oracle is charged two units. -/
def exportCost : CostModel (OracleSpec.emptySpec + exported.spec) Nat :=
  ⟨fun | .inl q => q.elim | .inr _ => 2⟩

/-- The exported query's implementation makes two unit-cost queries. -/
theorem exportMap_cost (q : exported.spec.Domain) :
    WorstCaseCostBound (exportMap.impl q) (unitCost prefixResources.spec) 2 := by
  exact (worstCaseCostBound_query _ _).bind fun _ => (worstCaseCostBound_query _ _).bind
    fun _ => (worstCaseCostBound_pure _ _ (0 : Nat)).mpr le_rfl

-- A use of `OracleMap.withAmbient_worstCaseCost`: one exported query, charged two units, routed
-- through `exportMap` costs at most two unit-cost queries to the prefix resources.
example : WorstCaseCostBound
    (simulateQ (exportMap.withAmbient OracleSpec.emptySpec)
      (liftM ((OracleSpec.emptySpec + exported.spec).query (.inr ⟨⟨⟩, ()⟩)) :
        OracleComp (OracleSpec.emptySpec + exported.spec) Nat))
    (unitCost _) 2 := by
  have hquery : WorstCaseCostBound
      (liftM ((OracleSpec.emptySpec + exported.spec).query (.inr ⟨⟨⟩, ()⟩)) :
        OracleComp (OracleSpec.emptySpec + exported.spec) Nat) exportCost 2 :=
    worstCaseCostBound_query (.inr ⟨⟨⟩, ()⟩) exportCost
  exact OracleMap.withAmbient_worstCaseCost
    (In := Resources.ofFamily prefixResources) (Out := Resources.ofFamily exported)
    (ambient := OracleSpec.emptySpec) (sourceCost := exportCost) (targetCost := unitCost _)
    exportMap hquery (fun q => q.elim) exportMap_cost

end Interaction.Core.SourceRoutingExampleTests

run_cmd do
  for decl in [``Interaction.Core.OracleMap.withAmbient_worstCaseCost] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
