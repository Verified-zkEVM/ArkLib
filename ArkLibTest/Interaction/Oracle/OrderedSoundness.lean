/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.OrderedSoundness
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# A probabilistic client of ordered soundness

Two actual reductions change statements from `Unit` to `Bool` to `Nat`. Each false input
can become accepted and true with probability one quarter. The first stage also rejects one
quarter of its draws. The second stage preserves a true middle statement without any soundness
premise on that input, so both error terms matter. Oracle behavior is retained throughout.
-/

namespace Interaction.Oracle.OrderedSoundnessTest

open OracleComp OracleSpec

noncomputable section

attribute [local implicit_reducible] OracleInterface.toOracleSpec OracleInterface.Response

/-- A scalar interface keeps the boundary state function-valued. -/
@[reducible]
def family : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => OracleInterface.instDefault⟩

/-- Heterogeneous statements share the same retained oracle and trivial private payload. -/
@[reducible]
def boundary (S : Type) : ExecutionInterface := ⟨S, Unit, fun _ => Nat, family, Unit⟩

local instance (S : Type) : MeasurableSpace (boundary S).State := ⊤

local instance (S : Type) : DiscreteMeasurableSpace (boundary S).State := ⟨fun _ => trivial⟩

/-- The output oracle forwards exactly the original behavior. -/
def passthrough : VirtualOracle family.spec family := ⟨fun q => liftM (family.spec.query q)⟩

/-- Sample a fresh challenge and export the selected optional public statement. -/
def stage {S T : Type} (select : S → Fin 4 → Option T) :
    ClosedStage unifSpec (boundary S) (boundary T) where
  protocol := fun _ => .done
  Witness := fun _ => Unit
  OutP := fun _ _ => Unit
  witness := fun _ _ => ()
  nextPrivate := fun _ _ _ _ => ()
  reduction := fun _ => {
    prover := fun _ _ => pure ()
    verifier := fun stmt => do
      let r ← OracleComp.liftComp ($ᵗ (Fin 4)) (unifSpec + family.spec)
      return (select stmt r).map (fun next => ⟨next, passthrough⟩) }

/-- The first draw has a success, two accepted failures, and a rejection. -/
def first (reject : Bool) : ClosedStage unifSpec (boundary Unit) (boundary Bool) :=
  stage (fun _ r => if reject = true ∨ r = 3 then none else some (decide (r = 0)))

/-- A true middle claim stays true; a false one needs another independent lucky draw. -/
def second : ClosedStage unifSpec (boundary Bool) (boundary Nat) :=
  stage (fun old r => some (if old = true ∨ r = 0 then 1 else 0))

set_option backward.isDefEq.respectTransparency false in
/-- The generic adapter executes the selected optional statement and keeps the actual behavior. -/
theorem stage_run {S T : Type} (select : S → Fin 4 → Option T)
    (input : (boundary S).State) :
    (stage select).run input =
      (fun r => (select input.1.stmt r).map (fun next => (⟨next, input.1.oracles⟩, ()))) <$>
        ($ᵗ (Fin 4)) := by
  simp only [ClosedStage.run_eq_executeCore, stage, executeCore, Reduction.execute,
    executeStrategies, Protocol.done_tree, Protocol.done_roles, Protocol.done_oracles,
    TypeTree.toTypeTree_done, TypeTree.RoleDecoration.toTypeTreeRoles_done,
    TwoParty.run, InteractionOver.runTypeTree, InteractionOver.TwoParty.pairedTypeTree,
    InteractionOver.TwoParty.paired, TwoParty.participantProfile,
    TwoParty.collectParticipantOutputs, Verifier.toCounterpart]
  simp only [pure_bind, simulateQ_bind, simulateQ_pure, bind_assoc]
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' unifSpec)
    (fun _ => rfl), simulateQ_id']
  simp only [CoreRun.closed, map_eq_bind_pure_comp, Option.map_map]
  congr 1

/-- Actual dependent boundaries of the two reductions. -/
abbrev interfaces (i : Fin 3) : ExecutionInterface :=
  match i.val with
  | 0 => boundary Unit
  | 1 => boundary Bool
  | _ => boundary Nat

local instance (i : Fin 3) : MeasurableSpace (interfaces i).State := ⊤

local instance (i : Fin 3) : DiscreteMeasurableSpace (interfaces i).State := ⟨fun _ => trivial⟩

/-- Select the actual reductions at their heterogeneous types. -/
def stages (reject : Bool) :
    (i : Fin 2) → ClosedStage unifSpec (interfaces i.castSucc) (interfaces i.succ) :=
  Fin.cons (first reject) (Fin.cons second (fun i => Fin.elim0 i))

/-- Truth is false initially, the Boolean in the middle, and equality to one at the end. -/
def relation (i : Fin 3) : (interfaces i).State → Prop :=
  match i with
  | ⟨0, _⟩ => fun _ => False
  | ⟨1, _⟩ => fun state => state.1.stmt = true
  | ⟨2, _⟩ => fun state => (show Nat from state.1.stmt) = 1

/-- From each false boundary, accepted truth has exact mass one quarter. -/
theorem stage_mass (i : Fin 2) (input : (interfaces i.castSucc).State)
    (hfalse : ¬ relation i.castSucc input) :
    𝒟[(stages false i).run input]
      {result | ∃ output, result = some output ∧ relation i.succ output} = 1 / 4 := by
  fin_cases i
  · change 𝒟[(first false).run input]
      {result | ∃ output, result = some output ∧ output.1.stmt = true} = 1 / 4
    unfold first
    rw [stage_run, ← prEvent_eq_evalDist_of_discrete, prEvent_map]
    simp only [Bool.false_eq_true, false_or]
    have hevent (r : Fin 4) :
        (∃ output : (boundary Bool).State,
          (if r = 3 then none else some (decide (r = 0))).map
          (fun next => (⟨next, input.1.oracles⟩, ())) = some output ∧
          output.1.stmt = true) ↔ r = 0 := by
      fin_cases r <;> simp
    rw [prEvent_congr _ _ _ hevent, SampleableType.prEvent_uniformSample_eq_singleton]
    norm_num
  · change 𝒟[second.run input]
      {result | ∃ output, result = some output ∧ output.1.stmt = (1 : Nat)} = 1 / 4
    have hold : input.1.stmt = false := by
      cases hb : input.1.stmt <;> simp_all [relation, interfaces]
    unfold second
    rw [stage_run, ← prEvent_eq_evalDist_of_discrete, prEvent_map]
    simp only [hold, Bool.false_eq_true, false_or, Option.map_some]
    have hevent (r : Fin 4) :
        (∃ output : (boundary Nat).State,
          some (⟨if r = 0 then 1 else 0, input.1.oracles⟩, ()) = some output ∧
          output.1.stmt = 1) ↔ r = 0 := by
      fin_cases r <;> simp
    rw [prEvent_congr _ _ _ hevent, SampleableType.prEvent_uniformSample_eq_singleton]
    norm_num

/-- Both positive errors accumulate to a nonvacuous half bound on the actual executor. -/
example (answers : family.Behavior) :
    𝒟[OrderedExecution.run 2 interfaces (stages false) (⟨(), answers⟩, ())]
      {result | ∃ output, result = some output ∧ output.1.stmt = (1 : Nat)} ≤ 1 / 2 := by
  have h := OrderedExecution.run_soundness_measure 2 interfaces (stages false) relation
    (fun _ => 1 / 4) (fun i input hf => (stage_mass i input hf).le)
    (⟨(), answers⟩, ()) (by simp [relation])
  exact h.trans (by
    rw [Fin.sum_univ_two, ← ENNReal.add_div]
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    rw [mul_comm, ← mul_div_assoc, mul_one,
      show (4 : ENNReal) = 2 * 2 by norm_num,
      ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
    norm_num)

/-- Forced first-stage rejection is absorbing even though the suffix could return true. -/
example (answers : family.Behavior) :
    OrderedExecution.run 2 interfaces (stages true) (⟨(), answers⟩, ()) =
      (fun _ : Fin 4 => none) <$> ($ᵗ (Fin 4)) := by
  simp [OrderedExecution.run, stages, first, stage_run, map_eq_bind_pure_comp, bind_assoc]

/--
info: 'Interaction.Oracle.OrderedExecution.run_soundness_measure' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OrderedExecution.run_soundness_measure

end
end Interaction.Oracle.OrderedSoundnessTest
