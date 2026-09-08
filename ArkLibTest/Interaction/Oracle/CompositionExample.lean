/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Composition
import ArkLibTest.Interaction.Oracle.CoreRunExample

/-!
# Heterogeneous ordered oracle execution

The middle statement changes from `Unit` to `Bool`, the final statement is `Nat`, and the final
oracle answers `Bool` rather than `Nat`. The second protocol has genuinely different message
types on its two branches. A stateful logger detects reordered, duplicated, or post-rejection
execution. The final oracle must observe the first stage's derived behavior, not a replacement
handler. The separate lower-adapter check retains the actual hidden output of an oracle message.
-/

namespace Interaction.Oracle.CompositionExample

open OracleComp

/- Normalize the concrete scalar-family response types while rewriting the staged run laws. -/
attribute [local implicit_reducible] OracleInterface.toOracleSpec OracleInterface.Response

/-- Tagged ambient events expose ordering to a noncommutative interpreter. -/
abbrev ambient := CoreRunExample.ambient

/-- Scalar natural-number interface. -/
@[reducible]
def naturals : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => OracleInterface.instDefault⟩

/-- A distinct scalar Boolean interface. -/
@[reducible]
def booleans : OracleFamily Unit (fun _ => Bool) := ⟨fun _ => OracleInterface.instDefault⟩

/-- Initial statement, oracle, and hidden payload types. -/
@[reducible]
def first : ExecutionInterface := ⟨Unit, Unit, fun _ => Nat, naturals, Nat⟩

/-- The explicitly exported middle interface. -/
@[reducible]
def middle : ExecutionInterface := ⟨Bool, Unit, fun _ => Nat, naturals, Nat⟩

/-- Both public statement and oracle behavior differ from the middle interface. -/
@[reducible]
def last : ExecutionInterface := ⟨Nat, Unit, fun _ => Bool, booleans, Nat × Nat⟩

/-- The first stage exports an observable transformation of its input oracle. -/
def addEleven : VirtualOracle naturals.spec naturals := ⟨fun q => do
  let old : Nat ← liftM (naturals.spec.query q)
  return old + 11⟩

/-- A terminal first-stage verifier that can explicitly reject. -/
def firstVerifier (accept : Bool) :
    OracleComp (ambient + naturals.spec) (Option (OracleClaim naturals.spec Bool naturals)) := do
  let _ ← liftM ((ambient + naturals.spec).query (.inl 1))
  let old : Nat ← liftM ((ambient + naturals.spec).query (.inr ⟨(), ()⟩))
  return if accept then some ⟨old % 2 == 0, addEleven⟩ else none

/-- The first actual reduction has no interaction nodes but does perform ordered effects. -/
def firstReduction (accept : Bool) :
    Reduction ambient .done naturals.spec.toPFunctor Unit Nat (fun _ => Nat)
      (TerminalClaim .done naturals.spec.toPFunctor (fun _ => Bool) (fun _ => naturals)) where
  prover := fun _ hidden => do
    let _ ← liftM (ambient.query 0)
    return hidden + 1
  verifier := fun _ => firstVerifier accept

/-- A true branch sends a natural number; a false branch sends a Boolean. -/
abbrev branchProtocol : Oracle.Protocol :=
  .public .sender Bool fun choice =>
    if choice then .public .sender Nat (fun _ => .done)
    else .public .sender Bool (fun _ => .done)

/-- The last oracle observes the exact middle behavior through its declared query interface. -/
def isEven : VirtualOracle naturals.spec booleans := ⟨fun _ => do
  let value : Nat ← liftM (naturals.spec.query ⟨(), ()⟩)
  return value % 2 == 0⟩

/-- Terminal verifier computation, after either heterogeneous branch. -/
def secondTerminal (message : Nat) :
    OracleComp (ambient + naturals.spec) (Option (OracleClaim naturals.spec Nat booleans)) := do
  let _ ← liftM ((ambient + naturals.spec).query (.inl 3))
  let value : Nat ← liftM ((ambient + naturals.spec).query (.inr ⟨(), ()⟩))
  return some ⟨message + value, isEven⟩

/-- The prover carries hidden data through either branch; it is not the verifier's statement. -/
def secondProver (choice : Bool) (hidden : Nat) :
    Prover.Strategy ambient branchProtocol.tree branchProtocol.roles (fun _ => Nat) := by
  refine pure ⟨choice, ?_⟩
  cases choice with
  | false => exact pure ⟨decide (hidden > 0), hidden + 1⟩
  | true => exact pure ⟨hidden, hidden + 1⟩

/-- Each branch receives its own message type before querying the middle resource. -/
def secondVerifier : Verifier.Strategy ambient branchProtocol.tree branchProtocol.roles
    branchProtocol.oracles naturals.spec.toPFunctor
    (TerminalClaim branchProtocol naturals.spec.toPFunctor (fun _ => Nat) (fun _ => booleans)) := by
  intro choice
  cases choice with
  | false => exact pure (fun (message : Bool) => pure (secondTerminal
      (if message then 100 else 200)))
  | true => exact pure (fun (message : Nat) => pure (secondTerminal message))

/-- A genuine branching second reduction. -/
def secondReduction : Reduction ambient branchProtocol naturals.spec.toPFunctor Bool Nat
    (fun _ => Nat)
    (TerminalClaim branchProtocol naturals.spec.toPFunctor (fun _ => Nat) (fun _ => booleans)) where
  prover := fun choice hidden => do
    let _ ← liftM (ambient.query 2)
    return secondProver choice hidden
  verifier := fun _ => secondVerifier

/-- The first handoff closes the actual reduction output and retains its hidden output. -/
def firstStage (accept : Bool) : ClosedStage ambient first middle where
  protocol := fun _ => .done
  Witness := fun _ => Nat
  OutP := fun _ _ => Nat
  witness := fun _ hidden => hidden
  nextPrivate := fun _ _ _ output => output
  reduction := fun _ => firstReduction accept

/-- The second handoff keeps old and new hidden state separately. -/
def secondStage : ClosedStage ambient middle last where
  protocol := fun _ => branchProtocol
  Witness := fun _ => Nat
  OutP := fun _ _ => Nat
  witness := fun _ hidden => hidden
  nextPrivate := fun _ hidden _ output => (hidden, output)
  reduction := fun _ => secondReduction

/-- Normalize only the first actual stage before composing it with another reduction. -/
theorem firstStage_run (accept : Bool) (answers : naturals.spec.Domain → Nat) (hidden : Nat) :
    (firstStage accept).run (⟨(), answers⟩, hidden) = (do
      let _ ← liftM (ambient.query 0)
      let _ ← liftM (ambient.query 1)
      return if accept then some
        (⟨(answers ⟨(), ()⟩ : Nat) % 2 == 0,
          fun q => (answers q : Nat) + 11⟩, hidden + 1) else none) := by
  cases accept <;> rfl

/-- Normalize the heterogeneous second stage once, preserving both possible message types. -/
theorem secondStage_run (choice : Bool) (answers : naturals.spec.Domain → Nat) (hidden : Nat) :
    secondStage.run (⟨choice, answers⟩, hidden) = (do
      let _ ← liftM (ambient.query 2)
      let _ ← liftM (ambient.query 3)
      return some
        (⟨(if choice then hidden else if decide (hidden > 0) then 100 else 200) +
            (answers ⟨(), ()⟩ : Nat),
          fun _ => (answers ⟨(), ()⟩ : Nat) % 2 == 0⟩, (hidden, hidden + 1))) := by
  cases choice <;> rfl

/-- Three distinct boundary interfaces for two stages. -/
@[reducible]
def interfaces (i : Fin 3) : ExecutionInterface :=
  match i.val with
  | 0 => first
  | 1 => middle
  | _ => last

/-- The dependent finite family selects actual reductions with matching middle interfaces. -/
def stages (accept : Bool) :
    (i : Fin 2) → ClosedStage ambient (interfaces i.castSucc) (interfaces i.succ) :=
  Fin.cons (firstStage accept) (Fin.cons secondStage (fun i => Fin.elim0 i))

/-- Resolve the first dependent stage index without unfolding its execution. -/
@[simp]
theorem stages_zero (accept : Bool) : stages accept (0 : Fin 2) = firstStage accept := rfl

/-- Resolve the second dependent stage index without unfolding its execution. -/
@[simp]
theorem stages_one (accept : Bool) : stages accept (1 : Fin 2) = secondStage := rfl

/-- Resolve the finite family once, leaving the two actual stage executions opaque. -/
theorem run_two (accept : Bool) (input : first.State) :
    OrderedExecution.run 2 interfaces (stages accept) input = (do
      let mid ← (firstStage accept).run input
      match mid with
      | none => pure none
      | some value => secondStage.run value) := by
  simp only [OrderedExecution.run]
  erw [stages_zero, stages_one]
  congr 1
  funext mid
  cases mid with
  | none => rfl
  | some value =>
    dsimp only [interfaces] at *
    trans (secondStage.run value >>= pure)
    · congr 1
      funext result
      cases result <;> rfl
    · exact bind_pure _

/-- Run the public composition API under the same stateful logger as the core executor tests. -/
def observed (accept : Bool) (answer hidden : Nat) : Option last.State × List Nat :=
  (simulateQ CoreRunExample.logger
    (OrderedExecution.run 2 interfaces (stages accept) (⟨(), fun _ => answer⟩, hidden))).run []

/-- Normalize the accepted execution once before checking its independently observable parts. -/
theorem observed_true (answer hidden : Nat) :
    observed true answer hidden =
      (some (⟨(if answer % 2 == 0 then hidden + 1
        else if decide (hidden + 1 > 0) then 100 else 200) + (answer + 11),
        fun _ => (answer + 11) % 2 == 0⟩, (hidden + 1, hidden + 1 + 1)), [0, 1, 2, 3]) := by
  have hrun := congrArg (fun program : OracleComp ambient (Option last.State) =>
    (simulateQ CoreRunExample.logger program).run [])
    (run_two true (⟨(), fun _ => answer⟩, hidden))
  refine hrun.trans ?_
  rw [firstStage_run]
  simp only [bind_assoc, pure_bind, ↓reduceIte]
  rw [secondStage_run]
  rfl

/-- Ordered execution retains every stage effect exactly once. -/
example : (observed true 7 40).2 = [0, 1, 2, 3] := by rw [observed_true]

/-- The false branch really receives `Bool`; the middle oracle answers 7 + 11. -/
example : (observed true 7 40).1.map (fun output => output.1.stmt) = some (118 : Nat) := by
  rw [observed_true]
  rfl

/-- The true branch receives `Nat`; the middle oracle answers 20 + 11. -/
example : (observed true 20 40).1.map (fun output => output.1.stmt) = some (72 : Nat) := by
  rw [observed_true]
  rfl

/-- The exported Boolean oracle is derived from the actual middle behavior. -/
example : (observed true 7 40).1.map (fun output => output.1.oracles ⟨(), ()⟩) = some true := by
  rw [observed_true]
  rfl

/-- Changing the initial behavior reaches the other branch and changes the final oracle. -/
example : (observed true 20 40).1.map (fun output => output.1.oracles ⟨(), ()⟩) = some false := by
  rw [observed_true]
  rfl

/-- Private outputs remain distinct from public results and cross the actual stage handoff. -/
example : (observed true 7 40).1.map Prod.snd = some (41, 42) := by
  rw [observed_true]
  rfl

/-- A rejecting first stage does not execute either second-stage ambient event. -/
example : observed false 7 40 = (none, [0, 1]) := rfl

/-- The lower-level adapter also preserves actual hidden oracle-message output. -/
example (hidden : Nat) :
    ((simulateQ CoreRunExample.logger
      (executeClosed (CoreRunExample.reduction true) (fun _ => 7) () (11, hidden))).run []).1.map
        (fun output => (output.2.1.oracles ⟨(), ()⟩, output.2.2)) = some ((18 : Nat), hidden) := rfl

end Interaction.Oracle.CompositionExample
