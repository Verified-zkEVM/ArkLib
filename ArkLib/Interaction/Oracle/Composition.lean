/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.CoreRun
public import VCVio.OracleComp.EvalDist
public import VCVio.EvalDist.PFunctorMeasure

/-!
# Ordered execution of oracle reductions

`executeClosed` runs an actual oracle reduction and exposes its closed output interface together
with its private prover output. Closing uses the resources paired by `executeCore`; there is no
handler argument at the handoff. Rejection drops the handoff and short-circuits later stages.

`OrderedExecution.run` iterates actual reductions over a finite family of declared interfaces.
These interfaces can include dependent statements, closed oracle interfaces, private witnesses,
and history. This is an execution combinator, not a new protocol presentation: structural protocol
concatenation remains owned by PolyFun's `TypeTree.Chain.then`. No equality with flattened
strategy execution, commutative-monad assumption, provenance assertion, or security theorem is
claimed here.
-/

@[expose] public section

universe u v w

namespace Interaction.Oracle

/-- The accepted interface of a run, including its actual path and private prover output. -/
abbrev ClosedOutput (protocol : Oracle.Protocol.{u})
    (Stmt : protocol.tree.BranchPath → Type u)
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    (Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path))
    (OutP : protocol.tree.ExecutionPath → Type u) :=
  (path : protocol.tree.ExecutionPath) ×
    (ClosedClaim (Stmt path.toBranchPath) (Out path.toBranchPath) × OutP path)

/-- Project the closed middle interface and private output from the very same execution record. -/
def CoreRun.closedOutput {protocol : Oracle.Protocol.{u}} {initial : PFunctor.{u, u}}
    {Stmt : protocol.tree.BranchPath → Type u}
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type u}
    (run : CoreRun protocol initial Stmt Out OutP) : Option (ClosedOutput protocol Stmt Out OutP) :=
  run.closed.map fun claim => ⟨run.path, claim, run.proverOut⟩

/-- Run a reduction and close its output with its own paired input behavior and sent messages. -/
def executeClosed {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {protocol : Oracle.Protocol.{u}} {initial : PFunctor.{u, u}}
    {StatementIn : Type v} {WitnessIn : Type w}
    {Stmt : protocol.tree.BranchPath → Type u}
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type u}
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP
      (TerminalClaim protocol initial Stmt Out))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    OracleComp ambient (Option (ClosedOutput protocol Stmt Out OutP)) := do
  let run ← executeCore reduction impl stmt wit
  return run.closedOutput

/-- A declared public closed-claim interface and a separate private prover payload. -/
structure ExecutionInterface where
  /-- Public statement type. -/
  Stmt : Type u
  /-- Indices of exported oracle realizations. -/
  Index : Type u
  /-- Concrete realization types whose interfaces declare the exported queries. -/
  Realization : Index → Type u
  /-- Exported observable oracle interface. -/
  oracles : OracleFamily Index Realization
  /-- Private prover state passed between stages. -/
  Private : Type u

/-- Declared closed statement and oracle behavior at an execution boundary. -/
abbrev ExecutionInterface.Claim (I : ExecutionInterface.{u}) := ClosedClaim I.Stmt I.oracles

/-- The public interface and the separate private state required to execute the next stage. -/
abbrev ExecutionInterface.State (I : ExecutionInterface.{u}) := I.Claim × I.Private

/-- An actual reduction between declared closed interfaces. The next protocol and strategies
may depend on the public statement, but cannot inspect oracle behavior or private input during
their selection.
Private input is passed only to the selected prover through ordinary reduction execution. -/
structure ClosedStage {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (I J : ExecutionInterface.{u}) where
  /-- A protocol selected using the public statement only. -/
  protocol : I.Stmt → Oracle.Protocol.{u}
  /-- Private input type of the selected reduction. -/
  Witness : I.Stmt → Type u
  /-- Private output type, retaining its actual execution-path dependency. -/
  OutP : (stmt : I.Stmt) → (protocol stmt).tree.ExecutionPath → Type u
  /-- Prepare the reduction's private witness from the carried private state. -/
  witness : (stmt : I.Stmt) → I.Private → Witness stmt
  /-- Transport private state using the actual path and private output of this stage. -/
  nextPrivate : (stmt : I.Stmt) → I.Private →
    (path : (protocol stmt).tree.ExecutionPath) → OutP stmt path → J.Private
  /-- The actual reduction, whose input resource is exactly the declared middle interface. -/
  reduction : (stmt : I.Stmt) →
    Reduction ambient (protocol stmt) I.oracles.spec.toPFunctor I.Stmt (Witness stmt)
      (OutP stmt)
      (TerminalClaim (protocol stmt) I.oracles.spec.toPFunctor
        (fun _ => J.Stmt) (fun _ => J.oracles))

namespace ClosedStage

variable {ι : Type u} {ambient : OracleSpec.{u, u} ι} {I J : ExecutionInterface.{u}}

/-- Execute using exactly the input claim's behavior, and close with the resources of that run.
The concrete execution path remains private to the executor; only the declared output crosses
into the next stage. -/
def run (stage : ClosedStage ambient I J) (input : I.State) :
    OracleComp ambient (Option J.State) := do
  let result ← executeClosed (stage.reduction input.1.stmt) input.1.oracles input.1.stmt
    (stage.witness input.1.stmt input.2)
  return result.map fun output =>
    (output.2.1, stage.nextPrivate input.1.stmt input.2 output.1 output.2.2)

/-- The handoff comes from the same run's closing and private output, without a replacement
handler or exposure of its hidden messages to the next public protocol selector. -/
theorem run_eq_executeCore (stage : ClosedStage ambient I J) (input : I.State) :
    stage.run input = (do
      let result ← executeCore (stage.reduction input.1.stmt) input.1.oracles input.1.stmt
        (stage.witness input.1.stmt input.2)
      return result.closed.map fun claim =>
        (claim, stage.nextPrivate input.1.stmt input.2 result.path result.proverOut)) := by
  simp only [run, executeClosed, CoreRun.closedOutput, bind_assoc, pure_bind, Option.map_map]
  rfl

end ClosedStage

namespace OrderedExecution

variable {ι : Type u} {ambient : OracleSpec.{u, u} ι}

/-- Execute a finite family of actual oracle reductions across explicit dependent interfaces.
Each accepted closed interface supplies the exact input behavior for the next stage. -/
def run : (n : Nat) → (I : Fin (n + 1) → ExecutionInterface.{u}) →
    ((i : Fin n) → ClosedStage ambient (I i.castSucc) (I i.succ)) →
    (I ⟨0, Nat.zero_lt_succ _⟩).State → OracleComp ambient (Option (I (Fin.last n)).State)
  | 0, _, _, input => pure (some input)
  | n + 1, I, stages, input => do
      let mid ← (stages ⟨0, Nat.zero_lt_succ _⟩).run input
      match mid with
      | none => pure none
      | some value => run n (fun i => I i.succ) (fun i => stages i.succ) value

/-- A zero-stage execution preserves both the closed claim and private prover state. -/
@[simp]
theorem run_zero (I : Fin 1 → ExecutionInterface.{u})
    (stages : (i : Fin 0) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State) : run 0 I stages input = pure (some input) := rfl

/-- Execution performs the first actual reduction, then either rejects or runs the suffix. -/
theorem run_succ (n : Nat) (I : Fin (n + 2) → ExecutionInterface.{u})
    (stages : (i : Fin (n + 1)) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State) : run (n + 1) I stages input = (do
      let mid ← (stages ⟨0, Nat.zero_lt_succ _⟩).run input
      match mid with
      | none => pure none
      | some value => run n (fun i => I i.succ) (fun i => stages i.succ) value) := rfl

/-- An immediately rejecting stage skips every suffix reduction. -/
theorem run_succ_of_reject (n : Nat) (I : Fin (n + 2) → ExecutionInterface.{u})
    (stages : (i : Fin (n + 1)) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State)
    (h : (stages ⟨0, Nat.zero_lt_succ _⟩).run input = pure none) :
    run (n + 1) I stages input = pure none := by
  rw [run_succ, h]
  simp only [pure_bind]

/-- A per-stage deterministic acceptance invariant propagates from one initial state through
all stages. One initial invariant and per-stage preservation suffice; intermediate invariants are
derived. -/
theorem run_preserves (n : Nat) (I : Fin (n + 1) → ExecutionInterface.{u})
    (stages : (i : Fin n) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (Inv : (i : Fin (n + 1)) → (I i).State → Prop)
    (preserves : ∀ (i : Fin n) (input : (I i.castSucc).State), Inv i.castSucc input →
      ∃ output, (stages i).run input = pure (some output) ∧ Inv i.succ output)
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State) (hinput : Inv ⟨0, Nat.zero_lt_succ _⟩ input) :
    ∃ output, run n I stages input = pure (some output) ∧ Inv (Fin.last n) output := by
  induction n with
  | zero => exact ⟨input, rfl, hinput⟩
  | succ n ih =>
    obtain ⟨mid, hmid, hinv⟩ := preserves ⟨0, Nat.zero_lt_succ _⟩ input hinput
    obtain ⟨output, hout, hfinal⟩ := ih (fun i => I i.succ) (fun i => stages i.succ)
      (fun i => Inv i.succ) (fun i => preserves i.succ) mid hinv
    refine ⟨output, ?_, hfinal⟩
    rw [run_succ, hmid]
    simpa only [pure_bind] using hout


/-- Almost-sure stage acceptance and preservation imply almost-sure final acceptance and
preservation, starting from one initial invariant. The event excludes explicit rejection. -/
theorem run_preserves_prob [OracleSpec.IsUniformSpec ambient]
    (n : Nat) (I : Fin (n + 1) → ExecutionInterface.{u})
    (stages : (i : Fin n) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (Inv : (i : Fin (n + 1)) → (I i).State → Prop)
    (preserves : ∀ (i : Fin n) (input : (I i.castSucc).State), Inv i.castSucc input →
      probEvent ((stages i).run input)
        (fun result => ∃ output, result = some output ∧ Inv i.succ output) = 1)
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State)
    (hinput : Inv ⟨0, Nat.zero_lt_succ _⟩ input) :
    probEvent (run n I stages input)
      (fun result => ∃ output, result = some output ∧ Inv (Fin.last n) output) = 1 := by
  classical
  induction n with
  | zero =>
    rw [run_zero, probEvent_pure]
    exact if_pos ⟨input, rfl, hinput⟩
  | succ n ih =>
    have hfirst := probEvent_eq_one_iff.mp
      (preserves ⟨0, Nat.zero_lt_succ _⟩ input hinput)
    rw [run_succ]
    have hcont : ∀ mid ∈ support ((stages ⟨0, Nat.zero_lt_succ _⟩).run input),
        probEvent (match mid with
          | none => pure none
          | some value => run n (fun i => I i.succ) (fun i => stages i.succ) value)
          (fun result => ∃ output, result = some output ∧ Inv (Fin.last (n + 1)) output) = 1 := by
      intro mid hmid
      obtain ⟨value, rfl, hvalue⟩ := hfirst.2 mid hmid
      exact ih (fun i => I i.succ) (fun i => stages i.succ)
        (fun i => Inv i.succ) (fun i => preserves i.succ) value hvalue
    calc
      _ = (1 - probFailure ((stages ⟨0, Nat.zero_lt_succ _⟩).run input)) * 1 :=
        probEvent_bind_of_const _ hcont
      _ = 1 := by rw [hfirst.1]; simp

/-- Native discrete measure formulation of ordered perfect completeness. The explicit query
compatibility hypothesis relates the measure specification to the probability specification;
closing and stage execution themselves do not depend on either interpretation. -/
theorem run_preserves_measure [OracleSpec.IsUniformSpec ambient]
    [∀ q, MeasurableSpace (ambient q)]
    [ambient.toPFunctor.IsMeasureSpec]
    [∀ q, DiscreteMeasurableSpace (ambient q)] [∀ q, Countable (ambient q)]
    (hmeasure : ∀ q, PFunctor.IsMeasureSpec.toMeasure (P := ambient.toPFunctor) q =
      (PFunctor.IsProbabilitySpec.toPMF (P := ambient.toPFunctor) q).toMeasure)
    (n : Nat) (I : Fin (n + 1) → ExecutionInterface.{u})
    (stages : (i : Fin n) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (Inv : (i : Fin (n + 1)) → (I i).State → Prop)
    (preserves : ∀ (i : Fin n) (input : (I i.castSucc).State), Inv i.castSucc input →
      discreteEvalDist ((stages i).run input)
        {result | ∃ output, result = some output ∧ Inv i.succ output} = 1)
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State)
    (hinput : Inv ⟨0, Nat.zero_lt_succ _⟩ input) :
    discreteEvalDist (run n I stages input)
      {result | ∃ output, result = some output ∧ Inv (Fin.last n) output} = 1 := by
  have bridge : ∀ {α : Type u} (program : OracleComp ambient α) (event : α → Prop),
      discreteEvalDist program {result | event result} = probEvent program event := by
    intro α program event
    let : MeasurableSpace α := ⊤
    exact PFunctor.FreeM.evalDist_apply_setOf hmeasure program event
      MeasurableSet.of_discrete
  rw [bridge]
  apply run_preserves_prob n I stages Inv
  · intro i state hstate
    rw [← bridge]
    exact preserves i state hstate
  · exact hinput

/-- Splitting the ordered execution at any middle interface preserves its exact effect order.
The suffix starts with the accepted claim and private state returned by the prefix. -/
theorem run_append (m n : Nat) (I : Fin (n + m + 1) → ExecutionInterface.{u})
    (stages : (i : Fin (n + m)) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State) :
    run (n + m) I stages input = (do
      let mid : Option (I ⟨m, by omega⟩).State ←
        run (ambient := ambient) m (fun i => I ⟨i.val, by omega⟩)
          (fun i => stages ⟨i.val, by omega⟩) input
      Option.elim mid (pure none) (fun value =>
        cast (congrArg (fun j : Fin (n + m + 1) => OracleComp ambient (Option (I j).State))
          (show (⟨m + n, by omega⟩ : Fin (n + m + 1)) = Fin.last (n + m) from
            Fin.ext (Nat.add_comm m n)))
          (run n (fun i => I ⟨m + i.val, by omega⟩)
            (fun i => stages ⟨m + i.val, by omega⟩) value))) := by
  revert I stages input
  induction m with
  | zero =>
    intro I stages input
    simp only [run_zero, pure_bind, Option.elim_some]
    rw [eq_cast_iff_heq]
    congr! 3 <;> simp_all only [Nat.zero_add, Fin.ext_iff, heq_iff_eq]
  | succ m ih =>
    intro I stages input
    erw [run_succ (n + m)]
    simp only [run_succ, bind_assoc]
    congr 1
    funext mid
    cases mid with
    | none => rfl
    | some value =>
      dsimp only
      erw [ih]
      congr 1
      funext result
      cases result with
      | none => rfl
      | some final =>
        simp only [Option.elim_some]
        apply eq_of_heq
        simp only [cast_heq_iff_heq, heq_cast_iff_heq]
        congr! 3 <;>
          simp_all only [Fin.ext_iff, Fin.val_succ, Nat.add_right_comm m 1, heq_iff_eq]

end OrderedExecution

end Interaction.Oracle
