/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualSystemRefinement
public import ArkLib.Data.Matrix.BackSubstitutionMachine
/-!
# Closed residual coefficient recovery

The residual-system machine samples the materialized points, constructs their Vandermonde rows,
and performs forward elimination. This caller then allocates a width-`L` zero vector one cell
at a time and invokes actual echelon back-substitution. Every callee transition, wrapper,
handoff, zero constant, allocation and final tagged output is charged.

Input lists and the width are supplied. Bulk runs and zero-vector specifications occur only
in proofs. Retained registers are shared in the inherited primitive model; host fuel and scalar
bit costs are separate. The consistency hypothesis in the generic theorem is discharged by
concrete residual sampling in the refinement, rather than by an assumed solver or output vector.
No requested-coordinate lookup, point enumeration, or complete-decoder cost is asserted here.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ResidualCoefficientMachine

open Polynomial Matrix

abbrev Input := ResidualSystemMachine.Input
abbrev Pivot := ForwardEchelonMachine.Pivot
abbrev Row := PivotSelectionMachine.Row

/-- Preserve every solver cost field and separately count seed scalar constants. -/
@[ext] structure Cost where
  matrix : PivotEliminationMachine.Cost
  constants : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0⟩⟩
instance : Add Cost := ⟨fun a b ↦ ⟨a.matrix + b.matrix, a.constants + b.constants⟩⟩
@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0⟩ := rfl
@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.matrix + b.matrix, a.constants + b.constants⟩ := rfl

/-- Full primitive charge includes all nested arithmetic, outputs and seed constants. -/
def totalCost (c : Cost) : ℕ := PivotSelectionMachine.totalCost c.matrix + c.constants
/-- All callee fields are embedded unchanged. -/
def embed (c : PivotEliminationMachine.Cost) : Cost := ⟨c, 0⟩
/-- One wrapper dispatch reads and writes a retained callee state root. -/
def wrapperCost (n : ℕ) : Cost := ⟨⟨⟨0, 0, n, 2 * n, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Read the supplied point-list root and initialize the system callee. -/
def entryCost : Cost := ⟨⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Read pivots, residual rows and width; initialize counter and empty seed root. -/
def systemReturnCost : Cost := ⟨⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Test/decrement the counter, materialize zero, allocate a seed cell and update roots. -/
def initializeCost : Cost := ⟨⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 2⟩, 1⟩
/-- Read exhausted counter and seed, then initialize the back-substitution state. -/
def initializeDoneCost : Cost := ⟨⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 1⟩, 0⟩
/-- Read the callee result and retain the final tagged payload. -/
def returnCost : Cost := ⟨⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Read and emit the tagged coefficient-list handle. -/
def emitCost : Cost := ⟨⟨⟨0, 0, 1, 2, 1⟩, 0, 0, 0, 0⟩, 0⟩

/-- Both actual callees and the seed-allocation cursor are exposed. -/
inductive Configuration (F : Type*) where
  | start (points : List F)
  | system (state : ResidualSystemMachine.Configuration F)
  | initialize (pivots : List (Pivot F)) (rest : List (Row F)) (remaining : ℕ) (seed : List F)
  | backsub (state : BackSubstitutionMachine.Configuration F)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent rules delegate exactly one callee transition or allocate one seed cell. -/
inductive Step (input : Input F) (L : ℕ) : Configuration F → Cost → Configuration F → Prop where
  | enter {xs} : Step input L (.start xs) entryCost (.system (.start xs))
  | system {s t c} (h : ResidualSystemMachine.Step input L s c t) :
      Step input L (.system s) (embed c + wrapperCost 1) (.system t)
  | systemReturn {ps rs} : Step input L (.system (.done ps rs)) systemReturnCost
      (.initialize ps rs L [])
  | systemFailed : Step input L (.system .rejected) returnCost (.emit none)
  | initialize {ps rs n zs} : Step input L (.initialize ps rs (n + 1) zs) initializeCost
      (.initialize ps rs n (0 :: zs))
  | initializeDone {ps rs zs} : Step input L (.initialize ps rs 0 zs) initializeDoneCost
      (.backsub (.check rs ps zs))
  | backsub {s t c} (h : BackSubstitutionMachine.Step s c t) :
      Step input L (.backsub s) (embed c + wrapperCost 1) (.backsub t)
  | returned {xs} : Step input L (.backsub (.done xs)) returnCost (.emit (some xs))
  | inconsistent : Step input L (.backsub .inconsistent) returnCost (.emit none)
  | rejected : Step input L (.backsub .rejected) returnCost (.emit none)
  | emit {out} : Step input L (.emit out) emitCost (.done out)

/-- Literal dispatch contains no bulk run, zero-vector construction, or output assumption. -/
def step (input : Input F) (L : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start xs => some (.system (.start xs), entryCost)
  | .system s => match ResidualSystemMachine.step input L s with
      | some (t, c) => some (.system t, embed c + wrapperCost 1)
      | none => match s with
          | .done ps rs => some (.initialize ps rs L [], systemReturnCost)
          | .rejected => some (.emit none, returnCost)
          | _ => none
  | .initialize ps rs (n + 1) zs => some (.initialize ps rs n (0 :: zs), initializeCost)
  | .initialize ps rs 0 zs => some (.backsub (.check rs ps zs), initializeDoneCost)
  | .backsub s => match BackSubstitutionMachine.step s with
      | some (t, c) => some (.backsub t, embed c + wrapperCost 1)
      | none => match s with
          | .done xs => some (.emit (some xs), returnCost)
          | .inconsistent | .rejected => some (.emit none, returnCost)
          | _ => none
  | .emit out => some (.done out, emitCost)
  | .done _ => none

/-- Independent rules agree with executable dispatch and its charge. -/
theorem Step.step_eq {input : Input F} {L : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step input L s c t) : step input L s = some (t, c) := by
  cases h with
  | system h => simp [step, h.step_eq]
  | backsub h => simp [step, h.step_eq]
  | _ => rfl

/-- Every executable branch has an independent operational rule. -/
theorem step_sound {input : Input F} {L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step input L s = some (t, c)) : Step input L s c t := by
  cases s with
  | start xs => cases h; constructor
  | «initialize» ps rs n zs => cases n <;> cases h <;> constructor
  | emit out => cases h; constructor
  | done out => simp [step] at h
  | system s =>
      cases hs : ResidualSystemMachine.step input L s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.system (ResidualSystemMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
            rcases h with ⟨rfl, rfl⟩ <;> constructor
  | backsub s =>
      cases hs : BackSubstitutionMachine.step s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.backsub (BackSubstitutionMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
            rcases h with ⟨rfl, rfl⟩ <;> constructor

/-- Actual traces accumulate every primitive charge. -/
inductive Trace (input : Input F) (L : ℕ) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input L 0 s 0 s
  | cons {n s u t c d} (head : Step input L s c u) (tail : Trace input L n u d t) :
      Trace input L (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp only [cost_add, PivotEliminationMachine.cost_add,
    RowReductionMachine.cost_add, Nat.add_assoc]

omit [DecidableEq F] in
/-- Trace concatenation preserves exact lengths and costs. -/
theorem Trace.trans {input : Input F} {L n m : ℕ} {s t u : Configuration F} {c d : Cost}
    (h : Trace input L n s c t) (h' : Trace input L m t d u) :
    Trace input L (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_right_comm, cost_assoc] using Trace.cons head (ih h')

/-- Fuel exhaustion returns the actual suspended state, not a fabricated solution. -/
def runFuel (input : Input F) (L : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input L s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel input L n t; (result.1, c + result.2)

/-- Every interpreter result refines a trace with the same nested cost. -/
theorem runFuel_refines (input : Input F) (L fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace input L n s (runFuel input L fuel s).2 (runFuel input L fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step input L s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Surplus host fuel leaves a completed result and cost unchanged. -/
theorem Trace.runFuel_done {input : Input F} {L n : ℕ} {s : Configuration F} {c : Cost}
    {out : Option (List F)} (h : Trace input L n s c (.done out)) (extra : ℕ) :
    runFuel input L (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]

omit [DecidableEq F] in
/-- Lift actual system transitions without losing any callee fields or emissions. -/
theorem lift_system (input : Input F) (L : ℕ) {n : ℕ}
    {s t : ResidualSystemMachine.Configuration F} {c : PivotEliminationMachine.Cost}
    (h : ResidualSystemMachine.Trace input L n s c t) :
    Trace input L n (.system s) (embed c + wrapperCost n) (.system t) := by
  induction h with
  | nil s => simpa [embed, wrapperCost] using Trace.nil (input := input) (L := L) (.system s)
  | @cons n s u t c d head tail ih =>
      have heq : (embed c + wrapperCost 1) + (embed d + wrapperCost n) =
          embed (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [embed, wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.system head) ih

omit [DecidableEq F] in
/-- Lift actual back-substitution transitions, including all nested pivot-solve costs. -/
theorem lift_backsub (input : Input F) (L : ℕ) {n : ℕ}
    {s t : BackSubstitutionMachine.Configuration F} {c : PivotEliminationMachine.Cost}
    (h : BackSubstitutionMachine.Trace n s c t) :
    Trace input L n (.backsub s) (embed c + wrapperCost n) (.backsub t) := by
  induction h with
  | nil s => simpa [embed, wrapperCost] using Trace.nil (input := input) (L := L) (.backsub s)
  | @cons n s u t c d head tail ih =>
      have heq : (embed c + wrapperCost 1) + (embed d + wrapperCost n) =
          embed (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [embed, wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.backsub head) ih

/-- Exact charges for zero-vector allocation and its callee handoff. -/
def initializationCost (n : ℕ) : Cost :=
  ⟨⟨⟨0, 0, n + 1, 5 * n + 4, 0⟩, 0, 0, 0, 2 * n + 1⟩, n⟩

omit [DecidableEq F] in
/-- Every zero in the seed is backed by an actual charged allocation transition. -/
theorem initialization_trace (input : Input F) (L n : ℕ) (ps : List (Pivot F))
    (rs : List (Row F)) (zs : List F) :
    Trace input L (n + 1) (.initialize ps rs n zs) (initializationCost n)
      (.backsub (.check rs ps (List.replicate n 0 ++ zs))) := by
  induction n generalizing zs with
  | zero => simpa [initializationCost, initializeDoneCost] using
      Trace.cons (Step.initializeDone (input := input) (L := L)) (Trace.nil _)
  | succ n ih =>
      convert Trace.cons Step.initialize (ih (0 :: zs)) using 1
      · ext <;> simp [initializationCost, initializeCost] <;> omega
      · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]

/-- Uniform bound dominates back-substitution for any echelon output with at most `n` rows. -/
def solveBudget (L n : ℕ) : ℕ := BackSubstitutionMachine.budget L n n
/-- Polynomial host fuel for the complete system, initialization, solve and final output. -/
def fuel (input : Input F) (L n : ℕ) : ℕ :=
  ResidualSystemMachine.fuel input L n + solveBudget L n + L + 5
/-- Primitive bound retains full system work and all delegated, seed and return charges. -/
def workBound (input : Input F) (L n : ℕ) : ℕ :=
  ResidualSystemMachine.workBound input L n + 3 * ResidualSystemMachine.fuel input L n +
    4 * solveBudget L n + 9 * L + 23

private theorem solveBudget_le (L k m n : ℕ) (hk : k ≤ n) (hm : m ≤ n) :
    BackSubstitutionMachine.budget L k m ≤ solveBudget L n := by
  unfold solveBudget BackSubstitutionMachine.budget
  nlinarith

private theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b := by
  simp only [totalCost, cost_add, PivotSelectionMachine.totalCost,
    PivotEliminationMachine.cost_add, RowReductionMachine.cost_add]
  omega

private theorem total_embed (c : PivotEliminationMachine.Cost) :
    totalCost (embed c) = PivotSelectionMachine.totalCost c := rfl
private theorem total_wrapper (n : ℕ) : totalCost (wrapperCost n) = 3 * n := by
  simp [totalCost, wrapperCost, PivotSelectionMachine.totalCost]
  omega

omit [DecidableEq F] in
private theorem residual_rhs_zero (L : ℕ) (ps : List (Pivot F)) (rs : List (Row F))
    (he : ForwardEchelonMachine.Echelon L 0 ps rs) (x : ℕ → F)
    (hx : ForwardEchelonMachine.Solutions ps rs x) : ∀ r ∈ rs, r.2 = 0 := by
  intro r hr
  have hrow := hx r (List.mem_append_right _ hr)
  rw [← hrow]
  apply Finset.sum_eq_zero
  intro i hi
  have hlen := he.2.2.1 r hr
  have hz := he.2.2.2 i (by simpa only [hlen] using Finset.mem_range.mp hi) r hr
  change r.1.getD i 0 * x i = 0
  rw [hz, zero_mul]

omit [DecidableEq F] in
/-- Actual composition emits a width-`L` solution of the sampled system whenever it is consistent.
The initial vector is allocated by this machine, not supplied as a free solver seed. -/
theorem computation_trace (input : Input F) (L : ℕ) (samples : List F)
    (hconsistent : ∃ x : ℕ → F, PivotSelectionMachine.Satisfies
      (VandermondeMachine.rowsSpec L (ResidualBatchMachine.outputSpec input samples)) x) :
    ∃ out steps c, Trace input L steps (.start samples) c (.done (some out)) ∧
      out.length = L ∧ PivotSelectionMachine.Satisfies
        (VandermondeMachine.rowsSpec L (ResidualBatchMachine.outputSpec input samples))
        (fun i ↦ out.getD i 0) ∧
      steps ≤ fuel input L samples.length ∧ totalCost c ≤ workBound input L samples.length := by
  classical
  obtain ⟨ps, rs, ns, cs, hs, he, hcount, hsystem, hns, hcs⟩ :=
    ResidualSystemMachine.computation_trace input L samples
  obtain ⟨x, hx⟩ := hconsistent
  have hzero := residual_rhs_zero L ps rs he x ((hsystem x).mpr hx)
  obtain ⟨out, cb, hb, hlen, hsol, _hfree, hcb⟩ := BackSubstitutionMachine.evaluation_runFuel
    L ps rs (List.replicate L 0) he (by simp) hzero
  obtain ⟨nb, hnb, hbt⟩ := BackSubstitutionMachine.runFuel_refines
    (BackSubstitutionMachine.budget L ps.length rs.length) (.check rs ps (List.replicate L 0))
  rw [hb] at hbt
  have hi := initialization_trace input L L ps rs []
  simp only [List.append_nil] at hi
  have ht := Trace.cons Step.enter ((lift_system input L hs).trans
    (Trace.cons Step.systemReturn (hi.trans ((lift_backsub input L hbt).trans
      (Trace.cons Step.returned (Trace.cons Step.emit (Trace.nil _)))))))
  have hbudget := solveBudget_le L ps.length rs.length samples.length (by omega) (by omega)
  refine ⟨out, _, _, ht, hlen, (hsystem _).mp hsol, ?_, ?_⟩
  · dsimp [fuel]
    omega
  · simp only [total_add, total_embed, total_wrapper]
    change 4 + (PivotSelectionMachine.totalCost cs + 3 * ns +
      (6 + (totalCost (initializationCost L) +
        (PivotSelectionMachine.totalCost cb + 3 * nb + (3 + (4 + 0)))))) ≤ _
    have hiCost : totalCost (initializationCost L) = 9 * L + 6 := by
      simp [totalCost, initializationCost, PivotSelectionMachine.totalCost]
      omega
    rw [hiCost]
    dsimp [workBound]
    change PivotSelectionMachine.totalCost cs ≤
      ResidualSystemMachine.workBound input L samples.length at hcs
    change PivotSelectionMachine.totalCost cb ≤ _ at hcb
    omega

/-- The uniform interpreter fuel produces actual coefficients satisfying the input equations. -/
theorem computation_runFuel (input : Input F) (L : ℕ) (samples : List F)
    (hconsistent : ∃ x : ℕ → F, PivotSelectionMachine.Satisfies
      (VandermondeMachine.rowsSpec L (ResidualBatchMachine.outputSpec input samples)) x) :
    ∃ out c, runFuel input L (fuel input L samples.length) (.start samples) =
      (.done (some out), c) ∧ out.length = L ∧ PivotSelectionMachine.Satisfies
        (VandermondeMachine.rowsSpec L (ResidualBatchMachine.outputSpec input samples))
        (fun i ↦ out.getD i 0) ∧ totalCost c ≤ workBound input L samples.length := by
  obtain ⟨out, steps, c, ht, hlen, hsol, hf, hc⟩ := computation_trace input L samples hconsistent
  have hr := ht.runFuel_done (fuel input L samples.length - steps)
  rw [Nat.add_sub_of_le hf] at hr
  exact ⟨out, c, hr, hlen, hsol, hc⟩

end ReedSolomon.HiddenDerivative.ResidualCoefficientMachine
