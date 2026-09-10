/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.PivotSolveMachine

/-!
# Closed back substitution with supplied free coordinates

Residual RHS values are checked before any coordinate is changed. The actual pivot list is
reversed, then each row is solved by individual `PivotSolveMachine.Step` transitions. The input
vector is materialized and supplied by the caller. Only pivot coordinates are modified.
The contract assumes valid echelon data; residual coefficients are known zero from that invariant.
Costs include scalar work, list traversal/restoration, allocation and every driver/callee dispatch.
Input preparation, reclamation, interpreter fuel and scalar bit costs are separate obligations.

Every primitive pays one control dispatch. Data charges count residual cell/RHS reads and cursor
writes (3), reversal cell read, allocation and cursor writes (5), call initialization (7), and
return registers (3). Completion charges initialize reversal (4), enter solving (2), or emit (1).
Each delegated transition additionally reads and writes its inner configuration (2 data operations)
and pays a driver dispatch; all callee costs remain charged. Equality and emitted results are
counted separately. Configuration handles are shared immutable pointers in this abstract model.
-/

@[expose] public section

namespace Matrix.BackSubstitutionMachine

open ForwardEchelonMachine
abbrev Cost := PivotEliminationMachine.Cost

def checkCost : Cost := ⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 1, 0⟩
def contradictionCost : Cost := ⟨⟨0, 0, 1, 3, 1⟩, 0, 0, 1, 0⟩
def checkEndCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 0⟩
def reverseCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩
def reverseEndCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩
def callCost : Cost := ⟨⟨0, 0, 1, 7, 0⟩, 0, 0, 0, 0⟩
def returnCost : Cost := ⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 0, 0⟩
def emitCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩
def rejectCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩
def wrapperCost (n : ℕ) : Cost := ⟨⟨0, 0, n, 2 * n, 0⟩, 0, 0, 0, 0⟩

inductive Configuration (F : Type*) where
  | check (remaining : List (Row F)) (pivots : List (Pivot F)) (values : List F)
  | reverse (pending output : List (Pivot F)) (values : List F)
  | solve (pending : List (Pivot F)) (values : List F)
  | row (pivot : Pivot F) (original : List F) (pending : List (Pivot F))
      (inner : PivotSolveMachine.Configuration F)
  | done (values : List F)
  | inconsistent
  | rejected
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

inductive Step : Configuration F → Cost → Configuration F → Prop where
  | check {cs rs ps v} : Step (.check ((cs, 0) :: rs) ps v) checkCost (.check rs ps v)
  | contradiction {r rs ps v} (h : r.2 ≠ 0) :
      Step (.check (r :: rs) ps v) contradictionCost .inconsistent
  | checkEnd {ps v} : Step (.check [] ps v) checkEndCost (.reverse ps [] v)
  | reverse {p ps out v} : Step (.reverse (p :: ps) out v) reverseCost (.reverse ps (p :: out) v)
  | reverseEnd {ps v} : Step (.reverse [] ps v) reverseEndCost (.solve ps v)
  | call {p ps v} : Step (.solve (p :: ps) v) callCost (.row p v ps (.dot p.2.1 v 0))
  | inner {p v ps s c t} (h : PivotSolveMachine.Step p.2 p.1 v s c t) :
      Step (.row p v ps s) (c + wrapperCost 1) (.row p v ps t)
  | returned {p v ps out} : Step (.row p v ps (.done out)) returnCost (.solve ps out)
  | failed {p v ps} : Step (.row p v ps .rejected) rejectCost .rejected
  | emit {v} : Step (.solve [] v) emitCost (.done v)

def step : Configuration F → Option (Configuration F × Cost)
  | .check (r :: rs) ps v => if r.2 = 0 then some (.check rs ps v, checkCost)
      else some (.inconsistent, contradictionCost)
  | .check [] ps v => some (.reverse ps [] v, checkEndCost)
  | .reverse (p :: ps) out v => some (.reverse ps (p :: out) v, reverseCost)
  | .reverse [] ps v => some (.solve ps v, reverseEndCost)
  | .solve (p :: ps) v => some (.row p v ps (.dot p.2.1 v 0), callCost)
  | .solve [] v => some (.done v, emitCost)
  | .row p v ps s => match PivotSolveMachine.step p.2 p.1 v s with
      | some (t, c) => some (.row p v ps t, c + wrapperCost 1)
      | none => match s with
          | .done out => some (.solve ps out, returnCost)
          | .rejected => some (.rejected, rejectCost)
          | _ => none
  | .done _ | .inconsistent | .rejected => none

theorem Step.step_eq {s t : Configuration F} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by
  cases h with
  | check => simp [step]
  | contradiction h => simp [step, h]
  | inner h => simp only [step, h.step_eq]
  | _ => rfl

theorem step_sound {s t : Configuration F} {c : Cost} (h : step s = some (t, c)) : Step s c t := by
  cases s with
  | check rs ps v =>
      cases rs with
      | nil => cases h; exact Step.checkEnd
      | cons r rs =>
          by_cases hz : r.2 = 0
          · rcases r with ⟨cs, b⟩
            simp only at hz
            subst b
            simp only [step] at h
            rcases h with ⟨rfl, rfl⟩; exact Step.check
          · simp only [step, if_neg hz, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; exact Step.contradiction hz
  | reverse ps out v => cases ps <;> cases h <;> constructor
  | solve ps v => cases ps <;> cases h <;> constructor
  | done v => simp [step] at h
  | inconsistent => simp [step] at h
  | rejected => simp [step] at h
  | row p v ps s =>
      cases hs : PivotSolveMachine.step p.2 p.1 v s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.inner (PivotSolveMachine.step_sound hs)
      | none =>
          cases s with
          | done out => cases h; exact Step.returned
          | rejected => cases h; exact Step.failed
          | _ => simp [step, hs] at h

inductive Trace : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c d} (head : Step s c u) (tail : Trace n u d t) : Trace (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

omit [DecidableEq F] in
theorem Trace.trans {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace n s c u) (h' : Trace m u d t) : Trace (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

def runFuel : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let z := runFuel n t; (z.1, c + z.2)

theorem runFuel_refines (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace n s (runFuel fuel s).2 (runFuel fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

theorem Trace.runFuel_add {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace n s c t) (extra : ℕ) :
    runFuel (n + extra) s = ((runFuel extra t).1, c + (runFuel extra t).2) := by
  induction h with
  | nil s => simp
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih]
      simp only [cost_assoc]

omit [DecidableEq F] in
theorem lift_row {p : Pivot F} {v : List F} (ps : List (Pivot F)) {n : ℕ}
    {s t : PivotSolveMachine.Configuration F} {c : Cost}
    (h : PivotSolveMachine.Trace p.2 p.1 v n s c t) :
    Trace n (.row p v ps s) (c + wrapperCost n) (.row p v ps t) := by
  induction h with
  | nil s => simpa [wrapperCost] using Trace.nil (.row p v ps s)
  | @cons n s u t c d head tail ih =>
      have hc : (c + wrapperCost 1) + (d + wrapperCost n) =
          (c + d) + wrapperCost (n + 1) := by ext <;> simp [wrapperCost] <;> omega
      rw [← hc]
      exact Trace.cons (Step.inner head) ih

abbrev totalCost := PivotSelectionMachine.totalCost
private theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b := by
  simp only [totalCost, PivotSelectionMachine.totalCost, PivotEliminationMachine.cost_add,
    RowReductionMachine.cost_add]
  omega
private theorem total_wrapper (k : ℕ) : totalCost (wrapperCost k) = 3 * k := by
  simp [totalCost, PivotSelectionMachine.totalCost, wrapperCost]
  omega

/-- Polynomial bound for actual trace length and primitive cost. -/
def budget (n k m : ℕ) : ℕ := (200 * (n + 1) + 7) * k + 7 * m + 14

/-- All requested free coordinates, including positions outside the pivot set, are retained. -/
def FreePreserved (ps : List (Pivot F)) (input output : List F) : Prop :=
  ∀ i, (∀ p ∈ ps, i ≠ p.1) → output.getD i 0 = input.getD i 0

/-- Actual materialized coordinates satisfy each indexed augmented pivot equation. -/
def PivotEquations (ps : List (Pivot F)) (v : List F) : Prop :=
  ∀ p ∈ ps, AugmentedColumnMachine.rowValue p.2.1 (fun i => v.getD i 0) = p.2.2

omit [DecidableEq F] in
private theorem solve_trace (n : ℕ) (ps : List (Pivot F)) (v : List F)
    (horder : ps.Pairwise (fun p q => q.1 < p.1))
    (hvalid : ∀ p ∈ ps, PivotValid n 0 p) (hv : v.length = n) :
    ∃ out steps c, Trace steps (.solve ps v) c (.done out) ∧ out.length = n ∧
      PivotEquations ps out ∧ FreePreserved ps v out ∧
      steps + totalCost c ≤ 200 * (n + 1) * ps.length + 4 := by
  classical
  induction ps generalizing v with
  | nil =>
      refine ⟨v, 1, emitCost, ?_, hv, by simp [PivotEquations], ?_, ?_⟩
      · simpa using Trace.cons (Step.emit (v := v)) (Trace.nil _)
      · intro i hi; rfl
      · simp [totalCost, PivotSelectionMachine.totalCost, emitCost]
  | cons p ps ih =>
      obtain ⟨hlo, hj, hlen, hp, hz⟩ := hvalid p (by simp)
      obtain ⟨hbefore, htail⟩ := List.pairwise_cons.mp horder
      have hr := PivotSolveMachine.evaluation_runFuel p.2 p.1 v (by omega) (by omega) hp
      obtain ⟨s, hs, ht⟩ := PivotSolveMachine.runFuel_refines p.2 p.1 v
        (p.2.1.length + 3 * p.1 + 9) (.dot p.2.1 v 0)
      rw [hr] at ht
      have hlift := lift_row ps ht
      have hv' : (PivotSolveMachine.result p.2 p.1 v).length = n :=
        (PivotSolveMachine.result_length p.2 p.1 v).trans hv
      obtain ⟨out, t, ct, hrun, houtlen, heqs, hfree, hcost⟩ :=
        ih (PivotSolveMachine.result p.2 p.1 v) htail (fun p hp => hvalid p (by simp [hp])) hv'
      have hpre := Trace.cons Step.call (hlift.trans (Trace.cons Step.returned (Trace.nil _)))
      have h := hpre.trans hrun
      refine ⟨out, _, _, h, houtlen, ?_, ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with hqp | hq
        · subst q
          have hsolve := PivotSolveMachine.result_solves p.2 p.1 v (by omega) (by omega) hp
          rw [← hsolve]
          unfold AugmentedColumnMachine.rowValue
          apply Finset.sum_congr rfl
          intro i hi
          dsimp only
          by_cases hij : i < p.1
          · rw [hz i hij, zero_mul, zero_mul]
          · rw [hfree i (by
              intro q hq heq
              have hh := hbefore q hq
              omega)]
        · exact heqs q hq
      · intro i hi
        rw [hfree i (fun q hq => hi q (by simp [hq]))]
        exact PivotSolveMachine.result_unchanged p.2 p.1 v (by omega) i (hi p (by simp))
      · have hb := PivotSolveMachine.bounds n p.1 hj
        have hprebound : s + (0 + 1) + 1 +
            totalCost (callCost + ((PivotSolveMachine.cost p.2.1.length p.1 + wrapperCost s) +
              (returnCost + 0))) ≤ 200 * (n + 1) := by
          simp only [total_add, total_wrapper]
          change s + (0 + 1) + 1 + (8 + (totalCost (PivotSolveMachine.cost p.2.1.length p.1) +
            3 * s + (4 + 0))) ≤ _
          rw [hlen]
          rw [hlen] at hs
          change _ ∧ totalCost _ ≤ _ at hb
          omega
        simp only [total_add] at hprebound ⊢
        simp only [List.length_cons]
        nlinarith

omit [DecidableEq F] in
private theorem check_trace (rs : List (Row F)) (ps : List (Pivot F)) (v : List F)
    (hzero : ∀ r ∈ rs, r.2 = 0) :
    Trace (rs.length + 1) (.check rs ps v)
      ⟨⟨0, 0, rs.length + 1, 3 * rs.length + 4, 0⟩, 0, 0, rs.length, 0⟩
      (.reverse ps [] v) := by
  induction rs with
  | nil => simpa [checkEndCost] using Trace.cons (Step.checkEnd (ps := ps) (v := v)) (Trace.nil _)
  | cons r rs ih =>
      rcases r with ⟨cs, b⟩
      have hb := hzero (cs, b) (by simp)
      simp only at hb
      subst b
      have h := Trace.cons (Step.check (cs := cs)) (ih (fun r hr => hzero r (by simp [hr])))
      convert h using 1 <;> simp [checkCost, Nat.mul_add]; omega

omit [DecidableEq F] in
private theorem reverse_trace (ps out : List (Pivot F)) (v : List F) :
    Trace (ps.length + 1) (.reverse ps out v)
      ⟨⟨0, 0, ps.length + 1, 5 * ps.length + 2, 0⟩, 0, 0, 0, 0⟩
      (.solve (ps.reverse ++ out) v) := by
  induction ps generalizing out with
  | nil =>
      simpa [reverseEndCost] using Trace.cons (Step.reverseEnd (ps := out) (v := v)) (Trace.nil _)
  | cons p ps ih =>
      simpa [reverseCost, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons Step.reverse (ih (p :: out))

omit [DecidableEq F] in
private theorem inconsistent_trace (rs : List (Row F)) (ps : List (Pivot F)) (v : List F)
    (hbad : ¬∀ r ∈ rs, r.2 = 0) :
    ∃ steps c, Trace steps (.check rs ps v) c .inconsistent ∧
      steps + totalCost c ≤ 7 * rs.length := by
  classical
  induction rs with
  | nil => simp at hbad
  | cons r rs ih =>
      by_cases hz : r.2 = 0
      · rcases r with ⟨cs, b⟩
        simp only at hz
        subst b
        obtain ⟨s, c, ht, hc⟩ := ih (by simpa using hbad)
        refine ⟨s + 1, checkCost + c, Trace.cons Step.check ht, ?_⟩
        rw [total_add]
        change s + 1 + (5 + totalCost c) ≤ _
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
      · refine ⟨1, contradictionCost, ?_, ?_⟩
        · simpa using
            Trace.cons (Step.contradiction (rs := rs) (ps := ps) (v := v) hz) (Trace.nil _)
        · simp [totalCost, PivotSelectionMachine.totalCost, contradictionCost]

private theorem terminal_run {n B : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace n s c t) (ht : step t = none) (hn : n ≤ B) : runFuel B s = (t, c) := by
  have hx : runFuel (B - n) t = (t, (0 : Cost)) := by cases B - n <;> simp [runFuel, ht]
  have heq := h.runFuel_add (B - n)
  rw [show n + (B - n) = B by omega, hx] at heq
  simpa using heq

/-- Given consistent retained residuals, bounded actual execution solves every echelon equation
and preserves the caller's supplied nonpivot coordinates. -/
theorem evaluation_runFuel (n : ℕ) (ps : List (Pivot F)) (rs : List (Row F)) (v : List F)
    (he : Echelon n 0 ps rs) (hv : v.length = n) (hzero : ∀ r ∈ rs, r.2 = 0) :
    ∃ out c, runFuel (budget n ps.length rs.length) (.check rs ps v) = (.done out, c) ∧
      out.length = n ∧ Solutions ps rs (fun i => out.getD i 0) ∧ FreePreserved ps v out ∧
      totalCost c ≤ budget n ps.length rs.length := by
  have horder : ps.reverse.Pairwise (fun p q => q.1 < p.1) := by
    simpa only [List.pairwise_reverse] using he.1
  obtain ⟨out, t, ct, ht, hlen, heqs, hfree, hwork⟩ := solve_trace n ps.reverse v horder
    (fun p hp => he.2.1 p (List.mem_reverse.mp hp)) hv
  have hcheck := check_trace rs ps v hzero
  have hreverse := reverse_trace ps [] v
  simp only [List.append_nil] at hreverse
  have h := hcheck.trans (hreverse.trans ht)
  have hb : (rs.length + 1 + (ps.length + 1 + t)) +
      totalCost (⟨⟨0, 0, rs.length + 1, 3 * rs.length + 4, 0⟩, 0, 0, rs.length, 0⟩ +
        (⟨⟨0, 0, ps.length + 1, 5 * ps.length + 2, 0⟩, 0, 0, 0, 0⟩ + ct)) ≤
        budget n ps.length rs.length := by
    simp only [List.length_reverse] at hwork
    rw [total_add, total_add]
    simp only [totalCost, PivotSelectionMachine.totalCost] at hwork ⊢
    unfold budget
    nlinarith
  refine ⟨out, _, terminal_run h rfl (by omega), hlen, ?_, ?_, by omega⟩
  · unfold Solutions PivotSelectionMachine.Satisfies
    simp only [List.forall_mem_append, List.forall_mem_map]
    refine ⟨fun p hp => heqs p (List.mem_reverse.mpr hp), ?_⟩
    intro r hr
    rw [hzero r hr]
    apply Finset.sum_eq_zero
    intro i hi
    have hlenr := he.2.2.1 r hr
    have hz := he.2.2.2 i (by simpa only [hlenr] using Finset.mem_range.mp hi) r hr
    change r.1.getD i 0 * out.getD i 0 = 0
    rw [hz, zero_mul]
  · intro i hi
    exact hfree i (fun p hp => hi p (List.mem_reverse.mp hp))

/-- A contradictory residual produces a terminal result within the same polynomial budget,
including the cost of scanning preceding consistent rows. -/
theorem inconsistent_runFuel (n : ℕ) (ps : List (Pivot F)) (rs : List (Row F))
    (v : List F) (hbad : ∃ r ∈ rs, r.2 ≠ 0) :
    ∃ c, runFuel (budget n ps.length rs.length) (.check rs ps v) = (.inconsistent, c) ∧
      totalCost c ≤ budget n ps.length rs.length := by
  obtain ⟨s, c, ht, hc⟩ := inconsistent_trace rs ps v (by
    intro hz
    obtain ⟨r, hr, hb⟩ := hbad
    exact hb (hz r hr))
  have hb : 7 * rs.length ≤ budget n ps.length rs.length := by unfold budget; omega
  exact ⟨c, terminal_run ht rfl (by omega), by omega⟩

/-- On valid echelon input, inconsistency is reported exactly when a retained zero-coefficient
row has nonzero RHS. It is never inferred from a pivot-free column alone. -/
theorem inconsistent_iff (n : ℕ) (ps : List (Pivot F)) (rs : List (Row F)) (v : List F)
    (he : Echelon n 0 ps rs) (hv : v.length = n) :
    (runFuel (budget n ps.length rs.length) (.check rs ps v)).1 = .inconsistent ↔
      ∃ r ∈ rs, r.2 ≠ 0 := by
  classical
  by_cases hz : ∀ r ∈ rs, r.2 = 0
  · obtain ⟨out, c, hrun, _⟩ := evaluation_runFuel n ps rs v he hv hz
    simp only [hrun, reduceCtorEq, false_iff, not_exists]
    intro r hr
    exact hr.2 (hz r hr.1)
  · obtain ⟨s, c, ht, hc⟩ := inconsistent_trace rs ps v hz
    have hs : s ≤ budget n ps.length rs.length := by unfold budget; omega
    have hrun := terminal_run ht rfl hs
    simp only [hrun, true_iff]
    push Not at hz
    exact hz

end Matrix.BackSubstitutionMachine
