/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.ForwardEchelonSemantics

/-!
# Closed forward-echelon execution

The driver scans coefficient columns, delegates individual pivot-selection and augmented-column
transitions, and retains completed pivot rows with their logical indices. No-hit advances only
the column; successful elimination removes one active row. The final explicit reversal emits
ordered pivots and residual rows separately. Residual RHS values are retained for a later
consistency check. There is no back substitution or full-system solving in this machine.

Costs retain callee charges and add wrapper dispatch/root accesses. Row and tail pointers are
shared; cell/pair allocation and index updates are charged. Input preparation, reclamation,
constants, interpreter bookkeeping and scalar bit costs are outside the abstract model.
-/

@[expose] public section

namespace Matrix.ForwardEchelonMachine

abbrev Cost := PivotEliminationMachine.Cost

/-- Read column, remaining width and active rows; write remaining width and callee state. -/
def selectCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 2⟩
/-- Read selected rows and column; write successor column and active rows. -/
def nextCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 1⟩
/-- Read the successful result and its nonempty head; write the elimination callee state. -/
def eliminateCost : Cost := ⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 0, 0⟩
/-- Read head, column and accumulator; allocate indexed pair/cell and write three registers. -/
def storeCost : Cost := ⟨⟨0, 0, 1, 8, 0⟩, 0, 0, 0, 1⟩
/-- Read exhausted width, pivot and row roots; initialize reversal destination and test width. -/
def finishCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 1⟩
/-- Read completed-pivot cell/output pointer; allocate cell and update both pointers. -/
def reverseCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩
/-- Read exhausted cursor and both output roots; emit the tagged two-list result. -/
def emitCost : Cost := ⟨⟨0, 0, 1, 3, 1⟩, 0, 0, 0, 0⟩
/-- Read malformed/failed return and emit rejection. -/
def rejectCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩
/-- One outer dispatch and read/write of the suspended callee root for each actual inner step. -/
def wrapperCost (n : ℕ) : Cost := ⟨⟨0, 0, n, 2 * n, 0⟩, 0, 0, 0, 0⟩

/-- Fixed driver phases with actual suspended callees and materialized completed pivots. -/
inductive Configuration (F : Type*) where
  | loop (column left : ℕ) (rows : List (Row F)) (completed : List (Pivot F))
  | select (column left : ℕ) (completed : List (Pivot F))
      (inner : PivotSelectionMachine.Configuration F)
  | eliminate (column left : ℕ) (completed : List (Pivot F))
      (inner : AugmentedColumnMachine.Configuration F)
  | reverse (pending output : List (Pivot F)) (rest : List (Row F))
  | done (pivots : List (Pivot F)) (rest : List (Row F))
  | rejected
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent rules explicitly separate calls, delegated work and driver returns. -/
inductive Step : Configuration F → Cost → Configuration F → Prop where
  | select {j left rows rev} : Step (.loop j (left + 1) rows rev) selectCost
      (.select j left rev (.scan rows []))
  | finish {j rows rev} : Step (.loop j 0 rows rev) finishCost (.reverse rev [] rows)
  | selection {j left rev s c t} (h : PivotSelectionMachine.Step j s c t) :
      Step (.select j left rev s) (c + wrapperCost 1) (.select j left rev t)
  | nohit {j left rev rows} : Step (.select j left rev (.done false rows)) nextCost
      (.loop (j + 1) left rows rev)
  | found {j left rev p rows} : Step (.select j left rev (.done true (p :: rows))) eliminateCost
      (.eliminate j left rev (.pack (p :: rows) []))
  | selectionEmpty {j left rev} : Step (.select j left rev (.done true [])) rejectCost .rejected
  | selectionFailed {j left rev} : Step (.select j left rev .rejected) rejectCost .rejected
  | elimination {j left rev s c t} (h : AugmentedColumnMachine.Step j s c t) :
      Step (.eliminate j left rev s) (c + wrapperCost 1) (.eliminate j left rev t)
  | store {j left rev p rows} : Step (.eliminate j left rev (.done (p :: rows))) storeCost
      (.loop (j + 1) left rows ((j, p) :: rev))
  | eliminationEmpty {j left rev} : Step (.eliminate j left rev (.done [])) rejectCost .rejected
  | eliminationFailed {j left rev} : Step (.eliminate j left rev .rejected) rejectCost .rejected
  | reverse {p ps out rest} : Step (.reverse (p :: ps) out rest) reverseCost
      (.reverse ps (p :: out) rest)
  | emit {out rest} : Step (.reverse [] out rest) emitCost (.done out rest)

/-- Closed dispatch uses only local phases and one actual callee step at a time. -/
def step : Configuration F → Option (Configuration F × Cost)
  | .loop j (left + 1) rows rev => some (.select j left rev (.scan rows []), selectCost)
  | .loop _ 0 rows rev => some (.reverse rev [] rows, finishCost)
  | .select j left rev s => match PivotSelectionMachine.step j s with
      | some (t, c) => some (.select j left rev t, c + wrapperCost 1)
      | none => match s with
          | .done false rows => some (.loop (j + 1) left rows rev, nextCost)
          | .done true (p :: rows) =>
              some (.eliminate j left rev (.pack (p :: rows) []), eliminateCost)
          | .done true [] | .rejected => some (.rejected, rejectCost)
          | _ => none
  | .eliminate j left rev s => match AugmentedColumnMachine.step j s with
      | some (t, c) => some (.eliminate j left rev t, c + wrapperCost 1)
      | none => match s with
          | .done (p :: rows) => some (.loop (j + 1) left rows ((j, p) :: rev), storeCost)
          | .done [] | .rejected => some (.rejected, rejectCost)
          | _ => none
  | .reverse (p :: ps) out rest => some (.reverse ps (p :: out) rest, reverseCost)
  | .reverse [] out rest => some (.done out rest, emitCost)
  | .done _ _ | .rejected => none

/-- Every rule fixes both successor and cost. -/
theorem Step.step_eq {s t : Configuration F} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by
  cases h with
  | selection h => simp only [step, h.step_eq]
  | elimination h => simp only [step, h.step_eq]
  | _ => rfl

/-- Every executable transition has an independent rule. -/
theorem step_sound {s t : Configuration F} {c : Cost} (h : step s = some (t, c)) :
    Step s c t := by
  cases s with
  | loop j left rows rev => cases left <;> cases h <;> constructor
  | reverse ps out rest => cases ps <;> cases h <;> constructor
  | done ps rest => simp [step] at h
  | rejected => simp [step] at h
  | select j left rev s =>
      cases hs : PivotSelectionMachine.step j s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.selection (PivotSelectionMachine.step_sound hs)
      | none =>
          cases s with
          | done b rows => cases b <;> cases rows <;> cases h <;> constructor
          | rejected => cases h; exact Step.selectionFailed
          | _ => simp [step, hs] at h
  | eliminate j left rev s =>
      cases hs : AugmentedColumnMachine.step j s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.elimination (AugmentedColumnMachine.step_sound hs)
      | none =>
          cases s with
          | done rows => cases rows <;> cases h <;> constructor
          | rejected => cases h; exact Step.eliminationFailed
          | _ => simp [step, hs] at h

/-- Actual finite executions with accumulated primitive charges. -/
inductive Trace : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c d} (head : Step s c u) (tail : Trace n u d t) : Trace (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

omit [DecidableEq F] in
/-- Compose traces without hiding any work. -/
theorem Trace.trans {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace n s c u) (h' : Trace m u d t) : Trace (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Insufficient fuel exposes partial states. -/
def runFuel : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel n t; (result.1, c + result.2)

/-- Every interpreter result is backed by an identical-cost trace. -/
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

/-- A finite trace composes with remaining executable fuel. -/
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

/-- Completed traces stay completed under excess fuel, with no extra charge. -/
theorem Trace.runFuel_done {n : ℕ} {s : Configuration F} {c : Cost}
    {ps : List (Pivot F)} {rest : List (Row F)} (h : Trace n s c (.done ps rest)) (extra : ℕ) :
    runFuel (n + extra) s = (.done ps rest, c) := by
  have hd : runFuel extra (.done ps rest) = (.done ps rest, (0 : Cost)) := by cases extra <;> rfl
  rw [h.runFuel_add, hd]
  simp

omit [DecidableEq F] in
/-- Lift the actual pivot selection, with driver overhead on every inner transition. -/
theorem lift_selection {j left n : ℕ} (rev : List (Pivot F))
    {s t : PivotSelectionMachine.Configuration F} {c : Cost}
    (h : PivotSelectionMachine.Trace j n s c t) :
    Trace n (.select j left rev s) (c + wrapperCost n) (.select j left rev t) := by
  induction h with
  | nil s => simpa [wrapperCost] using Trace.nil (.select j left rev s)
  | @cons n s u t c d head tail ih =>
      have hc : (c + wrapperCost 1) + (d + wrapperCost n) =
          (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost] <;> omega
      rw [← hc]
      exact Trace.cons (Step.selection head) ih

omit [DecidableEq F] in
/-- Lift actual augmented elimination, including its own serialization and wrapper costs. -/
theorem lift_elimination {j left n : ℕ} (rev : List (Pivot F))
    {s t : AugmentedColumnMachine.Configuration F} {c : Cost}
    (h : AugmentedColumnMachine.Trace j n s c t) :
    Trace n (.eliminate j left rev s) (c + wrapperCost n) (.eliminate j left rev t) := by
  induction h with
  | nil s => simpa [wrapperCost] using Trace.nil (.eliminate j left rev s)
  | @cons n s u t c d head tail ih =>
      have hc : (c + wrapperCost 1) + (d + wrapperCost n) =
          (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost] <;> omega
      rw [← hc]
      exact Trace.cons (Step.elimination head) ih

/-- Total primitive cost in inherited categories. -/
abbrev totalCost := PivotSelectionMachine.totalCost

private theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b := by
  simp only [totalCost, PivotSelectionMachine.totalCost,
    PivotEliminationMachine.cost_add,
    RowReductionMachine.cost_add]
  omega

/-- A conservative budget covering one entire column, both callees and driver transitions. -/
def stageBudget (m n : ℕ) : ℕ := 1000 * (m + 1) * (n + 1)
/-- Polynomial fuel and primitive-cost budget, including final pivot-list materialization. -/
def budget (m n : ℕ) : ℕ := n * stageBudget m n + 7 * m + 13

omit [DecidableEq F] in
private theorem reverse_trace (ps out : List (Pivot F)) (rest : List (Row F)) :
    Trace (ps.length + 1) (.reverse ps out rest)
      ⟨⟨0, 0, ps.length + 1, 5 * ps.length + 3, 1⟩, 0, 0, 0, 0⟩
      (.done (ps.reverse ++ out) rest) := by
  induction ps generalizing out with
  | nil => simpa [emitCost] using Trace.cons (Step.emit (out := out) (rest := rest)) (Trace.nil _)
  | cons p ps ih =>
      simpa [reverseCost, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.reverse (ih (p :: out))

private theorem total_wrapper (k : ℕ) : totalCost (wrapperCost k) = 3 * k := by
  simp [totalCost, PivotSelectionMachine.totalCost, wrapperCost]
  omega

private theorem selection_bounds (M n j m s : ℕ) (c : Cost) (hj : j < n) (hm : m ≤ M)
    (hs : s ≤ PivotSelectionMachine.selectionFuel j m)
    (hc : totalCost c ≤ m * (7 * j + 26) + 9) :
    4 * s + totalCost c ≤ 100 * (M + 1) * (n + 1) := by
  have hsj : m * (j + 4) ≤ M * (n + 4) := Nat.mul_le_mul hm (by omega)
  have hcj : m * (7 * j + 26) ≤ M * (7 * n + 26) := Nat.mul_le_mul hm (by omega)
  simp only [PivotSelectionMachine.selectionFuel] at hs
  nlinarith

private theorem elimination_bounds (M n j k s : ℕ) (hj : j < n) (hk : k + 1 ≤ M)
    (hs : s ≤ AugmentedColumnMachine.fuel n k j) :
    4 * s + totalCost (AugmentedColumnMachine.cost n k j) ≤
      400 * (M + 1) * (n + 1) := by
  have hc := AugmentedColumnMachine.cost_total_le n k j hj
  have hkj : k * j ≤ k * n := Nat.mul_le_mul_left k (by omega)
  have hkn : (k + 1) * (n + 1) ≤ (M + 1) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
  simp only [AugmentedColumnMachine.fuel, AugmentedColumnMachine.columnFuel] at hs
  nlinarith

private theorem stage_combine (M n s e cs ce : ℕ)
    (hs : 4 * s + cs ≤ 100 * (M + 1) * (n + 1))
    (he : 4 * e + ce ≤ 400 * (M + 1) * (n + 1)) :
    4 * s + cs + 4 * e + ce + 25 ≤ stageBudget M n := by
  have hb : 1 ≤ (M + 1) * (n + 1) := by nlinarith [Nat.zero_le (M * n)]
  unfold stageBudget
  nlinarith

omit [DecidableEq F] in
/-- Valid active rows complete to materialized echelon data, preserving all augmented equations.
The bound simultaneously controls trace length and all primitive charges. -/
theorem loop_trace (M n left j : ℕ) (rows : List (Row F)) (rev : List (Pivot F))
    (hwidth : j + left = n) (hrect : Rectangular n rows) (hz : ZeroBefore j rows)
    (hsize : rows.length + rev.length ≤ M) :
    ∃ ps rest steps c, Trace steps (.loop j left rows rev) c (.done (rev.reverse ++ ps) rest) ∧
      Echelon n j ps rest ∧ ps.length + rest.length = rows.length ∧
      (∀ x, Solutions ps rest x ↔ PivotSelectionMachine.Satisfies rows x) ∧
      steps + totalCost c ≤ left * stageBudget M n + 7 * M + 13 := by
  classical
  induction left generalizing j rows rev with
  | zero =>
      have hj : j = n := by omega
      have h := Trace.cons (Step.finish (j := j)) (reverse_trace rev [] rows)
      refine ⟨[], rows, rev.length + 1 + 1, _, h, ?_, by simp, ?_, ?_⟩
      · exact ⟨by simp, by simp, hrect, hj ▸ hz⟩
      · intro x; rfl
      · simp only [totalCost, PivotSelectionMachine.totalCost, finishCost,
          PivotEliminationMachine.cost_add, RowReductionMachine.cost_add]
        omega
  | succ left ih =>
      have hj : j < n := by omega
      have hm : rows.length ≤ M := by omega
      obtain ⟨b, out, cs, hrun, hcorrect, hcs⟩ :=
        PivotSelectionMachine.selection_runFuel_rectangular j n rows hj hrect
      obtain ⟨ss, hss, hst⟩ := PivotSelectionMachine.runFuel_refines j
        (PivotSelectionMachine.selectionFuel j rows.length) (.scan rows [])
      rw [hrun] at hst
      have hsbound := selection_bounds M n j rows.length ss cs hj hm hss hcs
      have hperm := hcorrect.1
      have houtrect := hrect.perm hperm
      have houtzero := hz.perm hperm
      have houtlen : out.length = rows.length := hperm.length_eq.symm
      have hsel := lift_selection (left := left) rev hst
      cases b with
      | false =>
          have houtnext := houtzero.next hcorrect.2
          obtain ⟨ps, rest, t, ct, ht, he, hcount, hsol, hwork⟩ :=
            ih (j + 1) out rev (by omega) houtrect houtnext (by omega)
          have hpre := Trace.cons Step.select (hsel.trans (Trace.cons Step.nohit (Trace.nil _)))
          have h := hpre.trans ht
          refine ⟨ps, rest, _, _, h, he.weaken, hcount.trans houtlen, ?_, ?_⟩
          · intro x
            exact (hsol x).trans (PivotSelectionMachine.satisfies_perm hperm x)
          · have hprebound : (ss + (0 + 1) + 1) +
                totalCost (selectCost + ((cs + wrapperCost ss) + (nextCost + 0))) ≤
                  stageBudget M n := by
              simp only [total_add, total_wrapper]
              change ss + (0 + 1) + 1 + (8 + (totalCost cs + 3 * ss + (6 + 0))) ≤ _
              have hh := stage_combine M n ss 0 (totalCost cs) 0 hsbound (by omega)
              omega
            simp only [total_add] at hprebound ⊢
            simp only [Nat.succ_mul]
            omega
      | true =>
          obtain ⟨p, tail, a, rfl, hpa, ha⟩ := hcorrect.2
          have hplen := houtrect p (by simp)
          have hp : p.1.getD j 0 ≠ 0 := by simpa [List.getD, hpa] using ha
          have hjp : j < p.1.length := by omega
          have hlen : ∀ r ∈ tail, r.1.length = p.1.length := fun r hr =>
            (houtrect r (by simp [hr])).trans hplen.symm
          have haug := AugmentedColumnMachine.evaluation_runFuel j p tail hjp
            (by simpa only [List.getD_eq_getElem _ _ hjp] using hp) hlen
          obtain ⟨se, hse, het⟩ := AugmentedColumnMachine.runFuel_refines j
            (AugmentedColumnMachine.fuel p.1.length tail.length j) (.pack (p :: tail) [])
          rw [haug] at het
          have hebound := elimination_bounds M n j tail.length se hj (by simp at houtlen; omega)
            (by simpa only [hplen] using hse)
          have helt := lift_elimination (left := left) rev het
          obtain ⟨hnewrect, hnewzero⟩ := augmented_tail p tail houtrect houtzero hj hp
          obtain ⟨ps, rest, t, ct, ht, he, hcount, hsol, hwork⟩ :=
            ih (j + 1) (tail.map (AugmentedColumnMachine.transformRow p j)) ((j, p) :: rev)
              (by omega) hnewrect hnewzero (by simp at houtlen ⊢; omega)
          have hpre := Trace.cons Step.select (hsel.trans (Trace.cons Step.found
            (helt.trans (Trace.cons Step.store (Trace.nil _)))))
          have h := hpre.trans ht
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at h
          refine ⟨(j, p) :: ps, rest, _, _, h, ?_, ?_, ?_, ?_⟩
          · exact he.cons p hj hplen hp (fun i hi => houtzero i hi p (by simp))
          · simp only [List.length_map] at hcount
            simp only [List.length_cons] at houtlen ⊢
            omega
          · intro x
            exact (solutions_cons p j hsol x).trans
              ((AugmentedColumnMachine.solution_iff p tail j hlen x).trans
                (PivotSelectionMachine.satisfies_perm hperm x))
          · have hprebound : (ss + (se + (0 + 1) + 1) + 1) +
                totalCost (selectCost + ((cs + wrapperCost ss) +
                  (eliminateCost + ((AugmentedColumnMachine.cost p.1.length tail.length j +
                    wrapperCost se) + (storeCost + 0))))) ≤ stageBudget M n := by
              simp only [total_add, total_wrapper]
              change ss + (se + (0 + 1) + 1) + 1 + (8 + (totalCost cs + 3 * ss +
                (4 + (totalCost (AugmentedColumnMachine.cost p.1.length tail.length j) +
                  3 * se + (10 + 0))))) ≤ _
              have hh := stage_combine M n ss se (totalCost cs)
                (totalCost (AugmentedColumnMachine.cost p.1.length tail.length j)) hsbound
                (by simpa only [hplen] using hebound)
              omega
            simp only [total_add] at hprebound ⊢
            simp only [Nat.succ_mul]
            omega

/-- Uniform bounded execution produces materialized forward echelon data and preserves all RHS
solutions. The residual rows are retained, not declared consistent or discarded. -/
theorem evaluation_runFuel (n : ℕ) (rows : List (Row F)) (hrect : Rectangular n rows) :
    ∃ ps rest c, runFuel (budget rows.length n) (.loop 0 n rows []) = (.done ps rest, c) ∧
      Echelon n 0 ps rest ∧ ps.length + rest.length = rows.length ∧
      (∀ x, Solutions ps rest x ↔ PivotSelectionMachine.Satisfies rows x) ∧
      totalCost c ≤ budget rows.length n := by
  obtain ⟨ps, rest, steps, c, ht, he, hcount, hsol, hwork⟩ :=
    loop_trace rows.length n n 0 rows [] (by omega) hrect (by intro i hi; omega) (by simp)
  simp only [List.reverse_nil, List.nil_append] at ht
  have hsteps : steps ≤ budget rows.length n := by unfold budget; omega
  have hr := ht.runFuel_done (budget rows.length n - steps)
  have hsum : steps + (budget rows.length n - steps) = budget rows.length n := by omega
  rw [hsum] at hr
  exact ⟨ps, rest, c, hr, he, hcount, hsol, by unfold budget; omega⟩

end Matrix.ForwardEchelonMachine
