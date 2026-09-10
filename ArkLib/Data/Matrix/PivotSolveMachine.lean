/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.ForwardEchelonSemantics

/-!
# Closed correction of one pivot coordinate

The machine computes the complete row dot product, reads the pivot coefficient, forms
`(rhs-dot)/pivot`, and adds that correction to the supplied materialized vector at the pivot.
Indexed scanning and prefix restoration are explicit. Input handles are immutable parameters;
there is no evaluator or solver callback. Costs exclude input preparation and scalar bit costs.

Each transition pays one control dispatch. Dot updates read two cells and the accumulator and
write three registers (6 data operations). Lookup initialization writes six handles/registers;
lookup steps read a cell and update cursor/index/accumulator (4), with a terminal read and two
writes (3). Scalar unary operations read and write (2); binary operations read twice and write
once (3). Scaling also initializes the indexed update (8 total). Update scans and restoration
read a cell, allocate a cons and write three registers (5); the indexed hit similarly reads the
old value and correction, allocates and writes the output (5). Emission reads and writes its
handle (2). Index tests/decrements, field operations, equalities and outputs are separate fields.
Immutable list handles are shared; reclamation and interpreter fuel are outside this model.
-/

@[expose] public section

namespace Matrix.PivotSolveMachine

abbrev Row (F : Type*) := PivotSelectionMachine.Row F
abbrev Cost := PivotEliminationMachine.Cost

def dotCost : Cost := ⟨⟨1, 1, 1, 6, 0⟩, 0, 0, 0, 0⟩
def lookupStartCost : Cost := ⟨⟨0, 0, 1, 6, 0⟩, 0, 0, 0, 0⟩
def seekCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 2⟩
def hitCost : Cost := ⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 0, 1⟩
def checkCost : Cost := ⟨⟨0, 0, 1, 1, 0⟩, 0, 0, 1, 0⟩
def inverseCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 1, 0, 0, 0⟩
def negateCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 0, 1, 0, 0⟩
def addCost : Cost := ⟨⟨1, 0, 1, 3, 0⟩, 0, 0, 0, 0⟩
def scaleCost : Cost := ⟨⟨0, 1, 1, 8, 0⟩, 0, 0, 0, 0⟩
def updateSeekCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 2⟩
def updateHitCost : Cost := ⟨⟨1, 0, 1, 5, 0⟩, 0, 0, 0, 1⟩
def reverseCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩
def emitCost : Cost := ⟨⟨0, 0, 1, 2, 1⟩, 0, 0, 0, 0⟩
def rejectCost : Cost := ⟨⟨0, 0, 1, 2, 1⟩, 0, 0, 0, 0⟩
def zeroCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 1, 0⟩

inductive Configuration (F : Type*) where
  | dot (coefficients values : List F) (sum : F)
  | lookup (cursor : List F) (index : ℕ) (sum : F)
  | check (pivot sum : F)
  | inverse (pivot sum : F)
  | negate (inverse sum : F)
  | difference (inverse negative : F)
  | scale (inverse difference : F)
  | update (cursor : List F) (index : ℕ) (saved : List F) (delta : F)
  | restore (saved output : List F)
  | done (values : List F)
  | rejected
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent primitive transitions, including all list scans and scalar arithmetic. -/
inductive Step (r : Row F) (j : ℕ) (v : List F) :
    Configuration F → Cost → Configuration F → Prop where
  | dot {a as b bs s} : Step r j v (.dot (a :: as) (b :: bs) s) dotCost
      (.dot as bs (s + a * b))
  | dotEnd {s} : Step r j v (.dot [] [] s) lookupStartCost (.lookup r.1 j s)
  | dotLeft {b bs s} : Step r j v (.dot [] (b :: bs) s) rejectCost .rejected
  | dotRight {a as s} : Step r j v (.dot (a :: as) [] s) rejectCost .rejected
  | seek {x xs i s} : Step r j v (.lookup (x :: xs) (i + 1) s) seekCost (.lookup xs i s)
  | hit {x xs s} : Step r j v (.lookup (x :: xs) 0 s) hitCost (.check x s)
  | missing {i s} : Step r j v (.lookup [] i s) rejectCost .rejected
  | zero {s} : Step r j v (.check 0 s) zeroCost .rejected
  | check {p s} (hp : p ≠ 0) : Step r j v (.check p s) checkCost (.inverse p s)
  | inverse {p s} : Step r j v (.inverse p s) inverseCost (.negate p⁻¹ s)
  | negate {a s} : Step r j v (.negate a s) negateCost (.difference a (-s))
  | difference {a b} : Step r j v (.difference a b) addCost (.scale a (r.2 + b))
  | scale {a b} : Step r j v (.scale a b) scaleCost (.update v j [] (b * a))
  | updateSeek {x xs i rev d} : Step r j v (.update (x :: xs) (i + 1) rev d) updateSeekCost
      (.update xs i (x :: rev) d)
  | updateHit {x xs rev d} : Step r j v (.update (x :: xs) 0 rev d) updateHitCost
      (.restore rev ((x + d) :: xs))
  | updateMissing {i rev d} : Step r j v (.update [] i rev d) rejectCost .rejected
  | restore {x xs out} : Step r j v (.restore (x :: xs) out) reverseCost
      (.restore xs (x :: out))
  | emit {out} : Step r j v (.restore [] out) emitCost (.done out)

def step (r : Row F) (j : ℕ) (v : List F) : Configuration F → Option (Configuration F × Cost)
  | .dot (a :: as) (b :: bs) s => some (.dot as bs (s + a * b), dotCost)
  | .dot [] [] s => some (.lookup r.1 j s, lookupStartCost)
  | .dot [] (_ :: _) _ | .dot (_ :: _) [] _ => some (.rejected, rejectCost)
  | .lookup (_ :: xs) (i + 1) s => some (.lookup xs i s, seekCost)
  | .lookup (x :: _) 0 s => some (.check x s, hitCost)
  | .lookup [] _ _ => some (.rejected, rejectCost)
  | .check p s => if p = 0 then some (.rejected, zeroCost) else some (.inverse p s, checkCost)
  | .inverse p s => some (.negate p⁻¹ s, inverseCost)
  | .negate a s => some (.difference a (-s), negateCost)
  | .difference a b => some (.scale a (r.2 + b), addCost)
  | .scale a b => some (.update v j [] (b * a), scaleCost)
  | .update (x :: xs) (i + 1) rev d => some (.update xs i (x :: rev) d, updateSeekCost)
  | .update (x :: xs) 0 rev d => some (.restore rev ((x + d) :: xs), updateHitCost)
  | .update [] _ _ _ => some (.rejected, rejectCost)
  | .restore (x :: xs) out => some (.restore xs (x :: out), reverseCost)
  | .restore [] out => some (.done out, emitCost)
  | .done _ | .rejected => none

/-- The independent rules determine executable results and costs. -/
theorem Step.step_eq {r : Row F} {j : ℕ} {v : List F} {s t : Configuration F} {c : Cost}
    (h : Step r j v s c t) : step r j v s = some (t, c) := by
  cases h with
  | zero => simp [step]
  | check hp => simp [step, hp]
  | _ => rfl

theorem step_sound {r : Row F} {j : ℕ} {v : List F} {s t : Configuration F} {c : Cost}
    (h : step r j v s = some (t, c)) : Step r j v s c t := by
  cases s with
  | dot as bs s => cases as <;> cases bs <;> cases h <;> constructor
  | lookup xs i s => cases xs <;> cases i <;> cases h <;> constructor
  | check p s =>
      by_cases hp : p = 0
      · subst p
        simp only [step] at h
        rcases h with ⟨rfl, rfl⟩; exact Step.zero
      · simp only [step, if_neg hp, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩; exact Step.check hp
  | update xs i rev d => cases xs <;> cases i <;> cases h <;> constructor
  | restore xs out => cases xs <;> cases h <;> constructor
  | done out => simp [step] at h
  | rejected => simp [step] at h
  | _ => cases h; constructor

inductive Trace (r : Row F) (j : ℕ) (v : List F) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace r j v 0 s 0 s
  | cons {n s u t c d} (head : Step r j v s c u) (tail : Trace r j v n u d t) :
      Trace r j v (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

omit [DecidableEq F] in
theorem Trace.trans {r : Row F} {j : ℕ} {v : List F} {n m : ℕ}
    {s u t : Configuration F} {c d : Cost} (h : Trace r j v n s c u)
    (h' : Trace r j v m u d t) : Trace r j v (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

def runFuel (r : Row F) (j : ℕ) (v : List F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step r j v s with
      | none => (s, 0)
      | some (t, c) => let z := runFuel r j v n t; (z.1, c + z.2)

theorem runFuel_refines (r : Row F) (j : ℕ) (v : List F) (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace r j v n s (runFuel r j v fuel s).2 (runFuel r j v fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step r j v s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

theorem Trace.runFuel_eq {r : Row F} {j : ℕ} {v : List F} {n : ℕ}
    {s t : Configuration F} {c : Cost} (h : Trace r j v n s c t) :
    runFuel r j v n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-- Mathematical dot product used only as a specification. -/
def dot : List F → List F → F
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- Semantic correction and point update. -/
def correction (r : Row F) (j : ℕ) (v : List F) : F :=
  (r.2 - dot r.1 v) * (r.1.getD j 0)⁻¹

def result (r : Row F) (j : ℕ) (v : List F) : List F :=
  v.set j (v.getD j 0 + correction r j v)

def cost (n j : ℕ) : Cost := ⟨⟨n + 2, n + 1, n + 3 * j + 9, 6 * n + 14 * j + 32, 1⟩,
  1, 1, 1, 4 * j + 2⟩

omit [DecidableEq F] in
private theorem dot_trace (r : Row F) (j : ℕ) (v as bs : List F) (s : F)
    (hlen : as.length = bs.length) :
    Trace r j v (as.length + 1) (.dot as bs s)
      ⟨⟨as.length, as.length, as.length + 1, 6 * as.length + 6, 0⟩, 0, 0, 0, 0⟩
      (.lookup r.1 j (s + dot as bs)) := by
  induction as generalizing bs s with
  | nil =>
      cases bs with
      | nil => simpa [dot, lookupStartCost] using
          Trace.cons (Step.dotEnd (r := r) (j := j) (v := v) (s := s)) (Trace.nil _)
      | cons b bs => simp at hlen
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          have h := Trace.cons Step.dot (ih bs (s + a * b) (by simpa using hlen))
          convert h using 1 <;> simp [dot, dotCost, Nat.mul_add, add_assoc]; omega

omit [DecidableEq F] in
private theorem lookup_trace (r : Row F) (j : ℕ) (v xs : List F) (i : ℕ) (p s : F)
    (hp : xs[i]? = some p) :
    Trace r j v (i + 1) (.lookup xs i s)
      ⟨⟨0, 0, i + 1, 4 * i + 3, 0⟩, 0, 0, 0, 2 * i + 1⟩ (.check p s) := by
  induction i generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at hp
      | cons a xs =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
          subst a
          simpa [hitCost] using Trace.cons (Step.hit (r := r) (j := j) (v := v)
            (xs := xs) (s := s)) (Trace.nil _)
  | succ i ih =>
      cases xs with
      | nil => simp at hp
      | cons a xs =>
          simpa [seekCost, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Trace.cons (Step.seek (x := a)) (ih xs (by simpa using hp))

omit [DecidableEq F] in
private theorem restore_trace (r : Row F) (j : ℕ) (v rev out : List F) :
    Trace r j v (rev.length + 1) (.restore rev out)
      ⟨⟨0, 0, rev.length + 1, 5 * rev.length + 2, 1⟩, 0, 0, 0, 0⟩
      (.done (rev.reverse ++ out)) := by
  induction rev generalizing out with
  | nil => simpa [emitCost] using Trace.cons (Step.emit (r := r) (j := j) (v := v)
      (out := out)) (Trace.nil _)
  | cons x xs ih =>
      simpa [reverseCost, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.restore (ih (x :: out))

omit [DecidableEq F] in
private theorem update_trace (r : Row F) (j : ℕ) (v xs rev : List F) (i : ℕ) (d : F)
    (hi : i < xs.length) :
    Trace r j v (2 * i + rev.length + 2) (.update xs i rev d)
      ⟨⟨1, 0, 2 * i + rev.length + 2, 10 * i + 5 * rev.length + 7, 1⟩, 0, 0, 0, 2 * i + 1⟩
      (.done (rev.reverse ++ xs.set i (xs.getD i 0 + d))) := by
  induction i generalizing xs rev with
  | zero =>
      cases xs with
      | nil => simp at hi
      | cons x xs =>
          have h := Trace.cons Step.updateHit (restore_trace r j v rev ((x + d) :: xs))
          convert h using 1 <;> simp [updateHitCost]; omega
  | succ i ih =>
      cases xs with
      | nil => simp at hi
      | cons x xs =>
          have h := Trace.cons Step.updateSeek (ih xs (x :: rev) (by simpa using hi))
          convert h using 1 <;>
            simp [updateSeekCost, List.reverse_cons, List.append_assoc, Nat.mul_add] <;> omega

/-- Exact execution computes a materialized point correction through actual scalar/list steps. -/
theorem evaluation_runFuel (r : Row F) (j : ℕ) (v : List F)
    (hlen : r.1.length = v.length) (hj : j < r.1.length) (hp : r.1.getD j 0 ≠ 0) :
    runFuel r j v (r.1.length + 3 * j + 9) (.dot r.1 v 0) =
      (.done (result r j v), cost r.1.length j) := by
  have hd := dot_trace r j v r.1 v 0 hlen
  simp only [zero_add] at hd
  have hl := lookup_trace r j v r.1 j (r.1.getD j 0) (dot r.1 v)
    (by rw [List.getD_eq_getElem _ _ hj]; simp)
  have hu := update_trace r j v v [] j (correction r j v) (by omega)
  simp only [List.length_nil, List.reverse_nil, List.nil_append] at hu
  simp only [correction, sub_eq_add_neg] at hu
  have ha := Trace.cons (Step.check hp) (Trace.cons Step.inverse (Trace.cons Step.negate
    (Trace.cons Step.difference (Trace.cons Step.scale hu))))
  have h := hd.trans (hl.trans ha)
  have heq := h.runFuel_eq
  have hf : (r.1.length + 1) + (j + 1 + (2 * j + 0 + 2 + 1 + 1 + 1 + 1 + 1)) =
      r.1.length + 3 * j + 9 := by omega
  rw [hf] at heq
  convert heq using 1
  simp [result, correction, sub_eq_add_neg, cost, checkCost, inverseCost, negateCost,
      addCost, scaleCost]; omega

omit [DecidableEq F] in
/-- The recursive dot specification is the same coefficient-side sum used by augmented equations. -/
theorem dot_eq_rowValue (as bs : List F) (hlen : as.length = bs.length) :
    dot as bs = AugmentedColumnMachine.rowValue as (fun i => bs.getD i 0) := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [dot, AugmentedColumnMachine.rowValue]
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          rw [dot, ih bs (by simpa using hlen)]
          simp [AugmentedColumnMachine.rowValue, Finset.sum_range_succ', add_comm]

omit [DecidableEq F] in
/-- A valid materialized point update adds a delta at exactly one coordinate. -/
theorem getD_set_add (v : List F) (j : ℕ) (d : F) (hj : j < v.length) (i : ℕ) :
    (v.set j (v.getD j 0 + d)).getD i 0 = v.getD i 0 + if i = j then d else 0 := by
  induction v generalizing i j with
  | nil => simp at hj
  | cons x xs ih =>
      cases j with
      | zero => cases i <;> simp
      | succ j =>
          cases i with
          | zero => simp
          | succ i => simpa using ih j (by simpa using hj) i

omit [DecidableEq F] in
/-- Point updates have their expected linear effect on any same-width row equation. -/
theorem rowValue_set_add (as v : List F) (j : ℕ) (d : F)
    (hlen : as.length = v.length) (hj : j < as.length) :
    AugmentedColumnMachine.rowValue as (fun i => (v.set j (v.getD j 0 + d)).getD i 0) =
      AugmentedColumnMachine.rowValue as (fun i => v.getD i 0) + as.getD j 0 * d := by
  simp only [AugmentedColumnMachine.rowValue]
  simp_rw [getD_set_add v j d (by omega)]
  simp [mul_add, Finset.sum_add_distrib, mul_ite, Finset.mem_range, hj]

omit [DecidableEq F] in
/-- Correction solves the actual augmented equation, without assuming any system solution. -/
theorem result_solves (r : Row F) (j : ℕ) (v : List F) (hlen : r.1.length = v.length)
    (hj : j < r.1.length) (hp : r.1.getD j 0 ≠ 0) :
    AugmentedColumnMachine.rowValue r.1 (fun i => (result r j v).getD i 0) = r.2 := by
  rw [result, rowValue_set_add r.1 v j (correction r j v) hlen hj]
  rw [← dot_eq_rowValue r.1 v hlen]
  unfold correction
  field_simp
  ring

omit [DecidableEq F] in
/-- No coordinate other than the selected pivot is changed. -/
theorem result_unchanged (r : Row F) (j : ℕ) (v : List F) (hj : j < v.length)
    (i : ℕ) (hi : i ≠ j) : (result r j v).getD i 0 = v.getD i 0 := by
  rw [result, getD_set_add v j _ hj i, if_neg hi, add_zero]

omit [DecidableEq F] in
/-- Point correction retains the complete supplied vector length. -/
theorem result_length (r : Row F) (j : ℕ) (v : List F) : (result r j v).length = v.length := by
  simp [result]

/-- Both trace length and total primitive cost have linear width bounds. -/
theorem bounds (n j : ℕ) (hj : j < n) :
    n + 3 * j + 9 ≤ 13 * (n + 1) ∧
      PivotSelectionMachine.totalCost (cost n j) ≤ 80 * (n + 1) := by
  simp only [PivotSelectionMachine.totalCost, cost]
  omega

end Matrix.PivotSolveMachine
