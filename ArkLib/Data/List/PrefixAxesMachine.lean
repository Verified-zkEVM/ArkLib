/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.List.CartesianProductMachine

/-!
# Materialized prefix axes from a shared universe

Each supplied length resets a cursor to the shared materialized universe. A counter loop copies
its prefix, then explicit reversal restores element order. A separate allocation stores the axis;
the outer reversal restores length-list order. Exhausting the universe before the counter rejects
the entire construction. Zero lengths succeed with empty axes. Emission is a separate transition.

Costs use the scalar-free Cartesian-product categories. Cell reads return head and tail together;
retained pointers are shared. Constants, input materialization, reclamation and host fuel are
outside this model. No take, map or reverse primitive occurs in dispatch. The intended consumer
constructs anisotropic grid axes from a base-field or quadratic-field enumeration before the
Cartesian-product machine. This component neither evaluates points nor chooses grid lengths.
-/

@[expose] public section

namespace List.PrefixAxesMachine

abbrev Cost := CartesianProductMachine.Cost

/-- Read the bounds pointer and initialize the bounds/outer-accumulator cursors. -/
def startCost : Cost := ⟨1, 3, 0, 0⟩
/-- Read a bound cell and universe pointer; initialize counter, input cursor and empty prefix. -/
def takeCost : Cost := ⟨1, 5, 0, 0⟩
/-- Read counter/cell/prefix, allocate a cell, write three registers and test/decrement counter. -/
def copyCost : Cost := ⟨1, 7, 2, 0⟩
/-- Read/test exhausted counter and initialize the prefix reversal destination. -/
def copyFinishCost : Cost := ⟨1, 2, 1, 0⟩
/-- Read/test positive counter and exhausted cursor, then retain the failure tag for emission. -/
def rejectCost : Cost := ⟨1, 2, 1, 0⟩
/-- Read a cell/output pointer, allocate a cell and update both reversal cursors. -/
def reverseCost : Cost := ⟨1, 5, 0, 0⟩
/-- Read exhausted cursor and retain or initialize the next output pointer. -/
def finishCost : Cost := ⟨1, 2, 0, 0⟩
/-- Read axis/outer pointers, allocate a cell and write the outer root. -/
def saveCost : Cost := ⟨1, 4, 0, 0⟩
/-- Read and emit a success/failure result handle. -/
def emitCost : Cost := ⟨1, 1, 0, 1⟩

inductive Configuration (α : Type*) where
  | start (bounds : List ℕ)
  | scan (bounds : List ℕ) (axes : List (List α))
  | copy (bounds : List ℕ) (axes : List (List α)) (remaining : ℕ) (cursor buffer : List α)
  | reversePrefix (bounds : List ℕ) (axes : List (List α)) (remaining output : List α)
  | save (bounds : List ℕ) (axes : List (List α)) (axis : List α)
  | reverseAxes (remaining output : List (List α))
  | emit (result : Option (List (List α)))
  | done (result : Option (List (List α)))
  deriving DecidableEq, Repr

variable {α : Type*}

/-- Independent rules expose copying, both reversals, allocation and rejection. -/
inductive Step (u : List α) : Configuration α → Cost → Configuration α → Prop where
  | start {bs} : Step u (.start bs) startCost (.scan bs [])
  | take {n bs axes} : Step u (.scan (n :: bs) axes) takeCost
      (.copy bs axes n u [])
  | copy {bs axes n x xs rev} : Step u (.copy bs axes (n + 1) (x :: xs) rev) copyCost
      (.copy bs axes n xs (x :: rev))
  | copyFinish {bs axes xs rev} : Step u (.copy bs axes 0 xs rev) copyFinishCost
      (.reversePrefix bs axes rev [])
  | reject {bs axes n rev} : Step u (.copy bs axes (n + 1) [] rev) rejectCost (.emit none)
  | reversePrefix {bs axes x xs out} : Step u (.reversePrefix bs axes (x :: xs) out)
      reverseCost (.reversePrefix bs axes xs (x :: out))
  | prefixEnd {bs axes out} : Step u (.reversePrefix bs axes [] out) finishCost
      (.save bs axes out)
  | save {bs axes a} : Step u (.save bs axes a) saveCost (.scan bs (a :: axes))
  | scanEnd {axes} : Step u (.scan [] axes) finishCost (.reverseAxes axes [])
  | reverseAxes {a as out} : Step u (.reverseAxes (a :: as) out) reverseCost
      (.reverseAxes as (a :: out))
  | axesEnd {out} : Step u (.reverseAxes [] out) finishCost (.emit (some out))
  | emit {out} : Step u (.emit out) emitCost (.done out)

/-- Closed executable dispatch shares the universe pointer and copies only requested cells. -/
def step (u : List α) : Configuration α → Option (Configuration α × Cost)
  | .start bs => some (.scan bs [], startCost)
  | .scan (n :: bs) axes => some (.copy bs axes n u [], takeCost)
  | .scan [] axes => some (.reverseAxes axes [], finishCost)
  | .copy bs axes 0 _ rev => some (.reversePrefix bs axes rev [], copyFinishCost)
  | .copy bs axes (n + 1) (x :: xs) rev => some (.copy bs axes n xs (x :: rev), copyCost)
  | .copy _ _ (_ + 1) [] _ => some (.emit none, rejectCost)
  | .reversePrefix bs axes (x :: xs) out => some (.reversePrefix bs axes xs (x :: out), reverseCost)
  | .reversePrefix bs axes [] out => some (.save bs axes out, finishCost)
  | .save bs axes a => some (.scan bs (a :: axes), saveCost)
  | .reverseAxes (a :: as) out => some (.reverseAxes as (a :: out), reverseCost)
  | .reverseAxes [] out => some (.emit (some out), finishCost)
  | .emit out => some (.done out, emitCost)
  | .done _ => none

/-- Every rule agrees with dispatch and its primitive charge. -/
theorem Step.step_eq {u : List α} {s t : Configuration α} {c : Cost} (h : Step u s c t) :
    step u s = some (t, c) := by cases h <;> rfl

/-- Dispatch is exhausted by the independent rules. -/
theorem step_sound {u : List α} {s t : Configuration α} {c : Cost}
    (h : step u s = some (t, c)) : Step u s c t := by
  cases s with
  | start bs => cases h; constructor
  | scan bs axes => cases bs <;> cases h <;> constructor
  | copy bs axes n xs rev => cases n <;> cases xs <;> cases h <;> constructor
  | reversePrefix bs axes xs out => cases xs <;> cases h <;> constructor
  | save bs axes a => cases h; constructor
  | reverseAxes as out => cases as <;> cases h <;> constructor
  | emit out => cases h; constructor
  | done out => simp [step] at h

inductive Trace (u : List α) : ℕ → Configuration α → Cost → Configuration α → Prop where
  | nil (s) : Trace u 0 s 0 s
  | cons {n s v t c d} (head : Step u s c v) (tail : Trace u n v d t) :
      Trace u (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

/-- Concatenate executions, retaining all costs. -/
theorem Trace.append {u : List α} {n m : ℕ} {s v t : Configuration α} {c d : Cost}
    (h : Trace u n s c v) (h' : Trace u m v d t) : Trace u (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cost_assoc] using
      Trace.cons head (ih h')

/-- One transition per unit of fuel; insufficient fuel exposes the reached phase. -/
def runFuel (u : List α) : ℕ → Configuration α → Configuration α × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step u s with
    | none => (s, 0)
    | some (t, c) => let result := runFuel u n t; (result.1, c + result.2)

/-- Every interpreter run has a trace with the identical cost. -/
theorem runFuel_refines (u : List α) (fuel : ℕ) (s : Configuration α) :
    ∃ n ≤ fuel, Trace u n s (runFuel u fuel s).2 (runFuel u fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
    cases hs : step u s with
    | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil (u := u) s⟩
    | some pair =>
      obtain ⟨n, hn, h⟩ := ih pair.1
      exact ⟨n + 1, Nat.succ_le_succ hn, by
        simpa [runFuel, hs] using Trace.cons (step_sound hs) h⟩

/-- Extra host fuel does not add work after success or rejection. -/
theorem Trace.runFuel_done {u : List α} {n : ℕ} {s : Configuration α} {c : Cost}
    {out : Option (List (List α))} (h : Trace u n s c (.done out)) (extra : ℕ) :
    runFuel u (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
    rw [Nat.add_right_comm, runFuel, head.step_eq]
    dsimp only
    rw [ih ht]

private theorem total_add (a b : Cost) : (a + b).total = a.total + b.total := by
  simp only [CartesianProductMachine.Cost.total, CartesianProductMachine.cost_add]
  omega

/-- Each individual transition has bounded scalar-free work. -/
theorem Step.total_le {u : List α} {s t : Configuration α} {c : Cost} (h : Step u s c t) :
    c.total ≤ 12 := by cases h <;> decide

/-- Summing transition charges bounds the actual trace. -/
theorem Trace.total_le {u : List α} {n : ℕ} {s t : Configuration α} {c : Cost}
    (h : Trace u n s c t) : c.total ≤ 12 * n := by
  induction h with
  | nil s => decide
  | cons head tail ih => rw [total_add]; have hh := head.total_le; omega

/-- Proof-only ordered prefix axes; this map/take combination is not dispatched. -/
def axesSpec (u : List α) (bounds : List ℕ) : List (List α) := bounds.map (u.take ·)

/-- Uniform linear host fuel, sufficient for success and early rejection. -/
def constructionFuel (bounds : List ℕ) : ℕ := 2 * bounds.sum + 5 * bounds.length + 4

/-- Copy exactly the requested prefix, with a separately charged reversal phase. -/
theorem copy_trace (u : List α) (bs : List ℕ) (axes : List (List α)) (n : ℕ)
    (xs rev : List α) (h : n ≤ xs.length) :
    ∃ c, Trace u (n + 1) (.copy bs axes n xs rev) c
      (.reversePrefix bs axes ((xs.take n).reverse ++ rev) []) := by
  induction n generalizing xs rev with
  | zero => exact ⟨_, Trace.cons Step.copyFinish (Trace.nil _)⟩
  | succ n ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      obtain ⟨c, ht⟩ := ih xs (x :: rev) (by simpa using h)
      refine ⟨copyCost + c, ?_⟩
      simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.copy ht

/-- Reversal materializes the ordered prefix before allocating its outer axis cell. -/
theorem reversePrefix_trace (u : List α) (bs : List ℕ) (axes : List (List α)) (xs out : List α) :
    ∃ c, Trace u (xs.length + 1) (.reversePrefix bs axes xs out) c
      (.save bs axes (xs.reverse ++ out)) := by
  induction xs generalizing out with
  | nil => exact ⟨_, Trace.cons Step.prefixEnd (Trace.nil _)⟩
  | cons x xs ih =>
    obtain ⟨c, h⟩ := ih (x :: out)
    refine ⟨reverseCost + c, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reversePrefix h

/-- Restore axis order and separately emit the completed result. -/
theorem reverseAxes_trace (u : List α) (as out : List (List α)) :
    ∃ c, Trace u (as.length + 2) (.reverseAxes as out) c (.done (some (as.reverse ++ out))) := by
  induction as generalizing out with
  | nil => exact ⟨_, Trace.cons Step.axesEnd (Trace.cons Step.emit (Trace.nil _))⟩
  | cons a as ih =>
    obtain ⟨c, h⟩ := ih (a :: out)
    refine ⟨reverseCost + c, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverseAxes h

/-- Successful bounds are copied in order with exact linear transition fuel. -/
theorem scan_success (u : List α) (bs : List ℕ) (acc : List (List α))
    (hvalid : ∀ n ∈ bs, n ≤ u.length) :
    ∃ c, Trace u (2 * bs.sum + 5 * bs.length + acc.length + 3) (.scan bs acc) c
      (.done (some (acc.reverse ++ axesSpec u bs))) := by
  induction bs generalizing acc with
  | nil =>
    obtain ⟨c, h⟩ := reverseAxes_trace u acc []
    refine ⟨finishCost + c, ?_⟩
    simpa [axesSpec, Nat.add_assoc] using Trace.cons Step.scanEnd h
  | cons n bs ih =>
    have hn := hvalid n (by simp)
    obtain ⟨cc, hc⟩ := copy_trace u bs acc n u [] hn
    obtain ⟨rc, hr⟩ := reversePrefix_trace u bs acc (u.take n).reverse []
    simp only [List.append_nil] at hc
    simp only [List.reverse_reverse, List.append_nil] at hr
    obtain ⟨sc, hs⟩ := ih ((u.take n) :: acc) (fun k hk ↦ hvalid k (by simp [hk]))
    refine ⟨takeCost + (cc + (rc + (saveCost + sc))), ?_⟩
    convert Trace.cons Step.take (hc.append (hr.append (Trace.cons Step.save hs))) using 1 <;>
      simp [axesSpec, List.reverse_cons, List.append_assoc, List.length_take, Nat.min_eq_left hn,
        Nat.mul_add]; omega

/-- An oversized prefix rejects after traversing the available universe, with no partial output. -/
theorem copy_reject (u : List α) (bs : List ℕ) (axes : List (List α)) (n : ℕ)
    (xs rev : List α) (hbad : xs.length < n) :
    ∃ c, Trace u (xs.length + 2) (.copy bs axes n xs rev) c (.done none) := by
  induction xs generalizing n rev with
  | nil =>
    cases n with
    | zero => simp at hbad
    | succ n => exact ⟨_, Trace.cons Step.reject (Trace.cons Step.emit (Trace.nil _))⟩
  | cons x xs ih =>
    cases n with
    | zero => simp at hbad
    | succ n =>
      obtain ⟨c, ht⟩ := ih n (x :: rev) (by simpa using hbad)
      refine ⟨copyCost + c, ?_⟩
      simpa using Trace.cons Step.copy ht

/-- Any invalid bound causes complete rejection within the same linear fuel budget. -/
theorem scan_reject (u : List α) (bs : List ℕ) (acc : List (List α))
    (hbad : ∃ n ∈ bs, u.length < n) :
    ∃ steps c, steps ≤ 2 * bs.sum + 5 * bs.length + 3 ∧
      Trace u steps (.scan bs acc) c (.done none) := by
  induction bs generalizing acc with
  | nil => simp at hbad
  | cons n bs ih =>
    by_cases hn : n ≤ u.length
    · have htail : ∃ k ∈ bs, u.length < k := by
        obtain ⟨k, hk, h⟩ := hbad
        rcases List.mem_cons.mp hk with rfl | hk
        · omega
        · exact ⟨k, hk, h⟩
      obtain ⟨cc, hc⟩ := copy_trace u bs acc n u [] hn
      obtain ⟨rc, hr⟩ := reversePrefix_trace u bs acc (u.take n).reverse []
      simp only [List.append_nil] at hc
      simp only [List.reverse_reverse, List.append_nil] at hr
      obtain ⟨steps, c, hsteps, ht⟩ := ih ((u.take n) :: acc) htail
      have h := Trace.cons Step.take (hc.append (hr.append (Trace.cons Step.save ht)))
      refine ⟨_, _, ?_, h⟩
      simp only [List.length_reverse, List.length_take, Nat.min_eq_left hn]
      simp only [List.sum_cons, List.length_cons, Nat.mul_add]
      omega
    · obtain ⟨c, ht⟩ := copy_reject u bs acc n u [] (by omega)
      refine ⟨u.length + 3, takeCost + c, ?_, Trace.cons Step.take ht⟩
      simp only [List.sum_cons, List.length_cons, Nat.mul_add]
      omega

/-- Actual success emits exactly the supplied prefixes, with a linear primitive bound. -/
theorem success_runFuel (u : List α) (bs : List ℕ) (hvalid : ∀ n ∈ bs, n ≤ u.length) :
    ∃ c, runFuel u (constructionFuel bs) (.start bs) = (.done (some (axesSpec u bs)), c) ∧
      c.total ≤ 128 * (bs.sum + bs.length + 1) := by
  obtain ⟨c, ht⟩ := scan_success u bs [] hvalid
  have h := Trace.cons Step.start ht
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at h
  have hr := h.runFuel_done 0
  simp only [Nat.add_zero] at hr
  refine ⟨startCost + c, hr, ?_⟩
  have hc := h.total_le
  omega

/-- Actual failure never returns partial axes, even when an earlier prefix succeeded. -/
theorem reject_runFuel (u : List α) (bs : List ℕ) (hbad : ∃ n ∈ bs, u.length < n) :
    ∃ c, runFuel u (constructionFuel bs) (.start bs) = (.done none, c) ∧
      c.total ≤ 128 * (bs.sum + bs.length + 1) := by
  obtain ⟨steps, c, hsteps, ht⟩ := scan_reject u bs [] hbad
  have h := Trace.cons Step.start ht
  have hb : steps + 1 ≤ constructionFuel bs := by unfold constructionFuel; omega
  have hr := h.runFuel_done (constructionFuel bs - (steps + 1))
  rw [Nat.add_sub_of_le hb] at hr
  refine ⟨startCost + c, hr, ?_⟩
  have hc := h.total_le
  unfold constructionFuel at hb
  omega

/-- Every requested length is represented exactly, including zero and repeated lengths. -/
theorem axesSpec_lengths (u : List α) (bs : List ℕ) (hvalid : ∀ n ∈ bs, n ≤ u.length) :
    (axesSpec u bs).map List.length = bs := by
  induction bs with
  | nil => rfl
  | cons n bs ih =>
    simp only [axesSpec, List.map_cons, List.length_take]
    rw [Nat.min_eq_left (hvalid n (by simp))]
    congr 1
    exact ih (fun k hk ↦ hvalid k (by simp [hk]))

/-- Prefix materialization preserves universe distinctness on each axis. -/
theorem axesSpec_nodup (u : List α) (bs : List ℕ) (hu : u.Nodup) :
    ∀ a ∈ axesSpec u bs, a.Nodup := by
  intro a ha
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp ha
  exact hu.take

/-- A complete dichotomy identifies the success payload and rejects exactly oversized requests. -/
theorem construction_correct (u : List α) (bs : List ℕ) :
    ∃ out c, runFuel u (constructionFuel bs) (.start bs) = (.done out, c) ∧
      (out = none ↔ ∃ n ∈ bs, u.length < n) ∧
      (∀ axes, out = some axes → axes = axesSpec u bs ∧ axes.map List.length = bs) ∧
      c.total ≤ 128 * (bs.sum + bs.length + 1) := by
  by_cases hvalid : ∀ n ∈ bs, n ≤ u.length
  · obtain ⟨c, hr, hc⟩ := success_runFuel u bs hvalid
    refine ⟨some (axesSpec u bs), c, hr, ?_, ?_, hc⟩
    · simp only [Option.some_ne_none, false_iff, not_exists, not_and]
      intro n hn
      exact Nat.not_lt.mpr (hvalid n hn)
    · intro axes h
      cases h
      exact ⟨rfl, axesSpec_lengths u bs hvalid⟩
  · have hbad : ∃ n ∈ bs, u.length < n := by
      push Not at hvalid
      exact hvalid
    obtain ⟨c, hr, hc⟩ := reject_runFuel u bs hbad
    exact ⟨none, c, hr, by simp [hbad], by simp, hc⟩

end List.PrefixAxesMachine
