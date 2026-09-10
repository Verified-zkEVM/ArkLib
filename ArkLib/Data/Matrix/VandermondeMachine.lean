/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.PivotSelectionMachine
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Materialized augmented Vandermonde rows

The input is a materialized list of point/value pairs and a column count. Counter loops construct
ascending powers, reverse each coefficient list, allocate its augmented row and outer list cell,
and finally reverse and emit the ordered rows. One multiplication is executed per column,
including the final unused next power. No power, map, ofFn, or bulk reverse is dispatched.

Costs use the pivot-selection categories. Cell reads return head and tail together; retained
registers are shared. Pair allocation writes both slots. Constants, input materialization, host
fuel and scalar bit costs are outside this model. Sample evaluation and solving are separate
components. Specification and matrix representation maps below are mathematical interfaces only.
-/

@[expose] public section

namespace Matrix.VandermondeMachine

abbrev Row (F : Type*) := PivotSelectionMachine.Row F
abbrev Cost := PivotSelectionMachine.Cost
abbrev Sample (F : Type*) := F × F

/-- Reuse every scalar, natural, control, data and output category. -/
abbrev totalCost := PivotSelectionMachine.totalCost

/-- Read input and column count; initialize row cursor and empty accumulator. -/
def startCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 0⟩
/-- Read sample cell, point, RHS and column count; initialize row-loop registers. -/
def takeCost : Cost := ⟨⟨0, 0, 1, 10, 0⟩, 0, 0, 0, 0⟩
/-- Test/decrement counter, allocate a coefficient cell and update its cursor. -/
def coefficientCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 2⟩
/-- Read point/current power, multiply once and write the next power. -/
def multiplyCost : Cost := ⟨⟨0, 1, 1, 3, 0⟩, 0, 0, 0, 0⟩
/-- Test exhausted power counter and initialize the coefficient reversal destination. -/
def powerFinishCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 1⟩
/-- Read a cell/destination, allocate a cell and update both reversal pointers. -/
def reverseCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩
/-- Read exhausted cursor and retain the completed coefficient list. -/
def rowFinishCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩
/-- Read coefficient pointer and RHS; allocate both slots of the augmented row. -/
def packCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 0⟩
/-- Read augmented row and accumulator, allocate an outer cell and write its root. -/
def saveCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 0⟩
/-- Read exhausted sample cursor and initialize the outer reversal destination. -/
def outerFinishCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩
/-- Read exhausted outer cursor and retain the ordered output handle. -/
def finishCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩
/-- Read and emit the ordered augmented-row list. -/
def emitCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩

inductive Configuration (F : Type*) where
  | start (samples : List (Sample F))
  | scan (samples : List (Sample F)) (rows : List (Row F))
  | power (x y : F) (samples : List (Sample F)) (rows : List (Row F))
      (remaining : ℕ) (value : F) (coefficients : List F)
  | multiply (x y : F) (samples : List (Sample F)) (rows : List (Row F))
      (remaining : ℕ) (value : F) (coefficients : List F)
  | reverseRow (y : F) (samples : List (Sample F)) (rows : List (Row F))
      (remaining output : List F)
  | pack (y : F) (samples : List (Sample F)) (rows : List (Row F)) (coefficients : List F)
  | save (row : Row F) (samples : List (Sample F)) (rows : List (Row F))
  | reverseRows (remaining output : List (Row F))
  | emit (rows : List (Row F))
  | done (rows : List (Row F))
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F]

/-- Independent rules specify individual scalar, counter and allocation operations. -/
inductive Step (L : ℕ) : Configuration F → Cost → Configuration F → Prop where
  | start {ss} : Step L (.start ss) startCost (.scan ss [])
  | take {x y ss rows} : Step L (.scan ((x, y) :: ss) rows) takeCost
      (.power x y ss rows L 1 [])
  | coefficient {x y ss rows n p cs} : Step L (.power x y ss rows (n + 1) p cs)
      coefficientCost (.multiply x y ss rows n p (p :: cs))
  | multiply {x y ss rows n p cs} : Step L (.multiply x y ss rows n p cs) multiplyCost
      (.power x y ss rows n (p * x) cs)
  | powerFinish {x y ss rows p cs} : Step L (.power x y ss rows 0 p cs) powerFinishCost
      (.reverseRow y ss rows cs [])
  | reverseRow {y ss rows c cs out} : Step L (.reverseRow y ss rows (c :: cs) out) reverseCost
      (.reverseRow y ss rows cs (c :: out))
  | rowFinish {y ss rows out} : Step L (.reverseRow y ss rows [] out) rowFinishCost
      (.pack y ss rows out)
  | pack {y ss rows cs} : Step L (.pack y ss rows cs) packCost (.save (cs, y) ss rows)
  | save {r ss rows} : Step L (.save r ss rows) saveCost (.scan ss (r :: rows))
  | outerFinish {rows} : Step L (.scan [] rows) outerFinishCost (.reverseRows rows [])
  | reverseRows {r rs out} : Step L (.reverseRows (r :: rs) out) reverseCost
      (.reverseRows rs (r :: out))
  | finish {out} : Step L (.reverseRows [] out) finishCost (.emit out)
  | emit {out} : Step L (.emit out) emitCost (.done out)

/-- Literal dispatch contains no bulk list or polynomial primitive. -/
def step (L : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start ss => some (.scan ss [], startCost)
  | .scan ((x, y) :: ss) rows => some (.power x y ss rows L 1 [], takeCost)
  | .scan [] rows => some (.reverseRows rows [], outerFinishCost)
  | .power x y ss rows (n + 1) p cs =>
      some (.multiply x y ss rows n p (p :: cs), coefficientCost)
  | .power _ y ss rows 0 _ cs => some (.reverseRow y ss rows cs [], powerFinishCost)
  | .multiply x y ss rows n p cs => some (.power x y ss rows n (p * x) cs, multiplyCost)
  | .reverseRow y ss rows (c :: cs) out => some (.reverseRow y ss rows cs (c :: out), reverseCost)
  | .reverseRow y ss rows [] out => some (.pack y ss rows out, rowFinishCost)
  | .pack y ss rows cs => some (.save (cs, y) ss rows, packCost)
  | .save r ss rows => some (.scan ss (r :: rows), saveCost)
  | .reverseRows (r :: rs) out => some (.reverseRows rs (r :: out), reverseCost)
  | .reverseRows [] out => some (.emit out, finishCost)
  | .emit out => some (.done out, emitCost)
  | .done _ => none

/-- Each rule agrees with the executed successor and charge. -/
theorem Step.step_eq {L : ℕ} {s t : Configuration F} {c : Cost} (h : Step L s c t) :
    step L s = some (t, c) := by cases h <;> rfl

/-- Dispatch is exhausted by the independent rules. -/
theorem step_sound {L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step L s = some (t, c)) : Step L s c t := by
  cases s with
  | start ss => cases h; constructor
  | scan ss rows => cases ss with
    | nil => cases h; constructor
    | cons p ss => cases p; cases h; constructor
  | power x y ss rows n p cs => cases n <;> cases h <;> constructor
  | multiply x y ss rows n p cs => cases h; constructor
  | reverseRow y ss rows cs out => cases cs <;> cases h <;> constructor
  | pack y ss rows cs => cases h; constructor
  | save r ss rows => cases h; constructor
  | reverseRows rows out => cases rows <;> cases h <;> constructor
  | emit out => cases h; constructor
  | done out => simp [step] at h

inductive Trace (L : ℕ) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace L 0 s 0 s
  | cons {n s u t c d} (head : Step L s c u) (tail : Trace L n u d t) :
      Trace L (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

/-- Concatenation preserves all charged work. -/
theorem Trace.append {L n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace L n s c u) (h' : Trace L m u d t) : Trace L (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cost_assoc] using
      Trace.cons head (ih h')

/-- Fuel executes and charges one actual transition at a time. -/
def runFuel (L : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step L s with
    | none => (s, 0)
    | some (t, c) => let result := runFuel L n t; (result.1, c + result.2)

/-- Every actual execution refines a trace with identical cost. -/
theorem runFuel_refines (L fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace L n s (runFuel L fuel s).2 (runFuel L fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
    cases hs : step L s with
    | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil (L := L) s⟩
    | some pair =>
      obtain ⟨n, hn, h⟩ := ih pair.1
      exact ⟨n + 1, Nat.succ_le_succ hn, by
        simpa [runFuel, hs] using Trace.cons (step_sound hs) h⟩

/-- Exact trace fuel produces the certified result and cost. -/
theorem Trace.runFuel_eq {L n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace L n s c t) : runFuel L n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

private theorem totalCost_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b := by
  simp only [totalCost, PivotSelectionMachine.totalCost, PivotEliminationMachine.cost_add,
    RowReductionMachine.cost_add]
  omega

/-- Each literal transition has bounded primitive work. -/
theorem Step.total_le {L : ℕ} {s t : Configuration F} {c : Cost} (h : Step L s c t) :
    totalCost c ≤ 12 := by
  cases h <;> decide

/-- Summing individual transition charges bounds the full trace. -/
theorem Trace.total_le {L n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace L n s c t) : totalCost c ≤ 12 * n := by
  induction h with
  | nil s => decide
  | cons head tail ih => rw [totalCost_add]; have hh := head.total_le; omega

/-- Proof-only ascending powers from an arbitrary initial scalar. -/
def powersFrom (n : ℕ) (x p : F) : List F :=
  (List.range n).map (fun i ↦ p * x ^ i)

/-- One counter iteration emits the current power and advances it by one multiplication. -/
theorem powersFrom_succ (n : ℕ) (x p : F) :
    powersFrom (n + 1) x p = p :: powersFrom n x (p * x) := by
  simp [powersFrom, List.range_succ_eq_map, List.map_map, pow_succ,
    mul_assoc, mul_comm, mul_left_comm]

/-- Power generation builds a reversed prefix before its separately charged reversal. -/
theorem power_trace (L n : ℕ) (x y p : F) (ss : List (Sample F))
    (rows : List (Row F)) (acc : List F) :
    ∃ c, Trace L (2 * n + 1) (.power x y ss rows n p acc) c
      (.reverseRow y ss rows ((powersFrom n x p).reverse ++ acc) []) := by
  induction n generalizing p acc with
  | zero => exact ⟨_, Trace.cons Step.powerFinish (Trace.nil _)⟩
  | succ n ih =>
    obtain ⟨c, h⟩ := ih (p * x) (p :: acc)
    refine ⟨coefficientCost + (multiplyCost + c), ?_⟩
    convert Trace.cons Step.coefficient (Trace.cons Step.multiply h) using 1 <;>
      simp [powersFrom_succ, List.reverse_cons, List.append_assoc]; omega

/-- Row reversal visits every coefficient, then separately allocates the augmented pair. -/
theorem reverseRow_trace (L : ℕ) (y : F) (ss : List (Sample F)) (rows : List (Row F))
    (cs out : List F) :
    ∃ c, Trace L (cs.length + 2) (.reverseRow y ss rows cs out) c
      (.save (cs.reverse ++ out, y) ss rows) := by
  induction cs generalizing out with
  | nil => exact ⟨_, Trace.cons Step.rowFinish (Trace.cons Step.pack (Trace.nil _))⟩
  | cons x cs ih =>
    obtain ⟨c, h⟩ := ih (x :: out)
    refine ⟨reverseCost + c, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverseRow h

/-- Row specification uses powers only mathematically. -/
def rowSpec (L : ℕ) (s : Sample F) : Row F := (powersFrom L s.1 1, s.2)

/-- Ordered augmented-row specification; map is not a machine primitive. -/
def rowsSpec (L : ℕ) (ss : List (Sample F)) : List (Row F) := ss.map (rowSpec L)

/-- Outer reversal materializes the final order and pays a separate output transition. -/
theorem reverseRows_trace (L : ℕ) (rs out : List (Row F)) :
    ∃ c, Trace L (rs.length + 2) (.reverseRows rs out) c (.done (rs.reverse ++ out)) := by
  induction rs generalizing out with
  | nil => exact ⟨_, Trace.cons Step.finish (Trace.cons Step.emit (Trace.nil _))⟩
  | cons r rs ih =>
    obtain ⟨c, h⟩ := ih (r :: out)
    refine ⟨reverseCost + c, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverseRows h

/-- The outer loop includes each inner power loop, both reversals and all row allocations. -/
theorem scan_trace (L : ℕ) (ss : List (Sample F)) (acc : List (Row F)) :
    ∃ c, Trace L (ss.length * (3 * L + 6) + acc.length + 3) (.scan ss acc) c
      (.done (acc.reverse ++ rowsSpec L ss)) := by
  induction ss generalizing acc with
  | nil =>
    obtain ⟨c, h⟩ := reverseRows_trace L acc []
    refine ⟨outerFinishCost + c, ?_⟩
    simpa [rowsSpec, Nat.add_assoc] using Trace.cons Step.outerFinish h
  | cons s ss ih =>
    obtain ⟨pc, hp⟩ := power_trace L L s.1 s.2 1 ss acc []
    obtain ⟨rc, hr⟩ := reverseRow_trace L s.2 ss acc (powersFrom L s.1 1).reverse []
    simp only [List.append_nil] at hp
    simp only [List.reverse_reverse, List.append_nil] at hr
    obtain ⟨oc, ho⟩ := ih (rowSpec L s :: acc)
    have ht := Trace.cons Step.take (hp.append (hr.append (Trace.cons Step.save ho)))
    refine ⟨takeCost + (pc + (rc + (saveCost + oc))), ?_⟩
    convert ht using 1 <;>
      simp [rowsSpec, rowSpec, powersFrom, List.reverse_cons, List.append_assoc, Nat.add_mul]; omega

/-- Exact number of actual transitions, including final output. -/
def constructionFuel (L m : ℕ) : ℕ := m * (3 * L + 6) + 4

/-- Actual construction agrees with the ordered specification and has bilinear primitive cost. -/
theorem construction_runFuel (L : ℕ) (ss : List (Sample F)) :
    ∃ c, runFuel L (constructionFuel L ss.length) (.start ss) = (.done (rowsSpec L ss), c) ∧
      totalCost c ≤ 72 * (ss.length + 1) * (L + 1) := by
  obtain ⟨c, h⟩ := scan_trace L ss []
  have ht := Trace.cons Step.start h
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at ht
  change Trace L (constructionFuel L ss.length) _ _ _ at ht
  refine ⟨startCost + c, ht.runFuel_eq, ht.total_le.trans ?_⟩
  unfold constructionFuel
  nlinarith

/-- The produced coefficient list has exactly the supplied physical column count. -/
theorem powersFrom_length (L : ℕ) (x p : F) : (powersFrom L x p).length = L := by
  simp [powersFrom]

/-- The specification preserves every sample's position, including repeated points. -/
theorem rowsSpec_length (L : ℕ) (ss : List (Sample F)) : (rowsSpec L ss).length = ss.length := by
  simp [rowsSpec]

/-- Every output row has the requested number of coefficients, also when that count is zero. -/
theorem rowsSpec_rectangular (L : ℕ) (ss : List (Sample F)) :
    ∀ r ∈ rowsSpec L ss, r.1.length = L := by
  intro r hr
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
  exact powersFrom_length L s.1 1

/-- The ascending-power list agrees with ordinary finite coordinates. -/
theorem powersFrom_one_eq_ofFn (L : ℕ) (x : F) :
    powersFrom L x 1 = List.ofFn (fun i : Fin L ↦ x ^ i.val) := by
  apply List.ext_getElem
  · simp [powersFrom]
  · intro i hi hj
    simp [powersFrom]

/-- Mathematical rectangular Vandermonde matrix. This definition is not executed by dispatch. -/
def powerMatrix {m : ℕ} (L : ℕ) (points : Fin m → F) : Matrix (Fin m) (Fin L) F :=
  fun i j ↦ points i ^ j.val

/-- The ordered row specification is the standard augmented finite matrix representation. -/
theorem rowsSpec_ofFn {m : ℕ} (L : ℕ) (points values : Fin m → F) :
    rowsSpec L (List.ofFn (fun i ↦ (points i, values i))) =
      List.ofFn (fun i ↦ (List.ofFn (powerMatrix L points i), values i)) := by
  change rowsSpec L (List.ofFn (fun i ↦ (points i, values i))) =
    List.ofFn (fun i ↦ (List.ofFn (fun j : Fin L ↦ points i ^ j.val), values i))
  simp [rowsSpec, rowSpec, powersFrom_one_eq_ofFn, List.map_ofFn, Function.comp_def]

/-- List equations on the constructed rows are exactly the rectangular power-matrix system. -/
theorem rowsSpec_satisfies {m : ℕ} (L : ℕ) (points values : Fin m → F) (coefficients : ℕ → F) :
    PivotSelectionMachine.Satisfies (rowsSpec L (List.ofFn (fun i ↦ (points i, values i))))
      coefficients ↔ powerMatrix L points *ᵥ (fun i ↦ coefficients i.val) = values := by
  rw [rowsSpec_ofFn]
  exact PivotSelectionMachine.satisfies_ofFn _ values coefficients

/-- Actual output is rectangular, ordered, and satisfies exactly the represented finite system.
The premise supplies materialized samples; it does not charge or implement their evaluation. -/
theorem construction_system {m : ℕ} (L : ℕ) (points values : Fin m → F)
    (ss : List (Sample F)) (hs : ss = List.ofFn (fun i ↦ (points i, values i))) :
    ∃ rows c, runFuel L (constructionFuel L ss.length) (.start ss) = (.done rows, c) ∧
      rows = rowsSpec L ss ∧ rows.length = m ∧ (∀ r ∈ rows, r.1.length = L) ∧
      totalCost c ≤ 72 * (m + 1) * (L + 1) ∧
      (∀ coefficients : ℕ → F, PivotSelectionMachine.Satisfies rows coefficients ↔
        powerMatrix L points *ᵥ (fun i ↦ coefficients i.val) = values) := by
  obtain ⟨c, hrun, hc⟩ := construction_runFuel L ss
  refine ⟨rowsSpec L ss, c, hrun, rfl, ?_, rowsSpec_rectangular L ss, ?_, ?_⟩
  · simp [rowsSpec_length, hs]
  · simpa [hs] using hc
  · intro coefficients
    rw [hs]
    exact rowsSpec_satisfies L points values coefficients

/-- Square samples give the ordinary Vandermonde system used for coefficient recovery. -/
theorem construction_vandermonde {K : Type*} [CommRing K] {L : ℕ}
    (points values : Fin L → K)
    (ss : List (Sample K)) (hs : ss = List.ofFn (fun i ↦ (points i, values i))) :
    ∃ rows c, runFuel L (constructionFuel L ss.length) (.start ss) = (.done rows, c) ∧
      rows = rowsSpec L ss ∧ totalCost c ≤ 72 * (L + 1) ^ 2 ∧
      (∀ coefficients : ℕ → K, PivotSelectionMachine.Satisfies rows coefficients ↔
        Matrix.vandermonde points *ᵥ (fun i ↦ coefficients i.val) = values) := by
  obtain ⟨rows, c, hrun, hrows, _, _, hc, hsystem⟩ := construction_system L points values ss hs
  refine ⟨rows, c, hrun, hrows, ?_, hsystem⟩
  simpa only [pow_two, Nat.mul_assoc] using hc

end Matrix.VandermondeMachine
