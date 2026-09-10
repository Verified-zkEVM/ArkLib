/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.FiniteWitness
public import ArkLib.Data.ZMod.EnumerationMachine
public import ArkLib.Data.ZMod.NonsquareSearchMachine
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Data.List.Nodup

/-!
# Explicit quadratic coordinate enumeration

Nested scalar/counter loops construct every coordinate pair. Pair allocation and list-cell
allocation are separate phases. The complete list is reversed and emitted by explicit transitions.
Range, map, product and reverse occur only in specifications and proofs, never in dispatch.

The cost categories are those of the residue enumerator. Pair allocation writes two coordinate
slots; all cell allocations, scalar constants/increments, counter tests/decrements/resets and
emission are charged. Retained registers are not copied. Input materialization, host fuel and
integer/field bit costs are outside the model. Decoding coordinates is a semantic map, not a free
bulk conversion primitive. Nonsquare search and pair enumeration retain separate actual costs;
this component does not lower extension arithmetic or claim a composed setup runtime.
-/

@[expose] public section

namespace QuadraticAlgebra.EnumerationMachine

abbrev Cost := ZMod.EnumerationMachine.Cost
abbrev Pair (q : ℕ) := ZMod q × ZMod q

/-- Sum of the existing enumerator's separate primitive categories. -/
def totalCost (c : Cost) : ℕ := c.additions + c.equalities + c.natOperations + c.constants +
  c.control + c.data + c.output

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp only [ZMod.EnumerationMachine.cost_add, Nat.add_assoc]

private theorem cost_zero_add (c : Cost) : 0 + c = c := by
  cases c
  simp only [ZMod.EnumerationMachine.cost_add, ZMod.EnumerationMachine.cost_zero, Nat.zero_add]

private theorem totalCost_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b := by
  simp only [totalCost, ZMod.EnumerationMachine.cost_add]
  omega

/-- Read modulus; initialize the outer counter, zero scalar and empty accumulator. -/
def startCost : Cost := ⟨0, 0, 0, 2, 1, 4, 0⟩
/-- Test/decrement outer counter; read modulus and reset inner counter and scalar zero. -/
def outerCost : Cost := ⟨0, 0, 2, 1, 1, 5, 0⟩
/-- Test/decrement the inner counter, with its read and write. -/
def innerCost : Cost := ⟨0, 0, 2, 0, 1, 2, 0⟩
/-- Read two scalars and allocate the two coordinate slots of a pair. -/
def pairCost : Cost := ⟨0, 0, 0, 0, 1, 4, 0⟩
/-- Read pair and accumulator pointers; allocate a cell and update its pointer. -/
def saveCost : Cost := ⟨0, 0, 0, 0, 1, 4, 0⟩
/-- Materialize one; read, increment and write a scalar coordinate. -/
def incrementCost : Cost := ⟨1, 0, 0, 1, 1, 2, 0⟩
/-- Read/test the exhausted inner counter. -/
def finishInnerCost : Cost := ⟨0, 0, 1, 0, 1, 1, 0⟩
/-- Read/test exhausted outer counter and initialize the empty output pointer. -/
def beginReverseCost : Cost := ⟨0, 0, 1, 1, 1, 2, 0⟩
/-- Read one cell/output pointer, allocate a cell and update both cursors. -/
def reverseCost : Cost := ⟨0, 0, 0, 0, 1, 5, 0⟩
/-- Read exhausted reversal cursor/output pointer and emit the list handle. -/
def emitCost : Cost := ⟨0, 0, 0, 0, 1, 2, 1⟩

/-- Explicit pair construction is separate from list-cell construction. -/
inductive Configuration (q : ℕ) where
  | start
  | outer (remaining : ℕ) (x : ZMod q) (acc : List (Pair q))
  | inner (outerRemaining : ℕ) (x : ZMod q) (remaining : ℕ) (y : ZMod q) (acc : List (Pair q))
  | pack (outerRemaining : ℕ) (x : ZMod q) (remaining : ℕ) (y : ZMod q) (acc : List (Pair q))
  | save (outerRemaining : ℕ) (x : ZMod q) (remaining : ℕ) (y : ZMod q)
      (pair : Pair q) (acc : List (Pair q))
  | incrementInner (outerRemaining : ℕ) (x : ZMod q) (remaining : ℕ) (y : ZMod q)
      (acc : List (Pair q))
  | incrementOuter (remaining : ℕ) (x : ZMod q) (acc : List (Pair q))
  | reverse (remaining output : List (Pair q))
  | done (values : List (Pair q))
  deriving DecidableEq, Repr

variable {q : ℕ}

/-- Independent operational rules with explicit allocation and counter charges. -/
inductive Step : Configuration q → Cost → Configuration q → Prop where
  | start : Step .start startCost (.outer q 0 [])
  | outer {n x acc} : Step (.outer (n + 1) x acc) outerCost (.inner n x q 0 acc)
  | inner {n x r y acc} : Step (.inner n x (r + 1) y acc) innerCost (.pack n x r y acc)
  | pack {n x r y acc} : Step (.pack n x r y acc) pairCost (.save n x r y (x, y) acc)
  | save {n x r y p acc} : Step (.save n x r y p acc) saveCost
      (.incrementInner n x r y (p :: acc))
  | incrementInner {n x r y acc} : Step (.incrementInner n x r y acc) incrementCost
      (.inner n x r (y + 1) acc)
  | finishInner {n x y acc} : Step (.inner n x 0 y acc) finishInnerCost (.incrementOuter n x acc)
  | incrementOuter {n x acc} : Step (.incrementOuter n x acc) incrementCost (.outer n (x + 1) acc)
  | beginReverse {x acc} : Step (.outer 0 x acc) beginReverseCost (.reverse acc [])
  | reverse {p ps out} : Step (.reverse (p :: ps) out) reverseCost (.reverse ps (p :: out))
  | emit {out} : Step (.reverse [] out) emitCost (.done out)

/-- Executable dispatch has no bulk pair enumeration or list conversion primitive. -/
def step : Configuration q → Option (Configuration q × Cost)
  | .start => some (.outer q 0 [], startCost)
  | .outer 0 _ acc => some (.reverse acc [], beginReverseCost)
  | .outer (n + 1) x acc => some (.inner n x q 0 acc, outerCost)
  | .inner n x 0 _ acc => some (.incrementOuter n x acc, finishInnerCost)
  | .inner n x (r + 1) y acc => some (.pack n x r y acc, innerCost)
  | .pack n x r y acc => some (.save n x r y (x, y) acc, pairCost)
  | .save n x r y p acc => some (.incrementInner n x r y (p :: acc), saveCost)
  | .incrementInner n x r y acc => some (.inner n x r (y + 1) acc, incrementCost)
  | .incrementOuter n x acc => some (.outer n (x + 1) acc, incrementCost)
  | .reverse [] out => some (.done out, emitCost)
  | .reverse (p :: ps) out => some (.reverse ps (p :: out), reverseCost)
  | .done _ => none

/-- Every independent rule matches executable dispatch and its charge. -/
theorem Step.step_eq {s t : Configuration q} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by cases h <;> rfl

/-- Every executable branch has a corresponding independent rule. -/
theorem step_sound {s t : Configuration q} {c : Cost} (h : step s = some (t, c)) :
    Step s c t := by
  cases s with
  | start => cases h; exact Step.start
  | outer n x acc =>
      cases n with
      | zero => cases h; exact Step.beginReverse
      | succ n => cases h; exact Step.outer
  | inner n x r y acc =>
      cases r with
      | zero => cases h; exact Step.finishInner
      | succ r => cases h; exact Step.inner
  | pack n x r y acc => cases h; exact Step.pack
  | save n x r y p acc => cases h; exact Step.save
  | incrementInner n x r y acc => cases h; exact Step.incrementInner
  | incrementOuter n x acc => cases h; exact Step.incrementOuter
  | reverse ps out =>
      cases ps with
      | nil => cases h; exact Step.emit
      | cons p ps => cases h; exact Step.reverse
  | done out => simp [step] at h

/-- Both directions of the operational refinement include exact primitive costs. -/
theorem step_iff {s t : Configuration q} {c : Cost} : step s = some (t, c) ↔ Step s c t :=
  ⟨step_sound, Step.step_eq⟩

/-- Finite traces accumulate actual charges. -/
inductive Trace : ℕ → Configuration q → Cost → Configuration q → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c d} (head : Step s c u) (tail : Trace n u d t) :
      Trace (n + 1) s (c + d) t

/-- Concatenating traces accounts for every transition in both components. -/
theorem Trace.append {n m : ℕ} {s t u : Configuration q} {c d : Cost}
    (h : Trace n s c t) (h' : Trace m t d u) : Trace (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa only [Nat.zero_add, cost_zero_add] using h'
  | cons head tail ih =>
      simpa only [Nat.add_right_comm, cost_assoc] using Trace.cons head (ih h')

/-- Fuel exhaustion exposes the reached phase without fabricating output. -/
def runFuel : ℕ → Configuration q → Configuration q × Cost
  | 0, s => (s, 0)
  | n + 1, s =>
      match step s with
      | none => (s, 0)
      | some (t, c) =>
          let result := runFuel n t
          (result.1, c + result.2)

/-- Executable runs refine actual traces and preserve cost. -/
theorem runFuel_refines (fuel : ℕ) (s : Configuration q) :
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

/-- Exact trace fuel recovers the state and cost. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration q} {c : Cost}
    (h : Trace n s c t) : runFuel n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-- Each transition uses at most twelve operations in the declared primitive model. -/
theorem Step.total_le {s t : Configuration q} {c : Cost} (h : Step s c t) : totalCost c ≤ 12 := by
  cases h <;> norm_num [totalCost, startCost, outerCost, innerCost, pairCost, saveCost,
    incrementCost, finishInnerCost, beginReverseCost, reverseCost, emitCost]

/-- Total actual cost is bounded by twelve times the trace length. -/
theorem Trace.total_le {n : ℕ} {s t : Configuration q} {c : Cost} (h : Trace n s c t) :
    totalCost c ≤ 12 * n := by
  induction h with
  | nil s => simp [totalCost]
  | cons head tail ih =>
      rw [totalCost_add]
      have := head.total_le
      omega

/-- Ordered row specification; no executable phase calls this bulk list expression. -/
def rowSpec (r : ℕ) (x y : ZMod q) : List (Pair q) :=
  (List.range r).map (fun i : ℕ ↦ (x, y + (i : ZMod q)))

/-- The row specification unfolds one increment at a time. -/
theorem rowSpec_succ (r : ℕ) (x y : ZMod q) :
    rowSpec (r + 1) x y = (x, y) :: rowSpec r x (y + 1) := by
  simp only [rowSpec, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.cast_zero, add_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [Nat.cast_add, add_comm, add_left_comm]

/-- The inner loop constructs one pair and one list cell per iteration. -/
theorem inner_trace (n r : ℕ) (x y : ZMod q) (acc : List (Pair q)) :
    ∃ c, Trace (4 * r + 1) (.inner n x r y acc) c
      (.incrementOuter n x ((rowSpec r x y).reverse ++ acc)) := by
  induction r generalizing y acc with
  | zero => exact ⟨_, Trace.cons Step.finishInner (Trace.nil _)⟩
  | succ r ih =>
      obtain ⟨c, h⟩ := ih (y + 1) ((x, y) :: acc)
      have ht := Trace.cons Step.inner (Trace.cons Step.pack
        (Trace.cons Step.save (Trace.cons Step.incrementInner h)))
      refine ⟨innerCost + (pairCost + (saveCost + (incrementCost + c))), ?_⟩
      convert ht using 1 <;> simp [rowSpec_succ, List.reverse_cons, List.append_assoc]; omega

/-- Grid specification with arbitrary starting first coordinate. -/
def gridSpec (n : ℕ) (x : ZMod q) : List (Pair q) :=
  (List.range n).flatMap (fun i : ℕ ↦ rowSpec q (x + (i : ZMod q)) 0)

/-- One outer increment appends the complete inner row. -/
theorem gridSpec_succ (n : ℕ) (x : ZMod q) :
    gridSpec (n + 1) x = rowSpec q x 0 ++ gridSpec n (x + 1) := by
  simp only [gridSpec, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
    Nat.cast_zero, add_zero]
  congr 1
  apply List.flatMap_congr
  intro i hi
  congr 1
  simp [Nat.cast_add, add_comm, add_left_comm]

/-- Reversal explicitly allocates each ordered output cell. -/
theorem reverse_trace (ps out : List (Pair q)) :
    ∃ c, Trace (ps.length + 1) (.reverse ps out) c (.done (ps.reverse ++ out)) := by
  induction ps generalizing out with
  | nil => exact ⟨_, Trace.cons Step.emit (Trace.nil _)⟩
  | cons p ps ih =>
      obtain ⟨c, h⟩ := ih (p :: out)
      refine ⟨reverseCost + c, ?_⟩
      simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverse h

/-- The outer loop includes the cost of all inner loops and the final reversal. -/
theorem outer_trace (n : ℕ) (x : ZMod q) (acc : List (Pair q)) :
    ∃ c, Trace (n * (5 * q + 3) + acc.length + 2) (.outer n x acc) c
      (.done (acc.reverse ++ gridSpec n x)) := by
  induction n generalizing x acc with
  | zero =>
      obtain ⟨c, h⟩ := reverse_trace acc []
      refine ⟨beginReverseCost + c, ?_⟩
      simpa [gridSpec, Nat.add_assoc] using Trace.cons (Step.beginReverse (x := x)) h
  | succ n ih =>
      obtain ⟨ic, hi⟩ := inner_trace n q x 0 acc
      obtain ⟨oc, ho⟩ := ih (x + 1) ((rowSpec q x 0).reverse ++ acc)
      have ht := Trace.cons Step.outer (hi.append (Trace.cons Step.incrementOuter ho))
      refine ⟨outerCost + (ic + (incrementCost + oc)), ?_⟩
      convert ht using 1 <;>
        simp [gridSpec_succ, rowSpec, List.reverse_append, List.append_assoc, Nat.add_mul]; omega

/-- Exact transition fuel including pair construction, reversal, and final emission. -/
def enumerationFuel (q : ℕ) : ℕ := 5 * q ^ 2 + 3 * q + 3

/-- The actual machine emits precisely the grid specification at the declared cost bound. -/
theorem enumeration_runFuel (q : ℕ) :
    ∃ c, runFuel (enumerationFuel q) (.start : Configuration q) = (.done (gridSpec q 0), c) ∧
      totalCost c ≤ 12 * enumerationFuel q := by
  obtain ⟨c, h⟩ := outer_trace q (0 : ZMod q) []
  have ht := Trace.cons Step.start h
  have heq : q * (5 * q + 3) + ([] : List (Pair q)).length + 2 + 1 = enumerationFuel q := by
    simp only [List.length_nil, enumerationFuel]
    ring
  rw [heq] at ht
  exact ⟨startCost + c, ht.runFuel_eq, ht.total_le⟩

/-- The loop specification is the Cartesian product of the residue specifications. -/
theorem gridSpec_product (q : ℕ) :
    gridSpec q (0 : ZMod q) =
      ((List.range q).map (fun i : ℕ ↦ (i : ZMod q))) ×ˢ
        ((List.range q).map (fun i : ℕ ↦ (i : ZMod q))) := by
  change gridSpec q (0 : ZMod q) = List.product
    ((List.range q).map (fun i : ℕ ↦ (i : ZMod q)))
    ((List.range q).map (fun i : ℕ ↦ (i : ZMod q)))
  simp [gridSpec, rowSpec, List.product, List.flatMap_map, List.map_map, Function.comp_def]

/-- Actual output contains each coordinate pair once, with quadratic primitive cost. -/
theorem enumeration_correct (q : ℕ) (hq : 0 < q) :
    ∃ (values : List (Pair q)) (c : Cost),
      runFuel (enumerationFuel q) (.start : Configuration q) = (.done values, c) ∧
      values.length = q ^ 2 ∧ values.Nodup ∧ (∀ p : Pair q, p ∈ values) ∧
      totalCost c ≤ 60 * q ^ 2 + 36 * q + 36 := by
  obtain ⟨c, h, hc⟩ := enumeration_runFuel q
  refine ⟨gridSpec q 0, c, h, ?_, ?_, ?_, ?_⟩
  · simp [gridSpec_product, List.length_product, pow_two]
  · rw [gridSpec_product]
    exact (ZMod.EnumerationMachine.enumeration_spec_nodup q).product
      (ZMod.EnumerationMachine.enumeration_spec_nodup q)
  · intro p
    rw [gridSpec_product, List.mem_product]
    exact ⟨ZMod.EnumerationMachine.enumeration_spec_complete q hq p.1,
      ZMod.EnumerationMachine.enumeration_spec_complete q hq p.2⟩
  · calc
      totalCost c ≤ 12 * enumerationFuel q := hc
      _ = _ := by unfold enumerationFuel; ring

/-- Semantic decoding of one materialized pair; this does not run a bulk conversion. -/
def decode (a : ZMod q) (p : Pair q) : QuadraticAlgebra (ZMod q) a 0 := ⟨p.1, p.2⟩

/-- Distinct pairs represent distinct quadratic elements. -/
theorem decode_injective (a : ZMod q) : Function.Injective (decode a) := by
  intro p r h
  exact Prod.ext (congrArg QuadraticAlgebra.re h) (congrArg QuadraticAlgebra.im h)

/-- Every quadratic element has an explicit coordinate representation. -/
theorem decode_surjective (a : ZMod q) : Function.Surjective (decode a) := by
  intro z
  exact ⟨(z.re, z.im), by cases z; rfl⟩

/-- Nonsquare search and enumeration supply an actual parameter and all its coordinates.
The two charged executions remain separate; extension arithmetic is outside this contract. -/
theorem setup_correct (q : ℕ) (hq : q.Prime) (hodd : q ≠ 2) :
    ∃ (a : ZMod q) (values : List (Pair q)) (c : Cost),
      (ZMod.NonsquareSearchMachine.search q).1 = some a ∧ ¬IsSquare a ∧
      runFuel (enumerationFuel q) (.start : Configuration q) = (.done values, c) ∧
      values.length = q ^ 2 ∧ values.Nodup ∧
      (∀ z : QuadraticAlgebra (ZMod q) a 0, ∃ p ∈ values, decode a p = z) ∧
      (ZMod.NonsquareSearchMachine.search q).2.total ≤ 48 * q ^ 2 + 48 * q + 24 ∧
      totalCost c ≤ 60 * q ^ 2 + 36 * q + 36 := by
  obtain ⟨a, ha, hns, hs⟩ := ZMod.NonsquareSearchMachine.search_correct q hq hodd
  obtain ⟨values, c, hc, hl, hn, hall, hcost⟩ := enumeration_correct q hq.pos
  refine ⟨a, values, c, ha, hns, hc, hl, hn, ?_, hs, hcost⟩
  intro z
  obtain ⟨p, hp⟩ := decode_surjective a z
  exact ⟨p, hall p, hp⟩

/-- The represented extension has quadratic cardinality but retains prime characteristic. -/
theorem representation_size_characteristic (q : ℕ) (hq : q.Prime) (a : ZMod q) :
    Nat.card (QuadraticAlgebra (ZMod q) a 0) = q ^ 2 ∧
      ringChar (QuadraticAlgebra (ZMod q) a 0) = q := by
  let : Fact q.Prime := ⟨hq⟩
  constructor
  · rw [QuadraticAlgebra.finiteWitness_natCard, Nat.card_eq_fintype_card, ZMod.card]
  · rw [QuadraticAlgebra.finiteWitness_ringChar, ZMod.ringChar_zmod_n]

/-- The empty-modulus run still charges initialization, reversal setup and emission. -/
example : runFuel 3 (.start : Configuration 0) =
    (.done [], ⟨0, 0, 1, 3, 3, 8, 1⟩) := by decide

/-- Two complete rows preserve order, reset the inner scalar and charge all allocations. -/
example : runFuel 29 (.start : Configuration 2) =
    (.done [(0, 0), (0, 1), (1, 0), (1, 1)], ⟨6, 0, 15, 11, 29, 92, 1⟩) := by decide

/-- Allocating a coordinate pair does not also allocate its list cell. -/
example : runFuel 1 (.pack 0 1 0 2 [] : Configuration 3) =
    (.save 0 1 0 2 (1, 2) [], pairCost) := by decide

/-- Output remains pending until the separately charged emission transition. -/
example : runFuel 28 (.start : Configuration 2) =
    (.reverse [] [(0, 0), (0, 1), (1, 0), (1, 1)],
      ⟨6, 0, 15, 11, 28, 90, 0⟩) := by decide

end QuadraticAlgebra.EnumerationMachine
