/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Forall2
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Materialized finite Cartesian products

The machine reverses the axis pointers, then constructs suffix products from right to left.
Each chosen element allocates a tuple prefix sharing its existing suffix. Tuple-prefix and outer
list-cell allocation are separate transitions. Each accumulated product is explicitly reversed.
The resulting order is lexicographic in the original axis and element order; duplicates remain.

Costs count control, register/cell accesses and allocation, natural operations, and final output.
Cell reads return head and tail together; retained pointers and tuple tails are shared. Literal
empty pointers, input materialization, reclamation and host interpreter bookkeeping are outside
the model. No scalar operation or arbitrary callback is used. Bulk list operations appear only
in specifications and proofs. Consumers are anisotropic sampling grids and exponent-coordinate
boxes; neither evaluation of grid points nor filtering of exponent boxes is performed here.
-/

@[expose] public section

namespace List.CartesianProductMachine

@[ext] structure Cost where
  control : ℕ
  data : ℕ
  natural : ℕ
  output : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0, 0, 0⟩⟩
instance : Add Cost := ⟨fun c d ↦
  ⟨c.control + d.control, c.data + d.data, c.natural + d.natural, c.output + d.output⟩⟩

@[simp] theorem cost_add (c d : Cost) : c + d =
    ⟨c.control + d.control, c.data + d.data, c.natural + d.natural, c.output + d.output⟩ := rfl
@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0, 0, 0⟩ := rfl

/-- Total administrative work; this machine has no scalar arithmetic. -/
def Cost.total (c : Cost) : ℕ := c.control + c.data + c.natural + c.output

/-- Read input pointer and initialize reversal cursors. -/
def startCost : Cost := ⟨1, 3, 0, 0⟩
/-- Read cell/output pointer, allocate a cell, and write both reversal cursors. -/
def reverseCost : Cost := ⟨1, 5, 0, 0⟩
/-- Read exhausted axis cursor and allocate/write the singleton empty-tuple list. -/
def seedCost : Cost := ⟨1, 3, 0, 0⟩
/-- Read axis cell/products pointer and initialize axis, product and output cursors. -/
def axisCost : Cost := ⟨1, 5, 0, 0⟩
/-- Read an element cell/product pointer and retain the element and two cursors. -/
def elementCost : Cost := ⟨1, 5, 0, 0⟩
/-- Read tuple cell and element, allocate tuple prefix and write tuple/prefix pointers. -/
def prefixCost : Cost := ⟨1, 5, 0, 0⟩
/-- Read new tuple/output pointer, allocate an outer cell and write its root. -/
def saveCost : Cost := ⟨1, 4, 0, 0⟩
/-- Read exhausted tuple cursor before advancing to the next element. -/
def tupleEndCost : Cost := ⟨1, 1, 0, 0⟩
/-- Read exhausted element/reversal cursor and initialize or retain the output pointer. -/
def finishCost : Cost := ⟨1, 2, 0, 0⟩
/-- Read exhausted axis cursor; retain the completed product for emission. -/
def axesEndCost : Cost := ⟨1, 1, 0, 0⟩
/-- Read and emit the final product-list handle. -/
def emitCost : Cost := ⟨1, 1, 0, 1⟩

inductive Configuration (α : Type*) where
  | start (axes : List (List α))
  | reverseAxes (remaining output : List (List α))
  | axes (remaining products : List (List α))
  | elements (axes : List (List α)) (remaining : List α) (products output : List (List α))
  | tuples (axes : List (List α)) (x : α) (elements : List α)
      (products remaining output : List (List α))
  | save (axes : List (List α)) (x : α) (elements : List α)
      (products remaining output : List (List α)) (tuple : List α)
  | reverseProduct (axes remaining output : List (List α))
  | emit (products : List (List α))
  | done (products : List (List α))
  deriving DecidableEq, Repr

variable {α : Type*}

/-- Closed transitions expose every reversal and each of the two allocation phases. -/
inductive Step : Configuration α → Cost → Configuration α → Prop where
  | start {a} : Step (.start a) startCost (.reverseAxes a [])
  | reverseAxes {a as out} : Step (.reverseAxes (a :: as) out) reverseCost
      (.reverseAxes as (a :: out))
  | seed {out} : Step (.reverseAxes [] out) seedCost (.axes out [[]])
  | axis {a as ps} : Step (.axes (a :: as) ps) axisCost (.elements as a ps [])
  | element {as x xs ps out} : Step (.elements as (x :: xs) ps out) elementCost
      (.tuples as x xs ps ps out)
  | prefix {as x xs ps t ts out} : Step (.tuples as x xs ps (t :: ts) out) prefixCost
      (.save as x xs ps ts out (x :: t))
  | save {as x xs ps ts out t} : Step (.save as x xs ps ts out t) saveCost
      (.tuples as x xs ps ts (t :: out))
  | tupleEnd {as x xs ps out} : Step (.tuples as x xs ps [] out) tupleEndCost
      (.elements as xs ps out)
  | elementsEnd {as ps out} : Step (.elements as [] ps out) finishCost
      (.reverseProduct as out [])
  | reverseProduct {as t ts out} : Step (.reverseProduct as (t :: ts) out) reverseCost
      (.reverseProduct as ts (t :: out))
  | productEnd {as out} : Step (.reverseProduct as [] out) finishCost (.axes as out)
  | axesEnd {ps} : Step (.axes [] ps) axesEndCost (.emit ps)
  | emit {ps} : Step (.emit ps) emitCost (.done ps)

/-- No map, append, reverse or Cartesian-product primitive occurs in dispatch. -/
def step : Configuration α → Option (Configuration α × Cost)
  | .start a => some (.reverseAxes a [], startCost)
  | .reverseAxes (a :: as) out => some (.reverseAxes as (a :: out), reverseCost)
  | .reverseAxes [] out => some (.axes out [[]], seedCost)
  | .axes (a :: as) ps => some (.elements as a ps [], axisCost)
  | .axes [] ps => some (.emit ps, axesEndCost)
  | .elements as (x :: xs) ps out => some (.tuples as x xs ps ps out, elementCost)
  | .elements as [] _ out => some (.reverseProduct as out [], finishCost)
  | .tuples as x xs ps (t :: ts) out => some (.save as x xs ps ts out (x :: t), prefixCost)
  | .tuples as _ xs ps [] out => some (.elements as xs ps out, tupleEndCost)
  | .save as x xs ps ts out t => some (.tuples as x xs ps ts (t :: out), saveCost)
  | .reverseProduct as (t :: ts) out => some (.reverseProduct as ts (t :: out), reverseCost)
  | .reverseProduct as [] out => some (.axes as out, finishCost)
  | .emit ps => some (.done ps, emitCost)
  | .done _ => none

/-- Independent rules agree with actual dispatch and its costs. -/
theorem Step.step_eq {s t : Configuration α} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by cases h <;> rfl

/-- Dispatch contains exactly the independent rules. -/
theorem step_sound {s t : Configuration α} {c : Cost} (h : step s = some (t, c)) :
    Step s c t := by
  cases s with
  | start a => cases h; constructor
  | reverseAxes as out => cases as <;> cases h <;> constructor
  | axes as ps => cases as <;> cases h <;> constructor
  | elements as xs ps out => cases xs <;> cases h <;> constructor
  | tuples as x xs ps ts out => cases ts <;> cases h <;> constructor
  | save as x xs ps ts out t => cases h; constructor
  | reverseProduct as ts out => cases ts <;> cases h <;> constructor
  | emit ps => cases h; constructor
  | done ps => simp [step] at h

inductive Trace : ℕ → Configuration α → Cost → Configuration α → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c d} (head : Step s c u) (tail : Trace n u d t) : Trace (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

/-- Concatenate actual traces and their costs. -/
theorem Trace.append {n m : ℕ} {s u t : Configuration α} {c d : Cost}
    (h : Trace n s c u) (h' : Trace m u d t) : Trace (n + m) s (c + d) t := by
  induction h with
  | nil s => cases c; simpa using h'
  | cons head tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cost_assoc] using
      Trace.cons head (ih h')

/-- Execute individual transitions, retaining partial states on fuel exhaustion. -/
def runFuel : ℕ → Configuration α → Configuration α × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step s with
    | none => (s, 0)
    | some (t, c) => let result := runFuel n t; (result.1, c + result.2)

/-- Every actual run has an identical-cost trace. -/
theorem runFuel_refines (fuel : ℕ) (s : Configuration α) :
    ∃ n ≤ fuel, Trace n s (runFuel fuel s).2 (runFuel fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
    cases hs : step s with
    | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
    | some pair =>
      obtain ⟨n, hn, h⟩ := ih pair.1
      exact ⟨n + 1, Nat.succ_le_succ hn, by
        simpa [runFuel, hs] using Trace.cons (step_sound hs) h⟩

/-- Exact trace fuel realizes its result and accumulated charges. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration α} {c : Cost}
    (h : Trace n s c t) : runFuel n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

private theorem total_add (a b : Cost) : (a + b).total = a.total + b.total := by
  simp only [Cost.total, cost_add]
  omega

/-- Every transition performs bounded scalar-free administrative work. -/
theorem Step.total_le {s t : Configuration α} {c : Cost} (h : Step s c t) : c.total ≤ 8 := by
  cases h <;> decide

/-- Summing primitive costs along a trace. -/
theorem Trace.total_le {n : ℕ} {s t : Configuration α} {c : Cost}
    (h : Trace n s c t) : c.total ≤ 8 * n := by
  induction h with
  | nil s => decide
  | cons head tail ih => rw [total_add]; have hh := head.total_le; omega

/-- Proof-only extension by one axis, with the axis element as the slower-varying coordinate. -/
def extendSpec (axis : List α) (products : List (List α)) : List (List α) :=
  axis.flatMap (fun x ↦ products.map (x :: ·))

/-- Mathematical ordered Cartesian product. -/
def productSpec : List (List α) → List (List α)
  | [] => [[]]
  | a :: as => extendSpec a (productSpec as)

/-- Mathematical effect of processing already reversed axes from a supplied suffix product. -/
def processSpec : List (List α) → List (List α) → List (List α)
  | [], ps => ps
  | a :: as, ps => processSpec as (extendSpec a ps)

/-- Exact transition count for processing the remaining axes. -/
def processFuel : List (List α) → List (List α) → ℕ
  | [], _ => 2
  | a :: as, ps => a.length * (3 * ps.length + 2) + 3 +
      processFuel as (extendSpec a ps)

/-- Exact fuel, expressed mathematically; computing this expression is not a machine primitive. -/
def constructionFuel (axes : List (List α)) : ℕ :=
  axes.length + 2 + processFuel axes.reverse [[]]

/-- Tuple-prefix construction and outer-cell construction each take one explicit transition. -/
theorem tuples_trace (as : List (List α)) (x : α) (xs : List α)
    (ps ts out : List (List α)) :
    ∃ c, Trace (2 * ts.length + 1) (.tuples as x xs ps ts out) c
      (.elements as xs ps ((ts.map (x :: ·)).reverse ++ out)) := by
  induction ts generalizing out with
  | nil => exact ⟨_, Trace.cons Step.tupleEnd (Trace.nil _)⟩
  | cons t ts ih =>
    obtain ⟨c, h⟩ := ih ((x :: t) :: out)
    refine ⟨prefixCost + (saveCost + c), ?_⟩
    convert Trace.cons Step.prefix (Trace.cons Step.save h) using 1 <;>
      simp [List.reverse_cons, List.append_assoc]; omega

/-- The element loop emits every suffix once per axis element, preserving multiplicities. -/
theorem elements_trace (as : List (List α)) (xs : List α) (ps out : List (List α)) :
    ∃ c, Trace (xs.length * (2 * ps.length + 2) + 1) (.elements as xs ps out) c
      (.reverseProduct as ((extendSpec xs ps).reverse ++ out) []) := by
  induction xs generalizing out with
  | nil =>
    refine ⟨finishCost + 0, ?_⟩
    simpa [extendSpec] using Trace.cons (Step.elementsEnd (as := as) (ps := ps) (out := out))
      (Trace.nil _)
  | cons x xs ih =>
    obtain ⟨tc, ht⟩ := tuples_trace as x xs ps ps out
    obtain ⟨ec, he⟩ := ih ((ps.map (x :: ·)).reverse ++ out)
    refine ⟨elementCost + (tc + ec), ?_⟩
    convert Trace.cons Step.element (ht.append he) using 1 <;>
      simp [extendSpec, List.reverse_append, List.append_assoc, Nat.add_mul]; omega

/-- Restore the completed product's order by allocating its outer cells explicitly. -/
theorem reverseProduct_trace (as ts out : List (List α)) :
    ∃ c, Trace (ts.length + 1) (.reverseProduct as ts out) c (.axes as (ts.reverse ++ out)) := by
  induction ts generalizing out with
  | nil => exact ⟨_, Trace.cons Step.productEnd (Trace.nil _)⟩
  | cons t ts ih =>
    obtain ⟨c, h⟩ := ih (t :: out)
    refine ⟨reverseCost + c, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverseProduct h

/-- Extension cardinality counts duplicates as distinct list occurrences. -/
theorem extendSpec_length (axis : List α) (ps : List (List α)) :
    (extendSpec axis ps).length = axis.length * ps.length := by
  induction axis with
  | nil => simp [extendSpec]
  | cons x xs ih => simp [extendSpec, Nat.add_mul] at ih ⊢; omega

/-- Processing all reversed axes realizes the mathematical product transformation. -/
theorem process_trace (as ps : List (List α)) :
    ∃ c, Trace (processFuel as ps) (.axes as ps) c (.done (processSpec as ps)) := by
  induction as generalizing ps with
  | nil => exact ⟨_, Trace.cons Step.axesEnd (Trace.cons Step.emit (Trace.nil _))⟩
  | cons a as ih =>
    obtain ⟨ec, he⟩ := elements_trace as a ps []
    obtain ⟨rc, hr⟩ := reverseProduct_trace as (extendSpec a ps).reverse []
    simp only [List.append_nil] at he
    simp only [List.reverse_reverse, List.append_nil] at hr
    obtain ⟨pc, hp⟩ := ih (extendSpec a ps)
    refine ⟨axisCost + (ec + (rc + pc)), ?_⟩
    convert Trace.cons Step.axis (he.append (hr.append hp)) using 1 <;>
      simp [processFuel, processSpec, extendSpec_length, Nat.mul_add]; ring

/-- Axis reversal visits the complete input and allocates the seed product. -/
theorem reverseAxes_trace (as out : List (List α)) :
    ∃ c, Trace (as.length + 1) (.reverseAxes as out) c (.axes (as.reverse ++ out) [[]]) := by
  induction as generalizing out with
  | nil => exact ⟨_, Trace.cons Step.seed (Trace.nil _)⟩
  | cons a as ih =>
    obtain ⟨c, h⟩ := ih (a :: out)
    refine ⟨reverseCost + c, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverseAxes h

/-- Processing concatenated axis blocks composes their transformations in order. -/
theorem processSpec_append (as bs ps : List (List α)) :
    processSpec (as ++ bs) ps = processSpec bs (processSpec as ps) := by
  induction as generalizing ps with
  | nil => rfl
  | cons a as ih => exact ih _

/-- Reversing the axis pointers yields the original-coordinate lexicographic product. -/
theorem processSpec_reverse (as : List (List α)) :
    processSpec as.reverse [[]] = productSpec as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [List.reverse_cons, processSpec_append, processSpec, productSpec, ih]

/-- Actual completed construction equals the ordered Cartesian-product specification. -/
theorem construction_runFuel (as : List (List α)) :
    ∃ c, runFuel (constructionFuel as) (.start as) = (.done (productSpec as), c) ∧
      c.total ≤ 8 * constructionFuel as := by
  obtain ⟨rc, hr⟩ := reverseAxes_trace as []
  simp only [List.append_nil] at hr
  obtain ⟨pc, hp⟩ := process_trace as.reverse [[]]
  rw [processSpec_reverse] at hp
  have ht := Trace.cons Step.start (hr.append hp)
  have hn : (as.length + 1 + processFuel as.reverse [[]]) + 1 = constructionFuel as := by
    unfold constructionFuel
    omega
  rw [hn] at ht
  exact ⟨startCost + (rc + pc), ht.runFuel_eq, ht.total_le⟩

/-- Size parameter that also accounts for empty axes and partial suffix products. -/
def weight (axes : List (List α)) : ℕ := (axes.map (fun a ↦ a.length + 1)).prod

/-- The augmented size parameter is always positive, even with empty axes. -/
theorem weight_pos (axes : List (List α)) : 0 < weight axes := by
  induction axes with
  | nil => simp [weight]
  | cons a as ih => simpa [weight] using Nat.mul_pos (Nat.succ_pos a.length) ih

/-- Reversing axis pointers leaves the size parameter unchanged. -/
theorem weight_reverse (axes : List (List α)) : weight axes.reverse = weight axes := by
  simp [weight, List.map_reverse]

/-- Processing fuel is bounded without materializing the intermediate product specifications. -/
theorem processFuel_le (as ps : List (List α)) :
    processFuel as ps ≤ 3 * (as.length + 1) * weight as * (ps.length + 1) := by
  induction as generalizing ps with
  | nil => simp [processFuel, weight]; omega
  | cons a as ih =>
    have haxis : a.length * (3 * ps.length + 2) + 3 ≤
        3 * (a.length + 1) * (ps.length + 1) := by nlinarith
    have hsize : a.length * ps.length + 1 ≤ (a.length + 1) * (ps.length + 1) := by nlinarith
    have hfirst : 3 * (a.length + 1) * (ps.length + 1) ≤
        (3 * (a.length + 1) * (ps.length + 1)) * weight as := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left
        (3 * (a.length + 1) * (ps.length + 1)) (weight_pos as)
    have htail := (ih (extendSpec a ps)).trans
      (Nat.mul_le_mul_left (3 * (as.length + 1) * weight as)
        (by simpa only [extendSpec_length] using hsize))
    calc
      processFuel (a :: as) ps ≤
          (3 * (a.length + 1) * (ps.length + 1)) * weight as +
          3 * (as.length + 1) * weight as * ((a.length + 1) * (ps.length + 1)) :=
        Nat.add_le_add (haxis.trans hfirst) htail
      _ = _ := by simp only [List.length_cons, weight, List.map_cons, List.prod_cons]; ring

/-- An explicit polynomial host-fuel bound in dimension and augmented axis-size product. -/
theorem constructionFuel_le (axes : List (List α)) :
    constructionFuel axes ≤ 8 * (axes.length + 1) * weight axes := by
  have h := processFuel_le axes.reverse ([[]] : List (List α))
  simp only [List.length_reverse, weight_reverse, List.length_cons, List.length_nil] at h
  have hw := weight_pos axes
  unfold constructionFuel
  nlinarith

/-- Exact coordinate membership; no distinctness assumption discards duplicate occurrences. -/
theorem mem_productSpec (axes : List (List α)) (tuple : List α) :
    tuple ∈ productSpec axes ↔ List.Forall₂ (· ∈ ·) tuple axes := by
  induction axes generalizing tuple with
  | nil => simp [productSpec]
  | cons a as ih =>
    constructor
    · intro h
      obtain ⟨x, hx, hmap⟩ := List.mem_flatMap.mp h
      obtain ⟨t, hmem, rfl⟩ := List.mem_map.mp hmap
      exact List.Forall₂.cons hx ((ih t).mp hmem)
    · intro h
      cases h with
      | cons hx ht =>
        exact List.mem_flatMap.mpr ⟨_, hx, List.mem_map.mpr ⟨_, (ih _).mpr ht, rfl⟩⟩

/-- Every emitted tuple has one coordinate for each input axis. -/
theorem productSpec_width {axes : List (List α)} {tuple : List α}
    (h : tuple ∈ productSpec axes) : tuple.length = axes.length :=
  ((mem_productSpec axes tuple).mp h).length_eq

/-- The exact number of tuples, counting duplicates, is the ordinary axis-size product. -/
theorem productSpec_length (axes : List (List α)) :
    (productSpec axes).length = (axes.map List.length).prod := by
  induction axes with
  | nil => rfl
  | cons a as ih => simp [productSpec, extendSpec_length, ih]

/-- Any empty axis makes the complete product empty. -/
theorem productSpec_eq_nil_of_empty {axes : List (List α)} (h : [] ∈ axes) :
    productSpec axes = [] := by
  induction axes with
  | nil => simp at h
  | cons a as ih =>
    rcases List.mem_cons.mp h with ha | ht
    · subst a
      simp [productSpec, extendSpec]
    · simp [productSpec, extendSpec, ih ht]


/-- Distinct elements on each axis produce distinct coordinate tuples. -/
theorem productSpec_nodup (axes : List (List α)) (h : ∀ a ∈ axes, a.Nodup) :
    (productSpec axes).Nodup := by
  induction axes with
  | nil => simp [productSpec]
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb ↦ h b (by simp [hb]))
    apply List.nodup_flatMap.mpr
    constructor
    · intro x hx
      exact ht.map (fun _ _ heq ↦ (List.cons.inj heq).2)
    · exact ha.imp fun {x y} hxy t hx hy ↦ by
        obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨ys, _, heq⟩ := List.mem_map.mp hy
        exact hxy (List.cons.inj heq).1.symm

/-- A completed trace remains completed with the same cost under additional host fuel. -/
theorem Trace.runFuel_done {n : ℕ} {s : Configuration α} {c : Cost} {out : List (List α)}
    (h : Trace n s c (.done out)) (extra : ℕ) : runFuel (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
    rw [Nat.add_right_comm, runFuel, head.step_eq]
    dsimp only
    rw [ih ht]

/-- Actual execution under the explicit polynomial fuel bound has exact ordered output.
Its cost includes tuple-prefix/outer-cell allocations, reversals and final emission. -/
theorem construction_correct (axes : List (List α)) :
    ∃ c, runFuel (8 * (axes.length + 1) * weight axes) (.start axes) =
        (.done (productSpec axes), c) ∧
      c.total ≤ 128 * (axes.length + 1) * weight axes := by
  obtain ⟨c, hrun, hc⟩ := construction_runFuel axes
  obtain ⟨n, hn, ht⟩ := runFuel_refines (constructionFuel axes) (.start axes)
  rw [hrun] at ht
  have hb := constructionFuel_le axes
  have hext := ht.runFuel_done (8 * (axes.length + 1) * weight axes - n)
  have heq : n + (8 * (axes.length + 1) * weight axes - n) =
      8 * (axes.length + 1) * weight axes := by omega
  rw [heq] at hext
  refine ⟨c, hext, ?_⟩
  nlinarith

end List.CartesianProductMachine
