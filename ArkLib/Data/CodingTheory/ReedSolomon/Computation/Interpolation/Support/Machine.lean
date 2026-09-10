/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.List.CartesianProductMachine
public import Mathlib.Data.List.Range
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn
/-!
# Materialized interpolation column exponents

The integer inputs generate columns `[x,b₀,...,b_d]` for the full support used by descending
ambient-dimension search. Two counter loops materialize the coordinate universes, another loop
allocates the axes, and the Cartesian machine allocates every candidate tuple. A coordinate scan
computes total jet degree and the exact differential weight before retaining a tuple. No bulk
range, map, filter, sum, lookup or support oracle is executed by dispatch.

Work counts control, natural arithmetic/comparisons, register/cell reads and writes, allocation,
and emission. A cell read returns head and tail together; axis and tuple tails may share pointers.
The outer dispatch charges 32 primitive units per transition, an upper charge covering each
listed operation, and adds four wrapper units to each Cartesian transition charge.
Host fuel, garbage
collection and bit costs of natural arithmetic are outside this unit-cost model. The initial
charge includes computing `m*A`, `2*m` and `d+1` from the public integer inputs.

The direct consumer is interpolation-matrix column construction: coordinate zero denotes X and
coordinate j+1 denotes Y_j. This component emits exponents, not matrix entries or a kernel vector.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.InterpolationSupportMachine

namespace Product
export List.CartesianProductMachine (Configuration step Trace constructionFuel productSpec weight)
end Product

/-- Generic box parameters; the public wrapper supplies h=d+1, B=2m and T=mA. -/
structure Parameters where
  D : ℕ
  h : ℕ
  B : ℕ
  T : ℕ
  deriving DecidableEq, Repr

/-- All cursors are materialized list pointers or natural registers. -/
inductive Configuration where
  | start
  | rangeX (remaining : ℕ) (out : List ℕ)
  | rangeJet (xs : List ℕ) (remaining : ℕ) (out : List ℕ)
  | axes (xs jets : List ℕ) (remaining : ℕ) (out : List (List ℕ))
  | product (inner : Product.Configuration ℕ)
  | scan (remaining out : List (List ℕ))
  | test (row : List ℕ) (rows out : List (List ℕ))
      (remaining : List ℕ) (index total weighted : ℕ)
  | reverse (remaining out : List (List ℕ))
  | done (out : List (List ℕ))
  deriving DecidableEq, Repr

/-- One closed instruction; the test loop charges subtraction, multiplication, two sums and
index increment, together with cursor operations. The terminal test charges both comparisons. -/
def step (p : Parameters) : Configuration → Option (Configuration × ℕ)
  | .start => some (.rangeX p.T [], 32)
  | .rangeX (n + 1) out => some (.rangeX n (n :: out), 32)
  | .rangeX 0 out => some (.rangeJet out p.B [], 32)
  | .rangeJet xs (n + 1) out => some (.rangeJet xs n (n :: out), 32)
  | .rangeJet xs 0 out => some (.axes xs out p.h [], 32)
  | .axes xs js (n + 1) out => some (.axes xs js n (js :: out), 32)
  | .axes xs _ 0 out => some (.product (.start (xs :: out)), 32)
  | .product (.done rows) => some (.scan rows [], 32)
  | .product inner => match Product.step inner with
    | none => none
    | some (next, cost) => some (.product next, cost.total + 4)
  | .scan [] out => some (.reverse out [], 32)
  | .scan ([] :: rows) out => some (.scan rows out, 32)
  | .scan ((x :: bs) :: rows) out => some (.test (x :: bs) rows out bs 0 0 x, 32)
  | .test row rows out (b :: bs) j total weighted =>
      some (.test row rows out bs (j + 1) (total + b) (weighted + (p.D - j) * b), 32)
  | .test row rows out [] _ total weighted =>
      some (.scan rows (if total < p.B ∧ weighted < p.T then row :: out else out), 32)
  | .reverse (row :: rows) out => some (.reverse rows (row :: out), 32)
  | .reverse [] out => some (.done out, 32)
  | .done _ => none

/-- The interpreter accumulates exactly the charges returned by dispatch. -/
def runFuel (p : Parameters) : ℕ → Configuration → Configuration × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step p s with
    | none => (s, 0)
    | some (next, c) => let result := runFuel p n next; (result.1, c + result.2)

/-- A finite instruction trace, retaining the observed dispatch costs. -/
inductive Trace (p : Parameters) : ℕ → Configuration → ℕ → Configuration → Prop where
  | nil (s) : Trace p 0 s 0 s
  | cons {n s v t c k} (head : step p s = some (v, c)) (tail : Trace p n v k t) :
      Trace p (n + 1) s (c + k) t

/-- Sequential composition does not discard work. -/
theorem Trace.append {p : Parameters} {n m c k : ℕ} {s v t : Configuration}
    (h : Trace p n s c v) (h' : Trace p m v k t) :
    Trace p (n + m) s (c + k) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Completed runs do not consume further charged instructions. -/
theorem Trace.runFuel_done {p : Parameters} {n c : ℕ} {s : Configuration}
    {out : List (List ℕ)} (h : Trace p n s c (.done out)) (extra : ℕ) :
    runFuel p (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
    rw [Nat.add_right_comm, runFuel, head]
    dsimp only
    rw [ih ht]

/-- Each dispatched instruction fits the explicit primitive upper charge. -/
theorem step_cost_le {p : Parameters} {s t : Configuration} {c : ℕ}
    (h : step p s = some (t, c)) : c ≤ 32 := by
  cases s with
  | product inner =>
    cases inner <;> simp only [step] at h
    all_goals first
      | (cases h; omega)
      | (split at h
         · cases h
         · rename_i next cost heq
           have hh := (List.CartesianProductMachine.step_sound heq).total_le
           cases h
           omega)
  | start => cases h; omega
  | rangeX n out => cases n <;> cases h <;> omega
  | rangeJet xs n out => cases n <;> cases h <;> omega
  | axes xs js n out => cases n <;> cases h <;> omega
  | scan rows out => cases rows with
    | nil => cases h; omega
    | cons row rows => cases row <;> cases h <;> omega
  | test row rows out bs j total weighted => cases bs <;> cases h <;> omega
  | reverse rows out => cases rows <;> cases h <;> omega
  | done out => cases h

/-- Total primitive work is bounded by the number of dispatched instructions. -/
theorem Trace.cost_le {p : Parameters} {n c : ℕ} {s t : Configuration}
    (h : Trace p n s c t) : c ≤ 32 * n := by
  induction h with
  | nil s => omega
  | cons head tail ih => have hh := step_cost_le head; omega

/-- Proof-only coordinate axes. -/
def axesSpec (p : Parameters) : List (List ℕ) :=
  List.range p.T :: List.replicate p.h (List.range p.B)

/-- Proof-only differential jet weight, starting at variable Y_j. -/
def jetWeight (D : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | j, b :: bs => (D - j) * b + jetWeight D (j + 1) bs

/-- The two strict cutoffs, with X separated from the jet-degree sum. -/
def Accepted (p : Parameters) : List ℕ → Prop
  | [] => False
  | x :: bs => bs.sum < p.B ∧ x + jetWeight p.D 0 bs < p.T

instance (p : Parameters) (row : List ℕ) : Decidable (Accepted p row) := by
  cases row <;> unfold Accepted <;> infer_instance

/-- Ordered support specification; filtering here is used only by the proof. -/
def supportSpec (p : Parameters) : List (List ℕ) :=
  (Product.productSpec (axesSpec p)).filter (fun row => decide (Accepted p row))

/-- Exact scan instruction count before the final output reversal. -/
def scanFuel : List (List ℕ) → ℕ
  | [] => 1
  | [] :: rows => 1 + scanFuel rows
  | (_ :: bs) :: rows => bs.length + 2 + scanFuel rows

/-- Descending counters allocate the increasing interval without a range primitive. -/
theorem rangeX_trace (p : Parameters) (n : ℕ) (out : List ℕ) :
    ∃ c, Trace p (n + 1) (.rangeX n out) c
      (.rangeJet (List.range n ++ out) p.B []) := by
  induction n generalizing out with
  | zero => exact ⟨_, Trace.cons rfl (Trace.nil _)⟩
  | succ n ih =>
    obtain ⟨c, ht⟩ := ih (n :: out)
    refine ⟨32 + c, ?_⟩
    simpa [List.range_succ, List.append_assoc] using Trace.cons (by rfl) ht

theorem rangeJet_trace (p : Parameters) (xs : List ℕ) (n : ℕ) (out : List ℕ) :
    ∃ c, Trace p (n + 1) (.rangeJet xs n out) c
      (.axes xs (List.range n ++ out) p.h []) := by
  induction n generalizing out with
  | zero => exact ⟨_, Trace.cons rfl (Trace.nil _)⟩
  | succ n ih =>
    obtain ⟨c, ht⟩ := ih (n :: out)
    refine ⟨32 + c, ?_⟩
    simpa [List.range_succ, List.append_assoc] using Trace.cons (by rfl) ht

/-- Jet axes share their materialized universe but every outer axis cell is charged. -/
theorem axes_trace (p : Parameters) (xs js : List ℕ) (n : ℕ) (out : List (List ℕ)) :
    ∃ c, Trace p (n + 1) (.axes xs js n out) c
      (.product (.start (xs :: (List.replicate n js ++ out)))) := by
  induction n generalizing out with
  | zero => exact ⟨_, Trace.cons rfl (Trace.nil _)⟩
  | succ n ih =>
    obtain ⟨c, ht⟩ := ih (js :: out)
    refine ⟨32 + c, ?_⟩
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using
      Trace.cons (s := .axes xs js (n + 1) out) (by rfl) ht

/-- Every inner Cartesian instruction retains its full charge in the outer machine. -/
theorem product_trace {p : Parameters} {n : ℕ} {s t : Product.Configuration ℕ}
    {c : List.CartesianProductMachine.Cost} (h : Product.Trace n s c t) :
    Trace p n (.product s) (c.total + 4 * n) (.product t) := by
  induction h with
  | nil s => exact Trace.nil (p := p) (.product s)
  | @cons n s v t c k head tail ih =>
    have hs : step p (.product s) = some (.product v, c.total + 4) := by
      cases head <;> rfl
    have hc (a b : List.CartesianProductMachine.Cost) :
        (a + b).total = a.total + b.total := by
      simp [List.CartesianProductMachine.Cost.total]
      omega
    convert Trace.cons hs ih using 1
    rw [hc]
    omega

/-- The test loop computes both sums, with one charged instruction per jet coordinate. -/
theorem test_trace (p : Parameters) (row : List ℕ) (rows out : List (List ℕ))
    (bs : List ℕ) (j total weighted : ℕ) :
    ∃ c, Trace p (bs.length + 1) (.test row rows out bs j total weighted) c
      (.scan rows (if total + bs.sum < p.B ∧ weighted + jetWeight p.D j bs < p.T
        then row :: out else out)) := by
  induction bs generalizing j total weighted with
  | nil => exact ⟨_, by simpa [jetWeight] using Trace.cons (p := p) (by rfl) (Trace.nil _)⟩
  | cons b bs ih =>
    obtain ⟨c, ht⟩ := ih (j + 1) (total + b) (weighted + (p.D - j) * b)
    refine ⟨32 + c, ?_⟩
    convert Trace.cons (s := .test row rows out (b :: bs) j total weighted)
      (by rfl) ht using 1 <;> simp [jetWeight, Nat.add_assoc]
    congr 1

/-- Filtering preserves tuple order after a separately charged reversal. -/
theorem scan_trace (p : Parameters) (rows out : List (List ℕ)) :
    ∃ c, Trace p (scanFuel rows) (.scan rows out) c
      (.reverse ((rows.filter (fun row => decide (Accepted p row))).reverse ++ out) []) := by
  induction rows generalizing out with
  | nil => exact ⟨_, Trace.cons rfl (Trace.nil _)⟩
  | cons row rows ih =>
    cases row with
    | nil =>
      obtain ⟨c, ht⟩ := ih out
      refine ⟨32 + c, ?_⟩
      have he : decide (Accepted p []) = false := decide_eq_false (by intro h; exact h)
      simpa only [scanFuel, List.filter_cons, he, Bool.false_eq_true, if_false,
        Nat.add_comm] using Trace.cons (s := .scan ([] :: rows) out) (by rfl) ht
    | cons x bs =>
      obtain ⟨tc, ht⟩ := test_trace p (x :: bs) rows out bs 0 0 x
      simp only [Nat.zero_add] at ht
      by_cases ha : Accepted p (x :: bs)
      · simp only [Accepted] at ha
        rw [if_pos ha] at ht
        obtain ⟨c, hs⟩ := ih ((x :: bs) :: out)
        refine ⟨32 + (tc + c), ?_⟩
        convert Trace.cons (s := .scan ((x :: bs) :: rows) out) (by rfl) (ht.append hs)
          using 1 <;> simp [scanFuel, Accepted, ha, List.reverse_cons, List.append_assoc]
        omega
      · have hn : ¬ (bs.sum < p.B ∧ x + jetWeight p.D 0 bs < p.T) := ha
        rw [if_neg hn] at ht
        obtain ⟨c, hs⟩ := ih out
        refine ⟨32 + (tc + c), ?_⟩
        convert Trace.cons (s := .scan ((x :: bs) :: rows) out) (by rfl) (ht.append hs)
          using 1 <;> simp [scanFuel, Accepted, hn]
        omega

theorem reverse_trace (p : Parameters) (rows out : List (List ℕ)) :
    ∃ c, Trace p (rows.length + 1) (.reverse rows out) c (.done (rows.reverse ++ out)) := by
  induction rows generalizing out with
  | nil => exact ⟨_, Trace.cons rfl (Trace.nil _)⟩
  | cons row rows ih =>
    obtain ⟨c, ht⟩ := ih (row :: out)
    refine ⟨32 + c, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using Trace.cons (by rfl) ht


/-- Product dimensions and administrative weight specialize to elementary integer formulas. -/
theorem axesSpec_size (p : Parameters) :
    (axesSpec p).length = p.h + 1 ∧
      Product.weight (axesSpec p) = (p.T + 1) * (p.B + 1) ^ p.h ∧
      (Product.productSpec (axesSpec p)).length = p.T * p.B ^ p.h := by
  simp [axesSpec, List.CartesianProductMachine.weight,
    List.CartesianProductMachine.productSpec_length]

/-- A candidate scan takes linear work in the materialized box size and coordinate width. -/
theorem scanFuel_le (h : ℕ) (rows : List (List ℕ))
    (hw : ∀ row ∈ rows, row.length = h + 1) :
    scanFuel rows ≤ (h + 2) * rows.length + 1 := by
  induction rows with
  | nil => simp [scanFuel]
  | cons row rows ih =>
    have hr := hw row (by simp)
    have ht := ih (fun r hm => hw r (by simp [hm]))
    cases row with
    | nil => simp at hr
    | cons x bs => simp only [List.length_cons] at hr ⊢; simp only [scanFuel]; nlinarith

/-- Closed polynomial host fuel. Its dependence on T is linear for fixed h and B. -/
def fuel (p : Parameters) : ℕ :=
  p.T + p.B + p.h + 7 +
    8 * (p.h + 2) * ((p.T + 1) * (p.B + 1) ^ p.h) +
    (p.h + 3) * (p.T * p.B ^ p.h)

/-- A full materializing trace reaches the exact support within the closed fuel bound. -/
theorem construction_trace (p : Parameters) :
    ∃ n c, n ≤ fuel p ∧ Trace p n .start c (.done (supportSpec p)) := by
  obtain ⟨xc, hx⟩ := rangeX_trace p p.T []
  obtain ⟨bc, hb⟩ := rangeJet_trace p (List.range p.T) p.B []
  obtain ⟨ac, ha⟩ := axes_trace p (List.range p.T) (List.range p.B) p.h []
  simp only [List.append_nil] at hx hb ha
  obtain ⟨pc, hp, _⟩ := List.CartesianProductMachine.construction_runFuel (axesSpec p)
  obtain ⟨pn, hpn, hpTrace⟩ := List.CartesianProductMachine.runFuel_refines
    (Product.constructionFuel (axesSpec p)) (.start (axesSpec p))
  rw [hp] at hpTrace
  have hp' := product_trace (p := p) hpTrace
  obtain ⟨sc, hs⟩ := scan_trace p (Product.productSpec (axesSpec p)) []
  obtain ⟨rc, hr⟩ := reverse_trace p (supportSpec p).reverse []
  simp only [List.append_nil] at hs
  simp only [List.reverse_reverse, List.append_nil] at hr
  change Trace p _ _ sc (.reverse (supportSpec p).reverse []) at hs
  have ht := Trace.cons (s := .start) (by rfl)
    (hx.append (hb.append (ha.append (hp'.append
      (Trace.cons (s := .product (.done _)) (by rfl) (hs.append hr))))))
  refine ⟨_, _, ?_, ht⟩
  have hprod := List.CartesianProductMachine.constructionFuel_le (axesSpec p)
  have hscan := scanFuel_le p.h (Product.productSpec (axesSpec p)) (by
    intro row hm
    exact (List.CartesianProductMachine.productSpec_width hm).trans (axesSpec_size p).1)
  have hfilter : (supportSpec p).length ≤ (Product.productSpec (axesSpec p)).length :=
    List.length_filter_le _ _
  obtain ⟨hlen, hweight, hcount⟩ := axesSpec_size p
  simp only [hlen, hweight, hcount] at hprod hscan hfilter
  simp only [List.length_reverse]
  unfold fuel
  nlinarith

/-- Execution returns exactly the materialized support, including the empty-box boundaries. -/
theorem construction_correct (p : Parameters) :
    ∃ c, runFuel p (fuel p) .start = (.done (supportSpec p), c) ∧ c ≤ 32 * fuel p := by
  obtain ⟨n, c, hn, ht⟩ := construction_trace p
  have hr := ht.runFuel_done (fuel p - n)
  rw [Nat.add_sub_of_le hn] at hr
  exact ⟨c, hr, ht.cost_le.trans (Nat.mul_le_mul_left 32 hn)⟩

/-- Axis distinctness implies no repeated interpolation columns after filtering. -/
theorem supportSpec_nodup (p : Parameters) : (supportSpec p).Nodup := by
  apply List.Nodup.filter
  apply List.CartesianProductMachine.productSpec_nodup
  intro axis ha
  simp only [axesSpec, List.mem_cons, List.mem_replicate] at ha
  rcases ha with rfl | ⟨_, rfl⟩ <;> exact List.nodup_range

/-- Every column has exactly one X coordinate and h jet coordinates. -/
theorem supportSpec_width (p : Parameters) {row : List ℕ} (hr : row ∈ supportSpec p) :
    row.length = p.h + 1 :=
  (List.CartesianProductMachine.productSpec_width (List.mem_filter.mp hr).1).trans
    (axesSpec_size p).1

/-- Output size is bounded by the actual finite box, without a cardinality oracle. -/
theorem supportSpec_length_le (p : Parameters) : (supportSpec p).length ≤ p.T * p.B ^ p.h := by
  exact (List.length_filter_le _ _).trans_eq (axesSpec_size p).2.2

/-- The constant in the linear work bound depends only on jet count and jet cutoff. -/
def linearFactor (h B : ℕ) : ℕ :=
  B + h + 7 + 8 * (h + 2) * (B + 1) ^ h + (h + 3) * B ^ h

/-- The closed fuel is linear in the X-axis bound, including T=0. -/
theorem fuel_le_linear (p : Parameters) : fuel p ≤ linearFactor p.h p.B * (p.T + 1) := by
  unfold fuel linearFactor
  nlinarith [Nat.zero_le ((p.h + 3) * p.B ^ p.h)]

/-- Integer interpolation inputs with an explicit strict total-jet cutoff. -/
def parametersWithBudget (D d m J A : ℕ) : Parameters := ⟨D, d + 1, J, m * A⟩

/-- Legacy interpolation inputs specialize the strict total-jet cutoff to `2 * m`. -/
def parameters (D d m A : ℕ) : Parameters := ⟨D, d + 1, 2 * m, m * A⟩

/-- The executable enumerator with an explicit strict total-jet cutoff. -/
def enumerateWithBudget (D d m J A : ℕ) : Configuration × ℕ :=
  let p := parametersWithBudget D d m J A
  runFuel p (fuel p) .start

/-- The legacy executable enumerator uses strict cutoff `2 * m`. -/
def enumerate (D d m A : ℕ) : Configuration × ℕ :=
  enumerateWithBudget D d m (2 * m) A

/-- The integer program is correct and has linear-in-`m*A` work for fixed `d` and `J`. -/
theorem enumerateWithBudget_correct (D d m J A : ℕ) :
    ∃ c, enumerateWithBudget D d m J A =
        (.done (supportSpec (parametersWithBudget D d m J A)), c) ∧
      c ≤ 32 * linearFactor (d + 1) J * (m * A + 1) := by
  obtain ⟨c, hc, hb⟩ := construction_correct (parametersWithBudget D d m J A)
  refine ⟨c, hc, ?_⟩
  have h := Nat.mul_le_mul_left 32 (fuel_le_linear (parametersWithBudget D d m J A))
  exact hb.trans (by simpa [parametersWithBudget, Nat.mul_assoc] using h)

/-- Correctness of the legacy `2 * m` specialization. -/
theorem enumerate_correct (D d m A : ℕ) :
    ∃ c, enumerate D d m A = (.done (supportSpec (parameters D d m A)), c) ∧
      c ≤ 32 * linearFactor (d + 1) (2 * m) * (m * A + 1) := by
  simpa [enumerate, parameters, parametersWithBudget] using
    enumerateWithBudget_correct D d m (2 * m) A


/-- Membership in the materialized jet box is exactly coordinatewise boundedness and width. -/
theorem forall₂_jet_axes (bs : List ℕ) (h B : ℕ) :
    List.Forall₂ (· ∈ ·) bs (List.replicate h (List.range B)) ↔
      bs.length = h ∧ ∀ b ∈ bs, b < B := by
  induction bs generalizing h with
  | nil => cases h <;> simp
  | cons b bs ih =>
    cases h with
    | zero => simp
    | succ h =>
      simp [List.replicate_succ, List.forall₂_cons, ih, and_left_comm]

/-- Exact support membership in ordinary coordinate lists, including both strict cutoffs. -/
theorem mem_supportSpec (p : Parameters) (x : ℕ) (bs : List ℕ) :
    x :: bs ∈ supportSpec p ↔ bs.length = p.h ∧ x < p.T ∧
      (∀ b ∈ bs, b < p.B) ∧ bs.sum < p.B ∧ x + jetWeight p.D 0 bs < p.T := by
  rw [supportSpec, List.mem_filter]
  constructor
  · rintro ⟨hb, ha⟩
    have hbox := (List.CartesianProductMachine.mem_productSpec _ _).mp hb
    have hbox' : x < p.T ∧ bs.length = p.h ∧ ∀ b ∈ bs, b < p.B := by
      simpa only [axesSpec, List.forall₂_cons, List.mem_range, forall₂_jet_axes] using hbox
    have hgood : Accepted p (x :: bs) := of_decide_eq_true ha
    exact ⟨hbox'.2.1, hbox'.1, hbox'.2.2, hgood⟩
  · rintro ⟨hw, hx, hb, hs, ht⟩
    refine ⟨?_, decide_eq_true (show Accepted p (x :: bs) from ⟨hs, ht⟩)⟩
    apply (List.CartesianProductMachine.mem_productSpec _ _).mpr
    exact List.Forall₂.cons (List.mem_range.mpr hx) ((forall₂_jet_axes bs p.h p.B).mpr
      ⟨hw, hb⟩)

private theorem coordinate_le_sum (bs : List ℕ) (b : ℕ) (hb : b ∈ bs) : b ≤ bs.sum := by
  induction bs with
  | nil => simp at hb
  | cons a bs ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · simp
    · have hh := ih hb; simp only [List.sum_cons]; omega

/-- Individual box bounds are redundant once the nonnegative degree sums are bounded. -/
theorem mem_supportSpec_iff (p : Parameters) (x : ℕ) (bs : List ℕ) :
    x :: bs ∈ supportSpec p ↔ bs.length = p.h ∧ bs.sum < p.B ∧
      x + jetWeight p.D 0 bs < p.T := by
  rw [mem_supportSpec]
  constructor
  · tauto
  · rintro ⟨hw, hs, ht⟩
    refine ⟨hw, by omega, ?_, hs, ht⟩
    intro b hb
    exact (coordinate_le_sum bs b hb).trans_lt hs

/-- The recursive weight agrees with the finite-indexed differential weight used by a matrix. -/
theorem jetWeight_eq_sum (D j : ℕ) (bs : List ℕ) :
    jetWeight D j bs = ∑ i : Fin bs.length, (D - (j + i.val)) * bs.get i := by
  induction bs generalizing j with
  | nil => simp [jetWeight]
  | cons b bs ih =>
    simp [jetWeight, Fin.sum_univ_succ, ih, Nat.add_comm, Nat.add_left_comm]

/-- Finite coordinate functions use the same indexed differential weights. -/
theorem jetWeight_ofFn (D j n : ℕ) (b : Fin n → ℕ) :
    jetWeight D j (List.ofFn b) = ∑ i, (D - (j + i.val)) * b i := by
  induction n generalizing j with
  | zero => simp [jetWeight]
  | succ n ih =>
    rw [List.ofFn_succ, jetWeight, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    omega

/-- Matrix-facing exact column coverage: Y_j has weight D-j, with X weight one. No side
assumptions on d,D are hidden; the consumer's d<D makes every jet weight positive. -/
theorem mem_interpolation_columns (D d m A x : ℕ) (b : Fin (d + 1) → ℕ) :
    x :: List.ofFn b ∈ supportSpec (parameters D d m A) ↔
      (∑ j, b j) < 2 * m ∧ x + (∑ j, (D - j.val) * b j) < m * A := by
  rw [mem_supportSpec_iff]
  simp only [parameters, List.length_ofFn, true_and, List.sum_ofFn,
    jetWeight_ofFn, Nat.zero_add]

/-- Matrix-facing exact column coverage with an explicit strict total-jet cutoff. -/
theorem mem_interpolation_columnsWithBudget (D d m J A x : ℕ)
    (b : Fin (d + 1) → ℕ) :
    x :: List.ofFn b ∈ supportSpec (parametersWithBudget D d m J A) ↔
      (∑ j, b j) < J ∧ x + (∑ j, (D - j.val) * b j) < m * A := by
  rw [mem_supportSpec_iff]
  simp only [parametersWithBudget, List.length_ofFn, true_and, List.sum_ofFn, jetWeight_ofFn,
    Nat.zero_add]

/-- A zero X bound yields no columns, even when the jet box is nonempty. -/
theorem supportSpec_zero_T (p : Parameters) (h : p.T = 0) : supportSpec p = [] := by
  apply List.eq_nil_of_length_eq_zero
  have hb := supportSpec_length_le p
  simp only [h, Nat.zero_mul, Nat.le_zero] at hb
  exact hb

/-- A zero total-jet cutoff rejects even the all-zero exponent vector. -/
theorem supportSpec_zero_B (p : Parameters) (h : p.B = 0) : supportSpec p = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row hr
  have ha := (List.mem_filter.mp hr).2
  have hg : Accepted p row := of_decide_eq_true ha
  cases row <;> simp [Accepted, h] at hg

end ReedSolomon.HiddenDerivative.InterpolationSupportMachine
