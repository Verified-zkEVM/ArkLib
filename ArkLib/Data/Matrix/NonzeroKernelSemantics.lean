/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.NonzeroKernelMachine

/-!
# Correctness and polynomial cost of nonzero kernel extraction

A nonzero homogeneous solution forces a free echelon column: its largest nonzero coordinate
cannot be a pivot when every later coordinate is zero. The unit seed at a free column then
survives back substitution, whose solved equations transfer to the original input.
-/

@[expose] public section

namespace Matrix.NonzeroKernelMachine

open ForwardEchelonMachine

variable {F : Type*} [Field F] [DecidableEq F]

abbrev totalCost := PivotSelectionMachine.totalCost

/-- Primitive totals add under trace composition. -/
theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b := by
  simp only [totalCost, PivotSelectionMachine.totalCost, PivotEliminationMachine.cost_add,
    RowReductionMachine.cost_add]
  omega
/-- Wrapper cost is one dispatch and two data operations per callee step. -/
theorem total_wrapper (k : ℕ) : totalCost (wrapperCost k) = 3 * k := by
  simp [totalCost, PivotSelectionMachine.totalCost, wrapperCost,
    BackSubstitutionMachine.wrapperCost]
  omega
/-- The total of a single driver charge. -/
theorem total_charge (a b c e : ℕ) : totalCost (charge a b c e) = 1 + a + b + c + e := by
  simp [totalCost, PivotSelectionMachine.totalCost, charge]
  omega

omit [DecidableEq F] in
/-- Lift every forward-elimination transition, paying its driver wrapper. -/
theorem lift_forward {n k : ℕ} {s t : ForwardEchelonMachine.Configuration F} {c : Cost}
    (h : ForwardEchelonMachine.Trace k s c t) :
    Trace n k (.forward s) (c + wrapperCost k) (.forward t) := by
  induction h with
  | nil s => simpa [wrapperCost, BackSubstitutionMachine.wrapperCost] using Trace.nil (.forward s)
  | @cons k s u t c e head tail ih =>
      have hc : (c + wrapperCost 1) + (e + wrapperCost k) =
          (c + e) + wrapperCost (k + 1) := by
        ext <;> simp [wrapperCost, BackSubstitutionMachine.wrapperCost] <;> omega
      rw [← hc]
      exact Trace.cons (Step.forward head) ih

omit [DecidableEq F] in
/-- Lift every back-substitution transition, paying its driver wrapper. -/
theorem lift_back {n k j : ℕ} {s t : BackSubstitutionMachine.Configuration F} {c : Cost}
    (h : BackSubstitutionMachine.Trace k s c t) :
    Trace n k (.back j s) (c + wrapperCost k) (.back j t) := by
  induction h with
  | nil s => simpa [wrapperCost, BackSubstitutionMachine.wrapperCost] using Trace.nil (.back j s)
  | @cons k s u t c e head tail ih =>
      have hc : (c + wrapperCost 1) + (e + wrapperCost k) =
          (c + e) + wrapperCost (k + 1) := by
        ext <;> simp [wrapperCost, BackSubstitutionMachine.wrapperCost] <;> omega
      rw [← hc]
      exact Trace.cons (Step.back head) ih

omit [DecidableEq F] in
private theorem width_trace (n : ℕ) (orig rs : List (Row F)) (cs : List F) :
    Trace n (cs.length + 1) (.width orig rs cs cs.length)
      ⟨⟨0, 0, cs.length + 1, 3 * cs.length + 3, 0⟩, 0, 0, 0, 2 * cs.length + 1⟩
      (.check orig rs) := by
  induction cs with
  | nil => simpa [charge] using Trace.cons (Step.widthEnd (n := n) (orig := orig)) (Trace.nil _)
  | cons x xs ih =>
      convert Trace.cons (Step.width (x := x)) ih using 1 <;> simp [charge, Nat.mul_add]; omega

omit [DecidableEq F] in
private theorem check_trace (n : ℕ) (orig rs : List (Row F)) (hr : Rectangular n rs)
    (hh : ∀ r ∈ rs, r.2 = 0) :
    Trace n ((n + 2) * rs.length + 1) (.check orig rs)
      ⟨⟨0, 0, (n + 2) * rs.length + 1, (3 * n + 9) * rs.length + 5, 0⟩,
        0, 0, rs.length, (2 * n + 1) * rs.length⟩
      (.forward (.loop 0 n orig [])) := by
  induction rs with
  | nil => simpa [charge] using Trace.cons (Step.launch (n := n) (orig := orig)) (Trace.nil _)
  | cons r rs ih =>
      rcases r with ⟨cs, b⟩
      have hb := hh (cs, b) (by simp)
      simp only at hb
      subst b
      have hl := hr (cs, 0) (by simp)
      have hw := width_trace n orig rs cs
      rw [hl] at hw
      have hi := ih (fun r h => hr r (by simp [h])) (fun r h => hh r (by simp [h]))
      convert Trace.cons (Step.check (cs := cs)) (hw.trans hi) using 1 <;>
        simp [charge, Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;>
        omega

/-- Materialized unit seed; construction runs from the highest index down to zero. -/
def unitSeed (n j : ℕ) : List F := (List.range n).map fun i => if i = j then 1 else 0

omit [DecidableEq F] in
/-- The unit seed has exactly the declared width. -/
theorem unitSeed_length (n j : ℕ) : (unitSeed (F := F) n j).length = n := by simp [unitSeed]

omit [DecidableEq F] in
/-- The chosen in-bounds coordinate of the seed is one. -/
theorem unitSeed_chosen (n j : ℕ) (hj : j < n) : (unitSeed (F := F) n j).getD j 0 = 1 := by
  rw [List.getD_eq_getElem _ _ (by simpa only [unitSeed_length] using hj)]
  simp [unitSeed]

omit [DecidableEq F] in
private theorem seed_trace (n : ℕ) (ps : List (Pivot F)) (rs : List (Row F))
    (j k : ℕ) (out : List F) :
    Trace n (k + 1) (.seed ps rs j k out)
      ⟨⟨0, 0, k + 1, 5 * k + 6, 0⟩, 0, 0, 0, 3 * k + 1⟩
      (.back j (.check rs ps (unitSeed k j ++ out))) := by
  induction k generalizing out with
  | zero => simpa [unitSeed, charge] using
      Trace.cons (Step.backStart (n := n) (ps := ps) (rs := rs) (j := j)) (Trace.nil _)
  | succ k ih =>
      simpa [unitSeed, List.range_succ, List.map_append, List.append_assoc, charge,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons Step.seed (ih ((if k = j then 1 else 0) :: out))

omit [DecidableEq F] in
private theorem free_trace (n : ℕ) (ps : List (Pivot F)) (rs : List (Row F))
    (cur : List (Pivot F)) (j : ℕ)
    (horder : cur.Pairwise (fun p q => p.1 < q.1))
    (hlower : ∀ p ∈ cur, j ≤ p.1)
    (hfree : ∃ i, j ≤ i ∧ i < n ∧ ∀ p ∈ cur, i ≠ p.1) :
    ∃ i steps c, Trace n steps (.free ps rs cur j) c (.seed ps rs i n []) ∧
      j ≤ i ∧ i < n ∧ (∀ p ∈ cur, i ≠ p.1) ∧
      steps + totalCost c ≤ 11 * (cur.length + 1) := by
  induction cur generalizing j with
  | nil =>
      have hj : j < n := by obtain ⟨i, hi, hn, _⟩ := hfree; omega
      refine ⟨j, 1, charge 6 2 0 0, ?_, le_rfl, hj, by simp, ?_⟩
      · simpa using Trace.cons (Step.freeNil (ps := ps) (rs := rs) hj) (Trace.nil _)
      · simp [total_charge]
  | cons p cur ih =>
      have hj : j < n := by obtain ⟨i, hi, hn, _⟩ := hfree; omega
      by_cases hp : p.1 = j
      · obtain ⟨ho, ht⟩ := List.pairwise_cons.mp horder
        obtain ⟨i, steps, c, hr, hji, hin, hf, hc⟩ := ih (j + 1) ht
          (by intro q hq; have h := ho q hq; omega)
          (by
            obtain ⟨i, hi, hn, hf⟩ := hfree
            refine ⟨i, ?_, hn, fun q hq => hf q (by simp [hq])⟩
            have hh := hf p (by simp)
            omega)
        refine ⟨i, steps + 1, charge 6 3 0 0 + c,
          Trace.cons (Step.freeHit hj hp) hr, by omega, hin, ?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · omega
          · exact hf q hq
        · rw [total_add, total_charge]
          simp only [List.length_cons]
          omega
      · refine ⟨j, 1, charge 6 2 0 0, ?_, le_rfl, hj, ?_, ?_⟩
        · simpa using Trace.cons (Step.freeGap (ps := ps) (rs := rs) (cur := cur) hj hp)
            (Trace.nil _)
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Ne.symm hp
          · have hh := (List.pairwise_cons.mp horder).1 q hq
            have hl := hlower p (by simp)
            omega
        · simp [total_charge]
          omega

omit [DecidableEq F] in
/-- A nonzero homogeneous echelon solution implies a free column, regardless of row count. -/
theorem exists_free_of_nonzero_solution (n : ℕ) (ps : List (Pivot F)) (rs : List (Row F))
    (he : Echelon n 0 ps rs) (hh : ∀ p ∈ ps, p.2.2 = 0)
    (x : ℕ → F) (hx : Solutions ps rs x) (hne : ∃ i < n, x i ≠ 0) :
    ∃ i, i < n ∧ ∀ p ∈ ps, i ≠ p.1 := by
  classical
  by_contra h
  push Not at h
  let nonzero := (Finset.range n).filter fun i => x i ≠ 0
  have hn : nonzero.Nonempty := by
    obtain ⟨i, hi, hx⟩ := hne
    exact ⟨i, by simp [nonzero, hi, hx]⟩
  let i := nonzero.max' hn
  have him := nonzero.max'_mem hn
  have hin : i < n := Finset.mem_range.mp (Finset.mem_filter.mp him).1
  have hxi : x i ≠ 0 := (Finset.mem_filter.mp him).2
  obtain ⟨p, hp, hip⟩ := h i hin
  obtain ⟨_, _, hlen, hcoef, hbefore⟩ := he.2.1 p hp
  have heq := hx p.2 (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  change AugmentedColumnMachine.rowValue p.2.1 x = p.2.2 at heq
  rw [hh p hp] at heq
  have hsum : AugmentedColumnMachine.rowValue p.2.1 x = p.2.1.getD i 0 * x i := by
    unfold AugmentedColumnMachine.rowValue
    apply Finset.sum_eq_single i
    · intro k hk hki
      by_cases hlt : k < i
      · rw [hbefore k (by omega), zero_mul]
      · have hxk : x k = 0 := by
          by_contra hkx
          have hkn : k < n := by simpa only [hlen] using Finset.mem_range.mp hk
          have hmem : k ∈ nonzero := by simp [nonzero, hkn, hkx]
          have hh := Finset.le_max' nonzero k hmem
          omega
        rw [hxk, mul_zero]
    · intro hi
      exact (hi (by simp [hlen, hin])).elim
  rw [hsum] at heq
  exact mul_ne_zero (by simpa only [hip] using hcoef) hxi heq

/-- Polynomial budget, including input validation, both suspended callees, seed construction
and the final result. The back-substitution budget uses the preserved original row count. -/
def budget (m n : ℕ) : ℕ :=
  20 * (m + 1) * (n + 1) + 5 * ForwardEchelonMachine.budget m n +
    11 * (m + 1) + 10 * (n + 1) + 5 * ((200 * (n + 1) + 14) * m + 14) + 30

/-- A supplied nonzero homogeneous solution is enough for actual successful kernel extraction;
no inequality between the raw row and column counts is required. The returned chosen coordinate
is one, all original equations hold, and both fuel and primitive charges are polynomial. -/
theorem evaluation_runFuel (n : ℕ) (rows : List (Row F)) (hr : Rectangular n rows)
    (hh : ∀ r ∈ rows, r.2 = 0)
    (hne : ∃ x : ℕ → F, PivotSelectionMachine.Satisfies rows x ∧ ∃ i < n, x i ≠ 0) :
    ∃ j out c, runFuel n (budget rows.length n) (.check rows rows) = (.done j out, c) ∧
      out.length = n ∧ j < n ∧ out.getD j 0 = 1 ∧
      PivotSelectionMachine.Satisfies rows (fun i => out.getD i 0) ∧
      totalCost c ≤ budget rows.length n := by
  obtain ⟨ps, rs, cf, hfr, he, hcount, hsol, hfcost⟩ :=
    ForwardEchelonMachine.evaluation_runFuel n rows hr
  obtain ⟨kf, hkf, hft⟩ := ForwardEchelonMachine.runFuel_refines
    (ForwardEchelonMachine.budget rows.length n) (.loop 0 n rows [])
  rw [hfr] at hft
  dsimp only at hft
  change totalCost cf ≤ _ at hfcost
  have hzero : PivotSelectionMachine.Satisfies rows (fun _ => 0) := by
    intro r hr
    simpa using (hh r hr).symm
  have hall : ∀ r ∈ ps.map Prod.snd ++ rs, r.2 = 0 := by
    intro r hr
    have h := ((hsol (fun _ => 0)).mpr hzero) r hr
    simpa using h.symm
  have hpszero : ∀ p ∈ ps, p.2.2 = 0 := fun p hp =>
    hall p.2 (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  have hrszero : ∀ r ∈ rs, r.2 = 0 := fun r hr => hall r (List.mem_append_right _ hr)
  have hfree : ∃ i, i < n ∧ ∀ p ∈ ps, i ≠ p.1 := by
    obtain ⟨x, hx, hnx⟩ := hne
    exact exists_free_of_nonzero_solution n ps rs he hpszero x ((hsol x).mpr hx) hnx
  obtain ⟨j, kg, cg, hgt, _, hjn, hjfree, hgcost⟩ := free_trace n ps rs ps 0 he.1
    (fun p hp => (he.2.1 p hp).1) (by
      obtain ⟨i, hi, hf⟩ := hfree
      exact ⟨i, Nat.zero_le _, hi, hf⟩)
  have hseed := seed_trace n ps rs j n []
  simp only [List.append_nil] at hseed
  obtain ⟨out, cb, hbr, hlen, hbsol, hbfree, hbcost⟩ :=
    BackSubstitutionMachine.evaluation_runFuel n ps rs (unitSeed n j) he
      (unitSeed_length n j) hrszero
  obtain ⟨kb, hkb, hbt⟩ := BackSubstitutionMachine.runFuel_refines
    (BackSubstitutionMachine.budget n ps.length rs.length) (.check rs ps (unitSeed n j))
  rw [hbr] at hbt
  dsimp only at hbt
  change totalCost cb ≤ _ at hbcost
  have ht := (check_trace n rows rows hr hh).trans
    ((lift_forward hft).trans (Trace.cons Step.forwardDone
      (hgt.trans (hseed.trans ((lift_back hbt).trans (Trace.cons Step.emit (Trace.nil _)))))))
  have hcheck : (n + 2) * rows.length + 1 +
      totalCost ⟨⟨0, 0, (n + 2) * rows.length + 1, (3 * n + 9) * rows.length + 5, 0⟩,
        0, 0, rows.length, (2 * n + 1) * rows.length⟩ ≤
        20 * (rows.length + 1) * (n + 1) := by
    simp only [totalCost, PivotSelectionMachine.totalCost]
    nlinarith [Nat.zero_le (n * rows.length)]
  have hsbound : n + 1 + totalCost
      ⟨⟨0, 0, n + 1, 5 * n + 6, 0⟩, 0, 0, 0, 3 * n + 1⟩ ≤ 10 * (n + 1) := by
    simp only [totalCost, PivotSelectionMachine.totalCost]
    omega
  have hbmax : BackSubstitutionMachine.budget n ps.length rs.length ≤
      (200 * (n + 1) + 14) * rows.length + 14 := by
    unfold BackSubstitutionMachine.budget
    nlinarith [Nat.zero_le (n * rs.length)]
  have hbound : ((n + 2) * rows.length + 1 +
      (kf + (kg + (n + 1 + (kb + (0 + 1))) + 1))) +
      totalCost (⟨⟨0, 0, (n + 2) * rows.length + 1, (3 * n + 9) * rows.length + 5, 0⟩,
        0, 0, rows.length, (2 * n + 1) * rows.length⟩ +
        ((cf + wrapperCost kf) + (charge 6 0 0 0 +
          (cg + (⟨⟨0, 0, n + 1, 5 * n + 6, 0⟩, 0, 0, 0, 3 * n + 1⟩ +
            ((cb + wrapperCost kb) + (charge 3 0 0 1 + 0))))))) ≤ budget rows.length n := by
    simp only [total_add, total_wrapper, total_charge]
    change _ + (_ + (_ + (7 + (_ + (_ + (_ + (5 + 0))))))) ≤ _
    unfold budget
    omega
  refine ⟨j, out, _, terminal_run ht rfl (by omega), hlen, hjn, ?_,
    (hsol _).mp hbsol, by omega⟩
  rw [hbfree j hjfree]
  exact unitSeed_chosen n j hjn

end Matrix.NonzeroKernelMachine
