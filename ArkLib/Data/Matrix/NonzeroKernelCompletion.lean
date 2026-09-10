/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.NonzeroKernelSemantics

/-!
# Total completion of the actual homogeneous kernel solver

On rectangular homogeneous input the existing fuel either emits a certified nonzero solution
or reports full pivot coverage. Both alternatives carry observed primitive bounds. Fuel
exhaustion is not identified with no kernel. This supports finite search over failing candidates.
-/

@[expose] public section

namespace Matrix.NonzeroKernelMachine

open ForwardEchelonMachine

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
private theorem completion_width_trace (n : ℕ) (orig rs : List (Row F)) (cs : List F) :
    Trace n (cs.length + 1) (.width orig rs cs cs.length)
      ⟨⟨0, 0, cs.length + 1, 3 * cs.length + 3, 0⟩, 0, 0, 0, 2 * cs.length + 1⟩
      (.check orig rs) := by
  induction cs with
  | nil => simpa [charge] using Trace.cons (Step.widthEnd (n := n) (orig := orig)) (Trace.nil _)
  | cons x xs ih =>
      convert Trace.cons (Step.width (x := x)) ih using 1 <;> simp [charge, Nat.mul_add]; omega

omit [DecidableEq F] in
private theorem completion_check_trace (n : ℕ) (orig rs : List (Row F)) (hr : Rectangular n rs)
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
      have hw := completion_width_trace n orig rs cs
      rw [hl] at hw
      have hi := ih (fun r h => hr r (by simp [h])) (fun r h => hh r (by simp [h]))
      convert Trace.cons (Step.check (cs := cs)) (hw.trans hi) using 1 <;>
        simp [charge, Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;>
        omega

omit [DecidableEq F] in
/-- Full ordered pivot coverage executes every probe and ends at the genuine noFree state. -/
theorem coverage_trace (n : ℕ) (ps : List (Pivot F)) (rs : List (Row F))
    (cur : List (Pivot F)) (j : ℕ) (ho : cur.Pairwise (fun p q => p.1 < q.1))
    (hl : ∀ p ∈ cur, j ≤ p.1)
    (hc : ∀ i, j ≤ i → i < n → ∃ p ∈ cur, p.1 = i) :
    ∃ k c, Trace n k (.free ps rs cur j) c .noFree ∧
      k + totalCost c ≤ 11 * (cur.length + 1) := by
  induction cur generalizing j with
  | nil =>
    have hn : n ≤ j := by
      by_contra h
      obtain ⟨p, hp, _⟩ := hc j le_rfl (by omega)
      simp at hp
    refine ⟨1, charge 6 2 0 1, ?_, ?_⟩
    · simpa using Trace.cons (Step.noFree (ps := ps) (rs := rs) hn) (Trace.nil _)
    · simp [total_charge]
  | cons p cur ih =>
    by_cases hn : n ≤ j
    · refine ⟨1, charge 6 2 0 1, ?_, ?_⟩
      · simpa using Trace.cons (Step.noFree (ps := ps) (rs := rs) hn) (Trace.nil _)
      · simp [total_charge]
    · have hj : j < n := by omega
      obtain ⟨horder, htail⟩ := List.pairwise_cons.mp ho
      have hp : p.1 = j := by
        obtain ⟨q, hq, he⟩ := hc j le_rfl hj
        rcases List.mem_cons.mp hq with rfl | hq
        · exact he
        · have hh := horder q hq
          have hh' := hl p (by simp)
          omega
      obtain ⟨k, c, ht, hb⟩ := ih (j + 1) htail
        (by intro q hq; have hh := horder q hq; omega)
        (by
          intro i hi hin
          obtain ⟨q, hq, he⟩ := hc i (by omega) hin
          refine ⟨q, ?_, he⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · omega
          · exact hq)
      refine ⟨k + 1, charge 6 3 0 0 + c, Trace.cons (Step.freeHit hj hp) ht, ?_⟩
      rw [total_add, total_charge]
      simp only [List.length_cons]
      omega

/-- Rectangular homogeneous inputs complete at the public fuel, including genuinely full-rank
systems with redundant rows. A successful output retains its unit chosen coordinate. -/
theorem completion_runFuel (n : ℕ) (rows : List (Row F)) (hr : Rectangular n rows)
    (hh : ∀ r ∈ rows, r.2 = 0) :
    (∃ j out c, runFuel n (budget rows.length n) (.check rows rows) = (.done j out, c) ∧
      out.length = n ∧ j < n ∧ out.getD j 0 = 1 ∧
      PivotSelectionMachine.Satisfies rows (fun i => out.getD i 0) ∧
      totalCost c ≤ budget rows.length n) ∨
    (∃ c, runFuel n (budget rows.length n) (.check rows rows) = (.noFree, c) ∧
      totalCost c ≤ budget rows.length n ∧
      ¬∃ x : ℕ → F, PivotSelectionMachine.Satisfies rows x ∧ ∃ i < n, x i ≠ 0) := by
  by_cases hne : ∃ x : ℕ → F, PivotSelectionMachine.Satisfies rows x ∧ ∃ i < n, x i ≠ 0
  · exact Or.inl (evaluation_runFuel n rows hr hh hne)
  right
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
  have hz : ∀ r ∈ rs, r.2 = 0 := by
    intro r hr
    have hh' := (hsol (fun _ => 0)).mpr hzero r (List.mem_append_right _ hr)
    simpa using hh'.symm
  have hcoverage : ∀ i, 0 ≤ i → i < n → ∃ p ∈ ps, p.1 = i := by
    intro i _ hi
    by_contra hmissing
    have hfree : ∀ p ∈ ps, i ≠ p.1 := by
      intro p hp he
      exact hmissing ⟨p, hp, he.symm⟩
    obtain ⟨out, c, _, _, hs, hf, _⟩ := BackSubstitutionMachine.evaluation_runFuel n ps rs
      (unitSeed n i) he (unitSeed_length n i) hz
    apply hne
    refine ⟨fun j => out.getD j 0, (hsol _).mp hs, i, hi, ?_⟩
    change out.getD i 0 ≠ 0
    rw [hf i hfree, unitSeed_chosen n i hi]
    exact one_ne_zero
  obtain ⟨kg, cg, hgt, hgcost⟩ := coverage_trace n ps rs ps 0 he.1
    (fun p hp => (he.2.1 p hp).1) hcoverage
  have ht := (completion_check_trace n rows rows hr hh).trans
    ((lift_forward hft).trans (Trace.cons Step.forwardDone hgt))
  have hcheck : (n + 2) * rows.length + 1 +
      totalCost ⟨⟨0, 0, (n + 2) * rows.length + 1, (3 * n + 9) * rows.length + 5, 0⟩,
        0, 0, rows.length, (2 * n + 1) * rows.length⟩ ≤
        20 * (rows.length + 1) * (n + 1) := by
    simp only [totalCost, PivotSelectionMachine.totalCost]
    nlinarith [Nat.zero_le (n * rows.length)]
  have hbound : ((n + 2) * rows.length + 1 + (kf + (kg + 1))) +
      totalCost (⟨⟨0, 0, (n + 2) * rows.length + 1, (3 * n + 9) * rows.length + 5, 0⟩,
        0, 0, rows.length, (2 * n + 1) * rows.length⟩ +
        ((cf + wrapperCost kf) + (charge 6 0 0 0 + cg))) ≤ budget rows.length n := by
    simp only [total_add, total_wrapper, total_charge]
    unfold budget
    have hp : ps.length ≤ rows.length := by omega
    have hg := hgcost.trans (Nat.mul_le_mul_left 11 (Nat.add_le_add_right hp 1))
    omega
  exact ⟨_, terminal_run ht rfl (by omega), by omega, hne⟩

end Matrix.NonzeroKernelMachine
