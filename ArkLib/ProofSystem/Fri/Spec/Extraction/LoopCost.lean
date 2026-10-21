/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.WordCost

/-!
# Cost recurrences for extractor loops

The recurrences retain the actual branch decisions and intermediate states of the measured
program. Word-read bounds use the bounded sample-cache length as a potential.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- An empty round list performs no instructions. -/
@[simp]
theorem profile_checkRounds_nil (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (x : (ω.subdomain 0).toFinset) :
    (profile s o α (checkRounds s o α hs input x [])).2 = 0 := by
  simp [checkRounds]

/-- A round-list step pays its tick and check, then pays the suffix only after acceptance. -/
theorem profile_checkRounds_cons (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (x : (ω.subdomain 0).toFinset)
    (i : Fin (k + 1)) (indices : List (Fin (k + 1))) :
    (profile s o α (checkRounds s o α hs input x (i :: indices))).2 =
      embedArithmeticCost (arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F)) +
        (profile s o α (checkRoundProgram s o α hs input i x)).2 +
        if (profile s o α (checkRoundProgram s o α hs input i x)).1.val = true then
          (profile s o α (checkRounds s o α hs input x indices)).2 else 0 := by
  by_cases hb : (profile s o α (checkRoundProgram s o α hs input i x)).1.val = true <;>
    simp only [checkRounds, profile_bind, profile_pure,
      profile_liftComp_arithmetic, profileArithmetic_tick, hb, Bool.false_eq_true, dite_true,
      dite_false, ite_true, ite_false,
      add_zero, add_assoc]

/-- A short-circuit round list never exceeds the sum of all its local word-read counts. -/
theorem profile_checkRounds_word_le (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (x : (ω.subdomain 0).toFinset)
    (indices : List (Fin (k + 1))) :
    (profile s o α (checkRounds s o α hs input x indices)).2 (.inr .wordRead) ≤
      (indices.map (fun i ↦ 2 ^ (s i).val + if i.val < k then 1 else 0)).sum := by
  induction indices with
  | nil => simp
  | cons i indices ih =>
    rw [profile_checkRounds_cons]
    by_cases hb : (profile s o α (checkRoundProgram s o α hs input i x)).1.val = true <;>
      simp only [hb, Bool.false_eq_true, ite_true, ite_false, Pi.add_apply, embedArithmeticCost,
        Sum.elim_inr,
        Pi.zero_apply, zero_add, add_zero, profile_checkRoundProgram_word,
        List.map_cons, List.sum_cons] <;> omega

private theorem sum_nonfinal (m : ℕ) :
    (∑ i : Fin (m + 1), if i.val < m then 1 else 0) = m := by
  rw [Fin.sum_univ_castSucc]
  simp

/-- A position check uses at most the complete block reads and one read per non-final round. -/
theorem profile_checkPosition_word_le (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (z : Fin (2 ^ n))
    (x : {q : (ω.subdomain 0).toFinset // q = initialQuery z}) :
    (profile s o α (checkPosition s o α hs input z x)).2 (.inr .wordRead) ≤
      (∑ i, 2 ^ (s i).val) + k := by
  have h := profile_checkRounds_word_le s o α hs input x.val (List.finRange (k + 1))
  have hsum : ((List.finRange (k + 1)).map
      (fun i ↦ 2 ^ (s i).val + if i.val < k then 1 else 0)).sum =
        (∑ i, 2 ^ (s i).val) + k := by
    rw [← List.ofFn_eq_map, List.sum_ofFn, Finset.sum_add_distrib, sum_nonfinal]
  rw [hsum] at h
  simpa [checkPosition] using h

/-- The cache-length increase pays for every selected-sample read during a scan. -/
theorem profile_scanAux_word_potential (hs : (∑ j, (s j).val) ≤ n) (gen : Generator ω)
    (check : (z : Fin (2 ^ n)) →
      {x : (ω.subdomain 0).toFinset // x = initialQuery z} →
      OracleComp (InstructionSpec s o α)
        {b : Bool // b = true ↔ z ∈ acceptingQueries s hs o α})
    (W : ℕ) (hcheck : ∀ z x, (profile s o α (check z x)).2 (.inr .wordRead) ≤ W)
    {D : ℕ} (xs : List (Fin (2 ^ n))) (state : Selection s o D) :
    (profile s o α (scanAux s o α hs gen check xs state)).2 (.inr .wordRead) +
      state.selected.length ≤ xs.length * W +
        (profile s o α (scanAux s o α hs gen check xs state)).1.val.selected.length := by
  induction xs generalizing state with
  | nil => simp [scanAux, embedArithmeticCost]
  | cons z zs ih =>
    let x := (profile s o α (generateInitialQuery s o α gen z)).1
    let b := (profile s o α (check z x)).1
    have hc := hcheck z x
    by_cases hb : b.val = true
    · let next := (profile s o α (selectSample s o α state z x)).1
      have hr := ih next.val
      have hp := profile_selectSample_word_potential s o α state z x
      simp only [scanAux, profile_bind, profile_liftComp_arithmetic,
        profileArithmetic_tick, Pi.add_apply, embedArithmeticCost, Sum.elim_inr,
        zero_add, profile_generateInitialQuery_word]
      dsimp only [b, x] at hb hc
      simp only [hb, dite_true, profile_bind, profile_pure, Pi.add_apply, add_zero]
      dsimp only [next, x] at hr hp
      simp only [List.length_cons, Nat.add_mul, one_mul]
      omega
    · have hr := ih state
      simp only [scanAux, profile_bind, profile_liftComp_arithmetic,
        profileArithmetic_tick, Pi.add_apply, embedArithmeticCost, Sum.elim_inr,
        zero_add, profile_generateInitialQuery_word]
      dsimp only [b, x] at hb hc
      simp only [hb, Bool.false_eq_true, dite_false, profile_bind, profile_pure, add_zero]
      simp only [List.length_cons, Nat.add_mul, one_mul]
      omega

/-- A full scan adds at most the sample-cache capacity to its local-check word reads. -/
theorem profile_scan_word_le (hs : (∑ j, (s j).val) ≤ n) (gen : Generator ω)
    (check : (z : Fin (2 ^ n)) →
      {x : (ω.subdomain 0).toFinset // x = initialQuery z} →
      OracleComp (InstructionSpec s o α)
        {b : Bool // b = true ↔ z ∈ acceptingQueries s hs o α})
    (W : ℕ) (hcheck : ∀ z x, (profile s o α (check z x)).2 (.inr .wordRead) ≤ W)
    (D : ℕ) :
    (profile s o α (scan s o α hs gen check D)).2 (.inr .wordRead) ≤ 2 ^ n * W + D := by
  have h := profile_scanAux_word_potential s o α hs gen check W hcheck
    (List.finRange (2 ^ n)) (emptySelection s o D)
  have hcap := (profile s o α (scanAux s o α hs gen check
    (List.finRange (2 ^ n)) (emptySelection s o D))).1.val.selected_le
  simpa [scan, profile_bind, emptySelection] using h.trans (by
    simpa using Nat.add_le_add_left hcap (2 ^ n * W))

end Fri.Spec.Extractor
