/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Folding
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for folding many words with equal-degree combiners -/

open Polynomial ReedSolomon
open scoped Finset

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The whole field `F₅` as the evaluation domain. -/
private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

-- One round folds the paper's rows `f₁, f₂` into `f₂ + (α + β x)(f₁ + θ f₂)`.
-- With zero-based rows these are `f 0` and `f 1`.
example {F ι : Type*} [Field F] (domain : ι ↪ F) (c : Fin 1 → F × F × F)
    (f : Fin (2 ^ 1) → ι → F) :
    foldWords domain 1 c f = equalDegreeWord domain (f 0) (f 1) (c 0).1 (c 0).2.1 (c 0).2.2 :=
  rfl

-- With one round, a bad folding is an exceptional pair for the single round.
example {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] (domain : ι ↪ F) (d A : ℕ)
    (c : Fin 1 → F × F × F) (f : Fin (2 ^ 1) → ι → F) :
    IsFoldingExceptional domain d A 1 c f ↔
      ∃ P, IsInterleavedEqualDegreeExceptional domain (evenRows f) (oddRows f) (d + 1) A 1
        (c 0).1 (c 0).2.1 (c 0).2.2 P := by
  simp [IsFoldingExceptional]

-- With one round, the polynomial fold is the equal-degree combination of `P 0` and `P 1`.
example {F : Type*} [Field F] (c : Fin 1 → F × F × F) (P : Fin (2 ^ 1) → F[X]) :
    foldPolynomials 1 c P =
      P 1 + affineMultiplier (c 0).2.1 (c 0).2.2 * (P 0 + C (c 0).1 * P 1) :=
  rfl

-- Two rounds with `θ = 0`, `α = 1`, `β = 0` add the four rows.
example (W : Fin (2 ^ 2) → (ZMod 5)[X]) :
    foldPolynomials 2 ![(0, 1, 0), (0, 1, 0)] W = W 0 + W 1 + W 2 + W 3 := by
  simp only [foldPolynomials, foldRoundPolynomials, evenRows, oddRows, affineMultiplier]
  simp [Fin.tail]
  ring_nf

-- Two rounds with `θ = 1`, `α = 2`, `β = 0` on the words `f k = k`.
-- The first round gives `f₁ + 2 (f₀ + f₁) = 3` and `f₃ + 2 (f₂ + f₃) = 3 + 2 · 5 = 3` in `𝔽₅`.
-- The second round gives `3 + 2 (3 + 3) = 0`.
example : foldWords fullDomain 2 ![(1, 2, 0), (1, 2, 0)] (fun k _ ↦ (k : ZMod 5)) = 0 := by
  funext x
  simp only [Nat.reducePow, Pi.zero_apply]
  revert x
  decide

-- The zero words are never bad for one round at threshold `2` on `𝔽₅` from degree `0`.
-- A candidate of degree at most one with two zeros vanishes, so zero witnesses lose nothing.
private theorem zero_not_isFoldingExceptional (c : Fin 1 → ZMod 5 × ZMod 5 × ZMod 5) :
    ¬ IsFoldingExceptional fullDomain 0 2 1 c 0 := by
  simp only [IsFoldingExceptional, or_false]
  rintro ⟨P, hP, hA, hexc⟩
  have hzero (k : Fin (2 ^ 0)) : P k = 0 := by
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hA
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (P k) S (fun x hx ↦ ?_) ?_
    · have := (mem_interleavedEqualDegreeAgreementSet ..).mp (hS hx) k
      simpa [equalDegreeWord, evenRows, oddRows, fullDomain] using this
    · rw [hcard]
      exact (natDegree_le_iff_degree_le.mpr (hP k)).trans_lt (by norm_num)
  have := hexc 0 0 (fun _ ↦ by simp) (fun _ ↦ by simp)
    (fun k ↦ by simp [hzero k])
  simp [interleavedEqualDegreeAgreementLoss, evenRows, oddRows] at this

-- The deterministic guarantee applies: the zero candidate has the zero witnesses.
example (c : Fin 1 → ZMod 5 × ZMod 5 × ZMod 5) :
    ∃ W : Fin (2 ^ 1) → (ZMod 5)[X], (∀ k, (W k).degree ≤ (0 : ℕ)) ∧
      foldPolynomials 1 c W = 0 ∧
      #{i ∈ Finset.univ | ∃ k, (W k).eval (fullDomain i) ≠ (0 : Fin (2 ^ 1) → ZMod 5 → ZMod 5) k i}
        ≤ 1 :=
  exists_foldPolynomials_eq_of_not_isFoldingExceptional fullDomain
    (zero_not_isFoldingExceptional c) (by simp) (fun i _ ↦ by
      simp [foldWords, foldRoundWords, equalDegreeWord, evenRows, oddRows])
    (by simp [ZMod.card])

-- A caller may supply its own decidable equality on the field.
example {F ι : Type*} [Field F] [Fintype F] [inst : DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (r d A : ℕ) :
    @foldingMcaError F _ inst ι _ _ domain r d A ≤ 1 :=
  foldingMcaError_le_one domain r d A

-- One round with error `ε` gives the folding bound `ε`.
example {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι] (domain : ι ↪ F)
    (d A : ℕ) :
    foldingMcaError domain 1 d A ≤ interleavedEqualDegreeMcaError domain 1 (d + 1) A 1 := by
  simpa using foldingMcaError_le_mul domain (r := 1) (d := d) (A := A)
    (ε := interleavedEqualDegreeMcaError domain 1 (d + 1) A 1) fun j hj ↦ by
      obtain rfl : j = 0 := by omega
      exact le_rfl

-- A sequential union bound on pairs of challenges in `Fin 2`.
example : #{c : Fin 2 → Fin 2 | c 0 = 0 ∨ Fin.tail c 0 = 0} ≤ 1 * 2 + 2 :=
  (Fin.card_filter_or_tail_le (fun a : Fin 2 ↦ a = 0) (fun _ c ↦ c 0 = 0)).trans (by decide)

/-- info: 'ReedSolomon.exists_foldPolynomials_eq_of_not_isFoldingExceptional' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_foldPolynomials_eq_of_not_isFoldingExceptional

/-- info: 'ReedSolomon.foldingMcaError_le_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.foldingMcaError_le_mul

/-- info: 'ReedSolomon.le_foldingMcaError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.le_foldingMcaError

/-- info: 'ReedSolomon.foldingMcaError_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.foldingMcaError_le_one

/-- info: 'ReedSolomon.evenRows_interleaveRows' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.evenRows_interleaveRows

/-- info: 'ReedSolomon.oddRows_interleaveRows' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.oddRows_interleaveRows

/-- info: 'ReedSolomon.exists_eq_evenRows_or_eq_oddRows' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_eq_evenRows_or_eq_oddRows

/-- info: 'Fin.card_filter_or_tail_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fin.card_filter_or_tail_le
