/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.ListDecodability

/-!
# A Johnson-type counting bound from pairwise agreement
The counting argument behind the Johnson bound uses nothing about the code beyond a uniform
bound on the agreement of two distinct codewords: if any two distinct codewords of `C ⊆ ι → A`
agree in at most `s² · |ι|` positions, then at most `1 / (2ηs)` codewords lie within relative
distance `1 - s - η` of any word.
This is the alphabet-agnostic core of `ReedSolomon.card_le_of_subset_closeCodewords`, and is what
lets the Reed–Solomon list-decoding bound be transported to interleaved Reed–Solomon codes, whose
alphabet is `Fin s → F`.
-/

namespace Code

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι] {A : Type*} [DecidableEq A]

/-- **Johnson-type counting bound.** If distinct codewords of `C` agree in at most `s² · |ι|`
positions, then any finite set of codewords within relative distance `1 - s - η` of a word `y`
has at most `1 / (2ηs)` elements. -/
theorem card_le_of_pairwise_agree_le {C : Set (ι → A)} {s η : ℝ} (hs : 0 < s) (hη : 0 < η)
    (hpair : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → (agree c c' : ℝ) ≤ s ^ 2 * (Fintype.card ι : ℝ))
    (y : ι → A) (T : Finset (ι → A))
    (hT : ∀ c ∈ T, c ∈ closeCodewordsRel C y (1 - s - η)) :
    (T.card : ℝ) ≤ 1 / (2 * η * s) := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set L : ℝ := (T.card : ℝ) with hL
  have hL0 : 0 ≤ L := by positivity
  -- lower bound on the agreement of each element of `T` with `y`
  have hclose : ∀ c ∈ T, (s + η) * n ≤ (agree c y : ℝ) := by
    intro c hc
    have hball := (mem_closeCodewordsRel_iff.mp (hT c hc)).2
    rw [relHammingDist_coe, div_le_iff₀ hnpos] at hball
    have hsum : (agree c y : ℝ) + (hammingDist c y : ℝ) = n := by
      rw [hn]
      exact_mod_cast congrArg (fun k : ℕ ↦ (k : ℝ)) agree_add_hammingDist
    have hcomm : (hammingDist y c : ℝ) = (hammingDist c y : ℝ) := by rw [hammingDist_comm]
    nlinarith [hball, hsum, hcomm]
  -- the sum of the agreements with `y`
  have hB : L * ((s + η) * n) ≤ ∑ c ∈ T, (agree c y : ℝ) := by
    calc L * ((s + η) * n) = ∑ _c ∈ T, ((s + η) * n) := by
          rw [Finset.sum_const, nsmul_eq_mul, hL]
      _ ≤ ∑ c ∈ T, (agree c y : ℝ) := Finset.sum_le_sum hclose
  -- the sum of all pairwise agreements
  have hA : ∑ c ∈ T, ∑ c' ∈ T, (agree c c' : ℝ) ≤ L * (n + (L - 1) * (s ^ 2 * n)) := by
    have hrow : ∀ c ∈ T, ∑ c' ∈ T, (agree c c' : ℝ) ≤ n + (L - 1) * (s ^ 2 * n) := by
      intro c hc
      have hsplit : ∑ c' ∈ T, (agree c c' : ℝ) =
          (agree c c : ℝ) + ∑ c' ∈ T.erase c, (agree c c' : ℝ) :=
        (Finset.add_sum_erase T (fun c' ↦ (agree c c' : ℝ)) hc).symm
      have herase : ∑ c' ∈ T.erase c, (agree c c' : ℝ) ≤ (L - 1) * (s ^ 2 * n) := by
        have hb : ∀ c' ∈ T.erase c, (agree c c' : ℝ) ≤ s ^ 2 * n := by
          intro c' hc'
          exact hpair c (mem_closeCodewordsRel_iff.mp (hT c hc)).1 c'
            (mem_closeCodewordsRel_iff.mp (hT c' (Finset.mem_of_mem_erase hc'))).1
            (Ne.symm (Finset.ne_of_mem_erase hc'))
        have hcard := Finset.sum_le_card_nsmul (T.erase c) (fun c' ↦ (agree c c' : ℝ)) _ hb
        rw [nsmul_eq_mul] at hcard
        have hcarderase : ((T.erase c).card : ℝ) = L - 1 := by
          rw [Finset.card_erase_of_mem hc, hL]
          have h1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨c, hc⟩
          push_cast [Nat.cast_sub h1]
          ring
        rwa [hcarderase] at hcard
      have hdiag : (agree c c : ℝ) = n := by rw [agree_self, hn]
      rw [hsplit, hdiag]
      linarith
    calc ∑ c ∈ T, ∑ c' ∈ T, (agree c c' : ℝ)
        ≤ ∑ _c ∈ T, (n + (L - 1) * (s ^ 2 * n)) := Finset.sum_le_sum hrow
      _ = L * (n + (L - 1) * (s ^ 2 * n)) := by rw [Finset.sum_const, nsmul_eq_mul, hL]
  -- Cauchy–Schwarz
  have hCS := sq_sum_agree_le (T := T) (u := y)
  rw [← hn] at hCS
  -- combine
  rcases eq_or_lt_of_le hL0 with hL0' | hLpos
  · rw [← hL0']
    positivity
  have hBnn : 0 ≤ L * ((s + η) * n) := by positivity
  have hsq : (L * ((s + η) * n)) ^ 2 ≤ (∑ c ∈ T, (agree c y : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hBnn hB 2
  have hkey : (L * ((s + η) * n)) ^ 2 ≤ n * (L * (n + (L - 1) * (s ^ 2 * n))) := by
    refine hsq.trans (hCS.trans ?_)
    exact mul_le_mul_of_nonneg_left hA (le_of_lt hnpos)
  have hdiv : L ^ 2 * (s + η) ^ 2 ≤ L * (1 + (L - 1) * s ^ 2) := by
    have hn2 : 0 < n ^ 2 := by positivity
    nlinarith [hkey, hn2]
  have hstep : L * (L * (2 * s * η + η ^ 2)) ≤ L * (1 - s ^ 2) := by nlinarith [hdiv]
  have hstep2 : L * (2 * s * η + η ^ 2) ≤ 1 - s ^ 2 := le_of_mul_le_mul_left hstep hLpos
  have hfinal : L * (2 * η * s) ≤ 1 := by
    nlinarith [hstep2, mul_nonneg hL0 (sq_nonneg η), sq_nonneg s]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * η * s)]
  exact hfinal

end Code
