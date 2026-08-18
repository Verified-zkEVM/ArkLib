/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The Johnson-type list-decoding bound for Reed–Solomon codes

  This file proves that the Reed–Solomon code
  `RS[F, L, m]` of rate `ρ` is `(1 - √ρ - η, 1/(2η√ρ))`-list decodable for every `η > 0`
  (`ReedSolomon.listDecodable_reedSolomon`) which appears as theorem 4.3
  in [ACFY24].
  The bound is independent of the size of `F`.

## References

  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]

-/

namespace ReedSolomon

open Finset ReedSolomon

variable {ι F : Type*} [Fintype ι] [Field F]

/-- The main counting estimate: any finite set of codewords within relative distance
`1 - √ρ - η` of a word `y` has at most `1/(2η√ρ)` elements. -/
lemma card_le_of_subset_closeCodewords [Nonempty ι] (domain : ι ↪ F) {m : ℕ} (hm : 0 < m)
    {η : ℝ} (hη : 0 < η) (y : ι → F) (T : Finset (ι → F))
    (hT : ∀ c ∈ T, c ∈ Code.closeCodewordsRel (ReedSolomon.code domain m : Set (ι → F)) y
      (1 - (ReedSolomon.sqrtRate m domain : ℝ) - η)) :
    (T.card : ℝ) ≤ 1 / (2 * η * (ReedSolomon.sqrtRate m domain : ℝ)) := by
  classical
  set s : ℝ := (ReedSolomon.sqrtRate m domain : ℝ) with hs
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast hcard
  have hspos : 0 < s := sqrtRate_pos hm (domain := domain)
  have hs1 : s ^ 2 ≤ 1 := sqrtRate_sq_le_one m domain
  set L : ℝ := (T.card : ℝ) with hL
  have hL0 : 0 ≤ L := by positivity
  -- lower bound on the agreement of each element of `T` with `y`
  have hclose : ∀ c ∈ T, (s + η) * n ≤ (Code.agree c y : ℝ) := by
    intro c hc
    have hball := (hT c hc).2
    simp only [Code.mem_relHammingBall_iff, Code.relHammingDist_coe] at hball
    rw [div_le_iff₀ hnpos] at hball
    have hsum : (Code.agree c y : ℝ) + (hammingDist c y : ℝ) = n := by
      rw [hn]
      exact_mod_cast congrArg (fun k : ℕ ↦ (k : ℝ)) Code.agree_add_hammingDist
    have hcomm : (hammingDist y c : ℝ) = (hammingDist c y : ℝ) := by
      rw [hammingDist_comm]
    grind
  -- upper bound on the pairwise agreements inside `T`
  have hpair : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → (Code.agree c c' : ℝ) ≤ s ^ 2 * n := by
    intro c hc c' hc' hne
    have h1 : Code.agree c c' ≤ min m (Fintype.card ι) :=
      le_min (le_of_lt
        (agree_lt_of_mem_code (hT c hc).1 (hT c' hc').1 hne)) Code.agree_le_card
    have h2 : (Code.agree c c' : ℝ) ≤ (min m (Fintype.card ι) : ℝ) := by exact_mod_cast h1
    rw [sqrtRate_sq]
    rw [div_mul_cancel₀ _ (ne_of_gt hnpos)]
    exact h2
  -- the sum of the agreements with `y`
  have hB : L * ((s + η) * n) ≤ ∑ c ∈ T, (Code.agree c y : ℝ) := by
    calc L * ((s + η) * n) = ∑ _c ∈ T, ((s + η) * n) := by
          rw [Finset.sum_const, nsmul_eq_mul, hL]
      _ ≤ ∑ c ∈ T, (Code.agree c y : ℝ) := Finset.sum_le_sum hclose
  -- the sum of all pairwise agreements
  have hA :
      ∑ c ∈ T, ∑ c' ∈ T, (Code.agree c c' : ℝ) ≤
        L * (n + (L - 1) * (s ^ 2 * n)) := by
    have hrow :
        ∀ c ∈ T, ∑ c' ∈ T, (Code.agree c c' : ℝ) ≤
          n + (L - 1) * (s ^ 2 * n) := by
      intro c hc
      have hsplit : ∑ c' ∈ T, (Code.agree c c' : ℝ) =
        (Code.agree c c : ℝ) + ∑ c' ∈ T.erase c, (Code.agree c c' : ℝ) :=
        (Finset.add_sum_erase T (fun c' ↦ (Code.agree c c' : ℝ)) hc).symm
      have herase : ∑ c' ∈ T.erase c, (Code.agree c c' : ℝ) ≤ (L - 1) * (s ^ 2 * n) := by
        have hb : ∀ c' ∈ T.erase c, (Code.agree c c' : ℝ) ≤ s ^ 2 * n := by
          intro c' hc'
          exact hpair c hc c' (Finset.mem_of_mem_erase hc') (Ne.symm (Finset.ne_of_mem_erase hc'))
        have := Finset.sum_le_card_nsmul (T.erase c) (fun c' ↦ (Code.agree c c' : ℝ)) _ hb
        rw [nsmul_eq_mul] at this
        have hcarderase : ((T.erase c).card : ℝ) = L - 1 := by
          rw [Finset.card_erase_of_mem hc, hL]
          have : 1 ≤ T.card := Finset.card_pos.mpr ⟨c, hc⟩
          push_cast [Nat.cast_sub this]
          ring
        rwa [hcarderase] at this
      have hdiag : (Code.agree c c : ℝ) = n := by
        rw [Code.agree_self, hn]
      rw [hsplit, hdiag]
      linarith
    calc ∑ c ∈ T, ∑ c' ∈ T, (Code.agree c c' : ℝ)
        ≤ ∑ _c ∈ T, (n + (L - 1) * (s ^ 2 * n)) := Finset.sum_le_sum hrow
      _ = L * (n + (L - 1) * (s ^ 2 * n)) := by rw [Finset.sum_const, nsmul_eq_mul, hL]
  -- Cauchy–Schwarz
  have hCS := Code.sq_sum_agree_le (T := T) (u := y)
  rw [←hn] at hCS
  -- combine
  rcases eq_or_lt_of_le hL0 with hL0' | hLpos
  · rw [←hL0']
    positivity
  have hBnn : 0 ≤ L * ((s + η) * n) := by positivity
  have hsq : (L * ((s + η) * n)) ^ 2 ≤ (∑ c ∈ T, (Code.agree c y : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hBnn hB 2
  have hkey : (L * ((s + η) * n)) ^ 2 ≤ n * (L * (n + (L - 1) * (s ^ 2 * n))) := by
    refine hsq.trans (hCS.trans ?_)
    exact mul_le_mul_of_nonneg_left hA (le_of_lt hnpos)
  have hdiv : L ^ 2 * (s + η) ^ 2 ≤ L * (1 + (L - 1) * s ^ 2) := by
    have hn2 : 0 < n ^ 2 := by positivity
    nlinarith [hkey, hn2]
  have hstep : L * (L * (2 * s * η + η ^ 2)) ≤ L * (1 - s ^ 2) := by nlinarith [hdiv]
  have hstep2 : L * (2 * s * η + η ^ 2) ≤ 1 - s ^ 2 :=
    le_of_mul_le_mul_left hstep hLpos
  have hfinal : L * (2 * η * s) ≤ 1 := by
    nlinarith [hstep2, mul_nonneg hL0 (sq_nonneg η), sq_nonneg s]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * η * s)]
  exact hfinal

open NNReal in
/-- **Theorem 4.3.** The Reed–Solomon code `RS[F, domain, m]` of rate `ρ` is
`(1 - √ρ - η, 1/(2η√ρ))`-list decodable, for every `η > 0`. -/
theorem listDecodable_reedSolomon [Nonempty ι] (domain : ι ↪ F) {m : ℕ} (hm : 0 < m)
    {η : ℝ≥0} (hη : 0 < η) :
    Code.IsListDecodable (ReedSolomon.code domain m : Set (ι → F))
      (1 - (ReedSolomon.sqrtRate m domain) - η)
      (1 / (2 * η * (ReedSolomon.sqrtRate m domain))) := by
  rw [Code.isListDecodable_iff_forall_finset_card_le]
  intro y T hT
  exact card_le_of_subset_closeCodewords domain hm hη y T fun c hc ↦ hT _ hc

end ReedSolomon
