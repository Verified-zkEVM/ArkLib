/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Exact counting bounds from pairwise agreement

For a finite family of words over a finite index set of size `n`, where every word agrees with a
received word in at least `A` positions and distinct words agree in at most `r` positions, this
file proves three list-size bounds.

## Main statements

- `Code.card_mul_sq_minAgreement_sub_pairAgreement_le`: `|T| (A² - n r) ≤ n (n - r)`, the exact
  Cauchy–Schwarz form, for `r ≤ n`.
- `Code.card_le_one_of_pairwise_agree_le`: if `n + r < 2A`, the family has at most one word.
- `Code.card_mul_minAgreement_le_of_pairwise_agree_eq_zero`: if distinct words never agree,
  `|T| A ≤ n`.

Unlike the relative-radius bound `Code.card_le_of_pairwise_agree_le` in `AgreementBound`, the
first bound keeps the exact square, so it still gives integral bounds at boundary parameters. It
reuses `Code.sq_sum_agree_le`.

-/
@[expose] public section

namespace Code

open Finset

variable {index alphabet : Type*} [Fintype index] [DecidableEq alphabet]

/-- The exact Cauchy–Schwarz agreement estimate for a finite family of words:
`|T| (A² - n r) ≤ n (n - r)`.

The hypothesis `r ≤ n` is needed: for the empty family the left side is `0`, and the right side
`n (n - r)` is negative when `r > n`. -/
theorem card_mul_sq_minAgreement_sub_pairAgreement_le
    (received : index → alphabet) (words : Finset (index → alphabet))
    (minAgreement pairAgreement : ℕ)
    (hPairAgreement : pairAgreement ≤ Fintype.card index)
    (hClose : ∀ word ∈ words, minAgreement ≤ agree word received)
    (hPair : ∀ word ∈ words, ∀ word' ∈ words, word ≠ word' →
      agree word word' ≤ pairAgreement) :
    (words.card : ℝ) *
        ((minAgreement : ℝ) ^ 2 -
          (Fintype.card index : ℝ) * (pairAgreement : ℝ)) ≤
      (Fintype.card index : ℝ) *
        ((Fintype.card index : ℝ) - (pairAgreement : ℝ)) := by
  classical
  set n : ℝ := (Fintype.card index : ℝ) with hn
  set L : ℝ := (words.card : ℝ) with hL
  set A : ℝ := (minAgreement : ℝ) with hA
  set r : ℝ := (pairAgreement : ℝ) with hr
  have hn_nonneg : 0 ≤ n := by positivity
  have hL_nonneg : 0 ≤ L := by positivity
  have hr_le_n : r ≤ n := by
    dsimp [r, n]
    exact_mod_cast hPairAgreement
  have hsum_lower : L * A ≤ ∑ word ∈ words, (agree word received : ℝ) := by
    calc
      L * A = ∑ _word ∈ words, A := by
        rw [Finset.sum_const, nsmul_eq_mul, hL]
      _ ≤ ∑ word ∈ words, (agree word received : ℝ) := by
        exact Finset.sum_le_sum fun word hword => by
          dsimp [A]
          exact_mod_cast hClose word hword
  have hpairs_upper :
      ∑ word ∈ words, ∑ word' ∈ words, (agree word word' : ℝ) ≤
        L * (n + (L - 1) * r) := by
    have hrow : ∀ word ∈ words,
        ∑ word' ∈ words, (agree word word' : ℝ) ≤ n + (L - 1) * r := by
      intro word hword
      have hsplit : ∑ word' ∈ words, (agree word word' : ℝ) =
          (agree word word : ℝ) +
            ∑ word' ∈ words.erase word, (agree word word' : ℝ) :=
        (Finset.add_sum_erase words (fun word' => (agree word word' : ℝ)) hword).symm
      have herase :
          ∑ word' ∈ words.erase word, (agree word word' : ℝ) ≤ (L - 1) * r := by
        have hterm : ∀ word' ∈ words.erase word, (agree word word' : ℝ) ≤ r := by
          intro word' hword'
          dsimp [r]
          exact_mod_cast hPair word hword word' (Finset.mem_of_mem_erase hword')
            (Ne.symm (Finset.ne_of_mem_erase hword'))
        have hcard := Finset.sum_le_card_nsmul (words.erase word)
          (fun word' => (agree word word' : ℝ)) r hterm
        rw [nsmul_eq_mul] at hcard
        have hcard_erase : ((words.erase word).card : ℝ) = L - 1 := by
          rw [Finset.card_erase_of_mem hword, hL]
          have hone : 1 ≤ words.card := Finset.card_pos.mpr ⟨word, hword⟩
          push_cast [Nat.cast_sub hone]
          ring
        rwa [hcard_erase] at hcard
      have hdiag : (agree word word : ℝ) = n := by rw [agree_self, hn]
      rw [hsplit, hdiag]
      linarith
    calc
      ∑ word ∈ words, ∑ word' ∈ words, (agree word word' : ℝ) ≤
          ∑ _word ∈ words, (n + (L - 1) * r) := Finset.sum_le_sum hrow
      _ = L * (n + (L - 1) * r) := by
        rw [Finset.sum_const, nsmul_eq_mul, hL]
  have hCS := sq_sum_agree_le (T := words) (u := received)
  rw [← hn] at hCS
  rcases eq_or_lt_of_le hL_nonneg with hL_zero | hL_pos
  · rw [← hL_zero]
    simpa using mul_nonneg hn_nonneg (sub_nonneg.mpr hr_le_n)
  · have hLA_nonneg : 0 ≤ L * A := by positivity
    have hsquare : (L * A) ^ 2 ≤
        (∑ word ∈ words, (agree word received : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hLA_nonneg hsum_lower 2
    have hkey : (L * A) ^ 2 ≤ n * (L * (n + (L - 1) * r)) := by
      exact hsquare.trans (hCS.trans (mul_le_mul_of_nonneg_left hpairs_upper hn_nonneg))
    nlinarith

/-- If `n + r < 2A`, the family contains at most one word. Two words each agreeing with the
received word in `A` positions agree with each other in at least `2A - n > r` positions, which
the pairwise bound forbids. -/
theorem card_le_one_of_pairwise_agree_le
    (received : index → alphabet) (words : Finset (index → alphabet))
    (minAgreement pairAgreement : ℕ)
    (hThreshold : Fintype.card index + pairAgreement < 2 * minAgreement)
    (hClose : ∀ word ∈ words, minAgreement ≤ agree word received)
    (hPair : ∀ word ∈ words, ∀ word' ∈ words, word ≠ word' →
      agree word word' ≤ pairAgreement) :
    words.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro word hword word' hword'
  by_contra hne
  have hclose_word := hClose word hword
  have hclose_word' := hClose word' hword'
  have hAgreement_le_card : minAgreement ≤ Fintype.card index :=
    hclose_word.trans Code.agree_le_card
  have hdist_word : hammingDist word received ≤ Fintype.card index - minAgreement := by
    have hsum := agree_add_hammingDist (u := word) (v := received)
    omega
  have hdist_word' : hammingDist received word' ≤ Fintype.card index - minAgreement := by
    have hsum := agree_add_hammingDist (u := word') (v := received)
    rw [hammingDist_comm received word']
    omega
  have hdist_pair : hammingDist word word' ≤ 2 * (Fintype.card index - minAgreement) :=
    (hammingDist_triangle word received word').trans (by omega)
  have hagree_pair := agree_add_hammingDist (u := word) (v := word')
  have hagree_pair_lower :
      2 * minAgreement ≤ Fintype.card index + agree word word' := by
    omega
  have hpair := hPair word hword word' hword' hne
  omega

/-- If distinct words never agree, their agreement sets with a received word are disjoint.
Thus the total required agreements cannot exceed the number of positions. -/
theorem card_mul_minAgreement_le_of_pairwise_agree_eq_zero
    (received : index → alphabet) (words : Finset (index → alphabet)) (minAgreement : ℕ)
    (hClose : ∀ word ∈ words, minAgreement ≤ agree word received)
    (hPair : ∀ word ∈ words, ∀ word' ∈ words, word ≠ word' → agree word word' = 0) :
    words.card * minAgreement ≤ Fintype.card index := by
  classical
  have hposition (i : index) : (words.filter fun word => word i = received i).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro word hw word' hw'
    obtain ⟨hw, hi⟩ := Finset.mem_filter.mp hw
    obtain ⟨hw', hi'⟩ := Finset.mem_filter.mp hw'
    by_contra hne
    have hz := hPair word hw word' hw' hne
    have hp : 0 < agree word word' := Finset.card_pos.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.trans hi'.symm⟩⟩
    omega
  calc
    words.card * minAgreement = ∑ _word ∈ words, minAgreement := by simp
    _ ≤ ∑ word ∈ words, agree word received := Finset.sum_le_sum hClose
    _ = ∑ i : index, (words.filter fun word => word i = received i).card := by
      simp only [agree, Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _i : index, 1 := Finset.sum_le_sum fun i _ => hposition i
    _ = Fintype.card index := by simp

end Code
