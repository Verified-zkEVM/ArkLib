/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ListDecodability.PairAgreementBound

/-!
# Pairwise-agreement list bound acceptance tests

Concrete families of words in `Fin 3 → Bool`, and a case showing that `r ≤ n` is needed in the
Cauchy–Schwarz bound.
-/

namespace Code

/-- The four words of `Fin 2 → Bool`, with received word `![false, false]`, `A = 0`, `r = 1`:
the bound reads `4 · (0 - 2) ≤ 2 · 1`. -/
example :
    ((Finset.univ : Finset (Fin 2 → Bool)).card : ℝ) *
        (((0 : ℕ) : ℝ) ^ 2 - (Fintype.card (Fin 2) : ℝ) * ((1 : ℕ) : ℝ)) ≤
      (Fintype.card (Fin 2) : ℝ) * ((Fintype.card (Fin 2) : ℝ) - ((1 : ℕ) : ℝ)) :=
  card_mul_sq_minAgreement_sub_pairAgreement_le ![false, false] Finset.univ 0 1
    (by simp) (fun _ _ => Nat.zero_le _) (by decide)

/-- With `n = 3`, `A = 3`, `r = 1`, the `n + r < 2A` bound gives at most one word: only the
received word itself agrees everywhere. -/
example (words : Finset (Fin 3 → Bool))
    (hClose : ∀ w ∈ words, 3 ≤ agree w ![true, false, true])
    (hPair : ∀ w ∈ words, ∀ w' ∈ words, w ≠ w' → agree w w' ≤ 1) :
    words.card ≤ 1 :=
  card_le_one_of_pairwise_agree_le ![true, false, true] words 3 1 (by simp) hClose hPair

/-- Two words that never agree, each agreeing with `![true, false, true]` in at least one place:
`2 · 1 ≤ 3`. -/
example :
    ({![true, true, true], ![false, false, false]} : Finset (Fin 3 → Bool)).card * 1 ≤
      Fintype.card (Fin 3) :=
  card_mul_minAgreement_le_of_pairwise_agree_eq_zero ![true, false, true] _ 1
    (by decide) (by decide)

/-- `pairAgreement ≤ n` is needed: for the empty family and `r = n + 1 = 4` the conclusion reads
`0 ≤ 3 · (3 - 4)`, which is false. -/
example : ¬ (((∅ : Finset (Fin 3 → Bool)).card : ℝ) *
        (((0 : ℕ) : ℝ) ^ 2 - (Fintype.card (Fin 3) : ℝ) * ((4 : ℕ) : ℝ)) ≤
      (Fintype.card (Fin 3) : ℝ) * ((Fintype.card (Fin 3) : ℝ) - ((4 : ℕ) : ℝ))) := by
  simp
  norm_num

end Code
