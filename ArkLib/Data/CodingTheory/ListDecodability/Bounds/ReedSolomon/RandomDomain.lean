/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.ReedSolomon.RankLoss
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Reed–Solomon codes at random distinct evaluation points

Let `F` be a finite field with `q` elements, `2 ≤ ℓ`, `0 < η` and `q ≥ n + k * 2 ^ (10ℓ/η)`.
This file shows that at most a `2 ^ (-ℓ n)` fraction of the tuples `α : Fin n ↪ F` of pairwise
distinct evaluation points give a Reed–Solomon code of dimension `k` with more than `ℓ` codewords
within relative radius `ℓ / (ℓ + 1) * (1 - k / n - η)` of some word.

For such a tuple `α` there are `1 ≤ s ≤ ℓ` and a `(k + η n)`-weakly partition-connected
hypergraph `H` on `s + 1` vertices that is not rigid for degree `k` at `α`; emptying the edges
with one vertex keeps both properties, so `H` can be taken among the
`(2 ^ (s + 1) - (s + 1)) ^ n` hypergraphs with no such edge. Summing the rank-loss counts of
`RankLoss.lean` over these hypergraphs gives two bounds on the number of bad tuples: one from a
single minor, and one from certificates of length `r = ⌊η n / 2⌋`. The first is used when
`η n < 4`, the second when `η n ≥ 4`. Below relative radius `1 / n` every list has at most one
element, and for `k ≤ 1` the single-minor count is zero.

## Main statements

* `exists_isWeaklyPartitionConnected_not_isRigid_of_lt_Lambda`: a long list gives a weakly
  partition-connected hypergraph with no edge of one vertex at which the code is not rigid.
* `card_filter_lt_Lambda_le_two_pow_neg_mul`: at most `2 ^ (-ℓ n) * |Fin n ↪ F|` tuples give a list
  of more than `ℓ` codewords at relative radius `ℓ / (ℓ + 1) * (1 - k / n - η)`.

## References

* [Alrabiah, O., Guruswami, V., and Li, R., *Randomly punctured Reed-Solomon codes achieve
    list-decoding capacity over linear-sized fields*][AGL24]
-/

@[expose] public section

namespace ReedSolomon

open Finset Code

variable {F : Type*} [Field F] {n k ℓ : ℕ}

/-- There are `2 ^ m - m` subsets of `Fin m` with other than one element. -/
private theorem card_filter_card_ne_one (m : ℕ) :
    #{e : Finset (Fin m) | #e ≠ 1} = 2 ^ m - m := by
  have h1 : #{e : Finset (Fin m) | #e = 1} = m := by
    rw [← powerset_univ, ← powersetCard_eq_filter, card_powersetCard, card_univ, Fintype.card_fin,
      Nat.choose_one_right]
  have h2 := card_filter_add_card_filter_not (s := (univ : Finset (Finset (Fin m))))
    fun e ↦ #e = 1
  rw [h1, card_univ, Fintype.card_finset, Fintype.card_fin] at h2
  simp only [ne_eq]
  omega

open Classical in
/-- **A long list gives a rank-deficient hypergraph.** If the Reed–Solomon code of dimension `k`
on `α` has more than `ℓ` codewords within relative radius `ℓ / (ℓ + 1) * (1 - κ / n)` of a word,
then for some `1 ≤ s ≤ ℓ` there is a `κ`-weakly partition-connected hypergraph `H` on `s + 1`
vertices, with no edge of exactly one vertex, that is not rigid for degree `k` at `α`. -/
theorem exists_isWeaklyPartitionConnected_not_isRigid_of_lt_Lambda (α : Fin n ↪ F) (hℓ : 0 < ℓ)
    {κ : ℝ} (h : (ℓ : ℕ∞) <
      Lambda (code α k : Set (Fin n → F)) ((ℓ : ℝ) / (ℓ + 1) * (1 - κ / n))) :
    ∃ s ∈ Icc 1 ℓ, ∃ H : Fin n → Finset (Fin (s + 1)), (∀ i, #(H i) ≠ 1) ∧
      IsWeaklyPartitionConnected H κ ∧ ¬IsRigid H k α := by
  have h' : (ℓ : ℕ∞) < Lambda (code α k : Set (Fin n → F))
      ((ℓ : ℝ) / (ℓ + 1) * (1 - κ / Fintype.card (Fin n))) := by
    rwa [Fintype.card_fin]
  obtain ⟨y, s, hs1, hsℓ, c, hc, hwpc⟩ :=
    exists_isWeaklyPartitionConnected_agreement_of_lt_Lambda hℓ h'
  refine ⟨s, mem_Icc.2 ⟨hs1, hsℓ⟩,
    fun i ↦ if #({j | c j i = y i} : Finset (Fin (s + 1))) ≤ 1 then ∅
      else ({j | c j i = y i} : Finset (Fin (s + 1))), fun i ↦ ?_,
    (isWeaklyPartitionConnected_congr_of_card_le_one fun i ↦ ?_).1 hwpc, ?_⟩
  · dsimp only
    split_ifs with h1
    · simp
    · omega
  · split_ifs with h1
    · exact Or.inr ⟨h1, by simp⟩
    · exact Or.inl rfl
  · refine not_isRigid_of_mem_code (c := ⇑c) (fun j ↦ (mem_closeCodewordsRel_iff.1 (hc j)).1)
      ⟨0, Fin.last s, c.injective.ne
        (Fin.ext_iff.not.2 (by simp only [Fin.val_zero, Fin.val_last]; omega))⟩
      (fun i j hj j' hj' ↦ ?_)
    split_ifs at hj hj' with h1
    · simp at hj
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
      exact hj.trans hj'.symm

variable [Fintype F]

open Classical in
/-- **Union bound over hypergraphs.** The number of tuples `α : Fin n ↪ F` at which the
Reed–Solomon code of dimension `k` has more than `ℓ` codewords within relative radius
`ℓ / (ℓ + 1) * (1 - κ / n)` of a word is at most the sum, over `1 ≤ s ≤ ℓ` and over the
`κ`-weakly partition-connected hypergraphs `H` on `s + 1` vertices with no edge of one vertex, of
the number of tuples at which `H` is not rigid for degree `k`. -/
private theorem card_filter_lt_Lambda_le_sum (hℓ : 0 < ℓ) (κ : ℝ) :
    #{α : Fin n ↪ F | (ℓ : ℕ∞) <
        Lambda (code α k : Set (Fin n → F)) ((ℓ : ℝ) / (ℓ + 1) * (1 - κ / n))} ≤
      ∑ s ∈ Icc 1 ℓ, ∑ H ∈ Fintype.piFinset
          (fun _ : Fin n ↦ ({e | #e ≠ 1} : Finset (Finset (Fin (s + 1)))))
          with IsWeaklyPartitionConnected H κ,
        #{α : Fin n ↪ F | ¬IsRigid H k α} := by
  refine (card_le_card fun α hα ↦ ?_).trans (card_biUnion_le.trans
    (sum_le_sum fun s _ ↦ card_biUnion_le))
  obtain ⟨s, hs, H, hH1, hHw, hHr⟩ :=
    exists_isWeaklyPartitionConnected_not_isRigid_of_lt_Lambda α hℓ (mem_filter.1 hα).2
  exact mem_biUnion.2 ⟨s, hs, mem_biUnion.2 ⟨H, mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i ↦
    mem_filter.2 ⟨mem_univ _, hH1 i⟩, hHw⟩, mem_filter.2 ⟨mem_univ _, hHr⟩⟩⟩

/-- There are `(2 ^ (s + 1) - (s + 1)) ^ n` hypergraphs `Fin n → Finset (Fin (s + 1))` with no
edge of one vertex. -/
private theorem card_piFinset_card_ne_one (n s : ℕ) :
    #(Fintype.piFinset fun _ : Fin n ↦ ({e | #e ≠ 1} : Finset (Finset (Fin (s + 1))))) =
      (2 ^ (s + 1) - (s + 1)) ^ n := by
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, card_filter_card_ne_one]

open Classical in
/-- **Long lists from one minor.** If `k ≤ κ`, the number `N` of tuples `α : Fin n ↪ F` at which
the Reed–Solomon code of dimension `k` has more than `ℓ` codewords within relative radius
`ℓ / (ℓ + 1) * (1 - κ / n)` of a word satisfies
`N * (q - n + 1) ≤ n * (k - 1) * (∑ s ∈ [1, ℓ], s * (2 ^ (s + 1) - (s + 1)) ^ n) * |Fin n ↪ F|`. -/
private theorem card_filter_lt_Lambda_mul_le (hℓ : 0 < ℓ) {κ : ℝ} (hκ : (k : ℝ) ≤ κ) :
    #{α : Fin n ↪ F | (ℓ : ℕ∞) <
        Lambda (code α k : Set (Fin n → F)) ((ℓ : ℝ) / (ℓ + 1) * (1 - κ / n))} *
        (Fintype.card F - n + 1) ≤
      n * (k - 1) * (∑ s ∈ Icc 1 ℓ, s * (2 ^ (s + 1) - (s + 1)) ^ n) *
        Fintype.card (Fin n ↪ F) := by
  refine (Nat.mul_le_mul_right _ (card_filter_lt_Lambda_le_sum hℓ κ)).trans ?_
  rw [sum_mul, mul_sum, sum_mul]
  refine sum_le_sum fun s _ ↦ ?_
  rw [sum_mul]
  calc _ ≤ ∑ H ∈ Fintype.piFinset
          (fun _ : Fin n ↦ ({e | #e ≠ 1} : Finset (Finset (Fin (s + 1)))))
          with IsWeaklyPartitionConnected H κ, n * (s * (k - 1)) * Fintype.card (Fin n ↪ F) :=
        sum_le_sum fun H hH ↦ card_filter_not_isRigid_mul_le ((mem_filter.1 hH).2.mono hκ)
    _ ≤ (2 ^ (s + 1) - (s + 1)) ^ n * (n * (s * (k - 1)) * Fintype.card (Fin n ↪ F)) := by
        rw [sum_const, smul_eq_mul, ← card_piFinset_card_ne_one n s]
        exact Nat.mul_le_mul_right _ (card_filter_le _ _)
    _ = _ := by ring

open Classical in
/-- **Long lists from certificates.** If `k + 2 r ≤ κ`, the number `N` of tuples
`α : Fin n ↪ F` at which the Reed–Solomon code of dimension `k` has more than `ℓ` codewords
within relative radius `ℓ / (ℓ + 1) * (1 - κ / n)` of a word satisfies
`N * (q - n + 1) ^ r ≤ (∑ s ∈ [1, ℓ], (2 ^ (s + 1) - (s + 1)) ^ n * n.choose r * 2 ^ ((s + 1) r) *
s ^ r) * (k - 1) ^ r * |Fin n ↪ F|`. -/
private theorem card_filter_lt_Lambda_mul_pow_le (hℓ : 0 < ℓ) {κ : ℝ} {r : ℕ}
    (hκ : (k : ℝ) + 2 * r ≤ κ) :
    #{α : Fin n ↪ F | (ℓ : ℕ∞) <
        Lambda (code α k : Set (Fin n → F)) ((ℓ : ℝ) / (ℓ + 1) * (1 - κ / n))} *
        (Fintype.card F - n + 1) ^ r ≤
      (∑ s ∈ Icc 1 ℓ, (2 ^ (s + 1) - (s + 1)) ^ n * n.choose r * (2 ^ (s + 1)) ^ r * s ^ r) *
        (k - 1) ^ r * Fintype.card (Fin n ↪ F) := by
  refine (Nat.mul_le_mul_right _ (card_filter_lt_Lambda_le_sum hℓ κ)).trans ?_
  rw [sum_mul, sum_mul, sum_mul]
  refine sum_le_sum fun s _ ↦ ?_
  rw [sum_mul]
  calc _ ≤ ∑ H ∈ Fintype.piFinset
          (fun _ : Fin n ↦ ({e | #e ≠ 1} : Finset (Finset (Fin (s + 1)))))
          with IsWeaklyPartitionConnected H κ,
          n.choose r * (2 ^ (s + 1)) ^ r * (s * (k - 1)) ^ r * Fintype.card (Fin n ↪ F) :=
        sum_le_sum fun H hH ↦ card_filter_not_isRigid_mul_pow_le ((mem_filter.1 hH).2.mono hκ)
    _ ≤ (2 ^ (s + 1) - (s + 1)) ^ n *
          (n.choose r * (2 ^ (s + 1)) ^ r * (s * (k - 1)) ^ r * Fintype.card (Fin n ↪ F)) := by
        rw [sum_const, smul_eq_mul, ← card_piFinset_card_ne_one n s]
        exact Nat.mul_le_mul_right _ (card_filter_le _ _)
    _ = _ := by rw [mul_pow]; ring

/-- `2 * (2 ^ (s + 1) - (s + 1)) ≤ 2 ^ (s + 2) - (s + 2)`. -/
private theorem two_mul_two_pow_sub_le (s : ℕ) :
    2 * (2 ^ (s + 1) - (s + 1)) ≤ 2 ^ (s + 1 + 1) - (s + 1 + 1) := by
  have h1 : s + 1 < 2 ^ (s + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by ring
  omega

/-- The weighted count of hypergraphs is dominated by its last term:
`(2 ^ n - 1) * ∑ s ∈ [1, ℓ], s * a_s ^ n ≤ 2 ^ n * ℓ * a_ℓ ^ n` for `a_s = 2 ^ (s + 1) - (s + 1)`,
since `2 * a_s ≤ a_(s + 1)`. -/
private theorem two_pow_sub_one_mul_sum_le (n ℓ : ℕ) :
    (2 ^ n - 1) * ∑ s ∈ Icc 1 ℓ, s * (2 ^ (s + 1) - (s + 1)) ^ n ≤
      2 ^ n * ℓ * (2 ^ (ℓ + 1) - (ℓ + 1)) ^ n := by
  obtain ⟨d, hd⟩ : ∃ d, 2 ^ n = d + 1 := ⟨2 ^ n - 1, by have := @Nat.one_le_two_pow n; omega⟩
  rw [hd, Nat.add_sub_cancel]
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have h2 : (d + 1) * (2 ^ (ℓ + 1) - (ℓ + 1)) ^ n ≤ (2 ^ (ℓ + 1 + 1) - (ℓ + 1 + 1)) ^ n := by
      rw [← hd, ← mul_pow]
      exact Nat.pow_le_pow_left (two_mul_two_pow_sub_le ℓ) n
    rw [sum_Icc_succ_top (by omega : 1 ≤ ℓ + 1), mul_add]
    nlinarith [ih, Nat.mul_le_mul_left ℓ h2, Nat.zero_le ((2 ^ (ℓ + 1 + 1) - (ℓ + 1 + 1)) ^ n)]

/-- `2 ^ (2 n) ≤ 2 * (2 ^ n - 1) ^ 2` for `2 ≤ n`. -/
private theorem two_pow_two_mul_le (hn : 2 ≤ n) : 2 ^ (2 * n) ≤ 2 * (2 ^ n - 1) ^ 2 := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨u, hu⟩ : ∃ u, 2 ^ n = u + 4 := ⟨2 ^ n - 4, by omega⟩
  rw [pow_mul', hu, show u + 4 - 1 = u + 3 by omega]
  ring_nf
  omega

/-- For `2 ≤ ℓ` and `7 ≤ n`, with `a_ℓ = 2 ^ (ℓ + 1) - (ℓ + 1)`:
`(2 ^ n * n * ℓ * a_ℓ ^ n) ^ 2 ≤ (2 ^ n - 1) ^ 2 * 2 ^ (3 ℓ n)`. -/
private theorem sq_two_pow_mul_le (hℓ : 2 ≤ ℓ) (hn : 7 ≤ n) :
    (2 ^ n * n * ℓ * (2 ^ (ℓ + 1) - (ℓ + 1)) ^ n) ^ 2 ≤ (2 ^ n - 1) ^ 2 * 2 ^ (3 * ℓ * n) := by
  have ha : 2 ^ (2 * n) ≤ 2 * (2 ^ n - 1) ^ 2 := two_pow_two_mul_le (by omega)
  rcases (by omega : ℓ = 2 ∨ ℓ = 3 ∨ 4 ≤ ℓ) with rfl | rfl | hℓ4
  · have h : ∀ m, 7 ≤ m → 2 * m * 10 ^ m + 8 ^ m ≤ 16 ^ m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ m hm ih =>
        rw [pow_succ (10 : ℕ) m, pow_succ (8 : ℕ) m, pow_succ (16 : ℕ) m]
        nlinarith [ih, Nat.mul_le_mul_right (10 ^ m) hm, Nat.zero_le (10 ^ m), Nat.zero_le (8 ^ m)]
    have key : 2 ^ n * n * 2 * 5 ^ n ≤ (2 ^ n - 1) * 2 ^ (3 * n) := by
      have e1 : 2 ^ n * n * 2 * 5 ^ n = 2 * n * 10 ^ n := by
        rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
        ring
      have e2 : (2 ^ n - 1) * 2 ^ (3 * n) = 16 ^ n - 8 ^ n := by
        rw [Nat.sub_mul, one_mul, pow_mul, ← mul_pow]
        norm_num
      have := h n hn
      rw [e1, e2]
      omega
    calc (2 ^ n * n * 2 * (2 ^ (2 + 1) - (2 + 1)) ^ n) ^ 2 = (2 ^ n * n * 2 * 5 ^ n) ^ 2 := by
          norm_num
      _ ≤ ((2 ^ n - 1) * 2 ^ (3 * n)) ^ 2 := Nat.pow_le_pow_left key 2
      _ = (2 ^ n - 1) ^ 2 * 2 ^ (3 * 2 * n) := by ring
  · have h : ∀ m, 7 ≤ m → 18 * m ^ 2 * (3 ^ m) ^ 2 ≤ (2 ^ m) ^ 5 := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ m hm ih =>
        have h1 := Nat.mul_le_mul_right ((3 ^ m) ^ 2) hm
        have h2 := Nat.mul_le_mul_right (m * (3 ^ m) ^ 2) hm
        rw [pow_succ (3 : ℕ) m, pow_succ (2 : ℕ) m]
        nlinarith [ih, h1, h2]
    have e4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    have e12 : (2 ^ (3 + 1) - (3 + 1) : ℕ) ^ n = (2 ^ n) ^ 2 * 3 ^ n := by
      rw [show (2 ^ (3 + 1) - (3 + 1) : ℕ) = 4 * 3 by norm_num, mul_pow, e4]
    have e9 : (2 : ℕ) ^ (3 * 3 * n) = (2 ^ n) ^ 9 := by
      rw [← pow_mul]
      ring_nf
    rw [e12, e9]
    have hfin : 2 * (2 ^ n * n * 3 * ((2 ^ n) ^ 2 * 3 ^ n)) ^ 2 ≤
        2 * ((2 ^ n - 1) ^ 2 * (2 ^ n) ^ 9) := by
      calc 2 * (2 ^ n * n * 3 * ((2 ^ n) ^ 2 * 3 ^ n)) ^ 2 =
            18 * n ^ 2 * (3 ^ n) ^ 2 * (2 ^ n) ^ 6 := by ring
        _ ≤ (2 ^ n) ^ 5 * (2 ^ n) ^ 6 := Nat.mul_le_mul_right _ (h n hn)
        _ = 2 ^ (2 * n) * (2 ^ n) ^ 9 := by ring
        _ ≤ 2 * (2 ^ n - 1) ^ 2 * (2 ^ n) ^ 9 := Nat.mul_le_mul_right _ ha
        _ = 2 * ((2 ^ n - 1) ^ 2 * (2 ^ n) ^ 9) := by ring
    exact Nat.le_of_mul_le_mul_left hfin (by norm_num)
  · obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 4 := ⟨ℓ - 4, by omega⟩
    have h : ∀ m', 2 * n ^ 2 * (m' + 4) ^ 2 ≤ 2 ^ ((m' + 2) * n) := by
      intro m'
      induction m' with
      | zero =>
        have h32 : ∀ j, 7 ≤ j → 32 * j ^ 2 ≤ 4 ^ j := by
          intro j hj
          induction j, hj using Nat.le_induction with
          | base => norm_num
          | succ j hj ih =>
            rw [pow_succ (4 : ℕ) j]
            nlinarith [ih, Nat.mul_le_mul_right j hj]
        have e : (2 : ℕ) ^ ((0 + 2) * n) = 4 ^ n := by
          rw [zero_add, pow_mul]
          norm_num
        rw [e]
        nlinarith [h32 n hn]
      | succ m' ih =>
        have e : (2 : ℕ) ^ ((m' + 1 + 2) * n) = 2 ^ n * 2 ^ ((m' + 2) * n) := by
          rw [← pow_add]
          congr 1
          ring
        have h2 : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hq : (m' + 1 + 4) ^ 2 ≤ 2 * (m' + 4) ^ 2 := by
          ring_nf
          omega
        rw [e]
        calc 2 * n ^ 2 * (m' + 1 + 4) ^ 2 ≤ 2 * n ^ 2 * (2 * (m' + 4) ^ 2) :=
              Nat.mul_le_mul_left _ hq
          _ = 2 * (2 * n ^ 2 * (m' + 4) ^ 2) := by ring
          _ ≤ 2 ^ n * 2 ^ ((m' + 2) * n) := Nat.mul_le_mul h2 ih
    have hA : 2 ^ (m + 4 + 1) - (m + 4 + 1) ≤ 2 ^ (m + 4 + 1) := Nat.sub_le _ _
    have hfin : 2 * (2 ^ n * n * (m + 4) * (2 ^ (m + 4 + 1) - (m + 4 + 1)) ^ n) ^ 2 ≤
        2 * ((2 ^ n - 1) ^ 2 * 2 ^ (3 * (m + 4) * n)) := by
      calc _ ≤ 2 * (2 ^ n * n * (m + 4) * (2 ^ (m + 4 + 1)) ^ n) ^ 2 := by gcongr
        _ = 2 * n ^ 2 * (m + 4) ^ 2 * (2 ^ (2 * n) * ((2 ^ (m + 4 + 1)) ^ n) ^ 2) := by ring
        _ ≤ 2 ^ ((m + 2) * n) * (2 ^ (2 * n) * ((2 ^ (m + 4 + 1)) ^ n) ^ 2) :=
            Nat.mul_le_mul_right _ (h m)
        _ = 2 ^ (2 * n) * 2 ^ (3 * (m + 4) * n) := by
            simp only [← pow_mul, ← pow_add]
            congr 1
            ring
        _ ≤ 2 * (2 ^ n - 1) ^ 2 * 2 ^ (3 * (m + 4) * n) := Nat.mul_le_mul_right _ ha
        _ = 2 * ((2 ^ n - 1) ^ 2 * 2 ^ (3 * (m + 4) * n)) := by ring
    exact Nat.le_of_mul_le_mul_left hfin (by norm_num)

/-- For `2 ≤ ℓ` and `4 ≤ n`: `2 * n * ℓ ≤ 2 ^ ((ℓ - 1) n)`. -/
private theorem two_mul_mul_le_two_pow (hℓ : 2 ≤ ℓ) (hn : 4 ≤ n) :
    2 * n * ℓ ≤ 2 ^ ((ℓ - 1) * n) := by
  have h4 : 4 * n ≤ 2 ^ n := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [pow_succ]
      omega
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 2 := ⟨ℓ - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  induction m with
  | zero =>
    simp only [zero_add, one_mul]
    omega
  | succ m ih =>
    have e : (2 : ℕ) ^ ((m + 1 + 1) * n) = 2 ^ ((m + 1) * n) * 2 ^ n := by
      rw [← pow_add]
      congr 1
      ring
    have h2 := Nat.mul_le_mul_left (2 ^ ((m + 1) * n)) (show 2 ≤ 2 ^ n by omega)
    rw [e]
    nlinarith [ih (by omega), h2, Nat.zero_le (n * m)]

/-- The certificate estimate, with `b = 2 ^ (ℓ + 1) * ℓ`:
`ℓ ^ 3 * (2 ^ (ℓ + 1) * a_ℓ) ^ (3 n) * b ^ n ≤ 2 ^ (10 ℓ n) * b ^ 2`. -/
private theorem pow_mul_pow_mul_pow_le (hℓ : 2 ≤ ℓ) (hn : 1 ≤ n) :
    ℓ ^ 3 * (2 ^ (ℓ + 1) * (2 ^ (ℓ + 1) - (ℓ + 1))) ^ (3 * n) * (2 ^ (ℓ + 1) * ℓ) ^ n ≤
      2 ^ (10 * ℓ * n) * (2 ^ (ℓ + 1) * ℓ) ^ 2 := by
  rcases (by omega : ℓ = 2 ∨ 3 ≤ ℓ) with rfl | hℓ3
  · have e1 : (2 ^ (2 + 1) * (2 ^ (2 + 1) - (2 + 1)) : ℕ) = 40 := by norm_num
    have e2 : (2 ^ (2 + 1) * 2 : ℕ) = 16 := by norm_num
    rw [e1, e2]
    calc 2 ^ 3 * 40 ^ (3 * n) * 16 ^ n = 8 * (40 ^ 3 * 16) ^ n := by
          rw [mul_pow, pow_mul]
          ring
      _ ≤ 256 * (2 ^ 20) ^ n := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by norm_num) n)
      _ = 2 ^ (10 * 2 * n) * 16 ^ 2 := by
          rw [← pow_mul]
          ring
  · obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 3 := ⟨ℓ - 3, by omega⟩
    have hl : m + 3 ≤ 2 ^ (m + 2) := by
      have : m + 2 < 2 ^ (m + 2) := Nat.lt_two_pow_self
      omega
    have hA : 2 ^ (m + 3 + 1) - (m + 3 + 1) ≤ 2 ^ (m + 3 + 1) := Nat.sub_le _ _
    calc (m + 3) ^ 3 * (2 ^ (m + 3 + 1) * (2 ^ (m + 3 + 1) - (m + 3 + 1))) ^ (3 * n) *
          (2 ^ (m + 3 + 1) * (m + 3)) ^ n
        ≤ (2 ^ (m + 2)) ^ 3 * (2 ^ (m + 3 + 1) * 2 ^ (m + 3 + 1)) ^ (3 * n) *
          (2 ^ (m + 3 + 1) * 2 ^ (m + 2)) ^ n := by gcongr
      _ = 2 ^ (3 * m + 6 + (8 * m + 30) * n) := by
          simp only [← pow_mul, ← pow_add]
          congr 1
          ring
      _ ≤ 2 ^ (10 * (m + 3) * n + 2 * (m + 4)) :=
          Nat.pow_le_pow_right (by norm_num) (by nlinarith [Nat.mul_le_mul_left m hn])
      _ = 2 ^ (10 * (m + 3) * n) * (2 ^ (m + 3 + 1)) ^ 2 := by
          simp only [← pow_mul, ← pow_add]
          congr 1
          ring
      _ ≤ 2 ^ (10 * (m + 3) * n) * (2 ^ (m + 3 + 1) * (m + 3)) ^ 2 := by
          gcongr
          exact Nat.le_mul_of_pos_right _ (by omega)

omit [Field F] in
/-- The field-size hypothesis bounds `(k - 1) / (q - n + 1)` by `2 ^ (-10 ℓ / η)`. -/
private theorem cast_sub_one_div_le_two_pow_neg (η : ℝ)
    (hF : (n : ℝ) + k * 2 ^ ((10 * ℓ : ℝ) / η) ≤ Fintype.card F) :
    ((k - 1 : ℕ) : ℝ) / ((Fintype.card F - n + 1 : ℕ) : ℝ) ≤ 2 ^ (-((10 * ℓ : ℝ) / η)) := by
  have hX : 0 < (2 : ℝ) ^ ((10 * ℓ : ℝ) / η) := Real.rpow_pos_of_pos two_pos _
  have hkX : (0 : ℝ) ≤ k * 2 ^ ((10 * ℓ : ℝ) / η) := by positivity
  have hq : n ≤ Fintype.card F := by exact_mod_cast (le_add_of_nonneg_right hkX).trans hF
  have hQ : ((Fintype.card F - n + 1 : ℕ) : ℝ) = Fintype.card F - n + 1 := by
    push_cast [Nat.cast_sub hq]
    ring
  have hk : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  rw [hQ, Real.rpow_neg two_pos.le, div_le_iff₀ (by linarith), inv_mul_eq_div, le_div_iff₀ hX]
  exact (mul_le_mul_of_nonneg_right hk hX.le).trans (by linarith)

/-- **The single-minor regime.** If `η n < 4` and `η n < n - 3`, then for
`p ≤ 2 ^ (-10 ℓ / η)`, `n * p * ∑ s ∈ [1, ℓ], s * (2 ^ (s + 1) - (s + 1)) ^ n ≤ 2 ^ (-ℓ n)`. -/
private theorem mul_mul_sum_le_two_pow_neg (hℓ : 2 ≤ ℓ) {η : ℝ} (hη : 0 < η)
    (hu4 : η * n < 4) (hu : η * n < n - 3) {p : ℝ} (hp : p ≤ 2 ^ (-((10 * ℓ : ℝ) / η))) :
    n * p * ((∑ s ∈ Icc 1 ℓ, s * (2 ^ (s + 1) - (s + 1)) ^ n : ℕ) : ℝ) ≤
      2 ^ (-(ℓ * n : ℝ)) := by
  have hG := two_pow_sub_one_mul_sum_le n ℓ
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ s ∈ Icc 1 ℓ, s * (2 ^ (s + 1) - (s + 1)) ^ n := ⟨_, rfl⟩
  rw [← hS] at hG ⊢
  have hn4 : 4 ≤ n := by
    have h0 : 0 ≤ η * n := by positivity
    have : (3 : ℝ) < n := by linarith
    have : 3 < n := by exact_mod_cast this
    omega
  have key (E : ℝ) (hE : E + ℓ * n ≤ (10 * ℓ : ℝ) / η) (hnS : (n : ℝ) * S ≤ 2 ^ E) :
      n * p * (S : ℝ) ≤ 2 ^ (-(ℓ * n : ℝ)) := by
    have hpE : p ≤ 2 ^ (-(E + ℓ * n)) :=
      hp.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (neg_le_neg hE))
    calc (n : ℝ) * p * S = p * (n * S) := by ring
      _ ≤ 2 ^ (-(E + ℓ * n)) * 2 ^ E := mul_le_mul hpE hnS (by positivity) (by positivity)
      _ = 2 ^ (-(ℓ * n : ℝ)) := by
          rw [← Real.rpow_add two_pos]
          congr 1
          ring
  by_cases h7 : 7 ≤ n
  · have hL1 := sq_two_pow_mul_le hℓ h7
    have hNat : (n * S) ^ 2 ≤ 2 ^ (3 * ℓ * n) := by
      have : ((2 ^ n - 1) * (n * S)) ^ 2 ≤ (2 ^ n - 1) ^ 2 * 2 ^ (3 * ℓ * n) :=
        calc ((2 ^ n - 1) * (n * S)) ^ 2 = (n * ((2 ^ n - 1) * S)) ^ 2 := by ring
          _ ≤ (n * (2 ^ n * ℓ * (2 ^ (ℓ + 1) - (ℓ + 1)) ^ n)) ^ 2 :=
              Nat.pow_le_pow_left (Nat.mul_le_mul_left n hG) 2
          _ = (2 ^ n * n * ℓ * (2 ^ (ℓ + 1) - (ℓ + 1)) ^ n) ^ 2 := by ring
          _ ≤ _ := hL1
      rw [mul_pow] at this
      have hd : 0 < 2 ^ n - 1 := by have := @Nat.one_lt_two_pow n (by omega); omega
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    refine key ((3 * ℓ * n : ℝ) / 2) ?_ ?_
    · rw [le_div_iff₀ hη]
      have := mul_le_mul_of_nonneg_left hu4.le (by positivity : (0 : ℝ) ≤ 5 * ℓ / 2)
      linarith
    · have h2 : ((n : ℝ) * S) ^ 2 ≤ ((2 : ℝ) ^ ((3 * ℓ * n : ℝ) / 2)) ^ 2 := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul two_pos.le]
        have e : (3 * ℓ * n : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((3 * ℓ * n : ℕ) : ℝ) := by
          push_cast
          ring
        rw [e, Real.rpow_natCast]
        exact_mod_cast hNat
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h2
  · have hn6 : (n : ℝ) ≤ 6 := by exact_mod_cast (by omega : n ≤ 6)
    obtain ⟨d, hd⟩ : ∃ d, 2 ^ n = d + 1 := ⟨2 ^ n - 1, by have := @Nat.one_le_two_pow n; omega⟩
    have hd1 : 1 ≤ d := by have := @Nat.one_lt_two_pow n (by omega); omega
    rw [hd, Nat.add_sub_cancel] at hG
    have hS2 : S ≤ 2 * ℓ * (2 ^ (ℓ + 1) - (ℓ + 1)) ^ n := by
      refine Nat.le_of_mul_le_mul_left (c := d + 1) ?_ (by omega)
      nlinarith [hG, Nat.mul_le_mul_right S hd1]
    have hNat : n * S ≤ 2 ^ (2 * ℓ * n) :=
      calc n * S ≤ n * (2 * ℓ * (2 ^ (ℓ + 1) - (ℓ + 1)) ^ n) := Nat.mul_le_mul_left n hS2
        _ = 2 * n * ℓ * (2 ^ (ℓ + 1) - (ℓ + 1)) ^ n := by ring
        _ ≤ 2 ^ ((ℓ - 1) * n) * (2 ^ (ℓ + 1)) ^ n :=
            Nat.mul_le_mul (two_mul_mul_le_two_pow hℓ hn4) (Nat.pow_le_pow_left (Nat.sub_le _ _) n)
        _ = 2 ^ (2 * ℓ * n) := by
            rw [← pow_mul, ← pow_add, ← add_mul, show ℓ - 1 + (ℓ + 1) = 2 * ℓ by omega]
    refine key (2 * ℓ * n) ?_ ?_
    · rw [le_div_iff₀ hη]
      have := mul_le_mul_of_nonneg_left (show η * n ≤ 3 by linarith)
        (by positivity : (0 : ℝ) ≤ 3 * ℓ)
      linarith
    · have : ((n * S : ℕ) : ℝ) ≤ ((2 ^ (2 * ℓ * n) : ℕ) : ℝ) := by exact_mod_cast hNat
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast] at this
      push_cast at this
      exact this

/-- **The certificate regime.** If `2 ≤ r`, `2 r + 4 ≤ n` and `η n < 2 r + 2`, then for
`0 ≤ p ≤ 2 ^ (-10 ℓ / η)`,
`(∑ s ∈ [1, ℓ], (2 ^ (s + 1) - (s + 1)) ^ n * n.choose r * 2 ^ ((s + 1) r) * s ^ r) * p ^ r ≤
2 ^ (-ℓ n)`. -/
private theorem sum_mul_pow_le_two_pow_neg (hℓ : 2 ≤ ℓ) {η : ℝ} (hη : 0 < η) {r : ℕ}
    (hr : 2 ≤ r) (hrn : 2 * r + 4 ≤ n) (hu : η * n < 2 * r + 2) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : p ≤ 2 ^ (-((10 * ℓ : ℝ) / η))) :
    ((∑ s ∈ Icc 1 ℓ, (2 ^ (s + 1) - (s + 1)) ^ n * n.choose r * (2 ^ (s + 1)) ^ r * s ^ r :
        ℕ) : ℝ) * p ^ r ≤ 2 ^ (-(ℓ * n : ℝ)) := by
  obtain ⟨T, hT⟩ : ∃ T,
      T = ∑ s ∈ Icc 1 ℓ, (2 ^ (s + 1) - (s + 1)) ^ n * n.choose r * (2 ^ (s + 1)) ^ r * s ^ r :=
    ⟨_, rfl⟩
  rw [← hT]
  have hlt : ℓ + 1 < 2 ^ (ℓ + 1) := Nat.lt_two_pow_self
  obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ (ℓ + 1) - (ℓ + 1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 2 ^ (ℓ + 1) * ℓ := ⟨_, rfl⟩
  have hY1 : 1 ≤ ℓ * (2 ^ (ℓ + 1) * A) ^ n :=
    Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega)
      (pow_ne_zero _ (mul_ne_zero (by positivity) (by omega))))
  have hB1 : 1 ≤ B := by
    rw [hB]
    exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by positivity) (by omega))
  have hmono : Monotone fun s : ℕ ↦ 2 ^ (s + 1) - (s + 1) :=
    monotone_nat_of_le_succ fun s ↦
      (Nat.le_mul_of_pos_left _ two_pos).trans (two_mul_two_pow_sub_le s)
  have hTle : 2 ^ (ℓ * n) * T ≤ ℓ * (2 ^ (ℓ + 1) * A) ^ n * B ^ r := by
    have hterm : ∀ s ∈ Icc 1 ℓ, (2 ^ (s + 1) - (s + 1)) ^ n * n.choose r * (2 ^ (s + 1)) ^ r *
        s ^ r ≤ A ^ n * 2 ^ n * (2 ^ (ℓ + 1)) ^ r * ℓ ^ r := fun s hs ↦ by
      have hsℓ := (mem_Icc.1 hs).2
      rw [hA]
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left (hmono hsℓ) n)
        (Nat.choose_le_two_pow n r)) (Nat.pow_le_pow_left (Nat.pow_le_pow_right two_pos
        (by omega)) r)) (Nat.pow_le_pow_left hsℓ r)
    have hsum := sum_le_card_nsmul _ _ _ hterm
    rw [Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel, ← hT] at hsum
    calc 2 ^ (ℓ * n) * T ≤ 2 ^ (ℓ * n) * (ℓ * (A ^ n * 2 ^ n * (2 ^ (ℓ + 1)) ^ r * ℓ ^ r)) :=
          Nat.mul_le_mul_left _ hsum
      _ = ℓ * (2 ^ (ℓ + 1) * A) ^ n * B ^ r := by rw [hB]; ring
  have hL3 : (ℓ * (2 ^ (ℓ + 1) * A) ^ n) ^ 3 * B ^ (n - 2) ≤ 2 ^ (10 * ℓ * n) := by
    have h := pow_mul_pow_mul_pow_le hℓ (by omega : 1 ≤ n)
    rw [← hA, ← hB] at h
    have hBn : B ^ n = B ^ (n - 2) * B ^ 2 := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [hBn] at h
    refine Nat.le_of_mul_le_mul_right (c := B ^ 2) ?_ (by positivity)
    calc (ℓ * (2 ^ (ℓ + 1) * A) ^ n) ^ 3 * B ^ (n - 2) * B ^ 2 =
          ℓ ^ 3 * (2 ^ (ℓ + 1) * A) ^ (3 * n) * (B ^ (n - 2) * B ^ 2) := by ring
      _ ≤ _ := h
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ℓ * (2 ^ (ℓ + 1) * A) ^ n * B ^ r := ⟨_, rfl⟩
  rw [← hZ] at hTle
  have hZpow : Z ^ (2 * (r + 1)) ≤ 2 ^ (10 * ℓ * n * r) := by
    rw [hZ]
    calc (ℓ * (2 ^ (ℓ + 1) * A) ^ n * B ^ r) ^ (2 * (r + 1)) =
          (ℓ * (2 ^ (ℓ + 1) * A) ^ n) ^ (2 * (r + 1)) * B ^ (r * (2 * (r + 1))) := by
          rw [mul_pow, ← pow_mul]
      _ ≤ (ℓ * (2 ^ (ℓ + 1) * A) ^ n) ^ (3 * r) * B ^ ((n - 2) * r) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right hY1 (by omega)) (Nat.pow_le_pow_right hB1
            (by rw [mul_comm r]; exact Nat.mul_le_mul_right r (by omega)))
      _ = ((ℓ * (2 ^ (ℓ + 1) * A) ^ n) ^ 3 * B ^ (n - 2)) ^ r := by ring
      _ ≤ (2 ^ (10 * ℓ * n)) ^ r := Nat.pow_le_pow_left hL3 r
      _ = 2 ^ (10 * ℓ * n * r) := by rw [← pow_mul]
  have hr1 : (0 : ℝ) < r + 1 := by positivity
  have hE : (Z : ℝ) ≤ 2 ^ ((5 * ℓ * n * r : ℝ) / (r + 1)) := by
    have h1 : (Z : ℝ) ^ (2 * (r + 1)) ≤
        ((2 : ℝ) ^ ((5 * ℓ * n * r : ℝ) / (r + 1))) ^ (2 * (r + 1)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul two_pos.le]
      have e : (5 * ℓ * n * r : ℝ) / (r + 1) * ((2 * (r + 1) : ℕ) : ℝ) =
          ((10 * ℓ * n * r : ℕ) : ℝ) := by
        push_cast
        field_simp
        ring
      rw [e, Real.rpow_natCast]
      exact_mod_cast hZpow
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).1 h1
  have hpr : p ^ r ≤ 2 ^ (-((5 * ℓ * n * r : ℝ) / (r + 1))) := by
    have hn : (n : ℝ) ≤ (2 * r + 2) / η := by
      rw [le_div_iff₀ hη]
      linarith
    have h5 : (5 * ℓ * n * r : ℝ) ≤ (10 * ℓ : ℝ) / η * r * (r + 1) :=
      calc (5 * ℓ * n * r : ℝ) = (5 * ℓ * r) * n := by ring
        _ ≤ (5 * ℓ * r) * ((2 * r + 2) / η) := mul_le_mul_of_nonneg_left hn (by positivity)
        _ = (10 * ℓ : ℝ) / η * r * (r + 1) := by
            field_simp
            ring
    calc p ^ r ≤ ((2 : ℝ) ^ (-((10 * ℓ : ℝ) / η))) ^ r := pow_le_pow_left₀ hp0 hp r
      _ = 2 ^ (-((10 * ℓ : ℝ) / η) * r) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul two_pos.le]
      _ ≤ 2 ^ (-((5 * ℓ * n * r : ℝ) / (r + 1))) := by
          refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
          rw [neg_mul, neg_le_neg_iff, div_le_iff₀ hr1]
          linarith
  have hT' : (T : ℝ) * 2 ^ (ℓ * n : ℝ) ≤ Z := by
    have : ((2 ^ (ℓ * n) * T : ℕ) : ℝ) ≤ Z := by exact_mod_cast hTle
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_mul] at this
    linarith
  have h1 : (2 : ℝ) ^ (ℓ * n : ℝ) * 2 ^ (-(ℓ * n : ℝ)) = 1 := by
    rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
  set E : ℝ := (5 * ℓ * n * r : ℝ) / (r + 1)
  calc (T : ℝ) * p ^ r ≤ T * 2 ^ (-E) := mul_le_mul_of_nonneg_left hpr (Nat.cast_nonneg _)
    _ = T * 2 ^ (ℓ * n : ℝ) * 2 ^ (-E) * 2 ^ (-(ℓ * n : ℝ)) := by
        linear_combination (T * 2 ^ (-E) : ℝ) * h1.symm
    _ ≤ 2 ^ E * 2 ^ (-E) * 2 ^ (-(ℓ * n : ℝ)) := by
        gcongr
        exact hT'.trans hE
    _ = 2 ^ (-(ℓ * n : ℝ)) := by
        rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul]

/-- A count bound `N * D ≤ X * E` with `D > 0` and `X / D ≤ y` gives `N ≤ y * E`. -/
private theorem cast_le_mul_of_mul_le {N D X E : ℕ} {y : ℝ} (hD : 0 < D) (h : N * D ≤ X * E)
    (hy : (X : ℝ) / D ≤ y) : (N : ℝ) ≤ y * E := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h' : (N : ℝ) * D ≤ X * E := by exact_mod_cast h
  calc (N : ℝ) ≤ X * E / D := by rw [le_div_iff₀ hD']; exact h'
    _ = X / D * E := by ring
    _ ≤ y * E := mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg _)

open Classical in
/-- **Random distinct evaluation points give short lists.** Let `2 ≤ ℓ`, `0 < η`, `n ≠ 0`
and `n + k * 2 ^ (10 ℓ / η) ≤ q`. At most `2 ^ (-ℓ n) * |Fin n ↪ F|` tuples `α : Fin n ↪ F` give
a Reed–Solomon code of dimension `k` with more than `ℓ` codewords within relative radius
`ℓ / (ℓ + 1) * (1 - k / n - η)` of some word. -/
theorem card_filter_lt_Lambda_le_two_pow_neg_mul (hℓ : 2 ≤ ℓ) {η : ℝ} (hη0 : 0 < η) (hn : n ≠ 0)
    (hF : (n : ℝ) + k * 2 ^ ((10 * ℓ : ℝ) / η) ≤ Fintype.card F) :
    (#{α : Fin n ↪ F | (ℓ : ℕ∞) < Lambda (code α k : Set (Fin n → F))
        ((ℓ : ℝ) / (ℓ + 1) * (1 - (k : ℝ) / n - η))} : ℝ) ≤
      2 ^ (-(ℓ * n : ℝ)) * Fintype.card (Fin n ↪ F) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hδ : (ℓ : ℝ) / (ℓ + 1) * (1 - (k : ℝ) / n - η) =
      (ℓ : ℝ) / (ℓ + 1) * (1 - ((k : ℝ) + η * n) / n) := by
    field_simp
    ring
  by_cases hsmall : (ℓ : ℝ) / (ℓ + 1) * (1 - (k : ℝ) / n - η) * n < 1
  · have h0 : #{α : Fin n ↪ F | (ℓ : ℕ∞) < Lambda (code α k : Set (Fin n → F))
        ((ℓ : ℝ) / (ℓ + 1) * (1 - (k : ℝ) / n - η))} = 0 := by
      refine card_eq_zero.2 (filter_eq_empty_iff.2 fun α _ ↦ not_lt.2 ?_)
      refine (Lambda_le_one_of_mul_card_lt_one (by simpa using hsmall)).trans ?_
      exact_mod_cast (by omega : 1 ≤ ℓ)
    rw [h0, Nat.cast_zero]
    positivity
  rw [hδ]
  have hκ0 : (k : ℝ) ≤ k + η * n := le_add_of_nonneg_right (by positivity)
  have hpa := cast_sub_one_div_le_two_pow_neg (F := F) η hF
  by_cases hk : k ≤ 1
  · have hB := card_filter_lt_Lambda_mul_le (F := F) (n := n) (k := k) (by omega : 0 < ℓ) hκ0
    rw [Nat.sub_eq_zero_of_le hk, mul_zero, zero_mul, zero_mul, Nat.le_zero, mul_eq_zero] at hB
    rcases hB with hB | hB
    · rw [hB, Nat.cast_zero]
      positivity
    · omega
  have hu : η * n < n - 3 := by
    have h1 : 1 ≤ (ℓ : ℝ) / (ℓ + 1) * (1 - (k : ℝ) / n - η) * n := not_lt.1 hsmall
    have h2 : (ℓ : ℝ) / (ℓ + 1) * (1 - (k : ℝ) / n - η) * n =
        ℓ * (n - k - η * n) / (ℓ + 1) := by
      field_simp
    rw [h2, le_div_iff₀ (by positivity), one_mul] at h1
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
    refine lt_of_not_ge fun h ↦ ?_
    have : (ℓ : ℝ) * (n - k - η * n) ≤ ℓ * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg ℓ)
    linarith
  by_cases h4 : η * n < 4
  · have hB := card_filter_lt_Lambda_mul_le (F := F) (n := n) (k := k) (by omega : 0 < ℓ) hκ0
    refine cast_le_mul_of_mul_le (by omega) hB ?_
    have hreg := mul_mul_sum_le_two_pow_neg hℓ hη0 h4 hu hpa
    rw [Nat.cast_mul, Nat.cast_mul]
    calc _ = n * (((k - 1 : ℕ) : ℝ) / ((Fintype.card F - n + 1 : ℕ) : ℝ)) *
          ((∑ s ∈ Icc 1 ℓ, s * (2 ^ (s + 1) - (s + 1)) ^ n : ℕ) : ℝ) := by ring
      _ ≤ _ := hreg
  · replace h4 := not_lt.1 h4
    set r := ⌊η * n / 2⌋₊ with hr
    have hfl : (r : ℝ) ≤ η * n / 2 := Nat.floor_le (by positivity)
    have hr2 : 2 ≤ r := Nat.le_floor (by norm_num; linarith)
    have hru : η * n < 2 * r + 2 := by
      have := Nat.lt_floor_add_one (η * n / 2)
      linarith
    have hrn : 2 * r + 4 ≤ n := by
      have : ((2 * r + 3 : ℕ) : ℝ) < n := by
        push_cast
        linarith
      have : 2 * r + 3 < n := by exact_mod_cast this
      omega
    have hκr : (k : ℝ) + 2 * r ≤ k + η * n := by linarith
    have hA := card_filter_lt_Lambda_mul_pow_le (F := F) (n := n) (k := k) (by omega : 0 < ℓ) hκr
    refine cast_le_mul_of_mul_le (by positivity) hA ?_
    have hreg := sum_mul_pow_le_two_pow_neg hℓ hη0 hr2 hrn hru (by positivity) hpa
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    calc _ = ((∑ s ∈ Icc 1 ℓ, (2 ^ (s + 1) - (s + 1)) ^ n * n.choose r * (2 ^ (s + 1)) ^ r *
            s ^ r : ℕ) : ℝ) *
          (((k - 1 : ℕ) : ℝ) / ((Fintype.card F - n + 1 : ℕ) : ℝ)) ^ r := by
          rw [div_pow]
          ring
      _ ≤ _ := hreg

end ReedSolomon
