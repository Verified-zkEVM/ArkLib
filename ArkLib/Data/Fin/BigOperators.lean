/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases

/-!

# More lemmas about Fin and big operators

-/

theorem mul_two_add_bit_lt_two_pow (a b c : ℕ) (i : Fin 2)
    (h_a : a < 2 ^ b) (h_b : b < c) :
    a * 2 + i.val < 2^c := by
  if h_b_eq_0: b = 0 then
    rw [h_b_eq_0, pow_zero] at h_a
    interval_cases a
    · simp only [zero_mul, zero_add];
      have h_c_gt_0: c > 0 := by omega
      have h_i_lt_2_pow_c: i.val < 2^c := by
        calc
          _ ≤ 2^1 := by omega
          _ ≤ 2^c := by apply pow_le_pow_right' (by omega) (by omega)
      exact h_i_lt_2_pow_c
  else
    have h_le: 2^(b+1) ≤ 2^c := by
      rw [pow_le_pow_iff_right₀ (a:=2) (n:=b+1) (m:=c) (by omega)]
      omega
    have h_a_mul_2_add_i_lt_2_pow_c: a * 2 + i ≤ 2^c - 1 := by
      calc
        _ ≤ 2^(b+1) - 1 := by omega
        _ ≤ 2^c - 1 := by omega
    exact Nat.lt_of_le_sub_one (n:=a * 2 + i) (m:=2^c) (by omega) (h_a_mul_2_add_i_lt_2_pow_c)

theorem div_two_pow_lt_two_pow (x i j : ℕ) (h_x_lt_2_pow_i : x < 2 ^ (i + j)): x / 2^j < 2^(i) := by
  by_cases h_i_eq_0: i = 0
  · simp only [h_i_eq_0, zero_add, pow_zero, Nat.lt_one_iff, Nat.div_eq_zero_iff, Nat.pow_eq_zero,
    OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at *;
    omega
  · push_neg at h_i_eq_0
    apply Nat.div_lt_of_lt_mul (m:=x) (n:=2^j) (k:=2^i) (by
      have h_rhs_eq : 2^(i+j) = 2^j * 2^i := by
        rw [pow_add (a:=2) (m:=i) (n:=j), mul_comm]
      rw [h_rhs_eq.symm]
      omega
    )

lemma lt_two_pow_of_lt_two_pow_exp_le (x i j: ℕ)
    (h_x_lt_2_pow_i: x < 2^i) (h_i_le_j: i ≤ j): x < 2^j := by
  calc
    _ < 2^i := by omega
    _ ≤ 2^j := by apply pow_le_pow_right' (by omega) (by omega)

variable {r : ℕ} [NeZero r]

lemma Fin.val_add_one' (a : Fin r) (h_a_add_1 : a + 1 < r) : (a + 1).val = a.val + 1 := by
  rw [←Nat.mod_eq_of_lt (a := 1) (b := r) (by omega)] -- ⊢ ↑(b + 1) = ↑b + 1 % r
  apply Fin.val_add_eq_of_add_lt -- ⊢ ↑b + ↑1 < r
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  exact h_a_add_1

@[simp]
theorem Fin.cast_val_eq_val {n m : ℕ} [NeZero n] (a : Fin n) (h_eq : n = m):
  (Fin.cast (h_eq) a).val = a.val := by
  subst h_eq
  rfl

lemma Fin.val_sub_one (a : Fin r) (h_a_sub_1 : a > 0) : (a - 1).val = a.val - 1 := by
  rw [Fin.val_sub_one_of_ne_zero (by omega)] -- can use Fin.sub_val_of_le

lemma Fin.lt_iff_le_pred (a b : Fin r) (h_b : b > 0) : a < b ↔ a ≤ b - 1 := by
  have h_b_sub_1 : (b - 1).val = b.val - 1 := Fin.val_sub_one (a := b) (h_a_sub_1 := h_b)
  constructor
  · intro h
    apply Fin.mk_le_of_le_val
    omega
  · intro h
    apply Fin.mk_lt_of_lt_val
    omega

lemma Fin.le_iff_lt_succ (a b : Fin r) (h_b : b + 1 < r) : a ≤ b ↔ a < b + 1 := by
  have h_b_add_1 := Fin.val_add_one' (a := b) (h_a_add_1 := h_b)
  constructor
  · intro h
    apply Fin.mk_lt_of_lt_val
    omega
  · intro h
    apply Fin.mk_le_of_le_val
    omega

lemma Fin.lt_succ' (a : Fin r) (h_a_add_1 : a + 1 < r) : a < a + 1 := by
  apply Fin.mk_lt_of_lt_val
  rw [Fin.val_add_one' (a := a) (h_a_add_1 := h_a_add_1)]
  exact Nat.lt_succ_self a.val

lemma Fin.le_succ (a : Fin r) (h_a_add_1 : a + 1 < r) : a ≤ a + 1 := by
  apply Fin.le_of_lt
  exact Fin.lt_succ' (a := a) (h_a_add_1 := h_a_add_1)

@[elab_as_elim] def Fin.succRecOnSameFinType {motive : Fin r → Sort _}
    (zero : motive (0 : Fin r))
    (succ : ∀ i : Fin r, i + 1 < r → motive i → motive (i + 1)) : ∀ (i : Fin r), motive i
  | ⟨0, _⟩ => by exact zero
  | ⟨Nat.succ i_val, h⟩ => by -- ⊢ motive ⟨i_val.succ, h⟩
    simp only [Nat.succ_eq_add_one] at h
    set i : Fin r := ⟨i_val, by omega⟩
    set i_succ : Fin r := ⟨i_val.succ, by omega⟩
    have i_succ_val_eq : i_succ.val = i_val.succ := by rfl
    if h_i_add_1 : i + 1 < r then -- ⊢ motive ⟨i.succ, h⟩
      have motive_prev : motive i := Fin.succRecOnSameFinType zero succ i
      have res := succ (i := i) h_i_add_1 motive_prev
      have h_i_succ_eq : i_succ = i + 1 := by
        rw [Fin.eq_mk_iff_val_eq]
        rw [i_succ_val_eq]
        rw [Fin.val_add_one']
        omega
      rw [h_i_succ_eq]
      exact res
    else
      by_contra h_i_add_1
      simp only at h_i_add_1
      contradiction

@[elab_as_elim] def Fin.predRecOnSameFinType {motive : Fin r → Sort _}
    (last : motive (⟨r - 1, by
      have h_r_ne_0: r ≠ 0 := by exact NeZero.ne r
      omega
    ⟩ : Fin r))
    (succ : ∀ i : Fin r, i.val > 0 → motive i → motive (⟨i.val - 1, by omega⟩ : Fin r))
    (i : Fin r): motive i := by
  have h_r_ne_0: r ≠ 0 := by exact NeZero.ne r
  if h_i_eq_last: i = ⟨r - 1, by omega⟩ then
    subst h_i_eq_last
    exact last
  else
    have h_i_ne_last: i < ⟨r - 1, by omega⟩ := by
      have h := Fin.lt_last_iff_ne_last (n:=r - 1) (a:=⟨i, by omega⟩)
      simp only [Fin.last, mk_lt_mk, ne_eq, mk.injEq] at h
      have h_i_val_ne_eq: (i.val ≠ r - 1) := by
        push_neg at h_i_eq_last
        exact Fin.val_ne_of_ne h_i_eq_last
      apply Fin.mk_lt_of_lt_val
      apply h.mpr
      exact h_i_val_ne_eq
    -- succ : (i : Fin r) → ↑i - 1 ≥ 0 → motive i → motive ⟨↑i - 1, ⋯⟩
    let i_next := i.val + 1
    have h_i_next_gt_0 : i_next > 0 := by omega
    have h_i_next_sub_one: i_next - 1 = i.val := by omega
    have motive_next := Fin.predRecOnSameFinType last succ ⟨i_next, by omega⟩
    have motive_next_ind := succ (i := ⟨i_next, by omega⟩) (by omega) (motive_next)
    convert motive_next_ind
termination_by (r - 1 - i.val)

-- The theorem statement and its proof.
-- TODO: state a more generalized and reusable version of this, where f is from Fin r → M
theorem Fin.sum_univ_odd_even {n : ℕ} {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ i : Fin (2 ^ n), f (2 * i)) + (∑ i : Fin (2 ^ n), f (2 * i + 1))
    = ∑ i: Fin (2 ^ (n+1)), f i := by
  set f_even := fun i => f (2 * i)
  set f_odd := fun i => f (2 * i + 1)
  conv_lhs =>
    enter [1, 2, i]
    change f_even i
  conv_lhs =>
    enter [2, 2, i]
    change f_odd i
  simp only [Fin.sum_univ_eq_sum_range]

  -- Let's define the sets of even and odd numbers.
  let evens: Finset ℕ := Finset.image (fun i ↦ 2 * i) (Finset.range (2^n))
  let odds: Finset ℕ := Finset.image (fun i ↦ 2 * i + 1) (Finset.range (2^n))

  conv_lhs =>
    enter [1];
    rw [←Finset.sum_image (g:=fun i => 2 * i) (by simp)]

  conv_lhs =>
    enter [2];
    rw [← Finset.sum_image (g:=fun i => 2 * i + 1) (by simp)]

  -- First, we prove that the set on the RHS is the disjoint union of evens and odds.
  have h_disjoint : Disjoint evens odds := by
    apply Finset.disjoint_iff_ne.mpr
  -- Assume for contradiction that an element `x` is in both sets.
    rintro x hx y hy hxy
    -- Unpack the definitions of `evens` and `odds`.
    rcases Finset.mem_image.mp hx with ⟨k₁, _, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨k₂, _, rfl⟩
    omega

  have h_union : evens ∪ odds = Finset.range (2 ^ (n + 1)) := by
    apply Finset.ext; intro x
    simp only [Finset.mem_union, Finset.mem_range]
    -- ⊢ x ∈ evens ∨ x ∈ odds ↔ x < 2 ^ (n + 1)
    constructor
    · -- First direction: `x ∈ evens ∪ odds → x < 2^(n+1)`
      -- This follows from the bounds of the original range `Finset.range (2^n)`.
      intro h
      rcases h with (h_even | h_odd)
      · rcases Finset.mem_image.mp h_even with ⟨k₁, hk₁, rfl⟩
        simp at hk₁
        omega
      · rcases Finset.mem_image.mp h_odd with ⟨k₂, hk₂, rfl⟩
        simp at hk₂
        omega
    · -- Second direction: `x < 2^(n+1) → x ∈ evens ∪ odds`
      intro hx
      obtain (⟨k, rfl⟩ | ⟨k, rfl⟩) := Nat.even_or_odd x
      · left;
        unfold evens
        simp only [Finset.mem_image, Finset.mem_range]
        use k;
        omega
      · right;
        unfold odds
        simp only [Finset.mem_image, Finset.mem_range]
        use k;
        omega
  -- Now, rewrite the RHS using this partition.
  rw [←h_union, Finset.sum_union h_disjoint]

theorem sum_Icc_split {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a b c : ℕ)
    (h₁ : a ≤ b) (h₂ : b ≤ c):
    ∑ i ∈ Finset.Icc a c, f i = ∑ i ∈ Finset.Icc a b, f i + ∑ i ∈ Finset.Icc (b+1) c, f i := by
  have h_disjoint: Disjoint (Finset.Icc a b) (Finset.Icc (b+1) c) := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    -- main theorem for converting disjoint condition into intersection = ∅ condition
    ext i
    simp only [Finset.mem_inter, Finset.mem_Icc]
    constructor
    · intro h
      -- Alternatively, we can use a single line: linarith [h.1.2, h.2.1]
      have h_le_b : i ≤ b := h.1.2
      have h_ge_b_plus_1 : b + 1 ≤ i := h.2.1
      have h_contradiction : b + 1 ≤ b := le_trans h_ge_b_plus_1 h_le_b
      have h_false : b < b := Nat.lt_of_succ_le h_contradiction
      exact absurd h_false (lt_irrefl b)
    · intro h -- h : i ∈ ∅
      exact absurd h (Finset.notMem_empty i)

  rw [←Finset.sum_union h_disjoint]
  · congr
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · intro h
      -- h : a ≤ j ∧ j ≤ c
      cases Nat.lt_or_ge j (b+1) with
      | inl h_lt => -- j < (b+1)
        left -- pick the left branch, for OR statement
        exact ⟨h.1, Nat.le_of_lt_succ h_lt⟩
      | inr h_ge => -- b + 1 ≤ j
        right
        exact ⟨h_ge, h.2⟩
    · intro h
      -- h : a ≤ j ∧ j ≤ b ∨ b + 1 ≤ j ∧ j ≤ c
      cases h with
      | inl h_left =>
        -- h_left : a ≤ j ∧ j ≤ b
        exact ⟨h_left.1, Nat.le_trans h_left.2 h₂⟩
      | inr h_right =>
        -- h_right : b + 1 ≤ j ∧ j ≤ c
        exact ⟨Nat.le_trans h₁ (Nat.le_of_succ_le h_right.1), h_right.2⟩
