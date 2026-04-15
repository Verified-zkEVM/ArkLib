/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.FieldTheory.AdditiveNTT.Domain

/-!
# Additive NTT Algorithm (Algorithm 2, LCH14)

This file contains the Additive NTT algorithm itself:

## Main Definitions

- `twiddleFactor`: stage-local butterfly twiddle computation
- `NTTStage`: one Additive NTT stage
- `additiveNTT`: full Additive NTT encoding algorithm
- `additiveNTT_correctness`: Main correctness statement of the encoding algorithm.
- `additiveNTTInvariant`: Describes the invariant for each loop in the algorithm,
which states whether the result of an encoding round is correct
- `NTTStage_correctness`: Main correctness statement of each NTT stage in the encoding algorithm,
this proves that if the previous round satisfies the invariant, then the current round also

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Reference the archived revision of [DP24] when comparing statement numbering.
* [Lin, S., Chung, W., and Han, Y.S., *Novel polynomial basis and its application to reed-solomon
    erasure codes*][LCH14]
* [Von zur Gathen, J. and Gerhard, J., *Arithmetic and factorization of polynomial over F2
    (extended abstract)*][GGJ96]

-/

set_option linter.style.longFile 3500

open Polynomial AdditiveNTT Module
namespace AdditiveNTT

universe u

-- We work over a generic field `L` which is an algebra over a ground field `𝔽q` of prime
-- characteristic.
variable {r : ℕ} [NeZero r]
variable {L : Type u} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type u) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]

-- Let `β` be a basis of `L` over `𝔽q`, indexed by natural numbers.
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ R_rate : ℕ} [NeZero ℓ] (h_ℓ_add_R_rate : ℓ + R_rate < r)-- ℓ ∈ {1, ..., r-1}

section AlgorithmCorrectness
/-- The twiddle factor -/
def twiddleFactor (i : Fin r) (h_i : i < ℓ)
  (u : Fin (2 ^ (ℓ + R_rate - i - 1))) : L :=
  ∑ (⟨k, hk⟩: Fin (ℓ + R_rate - i - 1)),
    if Nat.getBit k u.val = 1 then
      -- this branch maps to the above Nat.getBit = 1 branch
        -- (of evaluationPointω (i+1)) under (qMap i)(X)
      evalNormalizedWAt (β := β) (i := ⟨i, by omega⟩) (β ⟨i + 1 + k, by omega⟩)
    else 0
      -- 0 maps to the below Nat.getBit = 0 branch
        -- (of evaluationPointω (i+1)) under (qMap i)(X)

lemma evaluationPointω_eq_twiddleFactor_of_div_2 (i : Fin r) (h_i : i < ℓ)
  (x : Fin (2 ^ (ℓ + R_rate - i))) :
  evaluationPointω 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) x =
  twiddleFactor (β := β) h_ℓ_add_R_rate (i := i) (h_i := by omega) (u := ⟨x/2, by
    have h := div_two_pow_lt_two_pow (x:=x) (i := ℓ + R_rate - i - 1) (j:=1) (by
      rw [Nat.sub_add_cancel (by omega)]; omega)
    simp only [pow_one] at h
    calc _ < 2 ^ (ℓ + R_rate - i - 1) := by omega
      _ = _ := by rfl
  ⟩) + (x.val % 2: ℕ) * eval (β ⟨i, by omega⟩) (normalizedW 𝔽q β ⟨i, by omega⟩) := by
  unfold evaluationPointω twiddleFactor
  simp_rw [evalNormalizedWAt_eq_normalizedW (𝔽q := 𝔽q) (β := β)]
  set f_left := fun x_1 : Fin (ℓ + R_rate - i) =>
    if Nat.getBit x_1 x = 1 then
      eval (β ⟨i + x_1, by omega⟩) (normalizedW 𝔽q β ⟨i, by omega⟩)
    else 0
  conv_lhs =>
    rw [← Fin.sum_congr' (b := ℓ + R_rate - i) (a := ℓ + R_rate - (i + 1) + 1) (f := f_left) (h := by omega)]
    rw [Fin.sum_univ_succ (n := ℓ + R_rate - (i + 1))]
  unfold f_left
  simp only [Fin.val_cast, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ]
  have h_bit_shift : ∀ x_1 : Fin (ℓ + R_rate - (↑i + 1)),
      Nat.getBit (↑x_1 + 1) ↑x = Nat.getBit ↑x_1 (↑x / 2) := by
    intro x_1
    rw [← Nat.shiftRight_eq_div_pow (m := x) (n := 1)]
    exact Nat.getBit_of_shiftRight (n := x) (p := 1) (k := x_1).symm
  have h_sum_eq : ∀ x_1 : Fin (ℓ + R_rate - (↑i + 1)),
      i.val + (x_1.val + 1) = i.val + 1 + x_1.val := by omega
  conv_lhs =>
    enter [2, 2, x_1]
    rw [h_bit_shift]
    simp only [h_sum_eq x_1]
  set f_right := fun x_1 : Fin (ℓ + R_rate - (↑i + 1)) =>
    if Nat.getBit (↑x_1) (↑x / 2) = 1 then
      eval (β ⟨↑i + 1 + ↑x_1, by omega⟩) (normalizedW 𝔽q β ⟨↑i, by omega⟩)
    else 0
  rw [← Fin.sum_congr' (b := ℓ + R_rate - (↑i + 1)) (a := ℓ + R_rate - i - 1) (f := f_right) (h := by omega)]
  unfold f_right
  simp only [Fin.cast_eq_self]
  rw [add_comm]
  congr
  have h_i_lt_ℓ_add_R_rate : i < ℓ + R_rate := by omega
  have h_2_le_pow_ℓ_add_R_rate_sub_i : 2 ≤ 2 ^ (ℓ + R_rate - i.val) := by
    have h_2_eq : 2 = 2 ^ 1 := by rfl
    conv_lhs => rw [h_2_eq]
    apply Nat.pow_le_pow_right (by omega) (by omega)
  simp only [Nat.getBit, Nat.shiftRight_zero, Nat.and_one_is_mod]
  by_cases h_lsb_of_x_eq_0 : x.val % 2 = 0
  · simp only [h_lsb_of_x_eq_0, zero_ne_one, ↓reduceIte, Nat.cast_zero, zero_mul]
  · push_neg at h_lsb_of_x_eq_0
    simp only [ne_eq, Nat.mod_two_not_eq_zero] at h_lsb_of_x_eq_0
    simp only [h_lsb_of_x_eq_0, ↓reduceIte, Nat.cast_one, one_mul]

lemma eval_point_ω_eq_next_twiddleFactor_comp_qmap
  (i : Fin r) (h_i : i < ℓ) (x : Fin (2 ^ (ℓ + R_rate - (i + 1)))) :
  -- `j = u||b||v` => x here means u at level i
  evaluationPointω 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩) (h_i := by simp only; omega) x =
  eval (twiddleFactor (β := β) h_ℓ_add_R_rate (i := i) (h_i := by omega) (u := ⟨x.val, by
    calc x.val < 2 ^ (ℓ + R_rate - (i.val + 1)) := by omega
      _ = 2 ^ (ℓ + R_rate - i.val - 1) := by rfl
  ⟩)) (qMap 𝔽q β ⟨i, by omega⟩) := by
  simp [evaluationPointω, twiddleFactor, evalNormalizedWAt_eq_normalizedW (𝔽q := 𝔽q) (β := β)]
  set q_eval_is_linear_map := linear_map_of_comp_to_linear_map_of_eval (f := qMap 𝔽q β ⟨i, by omega⟩)
    (h_f_linear := qMap_is_linear_map 𝔽q β (i := ⟨i, by omega⟩))
  let eval_qmap_linear := polyEvalLinearMap (qMap 𝔽q β ⟨i, by omega⟩) q_eval_is_linear_map
  set right_inner_func := fun x_1 : Fin (ℓ + R_rate - i - 1) =>
    if Nat.getBit ↑x_1 ↑x = 1 then
      eval (β ⟨↑i + 1 + ↑x_1, by omega⟩) (normalizedW 𝔽q β ⟨↑i, by omega⟩)
    else 0
  have h_rhs : eval (∑ x_1 : Fin (ℓ + R_rate - i - 1), right_inner_func x_1)
      (qMap 𝔽q β ⟨↑i, by omega⟩) = ∑ x_1 : Fin (ℓ + R_rate - i - 1),
      (eval (right_inner_func x_1) (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
    change eval_qmap_linear (∑ x_1, right_inner_func x_1) = _
    rw [map_sum (g := eval_qmap_linear) (f := right_inner_func)
      (s := (Finset.univ : Finset (Fin (ℓ + R_rate - i - 1))))]
    congr
  rw [h_rhs]
  set left_inner_func := fun x_1 : Fin (ℓ + R_rate - (i.val + 1)) =>
    if Nat.getBit ↑x_1 ↑x = 1 then
      eval (β ⟨↑i + 1 + ↑x_1, by omega⟩) (normalizedW 𝔽q β ⟨↑i + 1, by omega⟩)
    else 0
  conv_lhs =>
    rw [← Fin.sum_congr' (b := ℓ + R_rate - (i.val + 1))
      (a := ℓ + R_rate - i - 1) (f := left_inner_func) (h := by omega)]
    simp only [Fin.cast_eq_self]
  congr
  funext x1
  have h_normalized_comp_qmap : normalizedW 𝔽q β ⟨i + 1, by omega⟩ =
    (qMap 𝔽q β ⟨i, by omega⟩).comp (normalizedW 𝔽q β ⟨i, by omega⟩) := by
    have res := qMap_comp_normalizedW 𝔽q β
      (i := ⟨i, by omega⟩) (h_i_add_1 := by simp only; omega)
    rw [res]
    congr
    simp only [Nat.add_mod_mod]
    rw [Nat.mod_eq_of_lt]
    omega
  simp only [left_inner_func, right_inner_func]
  by_cases h_bit_of_x_eq_0 : Nat.getBit x1 x = 0
  · simp only [h_bit_of_x_eq_0, zero_ne_one, ↓reduceIte]
    have h_0_is_algebra_map : (0 : L) = (algebraMap 𝔽q L) 0 := by
      simp only [map_zero]
    conv_rhs => rw [h_0_is_algebra_map]
    have h_res := qMap_eval_𝔽q_eq_0 𝔽q β (i := ⟨i, by omega⟩) (c := 0)
    rw [h_res]
  · push_neg at h_bit_of_x_eq_0
    have h_bit_lt_2 := Nat.getBit_lt_2 (k := x1) (n := x)
    have bit_eq_1 : Nat.getBit x1 x = 1 := by
      interval_cases Nat.getBit x1 x
      · contradiction
      · rfl
    simp only [bit_eq_1, ↓reduceIte]
    rw [h_normalized_comp_qmap]
    rw [eval_comp]

/--
The `2^R_rate`-fold tiling of coefficients `a` into the initial buffer `b`.
`b(v) = aⱼ`, where `j` are the `ℓ` LSBs of `v`.
-/
def tileCoeffs (a : Fin (2 ^ ℓ) → L) : Fin (2^(ℓ + R_rate)) → L :=
  fun v => a (Fin.mk (v.val % (2^ℓ)) (Nat.mod_lt v.val (pow_pos (zero_lt_two) ℓ)))

/--
A single stage of the Additive NTT for a given `i`.
It takes the buffer `b` from the previous stage and applies the butterfly operations.
This function implements one step of the `for i from ℓ-1 down to 0` loop.
-/
def NTTStage (β : Fin r → L) (h_ℓ_add_R_rate : ℓ + R_rate < r)
    (i : Fin r) (h_i : i < ℓ) (b : Fin (2 ^ (ℓ + R_rate)) → L) :
    Fin (2^(ℓ + R_rate)) → L :=
  have h_2_pow_i_lt_2_pow_ℓ_add_R_rate: 2^i.val < 2^(ℓ + R_rate) := by
    calc
      2^i.val < 2 ^ (ℓ) := by
        have hr := Nat.pow_lt_pow_right (a:=2) (m:=i.val) (n:=ℓ) (ha:=by omega) (by omega)
        exact hr
      _ ≤ 2 ^ (ℓ + R_rate) := by
        exact Nat.pow_le_pow_right (n:=2) (i := ℓ) (j:=ℓ + R_rate) (by omega) (by omega)
  fun (j : Fin (2^(ℓ + R_rate))) =>
    let u_b_v := j.val
    have h_u_b_v : u_b_v = j.val := by rfl
    let v: Fin (2^i.val) := ⟨Nat.getLowBits i.val u_b_v, by
      have res := Nat.getLowBits_lt_two_pow (numLowBits:=i.val) (n:=u_b_v)
      simp only [res]
    ⟩ -- the i LSBs
    let u_b := u_b_v / (2^i.val) -- the high (ℓ + R_rate - i) bits
    have h_u_b : u_b = u_b_v / (2^i.val) := by rfl
    have h_u_b_lt_2_pow : u_b < 2 ^ (ℓ + R_rate - i) := by
      -- {m n k : Nat} (h : m < n * k) : m / n < k :=
      have res := Nat.div_lt_of_lt_mul (m:=u_b_v) (n:=2^i.val) (k:=2^(ℓ + R_rate - i)) (by
        calc _ < 2 ^ (ℓ + R_rate) := by omega
          _ = 2 ^ i.val * 2 ^ (ℓ + R_rate - i.val) := by
            exact Eq.symm (pow_mul_pow_sub (a:=2) (m:=i.val) (n:=ℓ + R_rate) (by omega))
      )
      rw [h_u_b]
      exact res
    let u: ℕ := u_b / 2 -- the remaining high bits
    let b_bit := u_b % 2 -- the LSB of the high bits, i.e. the `i`-th Nat.getBit
    have h_u : u = u_b / 2 := by rfl
    have h_u_lt_2_pow: u < 2 ^ (ℓ + R_rate - (i + 1)) := by
      have h_u_eq: u = j.val / (2 ^ (i.val + 1)) := by
        rw [h_u, h_u_b, h_u_b_v]
        rw [Nat.div_div_eq_div_mul]
        rfl
      rw [h_u_eq]
      -- ⊢ ↑j / 2 ^ (↑i + 1) < 2 ^ (ℓ + R_rate - (↑i + 1))
      exact div_two_pow_lt_two_pow (x:=j.val) (i := ℓ + R_rate - (i.val + 1)) (j:=i.val + 1) (by
        rw [Nat.sub_add_cancel (by omega)]
        omega
      )
    let twiddleFactor : L := twiddleFactor (β := β) h_ℓ_add_R_rate (i := i) (h_i := by omega) ⟨u, h_u_lt_2_pow⟩
    let x0 := twiddleFactor -- since the last Nat.getBit of u||0 is 0
    let x1: L := x0 + 1 -- since the last Nat.getBit of u||1 is 1 and 1 * Ŵᵢ(βᵢ) = 1

    have h_b_bit : b_bit = Nat.getBit i.val j.val := by
      simp only [Nat.getBit, Nat.and_one_is_mod, b_bit, u_b, u_b_v]
      rw [←Nat.shiftRight_eq_div_pow (m:=j.val) (n:=i.val)]
    -- b remains unchanged through this whole function cuz we create new buffer
    if h_b_bit_zero: b_bit = 0 then -- This is the `b(u||0||v)` case
      let odd_split_index := u_b_v + 2^i.val
      have h_lt: odd_split_index < 2^(ℓ + R_rate) := by
        have h_exp_eq: (↑i + (ℓ + R_rate - i)) = ℓ + R_rate := by omega
        simp only [gt_iff_lt, odd_split_index, u_b_v]
        -- ⊢ ↑j + 2 ^ ↑i < 2 ^ (ℓ + R_rate)
        exact Nat.add_two_pow_of_getBit_eq_zero_lt_two_pow (n:=j.val) (m:=ℓ + R_rate)
          (i := i.val) (h_n:=by omega) (h_i := by omega) (h_getBit_at_i_eq_zero:=by
          rw [h_b_bit_zero] at h_b_bit
          exact h_b_bit.symm
        )
      b j + x0 * b ⟨odd_split_index, h_lt⟩
    else -- This is the `b(u||1||v)` case
      let even_split_index := u_b_v ^^^ 2^i.val
      have h_lt: even_split_index < 2^(ℓ + R_rate) := by
        have h_exp_eq: (↑i + (ℓ + R_rate - i)) = ℓ + R_rate := by omega
        simp only [even_split_index, u_b_v]
        apply Nat.xor_lt_two_pow (by omega) (by omega)
      -- b j is now the odd refinement P₁,₍₁ᵥ₎⁽ⁱ⁺¹⁾(X),
      -- b (j - 2^i) stores the even refinement P₀,₍₀ᵥ₎⁽ⁱ⁺¹⁾(X)
      b ⟨even_split_index, h_lt⟩ + x1 * b j

/--
**The Additive NTT Algorithm (Algorithm 2)**

Computes the Additive NTT on a given set of coefficients from the novel basis.
- `a`: The initial coefficient array `(a₀, ..., a_{2^ℓ-1})`.
-/
def additiveNTT (β' : Fin r → L) (h_ℓ_add_R_rate' : ℓ + R_rate < r)
    (a : Fin (2 ^ ℓ) → L) : Fin (2^(ℓ + R_rate)) → L :=
  let b: Fin (2^(ℓ + R_rate)) → L := tileCoeffs a -- Note: can optimize on this
  Fin.foldl (n:=ℓ) (f:= fun current_b i  =>
    NTTStage β' h_ℓ_add_R_rate' (i := ⟨ℓ - 1 - i, by omega⟩) (h_i := by simp only; omega)
      current_b
  ) (init:=b)

-- `∀ i ∈ {0, ..., ℓ}, coeffsBySuffix a i` represents the list of `2^(ℓ-i)` novel coefficients.
-- Note that `i=ℓ` means the result of the initial coefficient tiling process at the beginning.
-- for a specific suffix (LSBs) `v` of `i` bits at the `i-th` NTT stage
def coeffsBySuffix (a : Fin (2 ^ ℓ) → L) (i : Fin r) (h_i : i ≤ ℓ) (v : Fin (2 ^ i.val)) :
  Fin (2 ^ (ℓ - i)) → L :=
  fun ⟨j, hj⟩ => by
    set originalIndex := (j <<< i.val) ||| v;
    have h_originalIndex_lt_2_pow_ℓ: originalIndex < 2 ^ ℓ := by
      unfold originalIndex
      have res := Nat.append_lt (y:=j) (x:=v) (m:=ℓ - i.val) (n:=i.val) (by omega) (by omega)
      have h_exp_eq: (↑i + (ℓ - ↑i)) = ℓ := by omega
      rw [h_exp_eq] at res
      exact res
    exact a ⟨originalIndex, h_originalIndex_lt_2_pow_ℓ⟩

omit [Field L] [Fintype L] [DecidableEq L] [NeZero ℓ] in
lemma base_coeffsBySuffix (a : Fin (2 ^ ℓ) → L) :
  coeffsBySuffix (r:=r) (R_rate := R_rate) (a := a) (i := 0)
    (h_i := by simp only [Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, zero_le]) 0 = a := by
  unfold coeffsBySuffix
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.shiftLeft_zero, Fin.isValue,
    Nat.or_zero, Fin.eta]

omit [NeZero ℓ] [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
/-- `P₀, ₍ᵥ₎⁽ⁱ⁺¹⁾(X) = P₍₀ᵥ₎⁽ⁱ⁺¹⁾(X)`, where `v` consists of exactly `i` bits
Note that the even refinement `P₀, ₍ᵥ₎⁽ⁱ⁺¹⁾(X)` is constructed from the view of
stage `i`, while the novel polynomial `P₍₀ᵥ₎⁽ⁱ⁺¹⁾(X)` is constructed from the view of stage `i+1`.
-/
theorem evenRefinement_eq_novel_poly_of_0_leading_suffix (i : Fin r) (h_i : i < ℓ) (v : Fin (2 ^ i.val))
    (original_coeffs : Fin (2 ^ ℓ) → L) :
    have h_v: v.val < 2 ^ (i.val + 1) := by
      calc v.val < 2 ^ i.val := by omega
        _ < 2 ^ (i.val + 1) := by apply Nat.pow_lt_pow_right (by omega) (by omega)
    evenRefinement 𝔽q β h_ℓ_add_R_rate i (h_i := by omega) (coeffsBySuffix (r:=r)
      (R_rate:=R_rate) (a:=original_coeffs) (i := i) (h_i := by omega) v) =
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩) (h_i := by simp only; omega)
      (coeffsBySuffix (r:=r) (R_rate:=R_rate) original_coeffs (i := ⟨i.val+1, by omega⟩) (h_i := by simp only; omega) ⟨v, h_v⟩) := by
  simp only [evenRefinement, Fin.eta, intermediateEvaluationPoly]
  set right_inner_func := fun x: Fin (2^(ℓ - (i.val + 1))) =>
    C (coeffsBySuffix (ℓ := ℓ) (r := r) (R_rate:=R_rate) (a := original_coeffs) (i := ⟨i.val+1, by omega⟩) (h_i := by simp only; omega) ⟨v.val, by
      calc v.val < 2 ^ i.val := by omega
        _ < 2 ^ (i.val + 1) := by apply Nat.pow_lt_pow_right (by omega) (by omega)
    ⟩ x) *
      intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩) (h_i := by simp only; omega) x
  have h_right_sum_eq := Fin.sum_congr' (M:=L[X]) (b:=2^(ℓ - (i.val + 1)))
    (a:=2^(ℓ - i - 1)) (f:=right_inner_func) (h:=by rfl)
  conv_rhs =>
    simp only [Fin.cast_eq_self]
    rw [←h_right_sum_eq]
    simp only [Fin.cast_eq_self]
  congr
  funext x
  simp only [right_inner_func]
  have h_coeffs_eq: coeffsBySuffix (r:=r) (R_rate:=R_rate)
      original_coeffs (i := i) (h_i := by omega) v ⟨↑x * 2, by
    have h_x_mul_2_lt := mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i)
      ⟨0, by omega⟩ (by omega) (by omega)
    simp only [add_zero] at h_x_mul_2_lt
    simp only [gt_iff_lt]
    exact h_x_mul_2_lt
  ⟩
    = coeffsBySuffix (r:=r) (R_rate:=R_rate) original_coeffs
      (i := ⟨i.val + 1, by omega⟩) (h_i := by simp only; omega) (v:=⟨v, by
      calc v.val < 2 ^ i.val := by omega
        _ < 2 ^ (i.val + 1) := by apply Nat.pow_lt_pow_right (by omega) (by omega)
    ⟩) x := by
    simp only [coeffsBySuffix]
    -- ⊢ original_coeffs ⟨(↑x * 2) <<< ↑i ||| ↑v, ⋯⟩ = original_coeffs ⟨↑x <<< (↑i + 1) ||| ↑v, ⋯⟩
    have h_index_eq: (x.val * 2) <<< i.val ||| v.val = x.val <<< (i.val + 1) ||| v.val := by
      change (x.val * 2^1) <<< i.val ||| v.val = x.val <<< (i.val + 1) ||| v.val
      rw [←Nat.shiftLeft_eq, ←Nat.shiftLeft_add]
      conv_lhs => rw [add_comm]
    simp_rw [h_index_eq]
  rw [h_coeffs_eq]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
/-- `P₁, ₍ᵥ₎⁽ⁱ⁺¹⁾(X) = P₍₁ᵥ₎⁽ⁱ⁺¹⁾(X)`, where `v` consists of exactly `i` bits
Note that the odd refinement `P₁,₍ᵥ₎⁽ⁱ⁺¹⁾(X)` is constructed from the view of stage `i`,
while the novel polynomial `P₍₁ᵥ₎⁽ⁱ⁺¹⁾(X)` is constructed from the view of stage `i+1`.
-/
theorem oddRefinement_eq_novel_poly_of_1_leading_suffix (i : Fin r) (h_i : i < ℓ) (v : Fin (2 ^ i.val))
    (original_coeffs : Fin (2 ^ ℓ) → L) :
    have h_v: v.val ||| (1 <<< i.val) < 2 ^ (i.val + 1) := by
      apply Nat.or_lt_two_pow (x:=v.val) (y:=1 <<< i.val) (n:=i.val + 1) (by omega)
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    oddRefinement 𝔽q β h_ℓ_add_R_rate i h_i (coeffsBySuffix (r:=r) (R_rate:=R_rate)
      original_coeffs (i := i) (h_i := by omega) v) =
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i + 1, by omega⟩) (h_i := by simp only; omega)
      (coeffsBySuffix (r:=r) (R_rate:=R_rate) original_coeffs (i := ⟨i.val+1, by omega⟩) (h_i := by simp only; omega)
        ⟨v ||| (1 <<< i.val), h_v⟩) := by
  simp only [oddRefinement, Fin.eta, intermediateEvaluationPoly]
  set right_inner_func := fun x: Fin (2^(ℓ - (i.val + 1))) =>
    C (coeffsBySuffix (R_rate:=R_rate) (r := r) original_coeffs
      (i := ⟨i.val+1, by omega⟩) (h_i := by simp only; omega) ⟨v.val ||| (1 <<< i.val), by
      simp only;
      apply Nat.or_lt_two_pow
      · omega
      · rw [Nat.shiftLeft_eq, one_mul]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
    ⟩ x) *
      intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩) (h_i := by simp only; omega) x
  have h_right_sum_eq := Fin.sum_congr' (M:=L[X]) (b:=2^(ℓ - (i.val + 1)))
    (a:=2^(ℓ - i - 1)) (f:=right_inner_func) (h:=by rfl)
  conv_rhs =>
    simp only [Fin.cast_eq_self]
    rw [←h_right_sum_eq]
    simp only [Fin.cast_eq_self]
  congr
  funext x
  simp only [right_inner_func]
  have h_coeffs_eq: coeffsBySuffix (r:=r) (R_rate:=R_rate) original_coeffs
      (i := i) (h_i := by omega) v ⟨↑x * 2 + 1, by
    have h_x_mul_2_lt := mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i)
      ⟨1, by omega⟩ (by omega) (by omega)
    simp only at h_x_mul_2_lt
    simp only [gt_iff_lt]
    exact h_x_mul_2_lt
  ⟩
    = coeffsBySuffix (r:=r) (R_rate:=R_rate) original_coeffs (i := ⟨i.val + 1, by omega⟩) (h_i := by simp only; omega)
      (v:=⟨v.val ||| (1 <<< i.val), by
      simp only
      apply Nat.or_lt_two_pow (x:=v.val) (y:=1 <<< i.val) (n:=i.val + 1) (by omega)
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    ⟩) x := by
    simp only [coeffsBySuffix]
    -- ⊢ original_coeffs ⟨(↑x * 2 + 1) <<< ↑i ||| ↑v, ⋯⟩
    -- = original_coeffs ⟨↑x <<< (↑i + 1) ||| (↑v ||| 1 <<< ↑i), ⋯⟩
    have h_index_eq: (x.val * 2 + 1) <<< i.val ||| v.val
        = x.val <<< (i.val + 1) ||| (v.val ||| (1 <<< i.val)) := by
      change (x.val * 2^1 + 1) <<< i.val ||| v.val
        = x.val <<< (i.val + 1) ||| (v.val ||| (1 <<< i.val))
      rw [←Nat.shiftLeft_eq]
      conv_lhs =>
        rw [add_comm]
      conv_rhs =>
        rw [Nat.or_comm v.val (1 <<< i.val), ←Nat.or_assoc]
      congr
      -- ⊢ (1 + ↑x <<< 1) <<< ↑i = ↑x <<< (↑i + 1) ||| 1 <<< ↑i
      have h_left: 1 + (x.val <<< 1) = 1 ||| (x.val <<< 1) := by
        apply Nat.sum_of_and_eq_zero_is_or
        simp only [Nat.one_and_eq_mod_two, Nat.shiftLeft_eq]
        simp only [pow_one, Nat.mul_mod_left]
      rw [h_left, Nat.shiftLeft_add, Nat.shiftLeft_or_distrib, Nat.or_comm]
      rw [←Nat.shiftLeft_add, ←Nat.shiftLeft_add, Nat.add_comm]
    simp_rw [h_index_eq]
  rw [h_coeffs_eq]

/--
The main loop invariant for the `additiveNTT` algorithm: the evaluation buffer `b`
at the end of stage `i` (`i ∈ {0, ..., ℓ}`, `i=ℓ` means the initial tiled buffer)
holds the value `P⁽ⁱ⁾(ω_{u, b, v})` for all Nat.getBit mask index
`(u||b||v) ∈ {0, ..., 2^(ℓ+R_rate)-1}`, where the points `ω_{u, b, v}` are in the domain `S⁽ⁱ⁾`.

**Main statement:**
After round `i ∈ {ℓ-1, ℓ-2, ..., 0}`: the buffer `b` at index `j` (which can be
decomposed as `j = (u || b || v)` in little-endian order, where
- `u` is a bitstring of length `ℓ + R_rate - i - 1`,
- `b` is a single Nat.getBit (the LSB of the high bits),
- `v` is a bitstring of length `i` (the LSBs),
holds the value `P⁽ⁱ⁾(ω_{u, b, i})`,
where:
  - `P⁽ⁱ⁾` is the intermediate polynomial at round `i` (in the novel basis),
  - `ω_{u, b, i}` is the evaluation point in the subspace `S⁽ⁱ⁾` constructed
  as a linear combination of the basis elements of `S⁽ⁱ⁾`:
    - the Nat.getBit `b` is the coefficient for `Ŵᵢ(βᵢ)` (the LSB),
    - the LSB of `u` is the coefficient for `Ŵᵢ(β_{i+1})`, ..., the MSB of `u` is
    the coefficient for `Ŵᵢ(β_{ℓ+R_rate-1})`.
  - The value is replicated `2^i` times for each `v`
    (i.e., the last `i` bits do not affect the value).

More precisely, for all `j : Fin (2^(ℓ + R_rate))`,
let `u_b_v := j.val` (as a natural number),
- let `v := u_b_v % 2^i` (the `i` LSBs),
- let `u_b := u_b_v / 2^i` (the high bits),
- let `b := u_b % 2` (the LSB of the high bits),
- let `u := u_b / 2` (the remaining high bits),
then:
  b j = P⁽ⁱ⁾(ω_{u, b, i})
-/
def additiveNTTInvariant (evaluation_buffer : Fin (2 ^ (ℓ + R_rate)) → L)
    (original_coeffs : Fin (2 ^ ℓ) → L) (i : Fin (ℓ + 1)) : Prop :=
  ∀ (j : Fin (2^(ℓ + R_rate))),
    let u_b_v := j.val
    let v: Fin (2^i.val) := ⟨Nat.getLowBits i.val u_b_v, by
      have res := Nat.getLowBits_lt_two_pow (numLowBits:=i.val) (n:=u_b_v)
      simp only [res]
    ⟩ -- the i LSBs
    let u_b := u_b_v / (2^i.val) -- the high (ℓ + R_rate - i) bits
    have h_u_b : u_b = u_b_v / (2^i.val) := by rfl
    have h_u_b_lt_2_pow : u_b < 2 ^ (ℓ + R_rate - i) := by
      -- {m n k : Nat} (h : m < n * k) : m / n < k :=
      have res := Nat.div_lt_of_lt_mul (m:=u_b_v) (n:=2^i.val) (k:=2^(ℓ + R_rate - i)) (by
        calc _ < 2 ^ (ℓ + R_rate) := by omega
          _ = 2 ^ i.val * 2 ^ (ℓ + R_rate - i.val) := by
            exact Eq.symm (pow_mul_pow_sub (a:=2) (m:=i.val) (n:=ℓ + R_rate) (by omega))
      )
      rw [h_u_b]
      exact res
    let b_bit := Nat.getLowBits 1 u_b_v -- the LSB of the high bits, i.e. the `i`-th Nat.getBit
    let u := u_b / 2 -- the remaining high bits
    let coeffs_at_j: Fin (2 ^ (ℓ - i)) → L :=
      coeffsBySuffix (r:=r) (R_rate:=R_rate) original_coeffs (i := ⟨i, by omega⟩) (h_i := by simp only; omega) v
    let P_i: L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by simp only; omega) coeffs_at_j
    let ω := evaluationPointω 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by simp only; omega) (Fin.mk u_b (by omega))
    evaluation_buffer j = P_i.eval ω

omit [DecidableEq 𝔽q] hF₂ in
lemma initial_tiled_coeffs_correctness (h_ℓ : ℓ ≤ r) (a : Fin (2 ^ ℓ) → L) :
    let b: Fin (2^(ℓ + R_rate)) → L := tileCoeffs a
    additiveNTTInvariant 𝔽q β h_ℓ_add_R_rate b a (i := ⟨ℓ, by omega⟩) := by
    unfold additiveNTTInvariant
    simp only
    intro j
    unfold coeffsBySuffix
    simp only [tileCoeffs, evaluationPointω, intermediateEvaluationPoly, Fin.eta]
    have h_ℓ_sub_ℓ: 2^(ℓ - ℓ) = 1 := by norm_num
    set f_right: Fin (2^(ℓ - ℓ)) → L[X] :=
      fun ⟨x, hx⟩ => C (a ⟨↑x <<< ℓ ||| Nat.getLowBits ℓ (↑j), by
        simp only [tsub_self, pow_zero, Nat.lt_one_iff] at hx
        simp only [hx, Nat.zero_shiftLeft, Nat.zero_or]
        exact Nat.getLowBits_lt_two_pow (numLowBits:=ℓ) (n:=j.val)
      ⟩) * intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨ℓ, by omega⟩) (h_i := by simp only; omega) ⟨x, by omega⟩
    have h_sum_right : ∑ (x: Fin (2^(ℓ - ℓ))), f_right x =
      C (a ⟨Nat.getLowBits ℓ (↑j), by exact Nat.getLowBits_lt_two_pow ℓ⟩) *
    intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨ℓ, by omega⟩) (h_i := by simp only; omega) 0 := by
      have h_sum_eq := Fin.sum_congr' (b:=2^(ℓ - ℓ)) (a:=1) (f:=f_right) (by omega)
      rw [←h_sum_eq]
      rw [Fin.sum_univ_one]
      unfold f_right
      simp only [Fin.isValue, Fin.cast_zero, Fin.coe_ofNat_eq_mod, tsub_self, pow_zero,
        Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
      congr
    rw [h_sum_right]
    set f_left: Fin (ℓ + R_rate - ℓ) → L := fun x =>
      if Nat.getBit (x.val) (j.val / 2 ^ ℓ) = 1 then
        eval (β ⟨ℓ + x.val, by omega⟩) (normalizedW 𝔽q β ⟨ℓ, by omega⟩)
      else 0
    simp only [eval_mul, eval_C]
    have h_eval : eval (Finset.univ.sum f_left) (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate
      (i := ⟨ℓ, by omega⟩) (h_i := by simp only; omega) 0) = 1 := by
      have h_base_novel_basis := base_intermediateNovelBasisX 𝔽q β
        h_ℓ_add_R_rate ⟨ℓ, by exact Nat.lt_two_pow_self⟩
      simp only [intermediateNovelBasisX, Fin.coe_ofNat_eq_mod, tsub_self, pow_zero,
        Nat.zero_mod]
      set f_inner : Fin (ℓ - ℓ) → L[X] := fun x => (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
        (i := ⟨ℓ, by omega⟩) (k := x) (h_k := by simp only; omega)) ^ Nat.getBit (x.val) 0
      have h_sum_eq := Fin.prod_congr' (b:=ℓ - ℓ) (a:=0) (f:=f_inner) (by omega)
      simp_rw [←h_sum_eq, Fin.prod_univ_zero]
      simp only [eval_one]
    rw [h_eval, mul_one]
    simp only [Nat.getLowBits_eq_mod_two_pow]

-- /-- **Key Polynomial Identity (Equation 39)**. This identity is the foundation for the
-- butterfly operation in the Additive NTT. It relates a polynomial in the `i`-th basis to
-- its even and odd parts expressed in the `(i+1)`-th basis via the quotient map `q⁽ⁱ⁾`.
-- ∀ i ∈ {0, ..., ℓ-1}, `P⁽ⁱ⁾(X) = P₀⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) + X ⋅ P₁⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))` -/
/--
The correctness theorem for the `NTTStage` function. This is the inductive step
in the main proof. It asserts that if the invariant holds for `i+1`, then after
applying `NTTStage i`, the invariant holds for `i ∈ {0, ..., ℓ-1}`.
-/
lemma NTTStage_correctness (i : Fin (ℓ))
    (input_buffer : Fin (2 ^ (ℓ + R_rate)) → L) (original_coeffs : Fin (2 ^ ℓ) → L) :
    additiveNTTInvariant 𝔽q β h_ℓ_add_R_rate (evaluation_buffer:=input_buffer)
      (original_coeffs:=original_coeffs) (i := ⟨i.val+1, by omega⟩) →
    additiveNTTInvariant 𝔽q β h_ℓ_add_R_rate (evaluation_buffer:=NTTStage β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i := by simp only; omega) input_buffer) (original_coeffs:=original_coeffs) (i := ⟨i, by omega⟩) :=
by
  -- This proof is the core of the work, using the `key_polynomial_identity`.
  intro h_prev
  simp only [additiveNTTInvariant] at h_prev
  set output_buffer := NTTStage β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by simp only; omega) input_buffer
  unfold additiveNTTInvariant at *
  simp only at *
  intro j
  -- prove that at any `j ∈ {0, ..., 2^(ℓ+R_rate)-1}`,
  -- output_buffer j = P⁽ⁱ⁾(ω_{u, b, i}) where coeffs of P⁽ⁱ⁾ at j = `coeffsBySuffix a i v`
  have h_j_div_2_pow_i_lt := div_two_pow_lt_two_pow (x:=j.val)
    (i := ℓ + R_rate - i.val) (j:=i.val) (by
    rw [Nat.sub_add_cancel (by omega)]; omega)
  set cur_evaluation_point := evaluationPointω 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) (h_i := by simp only; omega) (⟨↑j / 2 ^ i.val, by simp only; exact h_j_div_2_pow_i_lt⟩) -- ω_{u, b, i}
  set cur_coeffs := coeffsBySuffix (R_rate:=R_rate) (r := r) original_coeffs (i := ⟨i, by omega⟩) (h_i := by simp only; omega)
    ⟨Nat.getLowBits i.val (↑j), by
      exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val)⟩ -- coeffs of P⁽ⁱ⁾ at j
  -- identity (39): `P⁽ⁱ⁾(X) = P₀⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) + X ⋅ P₁⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))`
  have h_P_i_split_even_odd := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) (h_i := by simp only; omega) cur_coeffs
  simp at h_P_i_split_even_odd
  set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by simp only; omega) cur_coeffs
  set even_coeffs_poly := evenRefinement 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by simp only; omega) cur_coeffs
  set odd_coeffs_poly := oddRefinement 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by simp only; omega) cur_coeffs
  conv_lhs =>
    unfold output_buffer NTTStage
    simp only [beq_iff_eq, Fin.eta]
  have h_bit: Nat.getBit i.val j.val = (j.val / (2 ^ i.val)) % 2 := by
    simp only [Nat.getBit, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have h_qmap_linear_map := qMap_is_linear_map 𝔽q β
    (i := ⟨i, by omega⟩)
  have h_qmap_additive: IsLinearMap 𝔽q fun x ↦ eval x (qMap 𝔽q β ⟨↑i, by omega⟩)
    := linear_map_of_comp_to_linear_map_of_eval
      (f := (qMap 𝔽q β ⟨i, by omega⟩)) (h_f_linear := h_qmap_linear_map)
  let eval_qmap_linear : L →ₗ[𝔽q] L := {
    toFun    := fun x ↦ eval x (qMap 𝔽q β ⟨i, by omega⟩),
    map_add' := h_qmap_additive.map_add,
    map_smul' := h_qmap_additive.map_smul
  }
  have h_lsb_and_two_pow_eq_zero : (Nat.getLowBits i.val j.val) &&& (1 <<< i.val) = 0 := by
    rw [Nat.shiftLeft_eq, one_mul]
    apply Nat.and_two_pow_eq_zero_of_getBit_0
    rw [Nat.getBit_of_lowBits];
    simp only [lt_self_iff_false, ↓reduceIte]
  have h_j_div_2_pow_i_add_1_lt := div_two_pow_lt_two_pow (x:=j.val)
    (i := ℓ + R_rate - (i.val + 1)) (j:=i.val + 1) (by
    rw [Nat.sub_add_cancel (by omega)]; omega)
  have h_j_div_2_pow_left: j.val / 2 ^ (i.val + 1) = (j.val / 2 ^ i.val) / 2 := by
    simp only [Nat.div_div_eq_div_mul]
    congr
  have h_j_div_2_pow_div_2_left_lt: j.val / 2 ^ i.val / 2 < 2 ^ (ℓ + R_rate - (i.val + 1)) := by
    rw [←h_j_div_2_pow_left]
    exact h_j_div_2_pow_i_add_1_lt
  have h_eval_qmap_at_1: eval 1 (qMap 𝔽q β ⟨↑i, by omega⟩) = 0 := by
    have h_1_is_algebra_map: (1: L) = algebraMap 𝔽q L 1 := by rw [map_one]
    rw [h_1_is_algebra_map]
    apply qMap_eval_𝔽q_eq_0 𝔽q β (i := ⟨i, by omega⟩) (c:=1)
  have h_msb_eq_j_xor_lsb: (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1))
      = j.val ^^^ Nat.getLowBits (i.val + 1) j.val := by
    have h_xor: j.val = Nat.getHighBits (i.val + 1) j.val ^^^ Nat.getLowBits (i.val + 1) j.val
      := Nat.num_eq_highBits_xor_lowBits (n:=j.val) (i.val + 1)
    conv_lhs => rw [←Nat.shiftLeft_eq]; rw [←Nat.shiftRight_eq_div_pow]
    change Nat.getHighBits (i.val + 1) j.val = _
    conv_rhs => enter [1]; rw [h_xor]
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have h_msb_eq_j_sub_lsb: (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1))
      = j.val - Nat.getLowBits (i.val + 1) j.val := by
    have h_msb := Nat.num_eq_highBits_add_lowBits (n:=j.val) (numLowBits:=i.val + 1)
    conv_rhs => enter [1]; rw [h_msb]
    norm_num; rw [Nat.getHighBits, Nat.getHighBits_no_shl, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
  by_cases h_b_bit_eq_0: (j.val / (2 ^ i.val)) % 2 = 0
  · simp only [h_b_bit_eq_0, ↓reduceDIte]
    simp only at h_b_bit_eq_0
    have bit_i_j_eq_0: Nat.getBit i.val j.val = 0 := by omega
    set x0 := twiddleFactor (β := β) h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by simp only; omega) ⟨j.val / 2 ^ i.val / 2, by
      rw [h_j_div_2_pow_left.symm]; exact h_j_div_2_pow_i_add_1_lt⟩
    have h_j_add_2_pow_i: j.val + 2 ^ i.val < 2 ^ (ℓ + R_rate):= by
      exact Nat.add_two_pow_of_getBit_eq_zero_lt_two_pow
        (n:=j.val) (m:=ℓ + R_rate) (i := i.val) (h_n:=by omega)
        (h_i := by omega) (h_getBit_at_i_eq_zero:=by
        rw [←h_b_bit_eq_0]
        simp only [Nat.getBit, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow])
    -- EVEN REFINEMENT coeffs correspondence at index j of level i--
    have h_even_split: input_buffer j =
      eval x0 (even_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev j]
      have h_twiddle_comp_qmap_eq_left := eval_point_ω_eq_next_twiddleFactor_comp_qmap
        𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (x:=⟨j.val / 2 ^ i.val / 2, by
        rw [←h_j_div_2_pow_left]; simp only [h_j_div_2_pow_i_add_1_lt]
      ⟩)
      simp only [Fin.is_lt, forall_true_left] at h_twiddle_comp_qmap_eq_left
      -- relation between ω and twiddle factor at level i and at point (j.val / 2 ^ i.val / 2)
      conv_rhs =>
        rw [eval_comp]
        simp only [x0]
        rw [←h_twiddle_comp_qmap_eq_left]
      -- ⊢ eval (ω_ᵢ₊₁(j / 2 ^ (i + 1))) (Pᵢ₊₁ (coeffsBySuffix (i+1) (get_lsb (j) (i+1)))) =
      -- eval (ω_ᵢ₊₁(j / 2 ^ i /2)) even_coeffs_poly => `h_j_div_2_pow_left` is dervied for this
      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_left] -- change the index of lhs to same as rhs
      simp only [even_coeffs_poly, cur_coeffs]
      have h_res := evenRefinement_eq_novel_poly_of_0_leading_suffix 𝔽q β h_ℓ_add_R_rate
        (i := ⟨i, by omega⟩) (h_i := by simp only; omega) ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val)⟩ original_coeffs
      simp only at h_res
      rw [h_res]
      have h_v_eq: Nat.getLowBits i.val j.val = Nat.getLowBits (i.val + 1) j.val := by
        -- i.e. v (i bits) = 0||v (i+1 bits)
        rw [Nat.getLowBits_succ]
        rw [h_bit, h_b_bit_eq_0, Nat.zero_shiftLeft, Nat.add_zero]
      simp_rw [h_v_eq]
    -- ODD REFINEMENT coeffs correspondence at index j of level i--
    have h_odd_split: input_buffer ⟨↑j + 2 ^ i.val, h_j_add_2_pow_i⟩
      = eval x0 (odd_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev ⟨j.val + 2^i.val, by omega⟩]
      have h_j_div_2_pow_right: (⟨j.val + 2^i.val, by omega⟩: Fin (2^(ℓ + R_rate))).val
        / 2 ^ (i.val + 1) = (j.val / 2 ^ i.val) / 2 := by
        simp only
        rw [Nat.div_div_eq_div_mul, ←Nat.pow_add (a:=2) (m:=i.val) (n:=1)]
        -- ⊢ (↑j + 2 ^ ↑i) / 2 ^ (↑i + 1) = ↑j / 2 ^ (↑i + 1)
        apply Nat.div_eq_of_lt_le (m:=(j.val + 2 ^ i.val))
          (n:=2 ^ (i.val + 1)) (k:=j.val / 2 ^ (i.val + 1))
        · -- ⊢ ↑j / 2 ^ (↑i + 1) * 2 ^ (↑i + 1) ≤ ↑j + 2 ^ ↑i:
          -- the lhs is basically erasing (i+1) lsb bits from j
          calc
            (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1)) ≤ j.val := by
              simp only [Nat.div_mul_le_self (m:=j.val) (n:=2^(i.val + 1))]
            _ ≤ _ := by exact Nat.le_add_right j.val (2 ^ i.val)
        · -- ⊢ ↑j + 2 ^ ↑i < (↑j / 2 ^ (↑i + 1) + 1) * 2 ^ (↑i + 1)
          rw [add_mul]; rw [one_mul];
          conv_rhs => enter [2]; rw [Nat.pow_succ, mul_two];
          rw [←Nat.add_assoc];
          apply Nat.add_lt_add_right;
          -- ⊢ ↑j < ↑j / 2 ^ (↑i + 1) * 2 ^ (↑i + 1) + 2 ^ ↑i
          have h_j: j = j / 2^(i.val + 1) * 2^(i.val + 1) + Nat.getLowBits i.val j.val := by
            conv_lhs => rw [Nat.num_eq_highBits_add_lowBits (n:=j.val) (numLowBits:=i.val + 1)]
            rw [Nat.getHighBits, Nat.getHighBits_no_shl, Nat.shiftLeft_eq,
              Nat.shiftRight_eq_div_pow]
            apply Nat.add_left_cancel_iff.mpr
            rw [Nat.getLowBits_succ]
            conv_rhs => rw [←Nat.add_zero (n:=Nat.getLowBits i.val j.val)]
            apply Nat.add_left_cancel_iff.mpr
            rw [bit_i_j_eq_0, Nat.zero_shiftLeft]
          conv_lhs => rw [h_j];
          apply Nat.add_lt_add_left;
          exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val) (n:=j.val)
      have h_twiddle_comp_qmap_eq_right :=  eval_point_ω_eq_next_twiddleFactor_comp_qmap 𝔽q β
        h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (x:=⟨j.val / 2 ^ i.val / 2, by
          exact h_j_div_2_pow_div_2_left_lt⟩)
      simp only [Fin.eta] at h_twiddle_comp_qmap_eq_right
      -- relation between ω and twiddle factor at level i and at point (j.val / 2 ^ i.val / 2)
      conv_rhs =>
        rw [eval_comp]
        simp only [x0]
        rw [←h_twiddle_comp_qmap_eq_right]
      -- ⊢ eval (ω_ᵢ₊₁((⟨j.val + 2 ^ i.val, h_j_add_2_pow_i⟩: Fin (2^(ℓ + R_rate))).val
      -- / 2 ^ (↑i + 1), ⋯⟩))) (Pᵢ₊₁ (coeffsBySuffix (i+1) (get_lsb (j + 2^i) (i+1)))) =
      -- eval (ω_ᵢ₊₁(↑⟨j.val / 2 ^ i.val / 2, ⋯⟩))) odd_coeffs_poly
      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_right] -- change the index of lhs to same as rhs
      simp only [odd_coeffs_poly, cur_coeffs]
      have h_res := oddRefinement_eq_novel_poly_of_1_leading_suffix 𝔽q β h_ℓ_add_R_rate
        (i := ⟨i, by omega⟩) (h_i := by simp only; omega) ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val)⟩ original_coeffs
      simp only [Fin.eta] at h_res
      rw [h_res]
      have h_j_and_2_pow_i_eq_0 : j.val &&& 2 ^ i.val = 0 := by
        apply Nat.and_two_pow_eq_zero_of_getBit_0
        omega
      have h_bit1: Nat.getBit (i.val) (j.val + 2 ^ i.val) = 1 := by
        rw [Nat.sum_of_and_eq_zero_is_or h_j_and_2_pow_i_eq_0]
        rw [Nat.getBit_of_or]
        rw [Nat.getBit_two_pow]
        rw [bit_i_j_eq_0]
        simp only [BEq.rfl, ↓reduceIte, Nat.zero_or]
      have h_v_eq: Nat.getLowBits (i.val + 1) (j.val + 2^i.val)
        = (Nat.getLowBits i.val j.val) ||| 1 <<< i.val := by
        -- i.e. v (i bits) = 0||v (i+1 bits)
        rw [Nat.getLowBits_succ]
        rw [h_bit1]
        have h_get_lsb_eq: Nat.getLowBits i.val (j.val + 2^i.val) = Nat.getLowBits i.val j.val := by
          apply Nat.eq_iff_eq_all_getBits.mpr; unfold Nat.getBit
          intro k
          change Nat.getBit k (Nat.getLowBits i.val (j.val + 2^i.val))
            = Nat.getBit k (Nat.getLowBits i.val j.val)
          rw [Nat.getBit_of_lowBits, Nat.getBit_of_lowBits]
          if h_k: k < i.val then
            simp only [h_k, ↓reduceIte]
            rw [Nat.getBit_of_add_distrib h_j_and_2_pow_i_eq_0]
            rw [Nat.getBit_two_pow]
            simp only [beq_iff_eq, Nat.add_eq_left, ite_eq_right_iff, one_ne_zero, imp_false]
            omega
          else
            simp only [h_k, ↓reduceIte]
        rw [h_get_lsb_eq]
        apply Nat.sum_of_and_eq_zero_is_or h_lsb_and_two_pow_eq_zero
      congr
    rw [h_even_split, h_odd_split]
    rw [h_P_i_split_even_odd]
    have h_x0_eq_cur_evaluation_point: x0 = cur_evaluation_point := by
      unfold x0 cur_evaluation_point
      simp only
      rw [evaluationPointω_eq_twiddleFactor_of_div_2 (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by exact i.isLt)]
      simp only [Fin.eta, h_b_bit_eq_0, Nat.cast_zero, zero_mul, add_zero]
    rw [h_x0_eq_cur_evaluation_point]
    simp only [eval_comp, eval_add, eval_mul, eval_X]
  · simp only [h_b_bit_eq_0, ↓reduceDIte]
    push_neg at h_b_bit_eq_0
    have bit_i_j_eq_1: Nat.getBit i.val j.val = 1 := by omega
    simp only [ne_eq, Nat.mod_two_not_eq_zero] at h_b_bit_eq_0
    set x1 := twiddleFactor (β := β) h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by simp only; omega)
      ⟨j.val / 2 ^ i.val / 2, by exact h_j_div_2_pow_div_2_left_lt⟩ + 1
    have h_j_xor_2_pow_i: j.val ^^^ 2 ^ i.val < 2 ^ (ℓ + R_rate):= by
      exact Nat.xor_lt_two_pow (by omega) (by
        apply Nat.pow_lt_pow_right (by omega) (by omega)
      )
    have h_2_pow_i_le_lsb_succ: 2 ^ i.val ≤ Nat.getLowBits (i.val + 1) j.val := by
      rw [Nat.getLowBits_succ]; rw [bit_i_j_eq_1, Nat.shiftLeft_eq, one_mul]; omega
    have h_2_pow_i_le_j: 2 ^ i.val ≤ j.val := by
      rw [Nat.num_eq_highBits_add_lowBits (n:=j.val) (numLowBits:=i.val + 1), add_comm]
      apply Nat.le_add_right_of_le -- ⊢ 2 ^ ↑i ≤ get_lsb (↑j) (↑i + 1)
      exact h_2_pow_i_le_lsb_succ
    have h_j_and_2_pow_i_eq_2_pow_i : j.val &&& 2 ^ i.val = 2 ^ i.val := by
      rw [Nat.and_two_pow_eq_two_pow_of_getBit_1 (n:=j.val) (i := i.val) (by omega)]
    have h_j_xor_2_pow_i_eq_sub: j.val ^^^ 2 ^ i.val = j.val - 2 ^ i.val := by
      exact Nat.xor_eq_sub_iff_submask (n:=j.val) (m:=2^i.val)
        (h:=h_2_pow_i_le_j).mpr h_j_and_2_pow_i_eq_2_pow_i
    have h_2_pow_i_le_lsb_succ_2: Nat.getLowBits i.val j.val < 2 ^ i.val := by
      exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val) (n:=j.val)
    have h_even_split: input_buffer ⟨↑j ^^^ 2 ^ i.val, h_j_xor_2_pow_i⟩
      = eval x1 (even_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev ⟨j.val ^^^ 2 ^ i.val, by omega⟩]
      -- left (top) is the full poly of level (i+1),
      -- right (bottom) is the even refinement of current level i
      have h_j_div_2_pow_right: (⟨j.val ^^^ 2 ^ i.val, h_j_xor_2_pow_i⟩:
        Fin (2^(ℓ + R_rate))).val / 2 ^ (i.val + 1) = (j.val / 2 ^ i.val) / 2 := by
        simp only
        rw [Nat.div_div_eq_div_mul, ←Nat.pow_add (a:=2) (m:=i.val) (n:=1)]
        -- ⊢ (↑j ^^^ 2 ^ ↑i) / 2 ^ (↑i + 1) = ↑j / 2 ^ (↑i + 1)
        apply Nat.div_eq_of_lt_le (m:=(j.val ^^^ 2 ^ i.val))
          (n:=2 ^ (i.val + 1)) (k:=j.val / 2 ^ (i.val + 1))
        · -- ⊢ ↑j / 2 ^ (↑i + 1) * 2 ^ (↑i + 1) ≤ ↑j ^^^ 2 ^ ↑i
          -- the lhs is basically erasing (i+1) msb bits from j
          calc
            (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1))
              = j.val - Nat.getLowBits (i.val + 1) j.val := by
              rw [h_msb_eq_j_sub_lsb]
            _ ≤ j.val ^^^ 2 ^ i.val := by
              rw [h_j_xor_2_pow_i_eq_sub]
              apply Nat.sub_le_sub_left (k:=j.val) (h:=h_2_pow_i_le_lsb_succ)
        · -- ⊢ ↑j ^^^ 2 ^ ↑i < (↑j / 2 ^ (↑i + 1) + 1) * 2 ^ (↑i + 1)
          rw [add_mul]; rw [one_mul];
          conv_rhs =>
            rw [h_msb_eq_j_sub_lsb] -- | ↑j - get_lsb (↑j) (↑i + 1) + 2 ^ (↑i + 1)
            rw [←Nat.sub_add_comm (h:=Nat.getLowBits_le_self (n:=j.val)
              (numLowBits:=i.val + 1)), Nat.pow_succ, mul_two]
            rw [←Nat.add_assoc]
            rw [Nat.getLowBits_succ, bit_i_j_eq_1, Nat.shiftLeft_eq, one_mul]
            rw [Nat.add_comm (Nat.getLowBits i.val j.val) (2 ^ i.val), ←Nat.sub_sub]
            rw [Nat.add_sub_cancel (m:=2^i.val)]
          rw [Nat.add_sub_assoc (n:=j.val) (m:=2^i.val)
            (k:=Nat.getLowBits i.val j.val) (h:=by omega)]
          -- ⊢ ↑j ^^^ 2 ^ ↑i < ↑j + (2 ^ ↑i - get_lsb ↑j ↑i)
          omega
      have h_twiddle_comp_qmap_eq_left := eval_point_ω_eq_next_twiddleFactor_comp_qmap 𝔽q β
        h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (x:=⟨j.val / 2 ^ i.val / 2, by
          exact h_j_div_2_pow_div_2_left_lt⟩)
      simp only [Fin.eta] at h_twiddle_comp_qmap_eq_left
      -- relation between ω and twiddle factor at level i and at point (j.val / 2 ^ i.val / 2)
      conv_rhs =>
        rw [eval_comp]
        simp only [x1]
      set t := twiddleFactor (β := β) h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by simp only; omega) (u:=⟨j.val / 2 ^ i.val / 2, by
        exact h_j_div_2_pow_div_2_left_lt⟩) with ht
      have hh := eval_qmap_linear.map_add' (x:=t) (y:=1)
      conv_rhs =>
        enter [1]
        change eval_qmap_linear.toFun (t + 1)
        rw [eval_qmap_linear.map_add' (x:=t) (y:=1)]
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, t]
        simp only [LinearMap.coe_mk, AddHom.coe_mk, eval_qmap_linear]
        rw [←h_twiddle_comp_qmap_eq_left]
      -- ⊢ eval (ω_ᵢ₊₁(j / 2 ^ (i + 1))) (Pᵢ₊₁ (coeffsBySuffix (i+1) (get_lsb (j) (i+1)))) =
      -- eval (ω_ᵢ₊₁(j / 2 ^ i /2)) even_coeffs_poly => `h_j_div_2_pow_left` is dervied for this
      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_left] -- change the index of lhs to same as rhs
        simp only [h_j_div_2_pow_right] -- change the index of lhs to same as rhs
      simp only [even_coeffs_poly, cur_coeffs]
      have h_res := evenRefinement_eq_novel_poly_of_0_leading_suffix 𝔽q β h_ℓ_add_R_rate
        (i := ⟨i, by omega⟩) (h_i := by simp only; omega) ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val)⟩ original_coeffs
      simp only [Fin.eta] at h_res
      rw [h_res]
      congr 1
      rw [h_eval_qmap_at_1, add_zero]
      have h_bit0: Nat.getBit (i.val) (j.val ^^^ 2 ^ i.val) = 0 := by
        rw [Nat.getBit_of_xor (n:=j.val) (m:=2^i.val) (k:=i.val)]
        rw [bit_i_j_eq_1, Nat.getBit_two_pow]
        simp only [BEq.rfl, ↓reduceIte, Nat.xor_self]
      have h_v_eq: Nat.getLowBits (i.val + 1) (j.val ^^^ 2^i.val) = Nat.getLowBits i.val j.val := by
        -- i.e. 0||v (i+1 bits) = v (i bits)
        rw [Nat.getLowBits_succ]
        rw [h_bit0, Nat.zero_shiftLeft, Nat.add_zero]
        apply Nat.eq_iff_eq_all_getBits.mpr; unfold Nat.getBit
        intro k
        change Nat.getBit k (Nat.getLowBits i.val (j.val ^^^ 2^i.val))
          = Nat.getBit k (Nat.getLowBits i.val j.val)
        rw [Nat.getBit_of_lowBits, Nat.getBit_of_lowBits]
        if h_k: k < i.val then
          simp only [h_k, ↓reduceIte]
          -- ⊢ Nat.getBit k (↑j ^^^ 2 ^ ↑i) = Nat.getBit k ↑j (precondition that Nat.getBit i j = 1)
          rw [Nat.getBit_of_xor, Nat.getBit_two_pow]
          have h_ne_i_eq_k: ¬(i.val = k) := by omega
          simp only [beq_iff_eq, h_ne_i_eq_k, ↓reduceIte, Nat.xor_zero]
        else
          simp only [h_k, ↓reduceIte]
      simp_rw [h_v_eq]
    have h_odd_split: input_buffer j = eval x1
      (odd_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev j]
      -- left (top) is the full poly of level (i+1),
      -- right (bottom) is the odd refinement of current level i
      have h_twiddle_comp_qmap_eq_left := eval_point_ω_eq_next_twiddleFactor_comp_qmap
        𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by simp only; omega) (x:=⟨j.val / 2 ^ i.val / 2, by
        rw [←h_j_div_2_pow_left]
        have h := div_two_pow_lt_two_pow (x:=j.val) (i :=
          ℓ + R_rate - (i.val + 1)) (j:=i.val + 1) (by
          rw [Nat.sub_add_cancel (by omega)]; omega)
        calc _ < 2 ^ (ℓ + R_rate - (i.val + 1)) := by omega
          _ = _ := by rfl
      ⟩)
      simp only [Fin.eta] at h_twiddle_comp_qmap_eq_left
      -- relation between ω and twiddle factor at level i and at point (j.val / 2 ^ i.val / 2)
      conv_rhs =>
        rw [eval_comp]
        simp only [x1]
      set t := twiddleFactor (β := β) h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by simp only; omega)
        (u:=⟨j.val / 2 ^ i.val / 2, by exact h_j_div_2_pow_div_2_left_lt⟩) with ht
      have hh := eval_qmap_linear.map_add' (x:=t) (y:=1)
      conv_rhs =>
        enter [1]
        change eval_qmap_linear.toFun (t + 1)
        rw [eval_qmap_linear.map_add' (x:=t) (y:=1)]
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, t]
        simp only [LinearMap.coe_mk, AddHom.coe_mk, eval_qmap_linear]
        rw [←h_twiddle_comp_qmap_eq_left]
      -- ⊢ eval (ω_ᵢ₊₁(j / 2 ^ (i + 1))) (Pᵢ₊₁ (coeffsBySuffix (i+1) (get_lsb (j) (i+1)))) =
      -- eval (ω_ᵢ₊₁(j / 2 ^ i /2)) even_coeffs_poly => `h_j_div_2_pow_left` is dervied for this
      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_left] -- change the index of lhs to same as rhs
      simp only [odd_coeffs_poly, cur_coeffs]
      have h_res := oddRefinement_eq_novel_poly_of_1_leading_suffix 𝔽q β h_ℓ_add_R_rate
        (i := ⟨i, by omega⟩) (h_i := by simp only; omega) ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val)⟩ original_coeffs
      simp only [Fin.eta] at h_res
      rw [h_res]
      congr
      rw [h_eval_qmap_at_1, add_zero]
      have h_v_eq: Nat.getLowBits (i.val + 1) j.val
        = Nat.getLowBits i.val j.val ||| 1 <<< i.val := by
        -- i.e. v (i bits) = 0||v (i+1 bits)
        rw [Nat.getLowBits_succ]
        rw [h_bit, h_b_bit_eq_0]
        apply Nat.sum_of_and_eq_zero_is_or h_lsb_and_two_pow_eq_zero
      simp_rw [h_v_eq]
    rw [h_even_split, h_odd_split]
    rw [h_P_i_split_even_odd]
    have h_x1_eq_cur_evaluation_point: x1 = cur_evaluation_point := by
      unfold x1 cur_evaluation_point
      simp only
      rw [evaluationPointω_eq_twiddleFactor_of_div_2 (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by exact i.isLt)]
      simp only [Fin.eta, h_b_bit_eq_0, Nat.cast_one, one_mul, add_right_inj]
      rw [normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β]
    rw [h_x1_eq_cur_evaluation_point]
    simp only [eval_comp, eval_add, eval_mul, eval_X]

-- foldl k times would result in the additiveNTTInvariant holding for the `ℓ - k`-th stage
lemma foldl_NTTStage_inductive_aux (h_ℓ : ℓ ≤ r) (k : Fin (ℓ + 1))
    (original_coeffs : Fin (2 ^ ℓ) → L) :
    additiveNTTInvariant 𝔽q β h_ℓ_add_R_rate
    (Fin.foldl k (fun current_b i ↦ NTTStage β h_ℓ_add_R_rate
      (i := ⟨ℓ - i -1, by omega⟩) (h_i := by simp only; omega) current_b) (tileCoeffs original_coeffs))
    original_coeffs ⟨ℓ - k, by omega⟩ := by
  have invariant_init := initial_tiled_coeffs_correctness 𝔽q β h_ℓ_add_R_rate  h_ℓ original_coeffs
  simp only at invariant_init
  induction k using Fin.succRecOnSameFinType with
  | zero =>
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.foldl_zero, tsub_zero]
    exact invariant_init
  | succ k k_h i_h =>
    have h_k_add_one := Fin.val_add_one' (a:=k) (by omega)
    simp only [h_k_add_one, Fin.val_cast]
    simp only [Fin.foldl_succ_last, Fin.val_last, Fin.val_castSucc]
    set ntt_round := ℓ - (k + 1)
    set input_buffer := Fin.foldl k (fun current_b i ↦ NTTStage β h_ℓ_add_R_rate
      (i := ⟨ℓ - i -1, by omega⟩) (h_i := by simp only; omega) current_b)
      (tileCoeffs original_coeffs)
    have correctness_transition := NTTStage_correctness
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨ntt_round, by omega⟩) (input_buffer:=input_buffer) (original_coeffs:=original_coeffs)
    simp only at correctness_transition
    have h_ℓ_sub_k : ℓ - k = ntt_round + 1 := by omega
    simp_rw [h_ℓ_sub_k] at i_h
    have res := correctness_transition i_h
    exact res

/--
**Main Correctness Theorem for Additive NTT**
If `b` is the output of `additiveNTT` on input `a`, then for all `j`, `b j`
is the evaluation of the polynomial `P` (from the novel basis coefficients `a`)
at the evaluation point `ω_{0, j}` in the domain `S⁰`.
-/
theorem additiveNTT_correctness (h_ℓ : ℓ ≤ r)
    (original_coeffs : Fin (2 ^ ℓ) → L)
    (output_buffer : Fin (2 ^ (ℓ + R_rate)) → L)
    (h_alg : output_buffer = additiveNTT h_ℓ_add_R_rate β h_ℓ_add_R_rate original_coeffs) :
    let P := polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ original_coeffs
    ∀ (j : Fin (2^(ℓ + R_rate))),
      output_buffer j = P.eval (evaluationPointω 𝔽q β h_ℓ_add_R_rate
        (i := ⟨0, by omega⟩) (h_i := by simp only; omega) j) :=
by
  simp only
  intro j
  simp only [h_alg]
  unfold additiveNTT
  set output_foldl := Fin.foldl ℓ (fun current_b i ↦ NTTStage β h_ℓ_add_R_rate
    (i := ⟨ℓ - i -1, by omega⟩) (h_i := by simp only; omega) current_b) (tileCoeffs original_coeffs)
  have output_foldl_correctness : additiveNTTInvariant 𝔽q β h_ℓ_add_R_rate
    output_foldl original_coeffs ⟨0, by omega⟩ := by
    have res := foldl_NTTStage_inductive_aux
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      h_ℓ
      (k:=⟨ℓ, by omega⟩) original_coeffs
    simp only [tsub_self, Fin.zero_eta] at res
    exact res
  have h_nat_point_ω_eq_j: j.val / 2 * 2 + j.val % 2 = j := by
    have h_j_mod_2_eq_0: j.val % 2 < 2 := by omega
    exact Nat.div_add_mod' (↑j) 2
  simp only [additiveNTTInvariant] at output_foldl_correctness
  have res := output_foldl_correctness j
  unfold output_foldl at res
  simp only [Fin.mk_zero', Nat.sub_zero, pow_zero, Nat.div_one, Fin.eta, Nat.pow_zero,
    Nat.getLowBits_zero_eq_zero (n := j.val), Fin.isValue, base_coeffsBySuffix] at res
  simp only [Fin.mk_zero', ← intermediate_poly_P_base 𝔽q β h_ℓ_add_R_rate h_ℓ original_coeffs]
  rw [←res]
  -- simp only [Nat.sub_right_comm] -- ℓ - 1 - ↑i = ℓ - ↑i - 1
  congr! 1
  funext coeffs
  funext i
  congr! 1
  have hIdx_eq : (i: Fin ℓ) → (⟨ℓ - 1 - i, by omega⟩ : Fin r) =
    (⟨ℓ - i - 1, by omega⟩ : Fin r) := fun i => by simp only [Fin.mk.injEq]; omega
  rw [hIdx_eq]

end AlgorithmCorrectness
end AdditiveNTT
