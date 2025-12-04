/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.FieldTheory.AdditiveNTT.AdditiveNTT
import ArkLib.Data.FieldTheory.BinaryField.Tower.Impl

namespace AdditiveNTT
open ConcreteBinaryTower

section HelperFunctions
/-- Converts an Array to a Fin function of a specific size `n`. -/
def Array.toFinVec {α : Type _} (n : ℕ) (arr : Array α) (h : arr.size = n) : Fin n → α :=
  fun i => arr[i]

/- The product of a function mapped over the list `0..n-1`. -/
lemma List.prod_finRange_eq_finset_prod {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) :
    ((List.finRange n).map f).prod = ∏ i : Fin n, f i := rfl
end HelperFunctions

universe u

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable {𝔽q : Type} [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
variable [hFq_card : Fact (Fintype.card 𝔽q = 2)]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
variable [h_β₀_eq_1 : Fact (β 0 = 1)]

section Algorithm
variable {ℓ R_rate : ℕ} (h_ℓ_add_R_rate : ℓ + R_rate < r)-- ℓ ∈ {1, ..., r-1}

/-- Define the mapping explicitly from the index k to the Submodule U. -/
def bitsToU (i : Fin r) (k : Fin (2 ^ i.val)) :
    AdditiveNTT.U (L := L) (𝔽q := 𝔽q) (β := β) i :=
  let val := (Finset.univ : Finset (Fin i)).sum fun j =>
    if (Nat.getBit (n := k.val) (k := j.val) == 1) then
      β ⟨j, by omega⟩
    else 0

  -- We essentially reuse your existing proof that this value is in the subspace
  ⟨val, by
    apply Submodule.sum_mem
    intro j _
    split
    · apply Submodule.subset_span
      -- refine ⟨j, ?_, rfl⟩
      refine Set.mem_image_of_mem β ?_
      rw [Set.mem_Ico]
      exact ⟨Fin.zero_le _, j.isLt⟩
    · exact Submodule.zero_mem _
  ⟩

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- The `bitsToU` mapping is a bijection: showing that iterating bits corresponds
exactly to the linear span. -/
theorem bitsToU_bijective (i : Fin r) :
  Function.Bijective (bitsToU (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate) i) := by
  -- A map between finite sets of the same size is bijective iff it is injective.
  apply (Fintype.bijective_iff_injective_and_card
    (f := bitsToU (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate) i)).mpr ?_
  constructor
  -- Part A: Injectivity (Linear Independence)
  · intro k1 k2 h_eq
    unfold bitsToU at h_eq
    simp only [Subtype.mk.injEq] at h_eq
    -- We define the coefficients c_j based on the bits of k
    let c (k : ℕ) (j : Fin i) : 𝔽q :=
      if (Nat.getBit (n := k) (k := j.val) == 1) then 1 else 0
    -- The sum can be rewritten as a linear combination with coefficients in Fq
    have h_sum (k : Fin (2^i.val)) :
      (Finset.univ.sum fun (j : Fin i) =>
        if (Nat.getBit (n := k.val) (k := j.val) == 1) then
          β ⟨j, by omega⟩
        else (0 : L)) =
      Finset.univ.sum fun j => (c k.val j) • β ⟨j, by omega⟩ := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [c]
      split_ifs <;> simp
    rw [h_sum k1, h_sum k2] at h_eq
    -- 1. Move everything to LHS: sum (c1 - c2) * beta = 0
    rw [←sub_eq_zero] at h_eq
    rw [←Finset.sum_sub_distrib] at h_eq
    simp_rw [←sub_smul] at h_eq
    rw [←sub_eq_zero] at h_eq
    -- 2. Establish that the first `i` basis elements are Linearly Independent
    have h_lin_indep := hβ_lin_indep.out
    -- We restrict the global independence (Fin r) to the subset (Fin i)
    have h_indep_restricted := LinearIndependent.comp h_lin_indep
      (Fin.castLE (Nat.le_of_lt_succ (by omega)) : Fin i → Fin r)
      (Fin.castLE_injective _)
    -- 3. Apply Linear Independence to show every coefficient is 0
    -- This gives us: ∀ j, c k1 j - c k2 j = 0
    simp only [sub_zero] at h_eq
    have h_coeffs_zero : ∀ j : Fin i, j ∈ Finset.univ → c k1.val j - c k2.val j = 0 :=
      linearIndependent_iff'.mp h_indep_restricted
        (Finset.univ)
        (fun j => c k1.val j - c k2.val j)
        h_eq
    -- 4. Prove k1 = k2 by showing all bits are equal
    ext
    apply Nat.eq_iff_eq_all_getBits.mpr
    intro n
    have h_bit_k1_lt_2 := Nat.getBit_lt_2 (n := k1) (k := n)
    have h_bit_k2_lt_2 := Nat.getBit_lt_2 (n := k2) (k := n)
    if hn : n < i.val then
      let j : Fin i := ⟨n, hn⟩
      have h_c_diff_zero := h_coeffs_zero j (Finset.mem_univ j)
      simp only [sub_eq_zero] at h_c_diff_zero
      dsimp only [beq_iff_eq, c] at h_c_diff_zero
      interval_cases hk1: Nat.getBit (n := k1) (k := j)
      · interval_cases hk2: Nat.getBit (n := k2) (k := j)
        · rfl;
        · simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl,
          zero_ne_one] at h_c_diff_zero;
      · interval_cases hk2: Nat.getBit (n := k2) (k := j)
        · simp only [BEq.rfl, ↓reduceIte, Nat.reduceBEq, Bool.false_eq_true,
          one_ne_zero] at h_c_diff_zero;
        · rfl
    else
      have h_k1 := Nat.getBit_of_lt_two_pow (n := i) (a := k1) (k := n)
      have h_k2 := Nat.getBit_of_lt_two_pow (n := i) (a := k2) (k := n)
      simp only [hn, ↓reduceIte] at h_k1 h_k2
      rw [h_k1, h_k2]
  -- Part B: Cardinality (Surjectivity check)
  · -- ⊢ Fintype.card (Fin (2 ^ ↑i)) = Fintype.card ↥(U i)
    rw [Fintype.card_fin]
    rw [AdditiveNTT.U_card (𝔽q := 𝔽q)
      (β := β) (i := i)]
    rw [hFq_card.out]

/-- Computes the elements of the subspace: `U_i = span({β_0, ..., β_{i-1}})`. -/
def getUElements (i : Fin r) : List L :=
  (List.finRange (2^i.val)).map fun k =>
    (Finset.univ : Finset (Fin i)).sum fun j =>
      if Nat.getBit (n := k.val) (k := j.val) == 1 then
        β ⟨j.val, by omega⟩
      else 0

/-- Evaluates the subspace vanishing polynomial `W_i(x) = ∏_{u ∈ U_i} (x - u).` -/
def evalWAt (i : Fin r) (x : L) : L :=
  ((getUElements (β := β) (ℓ := ℓ) (R_rate := R_rate) i).map (fun u => x - u)).prod

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Prove that `evalWAt` equals the standard definition of `W_i(x)`. -/
theorem evalWAt_eq_W (i : Fin r) (x : L) :
  evalWAt (β := β) (ℓ := ℓ) (R_rate := R_rate) (i := i) x =
    (W (𝔽q := 𝔽q) (β := β) (i := i)).eval x := by
  -- 1. Convert implementation to mathematical product over Fin(2^i)
  unfold evalWAt getUElements
  rw [List.map_map]
  rw [List.prod_finRange_eq_finset_prod] -- Now the pattern matches!
  -- 2. Prepare RHS
  rw [AdditiveNTT.W, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  -- 3. Use Finset.prod_bij to show equality via the bijection
  -- LHS: ∏ k : Fin(2^i), (x - bitsToU k), RHS: ∏ u : U i,      (x - u)
  apply Finset.prod_bij (s := ((Finset.univ (α := (Fin (2^(i.val)))))))
    (t := (Finset.univ : Finset (U 𝔽q β i)))
    (i := fun k _ =>
      bitsToU (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (r := r) (R_rate := R_rate) (L := L) (i := i) k)
    (hi := by
      -- Proof that the map lands in the target set (Finset.univ)
      intro a _
      exact Finset.mem_univ _)
    (i_inj := by
      -- Proof of Injectivity (uses our previous theorem)
      intro a₁ _ a₂ _ h_eq
      exact (bitsToU_bijective (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
        (r := r) (R_rate := R_rate) (L := L) (i := i)).1 h_eq)
    (i_surj := by
      -- Proof of Surjectivity (uses our previous theorem)
      intro b _
      -- We need to provide the element 'a' and the proof it is in the set
      obtain ⟨a, ha_eq⟩ := (bitsToU_bijective (𝔽q := 𝔽q)
        (β := β) (ℓ := ℓ) (r := r) (R_rate := R_rate) (L := L) (i := i)).2 b
      use a
      constructor
      · exact ha_eq
      · exact Finset.mem_univ a
    )
    (h := by -- Proof that the values are equal: (x - bitsToU k) = (x - (bitsToU k))
      intro a ha_univ
      rfl
    )

/-- Evaluates the normalized subspace vanishing polynomial `Ŵ_i(x) = W_i(x) / W_i(β_i)`. -/
def evalNormalizedWAt (i : Fin r) (x : L) : L :=
  let W_x := evalWAt (r := r) (L := L) (ℓ := ℓ) (β := β) (R_rate := R_rate) (i := i) x
  let beta_i := β i
  let W_beta := evalWAt (β := β) (ℓ := ℓ) (R_rate := R_rate) (i := i) beta_i
  W_x * W_beta⁻¹

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Prove that `evalNormalizedWAt` equals the standard definition of `Ŵ_i(x)`. -/
theorem evalNormalizedWAt_eq_normalizedW (i : Fin r) (x : L) :
  evalNormalizedWAt (β := β) (ℓ := ℓ) (R_rate := R_rate) (i := i) x
    = (normalizedW (𝔽q := 𝔽q) (β := β) (i := i)).eval x := by
  unfold evalNormalizedWAt
  -- 3. Apply the correctness theorem we just proved (evalWAt_eq_standardWAt)
  -- We apply it twice: once for 'x' and once for 'β i'
  rw [evalWAt_eq_W (r := r) (L := L) (𝔽q := 𝔽q) (β := β) i x]
  simp only
  rw [evalWAt_eq_W (r := r) (L := L) (𝔽q := 𝔽q) (β := β) i (β i)]
  -- normalizedW is defined as: C (eval (W i) (β i))⁻¹ * W i
  rw [AdditiveNTT.normalizedW]
  -- Property: (Constant * Poly).eval x = Constant * (Poly.eval x)
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  simp only [one_div]
  -- LHS: (W.eval x) * (W.eval beta)⁻¹, RHS: (W.eval beta)⁻¹ * (W.eval x)
  apply mul_comm

/-- Computes the twiddle factor used in the butterfly operation.
Corresponds to `AdditiveNTT.twiddleFactor`.
-/
def computableTwiddleFactor (i : Fin ℓ) (u : Fin (2 ^ (ℓ + R_rate - i - 1))) : L :=
  -- evalNormalizedWAt L i u
  ∑ (⟨k, hk⟩: Fin (ℓ + R_rate - i - 1)),
  if Nat.getBit k u.val = 1 then
    -- this branch maps to the above Nat.getBit = 1 branch
      -- (of evaluationPointω (i+1)) under (qMap i)(X)
    (evalNormalizedWAt (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (i := ⟨i, by omega⟩) (x := β ⟨i + 1 + k, by omega⟩))
  else 0

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Prove that `computableTwiddleFactor` equals the standard definition of `twiddleFactor`. -/
theorem computableTwiddleFactor_eq_twiddleFactor (i : Fin ℓ) :
  computableTwiddleFactor (r := r) (ℓ := ℓ) (β := β) (L := L)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) =
  twiddleFactor (𝔽q := 𝔽q) (L := L) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) := by
  unfold computableTwiddleFactor twiddleFactor
  simp_rw [evalNormalizedWAt_eq_normalizedW (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
    (R_rate := R_rate) (i := ⟨i, by omega⟩)]

/-- Performs one stage of the Additive NTT. This corresponds to `NTTStage` in the abstract
definition: `b` is the array of coefficients. `i` is the stage index (0 to r-1). -/
def computableNTTStage [Fact (LinearIndependent 𝔽q β)]
  (i : Fin ℓ) (b : Fin (2 ^ (ℓ + R_rate)) → L) : Fin (2^(ℓ + R_rate)) → L :=
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
    let twiddleFactor: L := computableTwiddleFactor (r := r) (ℓ := ℓ) (β := β) (L := L)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (u := ⟨u, by simp only; exact h_u_lt_2_pow⟩)
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

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Prove that `computableNTTStage` equals the standard definition of `NTTStage`. -/
theorem computableNTTStage_eq_NTTStage (i : Fin ℓ) :
  computableNTTStage (𝔽q := 𝔽q) (r := r) (L := L) (ℓ := ℓ) (β := β) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) =
  NTTStage (𝔽q := 𝔽q) (L := L) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) := by
  unfold computableNTTStage NTTStage
  simp only [Fin.eta]
  simp_rw [computableTwiddleFactor_eq_twiddleFactor (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
    (R_rate := R_rate) (i := ⟨i, by omega⟩)]

/-- The main computable Additive NTT function. `a` is the input array of coefficients.
`r` is the number of stages (dimension of the domain). The input array size must be at least 2^r. -/
def computableAdditiveNTT (a : Fin (2 ^ ℓ) → L) : Fin (2^(ℓ + R_rate)) → L :=
  let b: Fin (2^(ℓ + R_rate)) → L := tileCoeffs a -- Note: can optimize on this
  Fin.foldl (n:=ℓ) (f:= fun current_b i  =>
    computableNTTStage (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨ℓ - 1 - i, by omega⟩) (b:=current_b)
  ) (init:=b)

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Prove that `computableAdditiveNTT` equals the standard definition of `additiveNTT`. -/
theorem computableAdditiveNTT_eq_additiveNTT (a : Fin (2 ^ ℓ) → L) :
  computableAdditiveNTT (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (a := a) =
  additiveNTT (𝔽q := 𝔽q) (L := L) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (a := a) := by
  unfold computableAdditiveNTT additiveNTT
  simp only
  congr
  funext current_b i
  rw [computableNTTStage_eq_NTTStage (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨ℓ - 1 - i, by omega⟩)]

end Algorithm

section ConcreteBTFieldInstances

instance (k : ℕ) : NeZero (2^k) := by
  refine ⟨?_⟩
  have h₂ : (2 : ℕ) ≠ 0 := by decide
  simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]

/-- Computable basis for ConcreteBTField k over ConcreteBTField 0.
This is the explicit product of Z's. -/
def computableBasisExplicit (k : ℕ) (i : Fin (2 ^ k)) : ConcreteBTField k :=
  (Finset.univ : Finset (Fin k)).prod fun j =>
    if Nat.getBit (n := i.val) (k := j.val) == 1 then
      concreteTowerAlgebraMap (j.val + 1) k (by omega) (Z (j.val + 1))
    else
      1

omit [NeZero r] in
theorem hβ_lin_indep_concrete (k : ℕ) :
    letI := ConcreteBTFieldAlgebra (l:=0) (r:=k) (h_le:=by omega)
    LinearIndependent (R := ConcreteBTField 0)
      (v := computableBasisExplicit k) := by
  letI := ConcreteBTFieldAlgebra (l:=0) (r:=k) (h_le:=by omega)
  have h_eq : computableBasisExplicit k = fun i => multilinearBasis 0 k (by omega) i := by
    funext i
    unfold computableBasisExplicit
    rw [multilinearBasis_apply k 0 (by omega) i]
    simp only [beq_iff_eq, Nat.sub_zero, 𝕏, map_pow]
    congr 1
    funext x
    have h_lt := Nat.getBit_lt_2 (n := i) (k := x)
    by_cases h: Nat.getBit (k := x) (n := i) = 1
    · simp only [h, ↓reduceIte, pow_one]
      rw! (castMode := .all) [Nat.zero_add]
      rfl
    · have hBit_eq_0: Nat.getBit (k := x) (n := i) = 0 := by omega
      simp only [hBit_eq_0, zero_ne_one, ↓reduceIte, pow_zero]
  rw [h_eq]
  exact (multilinearBasis 0 k (by omega)).linearIndependent

abbrev BTF₃ := ConcreteBTField 3 -- 8 bits
instance : NeZero (2^3) := ⟨by norm_num⟩
instance : Field BTF₃ := instFieldConcrete
instance : DecidableEq BTF₃ := (inferInstance : DecidableEq (ConcreteBTField 3))
instance : Fintype BTF₃ := (inferInstance : Fintype (ConcreteBTField 3))

/-- Test of the computable additive NTT over BTF₃ (an 8-bit binary tower field `BTF₃`).
**Input polynomial:** p(x) = x (novel coefficients [7, 1, 0, 0]) of size `2^ℓ` in `BTF₃`
- `ℓ = 2`
- `R_rate = 2`: Repetition rate, evaluating at `S₀` of size `2^(ℓ + R_rate) = 16` points
- `r = 2^3 = 8`: Dimension of the basis for `BTF₃` over `GF(2)`
**Output:** A function `Fin 16 → BTF₃` giving the evaluations of `p(x) = x` at 16 points
in the evaluation domain `S₀` defined by the spanning basis elements `{β₀, ..., β_{ℓ + 𝓡 - 1}}`
of `BTF₃` over `GF(2)`. -/
def testNTTBTF₃ : Fin (2 ^ (2 + 2)) → BTF₃ := by
  let a : Fin 4 → BTF₃ := Array.toFinVec 4 #[7, 1, 0, 0] rfl
  letI : Algebra (ConcreteBTField 0) BTF₃ := ConcreteBTFieldAlgebra (l := 0) (r := 3)
    (h_le := by omega)
  haveI : Fact (LinearIndependent (ConcreteBTField 0) (computableBasisExplicit 3)) :=
    { out := hβ_lin_indep_concrete 3 }
  -- r is the size of the basis
  exact computableAdditiveNTT (𝔽q := ConcreteBTField 0) (L := BTF₃) (r := 2^3) (ℓ := 2)
    (R_rate := 2) (h_ℓ_add_R_rate := by omega) (β := computableBasisExplicit (k := 3)) (a := a)

-- #eval testNTTBTF₃
-- ![1#8, 0#8, 3#8, 2#8, 5#8, 4#8, 7#8, 6#8, 9#8, 8#8, 11#8, 10#8, 13#8, 12#8, 15#8, 14#8]

end ConcreteBTFieldInstances
end AdditiveNTT
