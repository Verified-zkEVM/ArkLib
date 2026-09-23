/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude.Folding

/-!
# Binary Basefold folding preserves polynomial evaluations
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec ProtocolSpec Polynomial MvPolynomial Binius.BinaryBasefold
open scoped NNReal Polynomial
open Finset AdditiveNTT Nat Matrix

noncomputable section       -- expands with 𝔽q in front
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}


section Essentials

section FoldTheory

/-- Evaluates polynomial P on the domain S⁽ʲ⁾.
    This function is index-agnostic: logic doesn't change based on the round. -/
def polyToOracleFunc {domainIdx : Fin r} (P : L[X]) :
    (sDomain 𝔽q β h_ℓ_add_R_rate domainIdx) → L :=
  fun y => P.eval y.val

omit [CharP L 2] [DecidableEq 𝔽q] [NeZero ℓ] in
/-- **Lemma 4.14** : if f⁽ⁱ⁾ is evaluation of P⁽ⁱ⁾(X) over S⁽ⁱ⁾, then fold(f⁽ⁱ⁾, r_chal)
  is evaluation of P⁽ⁱ⁺¹⁾(X) over S⁽ⁱ⁺¹⁾. At level `i = ℓ`, we have P⁽ˡ⁾ = c
-/
theorem fold_advances_evaluation_poly
    (i : Fin r) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
  (coeffs : Fin (2 ^ (ℓ - ↑i)) → L) (r_chal : L) : -- novel coeffs
  let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) coeffs
  let f_i := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := i) (P := P_i)
  let f_i_plus_1 := fold (i := i) (destIdx := destIdx) (h_destIdx := h_destIdx)
    (h_destIdx_le := h_destIdx_le) (f := f_i) (r_chal := r_chal)
  let new_coeffs := fun j : Fin (2^(ℓ - destIdx.val)) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      rw [←Nat.add_zero (j.val * 2)]
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx.val)
        (i := 0) (by omega) (by omega)
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx.val)
        (i := 1) (by omega) (by omega)
    ⟩)
  let P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by omega) new_coeffs
  f_i_plus_1 = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := destIdx) (P := P_i_plus_1) := by
  classical
  simp only
  funext y
  set fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
    h_destIdx h_destIdx_le (y := y)
  set x₀ := fiberMap 0
  set x₁ := fiberMap 1
  set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) coeffs
  set new_coeffs := fun j : Fin (2^(ℓ - destIdx)) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      have h : j.val * 2 < 2^(ℓ - destIdx) * 2 := by omega
      have h2 : 2^(ℓ - i) = 2^(ℓ - destIdx) * 2 := by
        conv_rhs => enter[2]; rw [←Nat.pow_one 2]
        rw [←pow_add]; congr
        rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega)]
        -- ⊢ ℓ - ↑i = ℓ - (↑i + 1 - 1)
        omega
      omega
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx) (i := 1)
      · omega
      · omega
    ⟩)
  have h_eval_qMap_x₀ : (AdditiveNTT.qMap 𝔽q β i (by omega)).eval x₀.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i h_destIdx h_destIdx_le x₀
    have h_val := congrArg Subtype.val h
    simp only at h_val
    rw [← h_val]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) h_destIdx h_destIdx_le
      (x := x₀) (y := y).mpr (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    exact congrArg Subtype.val h_res.symm
    -- exact qMap_eval_fiber_eq_self ⟦L⟧ ⟨i + 1, by omega⟩ (by simp only; omega) h_i_succ_lt y 0
  have h_eval_qMap_x₁ : (AdditiveNTT.qMap 𝔽q β i (by omega)).eval x₁.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i h_destIdx h_destIdx_le x₁
    have h_val := congrArg Subtype.val h
    simp only at h_val
    rw [← h_val]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) h_destIdx h_destIdx_le
      (x := x₁) (y := y).mpr (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    exact congrArg Subtype.val h_res.symm
  have hx₀ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)
    h_destIdx h_destIdx_le y 0
  have hx₁ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)
    h_destIdx h_destIdx_le y 1
  simp only [Fin.isValue] at hx₀ hx₁
  have h_fiber_diff : x₁.val - x₀.val = 1 := by
    simp only [Fin.isValue, x₁, x₀, fiberMap]
    rw [hx₁, hx₀]
    simp only [Fin.isValue, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    have h_index : ℓ + 𝓡 - i = (ℓ + 𝓡 - destIdx) + 1 := by omega
    rw! (castMode := .all) [h_index]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] -- (free_term + y_repr) - (free_term + y_repr) = 1
    -- First, simplify the free terms
    simp only [fiber_coeff, eqRec_eq_cast, lt_one_iff, reducePow, Fin.isValue,
      Fin.coe_ofNat_eq_mod, mod_succ, dite_smul, ite_smul, zero_smul, one_smul, zero_mod]
    have h_cast_0 :
        (cast (Eq.symm h_index ▸ rfl : Fin (ℓ + 𝓡 - ↑destIdx + 1) = Fin (ℓ + 𝓡 - ↑i)) 0).val =
        0 := by
      rw [←Fin.cast_eq_cast (h := by omega)]
      rw [Fin.cast_val_eq_val (h_eq := by omega)]
      simp only [Fin.coe_ofNat_eq_mod, mod_succ_eq_iff_lt, succ_eq_add_one, lt_add_iff_pos_left]
      omega
    simp only [h_cast_0, ↓reduceDIte]
    have h_getBit_0_of_0 : Nat.getBit (k := 0) (n := 0) = 0 := by
      simp only [getBit, shiftRight_zero, and_one_is_mod, zero_mod]
    have h_getBit_0_of_1 : Nat.getBit (k := 0) (n := 1) = 1 := by
      simp only [getBit, shiftRight_zero, Nat.and_self]
    simp only [h_getBit_0_of_1, one_ne_zero, ↓reduceIte, h_getBit_0_of_0, zero_add]
    rw! (castMode := .all) [←h_index]
    rw [cast_eq]
    simp only [get_sDomain_basis, Fin.coe_ofNat_eq_mod, zero_mod, add_zero, cast_eq]
    rw [normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β]
    -- ring
    conv_lhs => rw [←add_sub]
    conv_rhs => rw [←add_zero (a := 1)]
    rw [add_right_inj (a := 1)]
    rw [sub_eq_zero]
    apply Finset.sum_congr (h := by rfl)
    simp only [mem_univ, congr_eqRec, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ↓reduceDIte, add_tsub_cancel_right, Fin.eta, imp_self, implies_true]
  set P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by omega) new_coeffs
  -- Set up the even and odd refinement polynomials
  set P₀_coeffs := fun j : Fin (2^(ℓ - destIdx)) => coeffs ⟨j.val * 2, by
    have h1 : ℓ - destIdx + 1 = ℓ - i := by omega
    have h2 : 2^(ℓ - destIdx + 1) = 2^(ℓ - i) := by rw [h1]
    have h3 : 2^(ℓ - destIdx) * 2 = 2^(ℓ - destIdx + 1) := by rw [pow_succ]
    rw [← h2, ← h3]; omega⟩
  set P₁_coeffs := fun j : Fin (2^(ℓ - destIdx)) => coeffs ⟨j.val * 2 + 1, by
    have h1 : ℓ - destIdx + 1 = ℓ - i := by omega
    have h2 : 2^(ℓ - destIdx + 1) = 2^(ℓ - i) := by rw [h1]
    have h3 : 2^(ℓ - destIdx) * 2 = 2^(ℓ - destIdx + 1) := by rw [pow_succ]
    rw [← h2, ← h3]; omega⟩
  set P₀ := evenRefinement 𝔽q β h_ℓ_add_R_rate i (h_i := by omega) coeffs
  set P₁ := oddRefinement 𝔽q β h_ℓ_add_R_rate i (h_i := by omega) coeffs
  have h_P_i_eval := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate i (h_i := by omega) coeffs
  -- Equation 39 : P^(i)(X) = P₀^(i+1)(q^(i)(X)) + X · P₁^(i+1)(q^(i)(X))
  have h_equation_39_x₀ : P_i.eval x₀.val = P₀.eval y.val + x₀.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₀, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  have h_equation_39_x₁ : P_i.eval x₁.val = P₀.eval y.val + x₁.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₁, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  set f_i := fun (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i) => P_i.eval (x.val : L)
  set f_i_plus_1 := fold (i := i) (destIdx := destIdx) (h_destIdx := h_destIdx)
    (h_destIdx_le := h_destIdx_le) (f := f_i) (r_chal := r_chal)
  -- Unfold the definition of f_i_plus_1 using the fold function
  have h_fold_def : f_i_plus_1 y =
      f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
      f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := rfl
  -- Main calculation following the outline
  calc f_i_plus_1 y
    = f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
        f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := h_fold_def
    _ = P_i.eval x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
        P_i.eval x₁.val * (r_chal - (1 - r_chal) * x₀.val) := by simp only [f_i]
    _ = (P₀.eval y.val + x₀.val * P₁.eval y.val) * ((1 - r_chal) * x₁.val - r_chal) +
        (P₀.eval y.val + x₁.val * P₁.eval y.val) * (r_chal - (1 - r_chal) * x₀.val) := by
      rw [h_equation_39_x₀, h_equation_39_x₁]
    _ = P₀.eval y.val * ((1 - r_chal) * x₁.val - r_chal + r_chal - (1 - r_chal) * x₀.val) +
        P₁.eval y.val * (x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
          x₁.val * (r_chal - (1 - r_chal) * x₀.val)) := by ring
    _ = P₀.eval y.val * ((1 - r_chal) * (x₁.val - x₀.val)) +
        P₁.eval y.val * ((x₁.val - x₀.val) * r_chal) := by ring
    _ = P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal := by rw [h_fiber_diff]; ring
    _ = P_i_plus_1.eval y.val := by
      simp only [P_i_plus_1, P₀, P₁, new_coeffs, evenRefinement, oddRefinement,
        intermediateEvaluationPoly]
      conv_lhs => enter [1]; rw [mul_comm, ←Polynomial.eval_C_mul]
      conv_lhs => enter [2]; rw [mul_comm, ←Polynomial.eval_C_mul]
      -- ⊢ eval y (C (1-r) * ∑...) + eval y (C r * ∑...) = eval y (∑...)
      rw [←Polynomial.eval_add]
      -- ⊢ poly_left.eval y = poly_right.eval y
      congr! 1
      simp_rw [mul_sum, ←Finset.sum_add_distrib]
      have h_i_add_1_lt : i.val + 1 < r := by omega
      have h_destIdx_eq : destIdx = ⟨i + 1, h_i_add_1_lt⟩ := Fin.eq_of_val_eq (by omega)
      have h_fin_eq : Fin (2 ^ (ℓ - ↑i - 1)) = Fin (2 ^ (ℓ - ↑destIdx)) := by
        congr 1; congr 1; omega
      rw! (castMode := .all) [h_fin_eq]
      -- We now prove that the terms inside the sums are equal for each index.
      apply Finset.sum_congr (by congr!)
      -- simp only [mem_univ, map_sub, map_one, Fin.eta, map_add, map_mul, forall_const]
      intro j hj
      have h_j_lt : j.val < 2 ^ (ℓ - destIdx) := by omega
      subst h_destIdx_eq
      conv_lhs =>
        rw [mul_comm (a := Polynomial.C (coeffs ⟨j.val * 2, by
          rw [←Nat.add_zero (j.val * 2)]
          apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (i + 1))
            (i := 0) (by omega) (by omega)
          ⟩))]
        rw [←mul_assoc, mul_comm (a := Polynomial.C (1 - r_chal))]
        rw [mul_assoc]
      conv_lhs => enter [2]; rw [mul_comm (a := Polynomial.C (coeffs ⟨j.val * 2 + 1, by
        apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (i + 1))
          (i := 1) (by omega) (by omega)⟩)), ←mul_assoc,
        mul_comm (a := Polynomial.C r_chal)]; rw [mul_assoc]
      conv_rhs => rw [mul_comm]
      rw [←mul_add]
      congr
      simp only [←Polynomial.C_mul, ←Polynomial.C_add]

omit [CharP L 2] [DecidableEq 𝔽q] [NeZero ℓ] in
/-- **Lemma 4.14 Generalization** : if f⁽ⁱ⁾ is evaluation of P⁽ⁱ⁾(X) over S⁽ⁱ⁾,
then fold(f⁽ⁱ⁾, r_chal) is evaluation of P⁽ⁱ⁺¹⁾(X) over S⁽ⁱ⁺¹⁾.
At level `i = ℓ`, we have P⁽ˡ⁾ = c (constant polynomial).
-/
theorem iterated_fold_advances_evaluation_poly
    (i : Fin r) {destIdx : Fin r} (steps : ℕ) (h_destIdx : destIdx = i + steps)
  (h_destIdx_le : destIdx ≤ ℓ)
  (coeffs : Fin (2 ^ (ℓ - ↑i)) → L) (r_challenges : Fin steps → L) : -- novel coeffs
  let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) coeffs
  let f_i := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := i) (P := P_i)
  let f_i_plus_steps := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) h_destIdx h_destIdx_le (f := f_i) (r_challenges := r_challenges)
  let new_coeffs := fun j : Fin (2^(ℓ - destIdx)) =>
    ∑ m : Fin (2 ^ steps),
      multilinearWeight (r := r_challenges) (i := m) * coeffs ⟨j.val * 2 ^ steps + m.val, by
        apply index_bound_check j.val m.val (by rw [←h_destIdx]; omega) m.isLt (by omega)⟩
  let P_i_plus_steps :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by omega) new_coeffs
  f_i_plus_steps = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := destIdx) (P := P_i_plus_steps) := by
  classical
  revert destIdx h_destIdx h_destIdx_le
-- Induction on steps
  induction steps generalizing i with
  | zero =>
    intro destIdx h_destIdx h_destIdx_le
    simp only
    have h_i_eq_destIdx : i = destIdx := by omega
    subst h_i_eq_destIdx
    -- funext y -- Sum over Fin 1 (j=0)
    -- Base Case: 0 Steps
    dsimp only [iterated_fold, reduceAdd, Fin.val_castSucc, Fin.val_succ, Lean.Elab.WF.paramLet,
      id_eq, Fin.reduceLast, Fin.coe_ofNat_eq_mod, reduceMod, Nat.add_zero, Fin.eta,
      Fin.dfoldl_zero, Nat.pow_zero, multilinearWeight, Fin.val_eq_zero, zero_testBit,
      Bool.false_eq_true]
    simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, univ_eq_empty, Fin.val_eq_zero,
      zero_testBit, Bool.false_eq_true, ↓reduceIte, prod_empty, mul_one, add_zero, one_mul,
      sum_singleton, Subtype.coe_eta, Fin.dfoldl_zero, Fin.eta]
  | succ s ih =>
    intro destIdx h_destIdx h_destIdx_le
    simp only
    funext y
    -- 1. Unfold Fold (LHS)
    -- iterated_fold (s+1) = fold (iterated_fold s)
    set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) coeffs
    set f_i := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i) (P := P_i)
    let midIdx : Fin r := ⟨i + s, by omega⟩
    have h_midIdx : midIdx = i + s := by rfl
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := s)
      (h_midIdx := h_midIdx) (h_destIdx := by omega) (h_destIdx_le := by omega) (f := f_i)
      (r_challenges := r_challenges)]
    set f_i_plus_steps := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := s + 1) h_destIdx h_destIdx_le (f := f_i) (r_challenges := r_challenges)
    -- 2. Setup Inductive Step
    let r_s := Fin.init r_challenges
    let r_last := r_challenges (Fin.last s)
    -- Apply IH to the first s steps
    -- We need to construct the coefficients for step s
    let coeffs_s := fun j : Fin (2^(ℓ - (i + s))) =>
      ∑ m : Fin (2 ^ s),
        multilinearWeight (r := r_s) (i := m) * coeffs ⟨j.val * 2 ^ s + m.val, by
          apply index_bound_check j.val m.val j.isLt m.isLt (by omega)
        ⟩
    let f_folded_s_steps := (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := s) h_midIdx (by omega) (f := f_i) (r_challenges := r_s))
    let poly_eval_folded_s_steps :=
      polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := midIdx)
        (P := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate midIdx (h_i := by omega) coeffs_s)
    have h_eval_s : f_folded_s_steps = poly_eval_folded_s_steps := by
      unfold f_folded_s_steps poly_eval_folded_s_steps
      rw [ih (i := i)]
    unfold f_folded_s_steps at h_eval_s
    conv_lhs => rw [h_eval_s]
    -- 3. Apply Single Step Lemma
    -- fold(P_s, r_last) -> P_{s+1}
    -- The lemma fold_advances_evaluation_poly tells us the coefficients transform as:
    -- C_new[j] = (1 - r) * C_s[2j] + r * C_s[2j+1]
    let fold_advances_evaluation_poly_res := fold_advances_evaluation_poly 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (destIdx := destIdx)
      (h_destIdx := by omega) (h_destIdx_le := by omega) (coeffs := coeffs_s) (r_chal := r_last)
    simp only [r_last] at fold_advances_evaluation_poly_res
    unfold poly_eval_folded_s_steps
    conv_lhs => rw [fold_advances_evaluation_poly_res]
    --   ⊢ Polynomial.eval y ... = Polynomial.eval y ...
    congr 1
    congr 1
    funext (j : Fin (2 ^ (ℓ - destIdx)))
    unfold coeffs_s
    simp only
    have h_two_pow_s_succ_eq: 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by omega
    --- for rhs
    rw! (castMode := .all) [h_two_pow_s_succ_eq]
    rw [Fin.sum_univ_add]
    simp only [eqRec_eq_cast]
    rw [←Fin.cast_eq_cast (h := by omega)]
    simp only [Fin.val_castAdd, Fin.natAdd_eq_addNat, Fin.val_addNat]
    -- ∑ + ∑ = ∑ + ∑
    congr 1
    · conv_lhs => rw [mul_sum]
      congr 1
      funext (x : Fin (2 ^ s))
      conv_lhs => rw [←mul_assoc]
      congr 1
      · rw [multilinearWeight_succ_lower_half (h_lt := by simp only [Fin.val_cast, Fin.val_castAdd,
          Fin.is_lt])]
        rw [mul_comm]; rfl
      · simp_rw [←two_mul (n := 2 ^ s), ←mul_assoc]
    · conv_lhs => rw [mul_sum]
      congr 1
      funext (x : Fin (2 ^ s))
      conv_lhs => rw [←mul_assoc]
      congr 1
      · rw [multilinearWeight_succ_upper_half (r := r_challenges) (j := x)
          (h_eq := by simp only [Fin.val_cast, Fin.val_addNat]), mul_comm]
      · congr 1
        congr 1
        conv_lhs => rw [add_mul, one_mul, add_assoc]
        conv_rhs => rw [←two_mul (n := 2 ^ s), ←mul_assoc]
        omega

omit [DecidableEq L] [CharP L 2] [DecidableEq 𝔽q] h_Fq_char_prime
  hF₂ hβ_lin_indep h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma constantIntermediateEvaluationPoly_eval_eq_const
    (destIdx : Fin r) (coeffs : Fin (2 ^ (ℓ - destIdx.val)) → L)
  (h_destIdx : destIdx.val = ℓ) (x y : L) :
  let P := intermediateEvaluationPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := destIdx) (h_i := by omega) coeffs
  P.eval x = P.eval y := by
    intro P
    -- intermediateEvaluationPoly is a sum over Fin 1, which is just one term
    dsimp only [P, intermediateEvaluationPoly]
    rw [Finset.sum_eq_single (a := ⟨0, by
      simp only [Nat.ofNat_pos, pow_pos]⟩) (h₀ := fun j hj hj_ne => by
      have h_j_lt := j.isLt
      simp only [h_destIdx, tsub_self, pow_zero, Nat.lt_one_iff,
        Fin.val_eq_zero_iff] at h_j_lt -- j = 0
      simp only [Fin.mk_zero', ne_eq] at hj_ne
      exfalso; exact hj_ne h_j_lt
    ) (h₁ := fun h => by
      simp only [Fin.mk_zero', Finset.mem_univ, not_true_eq_false] at h)]
    -- By intermediateNovelBasisX_zero_eq_one, intermediateNovelBasisX ... 0 = 1
    rw [intermediateNovelBasisX_zero_eq_one 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (h_i := by omega)]
    -- So P = C (coeffs 0), which is constant
    simp only [Polynomial.eval_C, mul_one]

omit [CharP L 2] [DecidableEq 𝔽q] [NeZero ℓ] in
/-- When folding from level 0 all the way to level ℓ, the resulting function is constant
with value `t(challenges)`. -/
lemma iterated_fold_to_level_ℓ_eval
    (t : MultilinearPoly L ℓ) (destIdx : Fin r) (h_destIdx : destIdx.val = ℓ)
    (challenges : Fin ℓ → L) :
    let P₀ : L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => t.val.eval (bitsOfIndex ω))
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    let f_ℓ := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := ℓ)
      (destIdx := destIdx)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by omega)
      f₀ challenges
    f_ℓ = fun _ => t.val.eval challenges := by
  classical
  intro P₀ f₀ f_ℓ
  funext x
  let coeffs := fun (ω : Fin (2 ^ ℓ)) => t.val.eval (bitsOfIndex ω)
  have h_f_ℓ_eq_poly := iterated_fold_advances_evaluation_poly 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := ℓ) (destIdx := destIdx)
    (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
    (h_destIdx_le := by omega) (coeffs := coeffs) (r_challenges := challenges)
  -- h_f_ℓ_eq_poly says: f_ℓ = polyToOracleFunc P_ℓ where
  -- P_ℓ = intermediateEvaluationPoly with new_coeffs
  dsimp only [f_ℓ, f₀, P₀, polynomialFromNovelCoeffsF₂]
  -- Rewrite f_ℓ in terms of the intermediate polynomial at level ℓ.
  -- unfold polyToOracleFunc
  rw [←intermediate_poly_P_base 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_ℓ := by omega) (coeffs := coeffs)]
  -- Now f_ℓ x = (polyToOracleFunc P_ℓ) x = P_ℓ.eval x.val, and P_ℓ is constant.
  -- Evaluate both sides at x:
  have h_eq := congr_fun (h := h_f_ℓ_eq_poly) (a := x)
  conv_lhs => rw [h_eq]
  -- Use the lemma that the intermediate polynomial at level ℓ is the constant t(challenges).
  dsimp only [polyToOracleFunc]
  conv_rhs => rw [multilinear_eval_eq_sum_bool_hypercube]
  let new_coeffs : Fin (2 ^ (ℓ - destIdx.val)) → L := fun j =>
    ∑ m : Fin (2 ^ ℓ),
      multilinearWeight (r := challenges) (i := m) * coeffs ⟨j.val * 2 ^ ℓ + m.val, by
        have h_j : j.val = 0 := by
          have hj_lt := j.isLt
          simp only [h_destIdx, tsub_self, pow_zero, Nat.lt_one_iff] at hj_lt
          exact hj_lt
        rw [h_j, zero_mul, zero_add]
        exact m.isLt⟩
  change Polynomial.eval (↑x)
      (intermediateEvaluationPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := destIdx) (h_i := by omega) new_coeffs)
      = ∑ x, multilinearWeight challenges x * (MvPolynomial.eval (bitsOfIndex x)) ↑t
  have h_const_eval :
      Polynomial.eval (↑x)
        (intermediateEvaluationPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := destIdx) (h_i := by omega) new_coeffs)
      =
      Polynomial.eval (0 : L)
        (intermediateEvaluationPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := destIdx) (h_i := by omega) new_coeffs) := by
    exact constantIntermediateEvaluationPoly_eval_eq_const 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx) (coeffs := new_coeffs)
      (h_destIdx := h_destIdx) (x := ↑x) (y := 0)
  rw [h_const_eval]
  dsimp only [new_coeffs, intermediateEvaluationPoly]
  rw [Finset.sum_eq_single (a := ⟨0, by
    exact Nat.two_pow_pos (ℓ - destIdx.val)⟩) (h₀ := fun j _ hj_ne => by
    have h_j_lt := j.isLt
    simp only [h_destIdx, tsub_self, pow_zero, Nat.lt_one_iff, Fin.val_eq_zero_iff] at h_j_lt
    simp only [Fin.mk_zero', ne_eq] at hj_ne
    exfalso
    exact hj_ne h_j_lt
  ) (h₁ := fun h => by
    simp only [Fin.mk_zero', Finset.mem_univ, not_true_eq_false] at h)]
  rw [intermediateNovelBasisX_zero_eq_one 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := destIdx) (h_i := by omega)]
  simp only [Polynomial.eval_C, mul_one]
  apply Finset.sum_congr rfl
  intro m hm
  have h_idx_eq : (⟨0 * 2 ^ ℓ + m.val, by
      have h_j : (0 : Fin (2 ^ (ℓ - destIdx.val))).val = 0 := by
        simp only [Fin.val_zero]
      rw [zero_mul, zero_add]; exact m.isLt⟩ : Fin (2 ^ ℓ)) = m := by
    apply Fin.ext
    simp only [zero_mul, zero_add]
  rw [h_idx_eq]

omit [CharP L 2] [DecidableEq 𝔽q] [NeZero ℓ] in
/-- When folding from level 0 all the way to level ℓ, the resulting function is constant. -/
lemma iterated_fold_to_level_ℓ_is_constant
    (t : MultilinearPoly L ℓ) (destIdx : Fin r) (h_destIdx : destIdx.val = ℓ)
    (challenges : Fin ℓ → L) :
    let P₀ : L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => t.val.eval (bitsOfIndex ω))
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    let f_ℓ := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := ℓ)
      (destIdx := destIdx)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by omega)
      f₀ challenges
    ∀ x y, f_ℓ x = f_ℓ y := by
  classical
  intro P₀ f₀ f_ℓ x y
  dsimp only [f_ℓ]
  rw [iterated_fold_to_level_ℓ_eval 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by omega)]

end FoldTheory

/-- Given a point `v ∈ S^(0)`, extract the middle `steps` bits `{v_i, ..., v_{i+steps-1}}`
as a `Fin (2 ^ steps)`. -/
def extractMiddleFinMask (v : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨0, by exact pos_of_neZero r⟩)
    (i : Fin r) (steps : ℕ) : Fin (2 ^ steps) := by
  let vToFin := AdditiveNTT.sDomainToFin 𝔽q β h_ℓ_add_R_rate ⟨0, by
    exact pos_of_neZero r⟩ (by simp only [add_pos_iff]; left; exact pos_of_neZero ℓ) v
  simp only [tsub_zero] at vToFin
  let middleBits := Nat.getMiddleBits (offset := i.val) (len := steps) (n := vToFin.val)
  exact ⟨middleBits, Nat.getMiddleBits_lt_two_pow⟩

-- `eqTilde` is now defined generically in `ArkLib.Data.MvPolynomial.Multilinear` as
-- `MvPolynomial.eqTilde r r' := eval r' (eqPolynomial r)`, accessible here unqualified via the
-- file-level `open MvPolynomial`.

end Essentials

end
end Binius.BinaryBasefold
