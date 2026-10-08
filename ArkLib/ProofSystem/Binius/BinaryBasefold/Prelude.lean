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
  intro P_i f_i f_i_plus_1 new_coeffs P_i_plus_1
  funext y
  let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1) h_destIdx h_destIdx_le (y := y)
  have h_eval_qMap (k : Fin 2) :
      (AdditiveNTT.qMap 𝔽q β i (by omega)).eval (fiberMap k).val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i h_destIdx h_destIdx_le
      (fiberMap k)
    have h_val := congrArg Subtype.val h
    simp only at h_val
    rw [← h_val]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) h_destIdx
      h_destIdx_le (x := fiberMap k) (y := y).mpr
        (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    exact congrArg Subtype.val h_res.symm
  -- The two fiber points differ by the first basis vector of `S⁽ⁱ⁾`, which is `1`.
  have h_fiber_diff : (fiberMap 1).val - (fiberMap 0).val = 1 := by
    have hx₀ : fiberMap 0 = _ :=
      qMap_total_fiber_one_level_eq 𝔽q β i h_destIdx h_destIdx_le y 0
    have hx₁ : fiberMap 1 = _ :=
      qMap_total_fiber_one_level_eq 𝔽q β i h_destIdx h_destIdx_le y 1
    rw [hx₀, hx₁]
    simp only [Fin2ToF2, Fin.isValue, one_ne_zero, ↓reduceIte, one_smul, Submodule.coe_add,
      get_sDomain_first_basis_eq_1, zero_smul, zero_add, add_sub_cancel_right]
  let P₀ := evenRefinement 𝔽q β h_ℓ_add_R_rate i (h_i := by omega) coeffs
  let P₁ := oddRefinement 𝔽q β h_ℓ_add_R_rate i (h_i := by omega) coeffs
  have h_P_i_eval := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate i (h_i := by omega) coeffs
  -- Equation 39 : P^(i)(X) = P₀^(i+1)(q^(i)(X)) + X · P₁^(i+1)(q^(i)(X))
  have h_equation_39 (k : Fin 2) :
      P_i.eval (fiberMap k).val = P₀.eval y.val + (fiberMap k).val * P₁.eval y.val := by
    simp only [h_P_i_eval, Polynomial.eval_add, eval_comp,
      h_eval_qMap k, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  calc f_i_plus_1 y
    = P_i.eval (fiberMap 0).val * ((1 - r_chal) * (fiberMap 1).val - r_chal) +
        P_i.eval (fiberMap 1).val * (r_chal - (1 - r_chal) * (fiberMap 0).val) := rfl
    _ = P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal := by
      rw [h_equation_39 0, h_equation_39 1]
      linear_combination (P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal) * h_fiber_diff
    _ = P_i_plus_1.eval y.val := by
      obtain ⟨d, hd⟩ := destIdx
      obtain rfl : d = i.val + 1 := h_destIdx
      simp only [P_i_plus_1, P₀, P₁, new_coeffs, evenRefinement, oddRefinement,
        intermediateEvaluationPoly, Fin.eta, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

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
