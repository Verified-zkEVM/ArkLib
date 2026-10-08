/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude.Folding

/-!
# ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude

Definitions and results for this component of ArkLib.
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

noncomputable section -- expands with 𝔽q in front
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}


section Essentials

omit [CharP L 2] [DecidableEq 𝔽q] [NeZero ℓ] in
/-- Lemma 4.13 : if f⁽ⁱ⁾ is evaluation of P⁽ⁱ⁾(X) over S⁽ⁱ⁾, then fold(f⁽ⁱ⁾, r_chal)
  is evaluation of P⁽ⁱ⁺¹⁾(X) over S⁽ⁱ⁺¹⁾. At level `i = ℓ`, we have P⁽ˡ⁾ =
-/
theorem fold_advances_evaluation_poly
    (i : Fin (ℓ)) (h_i_succ_lt : i + 1 < ℓ + 𝓡)
  (coeffs : Fin (2 ^ (ℓ - ↑i)) → L) (r_chal : L) :
  let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) (h_i := by simp only; omega) coeffs
  let f_i := fun (x : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_trans (n := i) (k := r) (m := ℓ) (h₁ := by omega) (by omega)⟩) =>
    P_i.eval (x.val : L)
  let f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := by omega) (f := f_i) (r_chal := r_chal)
  let new_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      rw [←Nat.add_zero (j.val * 2)]
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
        (i := 0) (by omega) (by omega)
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
        (i := 1) (by omega) (by omega)
    ⟩)
  let P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i + 1, by omega⟩) (h_i := by simp only; omega) new_coeffs
  ∀ (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i+1, by omega⟩), f_i_plus_1 y = P_i_plus_1.eval y.val := by
  classical
  intro P_i f_i f_i_plus_1 new_coeffs P_i_plus_1 y
  let fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := 1)
    (h_i_add_steps := by simp only; omega) (y := y)
  let x₀ := fiberMap 0
  let x₁ := fiberMap 1
  have h_eval_qMap (k : Fin 2) : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩
      (by simp only; omega)).eval (fiberMap k).val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (destIdx := ⟨i + 1, by omega⟩)
      (h_destIdx := by simp) (h_destIdx_le := by simp only; omega) (fiberMap k)
    simp only [Subtype.ext_iff] at h
    rw [h.symm]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) (by omega)
      (x := fiberMap k) (y := y).mpr
        (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
  -- The two fiber points differ by the first basis vector of `S⁽ⁱ⁾`, which is `1`.
  have h_fiber_diff : x₁.val - x₀.val = 1 := by
    have hx₀ : x₀ = _ := qMap_total_fiber_one_level_eq 𝔽q β i (by omega) y 0
    have hx₁ : x₁ = _ := qMap_total_fiber_one_level_eq 𝔽q β i (by omega) y 1
    rw [hx₀, hx₁]
    simp only [Fin2ToF2, Fin.isValue, one_ne_zero, ↓reduceIte, one_smul, Submodule.coe_add,
      get_sDomain_first_basis_eq_1, zero_smul, zero_add, add_sub_cancel_right]
  let P₀ := evenRefinement 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) (h_i := by simp only; omega) coeffs
  let P₁ := oddRefinement 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) (h_i := by simp only; omega) coeffs
  have h_P_i_eval := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) (h_i := by simp only; omega) coeffs
  -- Equation 39 : P^(i)(X) = P₀^(i+1)(q^(i)(X)) + X · P₁^(i+1)(q^(i)(X))
  have h_equation_39 (k : Fin 2) :
      P_i.eval (fiberMap k).val = P₀.eval y.val + (fiberMap k).val * P₁.eval y.val := by
    simp only [h_P_i_eval, Polynomial.eval_add, eval_comp,
      h_eval_qMap k, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  calc f_i_plus_1 y
    = P_i.eval x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
        P_i.eval x₁.val * (r_chal - (1 - r_chal) * x₀.val) := rfl
    _ = P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal := by
      rw [h_equation_39 0, h_equation_39 1]
      linear_combination (P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal) * h_fiber_diff
    _ = P_i_plus_1.eval y.val := by
      simp only [P_i_plus_1, P₀, P₁, new_coeffs, evenRefinement, oddRefinement,
        intermediateEvaluationPoly, Fin.eta, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

/-- Given a point `v ∈ S^(0)`, extract the middle `steps` bits `{v_i, ..., v_{i+steps-1}}`
as a `Fin (2 ^ steps)`. -/
def extractMiddleFinMask (v : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨0, by exact pos_of_neZero r⟩)
    (i : Fin ℓ) (steps : ℕ) : Fin (2 ^ steps) := by
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
