/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.JohnsonLower.BinaryBasics
public import ArkLib.Data.Polynomial.SubspacePolynomial

/-!
# Reed--Solomon lower bound at the Johnson radius

This file proves the characteristic-two BCHKS25 construction using graphs of binary matrices,
subspace polynomials (`Polynomial.subspacePolynomial`), and Schwartz--Zippel.

The binary functionals live in `JohnsonLower.BinaryBasics`; this module develops the separator
construction and the public Reed--Solomon lower bound.

## Main result

- `exists_rs_epsCa_large_at_johnson_radius` is [BCHKS25, Corollary 1.7].

## References

- [BCHKS25] Corollary 1.7.
-/

@[expose] public section

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open JohnsonLowerInternal

private def binary_matrix_distinguishing_tuple {b : ℕ}
    (N : Matrix (Fin 2) (Fin b) (ZMod 2)) (j : Fin 2) : Fin (b + 2) → ZMod 2 :=
  Fin.append (fun i => -N j i) (fun j' => if j' = j then 1 else 0)

private theorem binary_matrix_parameter_card (b : ℕ) :
    Fintype.card (Matrix (Fin 2) (Fin b) (ZMod 2)) = 2 ^ (2 * b) := by
  change Fintype.card (Fin 2 → Fin b → ZMod 2) = _
  simp [ZMod.card, ← pow_mul, Nat.mul_comm]

private noncomputable def binary_matrix_row_difference_functional {b : ℕ}
    (M N : Matrix (Fin 2) (Fin b) (ZMod 2)) (j : Fin 2) :
    (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj j : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2).comp
    (Matrix.mulVecLin M - Matrix.mulVecLin N)

open scoped BigOperators in
private theorem binary_matrix_row_difference_functional_apply_basis {b : ℕ}
    (A N : Matrix (Fin 2) (Fin b) (ZMod 2)) (j : Fin 2) (i : Fin b) :
    binary_matrix_row_difference_functional A N j (binary_basis_vector i) =
      A j i - N j i := by
  classical
  unfold binary_matrix_row_difference_functional binary_basis_vector
  simp [Matrix.mulVec, dotProduct]

private theorem binary_matrix_row_difference_functional_ne_zero {b : ℕ}
    (A N : Matrix (Fin 2) (Fin b) (ZMod 2)) (j : Fin 2) (hrow : A j ≠ N j) :
    binary_matrix_row_difference_functional A N j ≠ 0 := by
  rcases Function.ne_iff.mp hrow with ⟨i, hi⟩
  intro hzero
  have hval := congrArg (fun f => f (binary_basis_vector i)) hzero
  rw [binary_matrix_row_difference_functional_apply_basis] at hval
  simp only [LinearMap.zero_apply] at hval
  exact hi (sub_eq_zero.mp hval)

private theorem binary_matrix_row_difference_functional_self {b : ℕ}
    (M : Matrix (Fin 2) (Fin b) (ZMod 2)) (j : Fin 2) :
    binary_matrix_row_difference_functional M M j = 0 := by
  ext x
  simp [binary_matrix_row_difference_functional]

open scoped NNReal in
private theorem binary_matrix_exponent_real_le
    (ε : ℝ≥0) (r : ℕ)
    (hscale : (2 : ℝ) ≤ (ε : ℝ) * (r + 4)) :
    ((r + 4 : ℕ) : ℝ) * (2 * ((1 : ℝ) - ε)) ≤
      ((2 * (r + 2) : ℕ) : ℝ) := by
  push_cast
  nlinarith

open scoped NNReal ENNReal in
private theorem binary_matrix_exponent_ennreal_le
    (ε : ℝ≥0) (r : ℕ)
    (hscale : (2 : ℝ) ≤ (ε : ℝ) * (r + 4)) :
    (((16 * 2 ^ r : ℕ) : ENNReal) ^ (2 * ((1 : ℝ) - ε))) ≤
      ((2 ^ (2 * (r + 2)) : ℕ) : ENNReal) := by
  have hexp := binary_matrix_exponent_real_le ε r hscale
  have hbase : 16 * 2 ^ r = 2 ^ (r + 4) := by
    rw [pow_add]
    norm_num
    ring
  rw [hbase]
  push_cast
  rw [← ENNReal.rpow_natCast_mul (2 : ENNReal) (r + 4)
    (2 * ((1 : ℝ) - ε))]
  rw [← ENNReal.rpow_natCast (2 : ENNReal) (2 * (r + 2))]
  exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp

private theorem binary_product_index_card (b : ℕ) :
    Fintype.card ((Fin b → ZMod 2) × (Fin 2 → ZMod 2)) = 2 ^ (b + 2) := by
  simp [Fintype.card_prod, ZMod.card, pow_add]

private theorem binary_product_index_card_add_two (r : ℕ) :
    Fintype.card ((Fin (r + 2) → ZMod 2) × (Fin 2 → ZMod 2)) =
      16 * 2 ^ r := by
  rw [binary_product_index_card]
  have h : r + 2 + 2 = r + 4 := by omega
  rw [h, pow_add]
  norm_num
  ring

private def binary_product_left_basis_tuple {b : ℕ} (i : Fin b) :
    Fin (b + 2) → ZMod 2 :=
  Fin.append (fun i' => if i' = i then 1 else 0) (fun _ => 0)

open scoped BigOperators in
private noncomputable def binary_product_linear_form_mv {b : ℕ}
    (w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2)) :
    MvPolynomial (Fin (b + 2)) (ZMod 2) :=
  (∑ i : Fin b, MvPolynomial.C (w.1 i) * MvPolynomial.X (Fin.castAdd 2 i)) +
    ∑ j : Fin 2, MvPolynomial.C (w.2 j) * MvPolynomial.X (Fin.natAdd b j)

open scoped BigOperators in
private noncomputable def binary_matrix_lambda_mv {b : ℕ}
    (M : Matrix (Fin 2) (Fin b) (ZMod 2)) : MvPolynomial (Fin (b + 2)) (ZMod 2) := by
  classical
  exact (∏ x : Fin b → ZMod 2,
    (Polynomial.X - Polynomial.C
      (binary_product_linear_form_mv (x, Matrix.mulVecLin M x)))).coeff
        (2 ^ (b - 1))

open scoped BigOperators in
private noncomputable def binary_matrix_direct_configuration_separator (b : ℕ) :
    MvPolynomial (Fin (b + 2)) (ZMod 2) := by
  classical
  exact
    (∏ w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2),
      if w = 0 then 1 else binary_product_linear_form_mv w) *
    (∏ M : Matrix (Fin 2) (Fin b) (ZMod 2), ∏ N : Matrix (Fin 2) (Fin b) (ZMod 2),
      if M = N then 1 else binary_matrix_lambda_mv M - binary_matrix_lambda_mv N)

private noncomputable def binary_matrix_good_coefficients
    {K : Type} [Field K] [DecidableEq K] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K) : Finset K := by
  exact Finset.univ.image (fun M : Matrix (Fin 2) (Fin b) (ZMod 2) =>
    MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binary_matrix_lambda_mv M))

private theorem binary_matrix_good_coefficients_card
    {K : Type} [Field K] [DecidableEq K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K)
    (hinj : Function.Injective (fun M : Matrix (Fin 2) (Fin b) (ZMod 2) =>
      MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binary_matrix_lambda_mv M))) :
    (binary_matrix_good_coefficients (K := K) (b := b) t).card = 2 ^ (2 * b) := by
  unfold binary_matrix_good_coefficients
  rw [Finset.card_image_of_injective Finset.univ hinj,
    Finset.card_univ, binary_matrix_parameter_card]

private theorem binary_matrix_good_coefficients_mem
    {K : Type} [Field K] [DecidableEq K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K) (γ : K) :
    γ ∈ binary_matrix_good_coefficients (K := K) (b := b) t ↔
      ∃ M : Matrix (Fin 2) (Fin b) (ZMod 2),
        MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
          (binary_matrix_lambda_mv M) = γ := by
  unfold binary_matrix_good_coefficients
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

private noncomputable def binary_matrix_separator_threshold (b : ℕ) : ℕ :=
  (binary_matrix_direct_configuration_separator b).totalDegree + 1

open scoped BigOperators in
private theorem binary_product_linear_form_mv_eval_distinguishing_tuple {b : ℕ}
    (A N : Matrix (Fin 2) (Fin b) (ZMod 2)) (j : Fin 2) (x : Fin b → ZMod 2) :
    MvPolynomial.eval (binary_matrix_distinguishing_tuple N j)
      (binary_product_linear_form_mv (x, Matrix.mulVecLin A x)) =
        binary_matrix_row_difference_functional A N j x := by
  classical
  have hcomm (r : Fin 2) :
      (∑ i : Fin b, x i * N r i) = ∑ i : Fin b, N r i * x i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  unfold binary_product_linear_form_mv binary_matrix_distinguishing_tuple
    binary_matrix_row_difference_functional
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, ZMod.neg_eq_self_mod_two, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, map_sum, Fin.sum_univ_two, map_add, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.append_left, Fin.append_right,
      ↓reduceIte, mul_one, one_ne_zero, mul_zero, add_zero, LinearMap.coe_comp,
      LinearMap.coe_proj, Function.comp_apply, Function.eval, LinearMap.sub_apply,
      Pi.sub_apply]
    rw [CharTwo.sub_eq_add, hcomm]
    ac_rfl
  · simp only [Fin.mk_one, Fin.isValue, ZMod.neg_eq_self_mod_two, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, map_sum, Fin.sum_univ_two, map_add, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.append_left, Fin.append_right,
      zero_ne_one, ↓reduceIte, mul_zero, mul_one, zero_add, LinearMap.coe_comp,
      LinearMap.coe_proj, Function.comp_apply, Function.eval, LinearMap.sub_apply,
      Pi.sub_apply]
    rw [CharTwo.sub_eq_add, hcomm]
    ac_rfl

open scoped BigOperators in
private theorem binary_matrix_lambda_mv_eval_distinguishing_tuple {b : ℕ}
    (A N : Matrix (Fin 2) (Fin b) (ZMod 2)) (j : Fin 2) :
    MvPolynomial.eval (binary_matrix_distinguishing_tuple N j)
        (binary_matrix_lambda_mv A) =
      (binary_functional_root_polynomial
        (binary_matrix_row_difference_functional A N j)).coeff (2 ^ (b - 1)) := by
  classical
  unfold binary_matrix_lambda_mv binary_functional_root_polynomial
  rw [← MvPolynomial.coeff_eval_eq_eval_coeff (Fin (b + 2))
    (binary_matrix_distinguishing_tuple N j)]
  apply congrArg (fun p : Polynomial (ZMod 2) => p.coeff (2 ^ (b - 1)))
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro x hx
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [binary_product_linear_form_mv_eval_distinguishing_tuple]

open scoped BigOperators in
private theorem binary_matrix_lambda_mv_injective {b : ℕ} (hb : 0 < b) :
    Function.Injective (binary_matrix_lambda_mv (b := b)) := by
  intro A N hEq
  by_contra hAN
  have hrowEx : ∃ j : Fin 2, A j ≠ N j := by
    by_contra hnone
    apply hAN
    funext j
    by_contra hrow
    exact hnone ⟨j, hrow⟩
  rcases hrowEx with ⟨j, hrow⟩
  have hne : binary_matrix_row_difference_functional A N j ≠ 0 :=
    binary_matrix_row_difference_functional_ne_zero A N j hrow
  have hEvalA :
      MvPolynomial.eval (binary_matrix_distinguishing_tuple N j)
        (binary_matrix_lambda_mv A) = 1 := by
    rw [binary_matrix_lambda_mv_eval_distinguishing_tuple,
      binary_functional_lambda_one _ hne]
  have hEvalN :
      MvPolynomial.eval (binary_matrix_distinguishing_tuple N j)
        (binary_matrix_lambda_mv N) = 0 := by
    rw [binary_matrix_lambda_mv_eval_distinguishing_tuple,
      binary_matrix_row_difference_functional_self, binary_functional_lambda_zero b hb]
  have hcongr := congrArg
    (fun p => MvPolynomial.eval (binary_matrix_distinguishing_tuple N j) p) hEq
  rw [hEvalA, hEvalN] at hcongr
  exact one_ne_zero hcongr

open scoped BigOperators in
private theorem binary_product_linear_form_mv_eval_left_basis {b : ℕ}
    (w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2)) (i : Fin b) :
    MvPolynomial.eval (binary_product_left_basis_tuple i)
      (binary_product_linear_form_mv w) = w.1 i := by
  classical
  unfold binary_product_linear_form_mv binary_product_left_basis_tuple
  simp [Fin.append_left, Fin.append_right]

private def binary_product_right_basis_tuple {b : ℕ} (j : Fin 2) :
    Fin (b + 2) → ZMod 2 :=
  Fin.append (fun _ => 0) (fun j' => if j' = j then 1 else 0)

open scoped BigOperators in
private theorem binary_product_linear_form_mv_eval_right_basis {b : ℕ}
    (w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2)) (j : Fin 2) :
    MvPolynomial.eval (binary_product_right_basis_tuple (b := b) j)
      (binary_product_linear_form_mv w) = w.2 j := by
  classical
  unfold binary_product_linear_form_mv binary_product_right_basis_tuple
  fin_cases j <;> simp [Fin.append_left, Fin.append_right]

open scoped BigOperators in
private theorem binary_product_linear_form_mv_ne_zero {b : ℕ}
    (w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2)) (hw : w ≠ 0) :
    binary_product_linear_form_mv w ≠ 0 := by
  classical
  by_cases hleft : w.1 = 0
  · have hright : w.2 ≠ 0 := by
      intro h
      apply hw
      apply Prod.ext
      · exact hleft
      · exact h
    rcases Function.ne_iff.mp hright with ⟨j, hj⟩
    intro hzero
    have heval := congrArg
      (fun p => MvPolynomial.eval (binary_product_right_basis_tuple (b := b) j) p) hzero
    rw [binary_product_linear_form_mv_eval_right_basis] at heval
    simp only [map_zero] at heval
    exact hj heval
  · rcases Function.ne_iff.mp hleft with ⟨i, hi⟩
    intro hzero
    have heval := congrArg
      (fun p => MvPolynomial.eval (binary_product_left_basis_tuple i) p) hzero
    rw [binary_product_linear_form_mv_eval_left_basis] at heval
    simp only [map_zero] at heval
    exact hi heval

open scoped BigOperators in
private theorem binary_matrix_configuration_separator_left_ne_zero (b : ℕ) :
    (∏ w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2),
      if w = 0 then (1 : MvPolynomial (Fin (b + 2)) (ZMod 2))
      else binary_product_linear_form_mv w) ≠ 0 := by
  classical
  rw [Finset.prod_ne_zero_iff]
  intro w hw
  by_cases hzero : w = 0
  · rw [ite_eq_left hzero]
    exact one_ne_zero
  · rw [ite_eq_right hzero]
    exact binary_product_linear_form_mv_ne_zero w hzero

open scoped BigOperators in
private theorem binary_matrix_direct_configuration_separator_ne_zero_of_injective (b : ℕ)
    (hinj : Function.Injective (binary_matrix_lambda_mv (b := b))) :
    binary_matrix_direct_configuration_separator b ≠ 0 := by
  classical
  unfold binary_matrix_direct_configuration_separator
  apply mul_ne_zero
  · exact binary_matrix_configuration_separator_left_ne_zero b
  · rw [Finset.prod_ne_zero_iff]
    intro M hM
    rw [Finset.prod_ne_zero_iff]
    intro N hN
    by_cases hMN : M = N
    · rw [ite_eq_left hMN]
      exact one_ne_zero
    · rw [ite_eq_right hMN]
      exact sub_ne_zero.mpr (hinj.ne hMN)

open scoped BigOperators in
private theorem binary_matrix_direct_configuration_separator_ne_zero
    (b : ℕ) (hb : 0 < b) :
    binary_matrix_direct_configuration_separator b ≠ 0 :=
  binary_matrix_direct_configuration_separator_ne_zero_of_injective b
    (binary_matrix_lambda_mv_injective hb)

open scoped BigOperators in
private noncomputable def binary_product_tuple_linear_map {K : Type} [Field K]
    [Algebra (ZMod 2) K] {b : ℕ} (t : Fin (b + 2) → K) :
    ((Fin b → ZMod 2) × (Fin 2 → ZMod 2)) →ₗ[ZMod 2] K where
  toFun w :=
    (∑ i : Fin b, w.1 i • t (Fin.castAdd 2 i)) +
      ∑ j : Fin 2, w.2 j • t (Fin.natAdd b j)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
    rw [smul_add, Finset.smul_sum, Finset.smul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul]
      rfl
    · apply Finset.sum_congr rfl
      intro j hj
      rw [smul_smul]
      rfl

open scoped BigOperators in
private theorem binary_product_linear_form_mv_eval₂
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K)
    (w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2)) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
      (binary_product_linear_form_mv w) = binary_product_tuple_linear_map t w := by
  classical
  unfold binary_product_linear_form_mv binary_product_tuple_linear_map
  simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    Algebra.smul_def]
  rfl

open scoped BigOperators in
private theorem binary_matrix_generic_tuple_of_separator_eval_ne_zero
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K)
    (heval : MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
      (binary_matrix_direct_configuration_separator b) ≠ 0) :
    Function.Injective (binary_product_tuple_linear_map t) ∧
      Function.Injective (fun M : Matrix (Fin 2) (Fin b) (ZMod 2) =>
        MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binary_matrix_lambda_mv M)) := by
  classical
  unfold binary_matrix_direct_configuration_separator at heval
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod] at heval
  rcases mul_ne_zero_iff.mp heval with ⟨hleft, hright⟩
  rw [Finset.prod_ne_zero_iff] at hleft hright
  constructor
  · intro x y hxy
    by_contra hne
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hfactor := hleft (x - y) (Finset.mem_univ _)
    rw [ite_eq_right hsub, binary_product_linear_form_mv_eval₂] at hfactor
    apply hfactor
    rw [LinearMap.map_sub, hxy, sub_self]
  · intro M N hMNval
    by_contra hMN
    have hinner := hright M (Finset.mem_univ _)
    rw [Finset.prod_ne_zero_iff] at hinner
    have hfactor := hinner N (Finset.mem_univ _)
    rw [ite_eq_right hMN] at hfactor
    apply hfactor
    rw [MvPolynomial.eval₂_sub]
    exact sub_eq_zero.mpr hMNval

/-- The graph `x ↦ t(x, M x)` of `M` composed with the tuple form `t`. -/
private noncomputable def binary_matrix_graph_hom {K : Type} [Field K] [Algebra (ZMod 2) K] {b : ℕ}
    (t : Fin (b + 2) → K) (M : Matrix (Fin 2) (Fin b) (ZMod 2)) : (Fin b → ZMod 2) →+ K :=
  ((binary_product_tuple_linear_map t).comp (LinearMap.id.prod (Matrix.mulVecLin M))).toAddMonoidHom

open scoped BigOperators in
private theorem binary_matrix_lambda_eval_eq_coeff
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K)
    (M : Matrix (Fin 2) (Fin b) (ZMod 2)) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binary_matrix_lambda_mv M) =
      (∏ x : Fin b → ZMod 2, (Polynomial.X - Polynomial.C (binary_matrix_graph_hom t M x))).coeff
        (2 ^ (b - 1)) := by
  classical
  unfold binary_matrix_lambda_mv
  rw [MvPolynomial.eval₂_eq_eval_map, ← Polynomial.coeff_map,
    ← MvPolynomial.coeff_eval_eq_eval_coeff (Fin (b + 2)) t]
  apply congrArg (fun p : Polynomial K => p.coeff (2 ^ (b - 1)))
  rw [Polynomial.map_prod, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, MvPolynomial.eval_map, binary_product_linear_form_mv_eval₂]
  rfl

open scoped NNReal ProbabilityTheory in
private theorem eps_ca_lower_of_finset_witness
    {ι F A : Type} [Fintype ι]
    [Field F] [Fintype F] [SampleableType F]
    [Finite A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0)
    (u : Code.WordStack A (Fin 2) ι) (S : Finset F)
    (hnot : ¬ Code.jointProximity C (u := u) δ_int)
    (hclose : ∀ γ ∈ S, δᵣ(u 0 + γ • u 1, C) ≤ (δ_fld : ENNReal)) :
    (S.card : ENNReal) / (Fintype.card F : ENNReal) ≤
      ProximityGap.epsCa (F := F) (A := A) C δ_fld δ_int := by
  classical
  let _ := Fintype.ofFinite A
  simp only [ProximityGap.epsCa_eq]
  refine le_trans ?_ (le_iSup _ u)
  rw [ite_eq_right hnot]
  rw [SampleableType.prEvent_uniformSample]
  apply ENNReal.div_le_div_right
  exact_mod_cast Finset.card_le_card (by
    intro γ hγ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hclose γ hγ⟩)

open scoped NNReal in
private theorem exists_binary_matrix_scale_parameter
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ r : ℕ, (2 : ℝ) ≤ (ε : ℝ) * (r + 4) := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨r, hr⟩ := Archimedean.arch (2 : ℝ) hεR
  refine ⟨r, ?_⟩
  simp only [nsmul_eq_mul] at hr
  have hεnonneg : (0 : ℝ) ≤ (ε : ℝ) := by positivity
  nlinarith

open scoped NNReal ENNReal in
private theorem exists_binary_matrix_exponent_parameter
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ r : ℕ,
      (((16 * 2 ^ r : ℕ) : ENNReal) ^ (2 * ((1 : ℝ) - ε))) ≤
        ((2 ^ (2 * (r + 2)) : ℕ) : ENNReal) := by
  obtain ⟨r, hr⟩ := exists_binary_matrix_scale_parameter ε hε
  exact ⟨r, binary_matrix_exponent_ennreal_le ε r hr⟩

private noncomputable def mapped_binary_matrix_direct_configuration_separator
    {K : Type} [Field K] [Algebra (ZMod 2) K] (b : ℕ) :
    MvPolynomial (Fin (b + 2)) K :=
  MvPolynomial.map (algebraMap (ZMod 2) K)
    (binary_matrix_direct_configuration_separator b)

open scoped BigOperators in
private theorem mapped_binary_matrix_direct_configuration_separator_ne_zero_of_injective
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K] (b : ℕ)
    (hinj : Function.Injective (binary_matrix_lambda_mv (b := b))) :
    mapped_binary_matrix_direct_configuration_separator (K := K) b ≠ 0 := by
  intro hzero
  apply binary_matrix_direct_configuration_separator_ne_zero_of_injective b hinj
  apply MvPolynomial.map_injective (f := algebraMap (ZMod 2) K)
    (RingHom.injective (algebraMap (ZMod 2) K))
  unfold mapped_binary_matrix_direct_configuration_separator at hzero
  simpa only [map_zero] using hzero

open scoped BigOperators in
private theorem mapped_binary_matrix_direct_configuration_separator_ne_zero
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (b : ℕ) (hb : 0 < b) :
    mapped_binary_matrix_direct_configuration_separator (K := K) b ≠ 0 :=
  mapped_binary_matrix_direct_configuration_separator_ne_zero_of_injective b
    (binary_matrix_lambda_mv_injective hb)

private theorem mv_polynomial_fin_exists_eval_ne_zero_of_total_degree_lt_card
    {n : ℕ} {K : Type} [Field K] [Fintype K]
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (hdeg : p.totalDegree < Fintype.card K) :
    ∃ t : Fin n → K, MvPolynomial.eval t p ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  have hone : (1 : ℚ≥0) ≤
      (p.totalDegree : ℚ≥0) / (Fintype.card K : ℚ≥0) := by
    simpa [hall, Fintype.card_ne_zero] using hsz
  have hcardpos : (0 : ℚ≥0) < (Fintype.card K : ℚ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hdeg' : (p.totalDegree : ℚ≥0) < (Fintype.card K : ℚ≥0) := by
    exact_mod_cast hdeg
  have hlt : (p.totalDegree : ℚ≥0) / (Fintype.card K : ℚ≥0) < 1 :=
    (div_lt_one hcardpos).2 hdeg'
  exact (not_le_of_gt hlt) hone

private theorem mv_polynomial_total_degree_map_le
    {R S σ : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial σ R) :
    (MvPolynomial.map f p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq]
  exact Finset.sup_mono (MvPolynomial.support_map_subset f p)

open scoped BigOperators in
private theorem exists_binary_matrix_direct_configuration_separator_eval_ne_zero
    {K : Type} [Field K] [Fintype K]
    [CharP K 2] [Algebra (ZMod 2) K]
    (b : ℕ) (hb : 0 < b)
    (hcard : binary_matrix_separator_threshold b ≤ Fintype.card K) :
    ∃ t : Fin (b + 2) → K,
      MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
      (binary_matrix_direct_configuration_separator b) ≠ 0 := by
  classical
  have horig :
      (binary_matrix_direct_configuration_separator b).totalDegree < Fintype.card K := by
    unfold binary_matrix_separator_threshold at hcard
    omega
  have hdeg :
      (mapped_binary_matrix_direct_configuration_separator (K := K) b).totalDegree <
        Fintype.card K := by
    unfold mapped_binary_matrix_direct_configuration_separator
    exact lt_of_le_of_lt
      (mv_polynomial_total_degree_map_le (algebraMap (ZMod 2) K)
        (binary_matrix_direct_configuration_separator b)) horig
  obtain ⟨t, ht⟩ :=
    mv_polynomial_fin_exists_eval_ne_zero_of_total_degree_lt_card
      (mapped_binary_matrix_direct_configuration_separator (K := K) b)
      (mapped_binary_matrix_direct_configuration_separator_ne_zero b hb) hdeg
  refine ⟨t, ?_⟩
  unfold mapped_binary_matrix_direct_configuration_separator at ht
  simpa only [MvPolynomial.eval_map] using ht

open scoped BigOperators in
private theorem exists_binary_matrix_generic_tuple
    {K : Type} [Field K] [Fintype K]
    [CharP K 2] [Algebra (ZMod 2) K]
    (b : ℕ) (hb : 0 < b)
    (hcard : binary_matrix_separator_threshold b ≤ Fintype.card K) :
    ∃ t : Fin (b + 2) → K,
      Function.Injective (binary_product_tuple_linear_map t) ∧
      Function.Injective (fun M : Matrix (Fin 2) (Fin b) (ZMod 2) =>
        MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binary_matrix_lambda_mv M)) := by
  classical
  obtain ⟨t, ht⟩ :=
    exists_binary_matrix_direct_configuration_separator_eval_ne_zero b hb hcard
  exact ⟨t, binary_matrix_generic_tuple_of_separator_eval_ne_zero t ht⟩

private theorem binary_matrix_graph_polynomial_decomposition
    {K : Type} [Field K] [Fintype K] [CharP K 2] [Algebra (ZMod 2) K]
    (r : ℕ) (t : Fin (r + 4) → K)
    (htinj : Function.Injective (binary_product_tuple_linear_map t))
    (M : Matrix (Fin 2) (Fin (r + 2)) (ZMod 2)) :
    ∃ R : Polynomial K,
      Polynomial.subspacePolynomial (binary_matrix_graph_hom t M).range =
        Polynomial.X ^ (2 ^ (r + 2)) +
          Polynomial.C
            (MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
              (binary_matrix_lambda_mv M)) *
            Polynomial.X ^ (2 ^ (r + 1)) + R ∧
      R.natDegree ≤ 2 ^ r := by
  classical
  set L := binary_matrix_graph_hom t M
  have hL : Function.Injective L := htinj.comp fun x y h => congrArg Prod.fst h
  set P := Polynomial.subspacePolynomial L.range
  have hdeg : P.natDegree = 2 ^ (r + 2) := by
    rw [Polynomial.natDegree_subspacePolynomial,
      ← Nat.card_congr (AddMonoidHom.ofInjective hL).toEquiv]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hT := Polynomial.subspaceTopPoly_sub_mem_degreeLT
    (Polynomial.isTwoLinearized_subspacePolynomial L.range)
    (Polynomial.monic_subspacePolynomial L.range) (a := r) hdeg
  set T := Polynomial.subspaceTopPoly r (r + 2) (Polynomial.subspaceTopCoeffs r (r + 2) P)
  refine ⟨Polynomial.C (P.coeff (2 ^ r)) * Polynomial.X ^ (2 ^ r) - (T - P), ?_, ?_⟩
  · have hT' : T = Polynomial.X ^ (2 ^ (r + 2)) +
        Polynomial.C (P.coeff (2 ^ r)) * Polynomial.X ^ (2 ^ r) +
          Polynomial.C (P.coeff (2 ^ (r + 1))) * Polynomial.X ^ (2 ^ (r + 1)) := by
      simp only [T, Polynomial.subspaceTopPoly, Polynomial.subspaceTopCoeffs]
      rw [Fin.sum_univ_eq_sum_range (fun j => Polynomial.C (P.coeff (2 ^ (r + j))) *
        Polynomial.X ^ (2 ^ (r + j))) (r + 2 - r), show r + 2 - r = 2 by omega,
        Finset.sum_range_succ, Finset.sum_range_one]
      ring_nf
    have hlam : MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binary_matrix_lambda_mv M) =
        P.coeff (2 ^ (r + 1)) := by
      rw [binary_matrix_lambda_eval_eq_coeff, show r + 2 - 1 = r + 1 by omega,
        ← Polynomial.subspacePolynomial_range_eq_prod L hL]
    rw [hlam, hT']
    ring
  · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _)
    · exact Polynomial.natDegree_le_of_degree_le
        (le_of_lt (Polynomial.mem_degreeLT.1 hT))

open scoped BigOperators in
private theorem binary_matrix_graph_agreement
    {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    (r : ℕ) (t : Fin (r + 4) → K)
    (htinj : Function.Injective (binary_product_tuple_linear_map t))
    (M : Matrix (Fin 2) (Fin (r + 2)) (ZMod 2)) :
    ∃ S : Finset ((Fin (r + 2) → ZMod 2) × (Fin 2 → ZMod 2)),
      S.card = 4 * 2 ^ r ∧
      ∃ p : Polynomial K,
        p.natDegree < 2 ^ r + 1 ∧
        ∀ i ∈ S,
          p.eval (binary_product_tuple_linear_map t i) =
            (binary_product_tuple_linear_map t i) ^ (2 ^ (r + 2)) +
              MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
                (binary_matrix_lambda_mv M) *
                (binary_product_tuple_linear_map t i) ^ (2 ^ (r + 1)) := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨R, hR, hdeg⟩ := binary_matrix_graph_polynomial_decomposition r t htinj M
  refine ⟨Finset.univ.map
    ⟨LinearMap.id.prod (Matrix.mulVecLin M), fun x y h => congrArg Prod.fst h⟩,
    ?_, -R, ?_, ?_⟩
  · simp [ZMod.card, pow_add]; ring
  · rw [Polynomial.natDegree_neg]
    omega
  · intro i hi
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hi
    have hroot := (Polynomial.eval_subspacePolynomial_eq_zero_iff
      (binary_matrix_graph_hom t M).range (binary_matrix_graph_hom t M x)).2 ⟨x, rfl⟩
    rw [hR] at hroot
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at hroot
    rw [Polynomial.eval_neg, CharTwo.neg_eq]
    exact (CharTwo.add_eq_zero.mp hroot).symm

open scoped BigOperators NNReal ENNReal in
private theorem binary_matrix_johnson_raw
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ q₀ : ℕ,
    ∀ {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2],
      q₀ ≤ Fintype.card FC →
      ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
        (domain : ιC ↪ FC) (d : ℕ) (G : Finset FC),
        0 < d ∧
        Fintype.card ιC = 16 * d ∧
        ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - ε))) ≤
          (G.card : ENNReal) ∧
        ∀ γ ∈ G,
          ∃ S : Finset ιC, ∃ p : Polynomial FC,
            S.card = 4 * d ∧
            p.natDegree < d + 1 ∧
            ∀ i ∈ S,
              p.eval (domain i) =
                domain i ^ (4 * d) + γ * domain i ^ (2 * d) := by
  obtain ⟨r, hrpow⟩ := exists_binary_matrix_exponent_parameter ε hε
  refine ⟨binary_matrix_separator_threshold (r + 2), ?_⟩
  intro FC _ _ _ _ hFC
  let : Algebra (ZMod 2) FC := ZMod.algebra FC 2
  obtain ⟨t, htinj, hcoeffinj⟩ :=
    exists_binary_matrix_generic_tuple (K := FC) (r + 2) (by omega) hFC
  let ιC : Type :=
    (Fin (r + 2) → ZMod 2) × (Fin 2 → ZMod 2)
  let domain : ιC ↪ FC :=
    ⟨binary_product_tuple_linear_map t, htinj⟩
  let d : ℕ := 2 ^ r
  let G : Finset FC := binary_matrix_good_coefficients (K := FC) (b := r + 2) t
  refine ⟨ιC, inferInstance, inferInstance, inferInstance, domain, d, G,
    ?_, ?_, ?_, ?_⟩
  · dsimp only [d]
    positivity
  · dsimp only [ιC, d]
    exact binary_product_index_card_add_two r
  · dsimp only [ιC, G]
    rw [binary_product_index_card_add_two,
      binary_matrix_good_coefficients_card (K := FC) (b := r + 2) t hcoeffinj]
    exact hrpow
  · intro γ hγ
    have hγ' : γ ∈ binary_matrix_good_coefficients (K := FC) (b := r + 2) t := by
      simpa only [G] using hγ
    obtain ⟨M, hM⟩ :=
      (binary_matrix_good_coefficients_mem t γ).mp hγ'
    obtain ⟨S, hScard, p, hpdeg, hagree⟩ :=
      binary_matrix_graph_agreement r t htinj M
    refine ⟨S, p, ?_, ?_, ?_⟩
    · dsimp only [d]
      exact hScard
    · dsimp only [d]
      exact hpdeg
    · intro i hi
      have h4 : 2 ^ (r + 2) = 4 * 2 ^ r := by
        rw [pow_add]
        norm_num
        ring
      have h2 : 2 ^ (r + 1) = 2 * 2 ^ r := by
        rw [pow_add]
        norm_num
        ring
      change p.eval (binary_product_tuple_linear_map t i) =
        (binary_product_tuple_linear_map t i) ^ (4 * 2 ^ r) +
          γ * (binary_product_tuple_linear_map t i) ^ (2 * 2 ^ r)
      simpa only [h4, h2, hM] using hagree i hi

open scoped NNReal in
private theorem rs_fold_close_of_graph_agreement
    {ι F : Type} [Fintype ι] [Nonempty ι]
    [Field F] [Finite F] [DecidableEq F]
    (domain : ι ↪ F) (d : ℕ)
    (hcard : Fintype.card ι = 16 * d)
    (γ : F) (S : Finset ι) (p : Polynomial F)
    (hScard : S.card = 4 * d)
    (hpdeg : p.natDegree < d + 1)
    (hagree : ∀ i ∈ S,
      p.eval (domain i) = domain i ^ (4 * d) + γ * domain i ^ (2 * d)) :
    δᵣ((fun i => domain i ^ (4 * d)) +
        γ • (fun i => domain i ^ (2 * d)),
      (ReedSolomon.code domain (d + 1) : Set (ι → F))) ≤ (3 / 4 : ℝ≥0) := by
  classical
  let _ := Fintype.ofFinite F
  let w : ι → F := fun i => p.eval (domain i)
  have hw : w ∈ (ReedSolomon.code domain (d + 1) : Set (ι → F)) :=
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval p hpdeg
      (fun _ => rfl)
  have hfloor :
      ⌊(3 / 4 : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ = 12 * d := by
    rw [hcard]
    push_cast
    have heq :
        (3 / 4 : ℝ≥0) * (16 * (d : ℝ≥0)) =
          ((12 * d : ℕ) : ℝ≥0) := by
      norm_num
      ring
    rw [heq, Nat.floor_natCast]
  rw [Code.relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨w, hw, ?_⟩
  rw [Code.relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, ?_, ?_⟩
  · rw [hfloor, hcard, hScard]
    omega
  · intro i
    constructor
    · intro hi
      dsimp only [w]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (hagree i hi).symm
    · intro hne hi
      apply hne
      dsimp only [w]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (hagree i hi).symm

private theorem rs_monomial_agreement_card_le_two_mul
    {ι F : Type} [Finite ι]
    [Field F] [Finite F]
    (domain : ι ↪ F) (d : ℕ) (hd : 0 < d)
    (v : ι → F)
    (hv : v ∈ (ReedSolomon.code domain (d + 1) : Set (ι → F)))
    (S : Finset ι)
    (hagree : ∀ i ∈ S, v i = domain i ^ (2 * d)) :
    S.card ≤ 2 * d := by
  classical
  let _ := Fintype.ofFinite ι
  let _ := Fintype.ofFinite F
  let : NeZero (d + 1) := ⟨by omega⟩
  obtain ⟨p, hpdeg, hpeval⟩ :=
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv
  let Q : Polynomial F := Polynomial.X ^ (2 * d) - p
  have hpdeg' : p.natDegree < 2 * d := by omega
  have hQnat : Q.natDegree = 2 * d := by
    unfold Q
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · rw [Polynomial.natDegree_X_pow]
    · simpa only [Polynomial.natDegree_X_pow] using hpdeg'
  have hQne : Q ≠ 0 := by
    apply Polynomial.ne_zero_of_natDegree_gt (n := 0)
    rw [hQnat]
    omega
  have hsub : S ⊆ Finset.univ.filter (fun i => Q.eval (domain i) = 0) := by
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    unfold Q
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      hpeval i, hagree i hi, sub_self]
  calc
    S.card ≤ (Finset.univ.filter (fun i => Q.eval (domain i) = 0)).card :=
      Finset.card_le_card hsub
    _ ≤ Q.natDegree :=
      AdditiveSetListDecoding.card_filter_eval_eq_zero_le_natDegree domain hQne
    _ = 2 * d := hQnat

open scoped NNReal in
private theorem binary_monomial_stack_not_joint
    {ι F : Type} [Fintype ι] [Nonempty ι]
    [Field F] [Finite F] [DecidableEq F]
    (domain : ι ↪ F) (d : ℕ) (hd : 0 < d)
    (hcard : Fintype.card ι = 16 * d)
    (δ_int : ℝ≥0) (hδ : (δ_int : ℝ) < 7 / 8) :
    ¬ Code.jointProximity
      (ReedSolomon.code domain (d + 1) : Set (ι → F))
      (u := Code.finMapTwoWords
        (fun i => domain i ^ (4 * d))
        (fun i => domain i ^ (2 * d))) δ_int := by
  classical
  let _ := Fintype.ofFinite F
  intro hj
  rw [← Code.jointAgreement_iff_jointProximity] at hj
  obtain ⟨S, hScard, v, hv⟩ := hj
  have hSgt : 2 * d < S.card :=
    agreement_card_gt_two_mul_of_lt_seven_eighths d hd δ_int S hcard hScard hδ
  have hv1 : v 1 ∈ (ReedSolomon.code domain (d + 1) : Set (ι → F)) :=
    (hv 1).1
  have hagree : ∀ i ∈ S, v 1 i = domain i ^ (2 * d) := by
    intro i hi
    have hmem := (hv 1).2 hi
    have heq := (Finset.mem_filter.mp hmem).2
    simpa only [Code.finMapTwoWords] using heq
  have hSle :=
    rs_monomial_agreement_card_le_two_mul domain d hd (v 1) hv1 S hagree
  omega

private theorem rs_relative_min_dist_fifteen_sixteen
    {ι K : Type} [Fintype ι]
    [Field K] [Finite K] [DecidableEq K]
    (domain : ι ↪ K) (t : ℕ) (ht : 0 < t)
    (hcard : Fintype.card ι = 16 * t) :
    (Code.minDist ((ReedSolomon.code domain (t + 1) : Set (ι → K))) : ℝ) /
        Fintype.card ι = (15 : ℝ) / 16 := by
  let _ := Fintype.ofFinite K
  have hkpos : 0 < t + 1 := by omega
  let : NeZero (t + 1) := ⟨hkpos.ne'⟩
  have hk : t + 1 ≤ Fintype.card ι := by
    rw [hcard]
    omega
  rw [ReedSolomon.minDist_of_le hk, hcard]
  have hnat : 16 * t - (t + 1) + 1 = 15 * t := by omega
  rw [hnat]
  push_cast
  field_simp

open scoped BigOperators NNReal ENNReal ProbabilityTheory in
/-- Over every sufficiently large characteristic-two field, constructs a Reed--Solomon code
of relative minimum distance `15 / 16` with large CA error at field radius `3 / 4`. -/
theorem exists_rs_epsCa_large_at_johnson_radius
    (ε : ℝ≥0) (_hε : 0 < ε) :
    ∃ q₀ : ℕ,
    ∀ {FC : Type} [Field FC] [Fintype FC] [SampleableType FC] [DecidableEq FC] [CharP FC 2],
      q₀ ≤ Fintype.card FC →
      ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
        (domain : ιC ↪ FC) (k : ℕ),
        (Code.minDist ((ReedSolomon.code domain k : Set (ιC → FC))) : ℝ)
            / Fintype.card ιC = (15 : ℝ) / 16 ∧
        ∀ δ_int : ℝ≥0, (δ_int : ℝ) < 7 / 8 →
          epsCa (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
              (3 / 4 : ℝ≥0) δ_int ≥
            ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - ε)))
              / (Fintype.card FC : ENNReal) := by
  classical
  obtain ⟨q₀, hraw⟩ := binary_matrix_johnson_raw ε _hε
  refine ⟨q₀, ?_⟩
  intro FC _ _ _ _ _ hFC
  obtain ⟨ιC, instι, neι, decι, domain, d, G,
    hd, hcard, hG, hagree⟩ := hraw hFC
  let : Fintype ιC := instι
  let : Nonempty ιC := neι
  let : DecidableEq ιC := decι
  refine ⟨ιC, inferInstance, inferInstance, inferInstance,
    domain, d + 1, rs_relative_min_dist_fifteen_sixteen domain d hd hcard, ?_⟩
  intro δ_int hδ
  let u : Code.WordStack FC (Fin 2) ιC :=
    Code.finMapTwoWords
      (fun i => domain i ^ (4 * d))
      (fun i => domain i ^ (2 * d))
  have hnot : ¬ Code.jointProximity
      (ReedSolomon.code domain (d + 1) : Set (ιC → FC))
      (u := u) δ_int := by
    simpa only [u] using
      (binary_monomial_stack_not_joint domain d hd hcard δ_int hδ)
  have hclose : ∀ γ ∈ G,
      δᵣ(u 0 + γ • u 1,
        (ReedSolomon.code domain (d + 1) : Set (ιC → FC))) ≤
          (3 / 4 : ℝ≥0) := by
    intro γ hγ
    obtain ⟨S, p, hScard, hpdeg, hpAgree⟩ := hagree γ hγ
    have hc := rs_fold_close_of_graph_agreement
      domain d hcard γ S p hScard hpdeg hpAgree
    simpa only [u, Code.finMapTwoWords] using hc
  exact le_trans (ENNReal.div_le_div_right hG _)
    (eps_ca_lower_of_finset_witness
      (ReedSolomon.code domain (d + 1) : Set (ιC → FC))
      (3 / 4 : ℝ≥0) δ_int u G hnot hclose)

end ReedSolomon

end CodingTheory
