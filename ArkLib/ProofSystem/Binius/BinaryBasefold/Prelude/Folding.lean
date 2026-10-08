/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude.Fibers

/-!
# Binary Basefold folding
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

/-- Single-step fold : Given `f : S⁽ⁱ⁾ → L` and challenge `r`, produce `S⁽ⁱ⁺¹⁾ → L`, where
`f⁽ⁱ⁺¹⁾ = fold(f⁽ⁱ⁾, r) : y ↦ [1-r, r] · [[x₁, -x₀], [-1, 1]] · [f⁽ⁱ⁾(x₀), f⁽ⁱ⁾(x₁)]`
-/
def fold (i : Fin r) (h_i : i + 1 < ℓ + 𝓡) (f : (sDomain 𝔽q β
    h_ℓ_add_R_rate) i → L) (r_chal : L) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (⟨i + 1, by omega⟩) → L :=
  fun y => by
    let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      (h_i_add_steps := h_i) (y := y)
    let x₀ := fiberMap 0
    let x₁ := fiberMap 1
    let f_x₀ := f x₀
    let f_x₁ := f x₁
    exact f_x₀ * ((1 - r_chal) * x₁.val - r_chal) + f_x₁ * (r_chal - (1 - r_chal) * x₀.val)

def baseFoldMatrix (i : Fin r) (h_i : i + 1 < ℓ + 𝓡)
    (y : ↥(sDomain 𝔽q β h_ℓ_add_R_rate ⟨↑i + 1, by omega⟩)) : Matrix (Fin 2) (Fin 2) L :=
  let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      (h_i_add_steps := h_i) (y := y)
  let x₀ := fiberMap 0
  let x₁ := fiberMap 1
  fun i j => match i, j with
  | 0, 0 => x₁
  | 0, 1 => -x₀
  | 1, 0 => -1
  | 1, 1 => 1

/-- `M_y` matrix which depends only on `y ∈ S^(i+ϑ)` -/
def foldMatrix (i : Fin r) (steps : Fin (ℓ + 1)) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨↑i + steps, by apply Nat.lt_trans (m := ℓ + 𝓡) (h_i_add_steps) h_ℓ_add_R_rate⟩) :
    Matrix (Fin (2 ^ steps.val)) (Fin (2 ^ steps.val)) L := by
  if h_steps_eq_1 : steps.val = 1 then
    have h_i : (i : ℕ) + 1 < ℓ + 𝓡 := by rw [← h_steps_eq_1]; omega
    have y' : sDomain 𝔽q β h_ℓ_add_R_rate
        ⟨↑i + 1, Nat.lt_trans (m := ℓ + 𝓡) h_i h_ℓ_add_R_rate⟩ := by
      simp_rw [← h_steps_eq_1]; omega
    rw [h_steps_eq_1, Nat.pow_one]
    exact baseFoldMatrix 𝔽q β i h_i y'
  else
    -- TODO : recursive definition of the fold matrix
    sorry

/-- Iterated fold over `steps` steps starting at domain index `i`. -/
def iterated_fold (i : Fin r) (steps : Fin (ℓ + 1)) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L) (r_challenges : Fin steps → L) :
    sDomain 𝔽q β h_ℓ_add_R_rate
      (⟨i + steps.val, Nat.lt_trans (m := ℓ + 𝓡) (h_i_add_steps) h_ℓ_add_R_rate⟩) → L := by
  let domain_type := sDomain 𝔽q β h_ℓ_add_R_rate
  let fold_func := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let α (j : Fin (steps + 1)) := domain_type (⟨i + j.val, by omega⟩) → L
  let fold_step (j : Fin steps) (f_acc : α ⟨j, by omega⟩) : α j.succ := by
    unfold α domain_type at *
    intro x
    have fold_func := fold_func (i := ⟨i + j.val, by omega⟩) (h_i := by
      simp only
      omega
    ) (f_acc) (r_challenges j)
    exact fold_func x
  exact Fin.dfoldl (n := steps) (α := α) (f := fun i (accF : α ⟨i, by omega⟩) =>
    have fSucc : α ⟨i.succ, by omega⟩ := fold_step i accF
    fSucc) (init := f)

omit [DecidableEq 𝔽q] in
/--
Transitivity of iterated_fold : folding for `steps₁` and then for `steps₂`
equals folding for `steps₁ + steps₂` with concatenated challenges.
-/
lemma iterated_fold_transitivity
    (i : Fin r) (steps₁ steps₂ : Fin (ℓ + 1))
    (h_bounds : i.val + steps₁ + steps₂ ≤ ℓ) -- A single, sufficient bounds check
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges₁ : Fin steps₁ → L) (r_challenges₂ : Fin steps₂ → L) :
    -- LHS : The nested fold (folding twice)
    have hi1 : i.val + steps₁ ≤ ℓ := by exact le_of_add_right_le h_bounds
    have hi2 : i.val + steps₂ ≤ ℓ := by
      rw [Nat.add_assoc, Nat.add_comm steps₁ steps₂, ←Nat.add_assoc] at h_bounds
      exact le_of_add_right_le h_bounds
    have hi12 : steps₁ + steps₂ < ℓ + 1 := by
      apply Nat.lt_succ_of_le; rw [Nat.add_assoc] at h_bounds;
      exact Nat.le_of_add_left_le h_bounds
    let lhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val + steps₁, by -- ⊢ ↑i + ↑steps₁ < r
        apply Nat.lt_of_le_of_lt (m := ℓ) (hi1) (ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate))⟩)
      (steps := steps₂)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; exact h_bounds)
      (f := by
        exact iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps₁)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; exact hi1) (f := f)
          (r_challenges := r_challenges₁)
      ) r_challenges₂
    let rhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := ⟨steps₁ + steps₂, hi12⟩)
      (h_i_add_steps := by
        simp only; rw [←Nat.add_assoc]; apply Nat.lt_add_of_pos_right_of_le; exact h_bounds)
      (f := f) (r_challenges := Fin.append r_challenges₁ r_challenges₂)
    lhs = by
      simp only [←Nat.add_assoc] at ⊢ rhs
      exact rhs := by
  sorry -- admitted for brevity, relies on a lemma like `Fin.dfoldl_add`

/-- Tensor product of challenge vectors : for a local fold length `steps`,
⨂_{j=0}^{steps-1}(1-r_j, r_j). -/
def challengeTensorProduct (steps : ℕ) (r_challenges : Fin steps → L) : Vector L (2 ^ steps) :=
  if h_steps_zero : steps = 0 then by
    -- Base case : steps = 0, return single element vector [1].
    rw [h_steps_zero, pow_zero]
    exact ⟨#[1], rfl⟩
  else
    -- Recursive case : compute tensor product iteratively
    Nat.rec
      (motive := fun k => k ≤ steps → Vector L (2^k))
      (fun _ => ⟨#[1], rfl⟩) -- Base : empty tensor product = [1]
      (fun k ih h_k_le =>
        -- Inductive step : extend tensor product by one more challenge
        let prev_vec := ih (Nat.le_trans (Nat.le_succ k) h_k_le)
        let r_k := r_challenges ⟨k, by omega⟩
        -- Each element of prev_vec gets multiplied by both (1-r_k) and r_k
        Vector.ofFn (fun idx : Fin (2^k.succ) =>
          let prev_idx : Fin (2^k) := ⟨idx.val / 2, by
            have h_succ : 2^k.succ = 2 * 2^k := by rw [pow_succ, mul_comm]
            rw [h_succ] at idx
            have : idx.val < 2 * 2^k := idx.isLt
            apply Nat.div_lt_of_lt_mul;
            omega⟩
          let bit := idx.val % 2
          let prev_val := prev_vec.get prev_idx
          if bit = 0 then (1 - r_k) * prev_val else r_k * prev_val))
      steps (le_refl steps)

/-- Evaluation vector [f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T -/
def fiberEvaluationMapping (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨↑i + steps, by apply Nat.lt_trans (m := ℓ + 𝓡) (h_i_add_steps) h_ℓ_add_R_rate⟩) :
    Fin (2 ^ steps) → L :=
  -- Get the fiber points
  let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := steps)
    (h_i_add_steps := h_i_add_steps) (y := y)
  -- Evaluate f at each fiber point
  fun idx => f (fiberMap idx)

/-- Matrix-vector multiplication form of iterated fold : For a local `steps > 0`,
`∀ i ∈ {0, ..., l-steps}`,
`y ∈ S^(i+steps)`,
`fold(f^(i), r_0, ..., r_{steps-1})(y) = [⨂_{j=0}^{steps-1}(1-r_j, r_j)] • M_y`
`• [f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T`,
where the right-hand vector's values `(x_0, ..., x_{2 ^ steps-1})` represent the fiber
`(q^(i+steps-1) ∘ ... ∘ q^(i))⁻¹({y}) ⊂ S^(i)`.
-/
def localized_fold_matrix_form (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (r_challenges : Fin steps → L)
  (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩)
  (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  L := by
    let challenge_vec : Vector L (2 ^ steps) := challengeTensorProduct (L := L)
      (ℓ := ℓ) (𝓡 := 𝓡) (r := r) steps r_challenges
    let fold_mat := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) ⟨steps, by omega⟩
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y
    -- Matrix-vector multiplication : challenge_vec^T • (fold_mat • fiber_eval_mapping)
    let intermediate_fn := Matrix.mulVec fold_mat fiber_eval_mapping
    let intermediate_vec := Vector.ofFn intermediate_fn
    simp only at intermediate_vec
    exact Vector.dotProduct challenge_vec intermediate_vec

/-- Wrapper of `localized_fold_matrix_form` with `fiber_eval_mapping` being specified
explicitly. -/
def localized_fold_eval (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by
        exact Fin.is_le') (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩) : L := by
    let fiber_eval_mapping := fiberEvaluationMapping 𝔽q β (steps := steps)
      (i := ⟨i, by omega⟩)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) f y
    exact localized_fold_matrix_form 𝔽q β (i := i) steps h_i_add_steps r_challenges y
      fiber_eval_mapping

omit [DecidableEq 𝔽q] in
/-- **Lemma 4.9.** The iterated fold equals the localized fold evaluation via matmul form -/
theorem iterated_fold_eq_matrix_form (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩) :
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ⟨steps, by apply Nat.lt_succ_of_le; exact Nat.le_of_add_left_le h_i_add_steps⟩)
      (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f
      r_challenges ⟨y, by exact Submodule.coe_mem y⟩) =
    localized_fold_eval 𝔽q β i (steps := steps) (h_i_add_steps := h_i_add_steps) f
      r_challenges (y := ⟨y, by exact Submodule.coe_mem y⟩) := by
  sorry

end Essentials

end

end Binius.BinaryBasefold
