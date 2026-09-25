/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude.Fibers

/-!
# Binary Basefold folding operators and matrix identities
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


/-- Single-step fold : Given `f : S⁽ⁱ⁾ → L` and challenge `r`, produce `S⁽ⁱ⁺¹⁾ → L`, where
`f⁽ⁱ⁺¹⁾ = fold(f⁽ⁱ⁾, r) : y ↦ [1-r, r] · [[x₁, -x₀], [-1, 1]] · [f⁽ⁱ⁾(x₀), f⁽ⁱ⁾(x₁)]`
-/
def fold (i : Fin r) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (h_destIdx_le : destIdx ≤ ℓ) (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L) (r_chal : L) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (i := destIdx) → L :=
  fun y => by
    let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y)
    let x₀ := fiberMap 0
    let x₁ := fiberMap 1
    let f_x₀ := f x₀
    let f_x₁ := f x₁
    exact f_x₀ * ((1 - r_chal) * x₁.val - r_chal) + f_x₁ * (r_chal - (1 - r_chal) * x₀.val)

/-- Helper to cast matrices between equal dimensions (needed for 2^(k+1) = 2^k + 2^k) -/
@[reducible, simp]
def reindexSquareMatrix {n m : Type} (e : n ≃ m) (M : Matrix n n L) : Matrix m m L :=
  Matrix.reindex (α := L) (eₘ := e) (eₙ := e) M

def butterflyMatrix (n : ℕ) (z₀ z₁ : L) : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
    -- 4. Construct the Butterfly Matrix using Scalar Identities
    --    [ z₁*I_{2^n}   -z₀*I_{2^n} ]
    --    [ -1*I_{2^n}     1*I_{2^n} ]
    let I_n : Matrix (Fin (2^n)) (Fin (2^n)) L := 1 -- Identity matrix
    let butterfly : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
      reindexSquareMatrix (e := finCongr (by omega)) (M := Matrix.from4Blocks
                                                (z₁ • I_n)  (-(z₀ • I_n))
                                                ((-1 : L) • I_n) ((1 : L) • I_n))
    butterfly

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- Characterization of butterflyMatrix at `n=0` (used in single-step folding). -/
@[simp]
lemma butterflyMatrix_zero_apply (z₀ z₁ : L) :
    butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := 0) z₀ z₁ = !![z₁, -z₀; -1, 1] := by
  rw [butterflyMatrix]
  simp only [reduceAdd, reducePow, reindexSquareMatrix, Nat.pow_zero, finCongr_refl, neg_smul,
    one_smul, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, submatrix_id_id]
  unfold Matrix.from4Blocks
  simp only [reduceAdd, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue, Matrix.smul_apply,
    smul_eq_mul, Matrix.neg_apply]
  funext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.one_apply]

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
lemma butterflyMatrix_det_ne_zero (n : ℕ) (z₀ z₁ : L) (h_ne : z₀ ≠ z₁) :
    (butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := n) z₀ z₁).det ≠ 0 := by
  -- Proof: det is (z₁ - z₀)^(2^n)
  -- 1. Use Matrix.det_from4Blocks (since blocks commute)
  -- 2. Simplify to det((z₁ - z₀) • I)
  -- 3. Use Matrix.det_smul and h_ne
  dsimp only [butterflyMatrix]
  -- The matrix is:
  -- [ z₁*I   -z₀*I ]
  -- [ -1*I    1*I  ]
  -- Since the blocks commute (scalar multiples of identity), det(M) = det(AD - BC)
  -- AD - BC = (z₁*I)(I) - (-z₀*I)(-I) = z₁*I - z₀*I = (z₁ - z₀)*I
  rw [Matrix.det_reindex_self]
  rw [Matrix.det_from4Blocks_of_squareSubblocks_commute]
  · -- Calculate the determinant of the combined block
    rw [one_smul, mul_one, Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal]
    -- ⊢ ((diagonal fun x ↦ z₁) - (-diagonal fun x ↦ z₀) * -1 • 1).det ≠ 0
    simp only [diagonal_neg, neg_smul, one_smul, mul_neg, mul_one, neg_neg, diagonal_sub,
      det_diagonal, prod_const, Finset.card_univ, Fintype.card_fin, ne_eq, Nat.pow_eq_zero,
      OfNat.ofNat_ne_zero, false_and, not_false_eq_true, pow_eq_zero_iff]
    -- ⊢ ¬z₁ - z₀ = 0
    exact sub_ne_zero_of_ne (Ne.symm h_ne)
  · -- Prove the blocks commute
    -- The bottom-right block is `1 • I = I`, which commutes with everything.
    -- ⊢ Commute (-1 • 1) (1 • 1)
    simp only [neg_smul, one_smul, Commute.one_right]

/-- `BlkDiagMat(n, Mz₀, Mz₁) = [Mz₀, 0;`
                                   `0, Mz₁]`
where `Mz₀` and `Mz₁` are set as the `n-step` `foldMatrix` of `z₀` and `z₁` in **Lemma 4.9**. -/
def blockDiagMatrix (n : ℕ)
    (Mz₀ Mz₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) L) :
    Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
  let zero_blk : Matrix (Fin (2^n)) (Fin (2^n)) L := 0
  let blk_diag : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
    reindexSquareMatrix (e := finCongr (by omega))
      (M := Matrix.from4Blocks Mz₀ zero_blk zero_blk Mz₁)
  blk_diag

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- Block Diagonal matrix multiplication on top half returns M_top * v_top
Proof similar to challengeTensorExpansionMatrix_mulVec_F₂_eq_Fin_merge_PO2.
-/
lemma blockDiagMatrix_mulVec_F₂_eq_Fin_merge_PO2 (n : ℕ)
    (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) L)
    (v_top : Fin (2 ^ n) → L) (v_bot : Fin (2 ^ n) → L) :
    mergeFinMap_PO2_left_right (n := n) (A *ᵥ v_top) (B *ᵥ v_bot)
    = blockDiagMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := n) (Mz₀ := A) (Mz₁ := B)
      *ᵥ mergeFinMap_PO2_left_right (n := n) v_top v_bot := by
  dsimp only [blockDiagMatrix]
  conv_rhs => -- Move reindexing from Matrix to Vector
    rw [Matrix.reindex_mulVec]
  funext k
  unfold mergeFinMap_PO2_left_right
  unfold Matrix.from4Blocks Fin.reindex Matrix.mulVec dotProduct
  -- Now unfold everything
  simp only [Matrix.zero_apply, finCongr_symm, Function.comp_apply, finCongr_apply,
    dite_mul, zero_mul,
    sum_dite_irrel, Fin.val_cast]
  simp_rw [Fin.sum_univ_add]
  simp_rw [←Finset.sum_add_distrib]
  simp only [Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.natAdd_eq_addNat, Fin.val_addNat,
    add_lt_iff_neg_right, _root_.not_lt_zero, add_zero, add_tsub_cancel_right, zero_add]

/-- The recursive definition of the `k-step` fold matrix of point `y`: `M_{k, y}`.
`M_{k, y} = butterflyMatrix(k, z₀, z₁) * [M_{k-1, z₀}, 0; 0, M_{k-1, z₁}]`
where `z₀` and `z₁` are the 1-step fiber of `y`. `M_{k, y}` is actually the
`inverse additive NTT (LCH14)` on the coset `(x₀, ..., x_{2^k-1})` **(Remark 4.10)**. -/
def foldMatrix (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L :=
  match steps with
  | 0 =>
    -- Base case: steps = 0. Identity matrix of size 1 (2^0).
    (1 : Matrix (Fin 1) (Fin 1) L) -- diagonal matrix
  | n + 1 => by
    -- Recursive step: n -> n + 1
    -- 1. Identify the "previous" y's (z₀ and z₁) from the fiber of the current y
    --    Note: y is at index i + n + 1. We need the fiber at i + n.
    let midIdx : Fin r := ⟨i + n, by omega⟩
    have h_midIdx_val : midIdx.val = i + n := by dsimp only [midIdx]
    let fiberMap := qMap_total_fiber 𝔽q β (i := midIdx) (steps := 1)
       h_destIdx h_destIdx_le (y := y)
    let z₀ : sDomain 𝔽q β h_ℓ_add_R_rate midIdx := fiberMap 0
    let z₁ : sDomain 𝔽q β h_ℓ_add_R_rate midIdx := fiberMap 1
    -- 2. Recursively compute M for z₀ and z₁
    --    These matrices have size 2^n x 2^n
    let M_z₀ := foldMatrix i n (destIdx := midIdx) (by omega) (by omega) z₀
    let M_z₁ := foldMatrix i n (destIdx := midIdx) (by omega) (by omega) z₁
    -- 3. Construct the Block Diagonal Matrix: [ M_z₀  0  ]
    --                                         [  0   M_z₁]
    let blk_diag : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
      blockDiagMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := n) (Mz₀ := M_z₀) (Mz₁ := M_z₁)
    -- 4. Construct the Butterfly Matrix using Scalar Identities
    --    [ z₁*I_{2^n}   -z₀*I_{2^n} ]
    --    [ -1*I_{2^n}     1*I_{2^n} ]
    let butterfly : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
      butterflyMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := n) (z₀ := z₀) (z₁ := z₁)
    exact butterfly * blk_diag

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma foldMatrix_det_ne_zero (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (destIdx)) :
    (foldMatrix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y)).det ≠ 0 := by
  revert destIdx h_destIdx h_destIdx_le y
  induction steps with
  | zero =>
    intro destIdx h_destIdx h_destIdx_le y
    simp only [Nat.pow_zero, foldMatrix, det_unique, one_apply_eq, ne_eq, one_ne_zero,
    not_false_eq_true];
  | succ n ih =>
    intro destIdx h_destIdx h_destIdx_le y
    rw [foldMatrix]
    -- 1. Determinant of product = product of determinants
    -- 2. det(butterfly) ≠ 0 because z₀ ≠ z₁ (by injectivity of qMap_total_fiber)
    -- 3. det(block_diag) ≠ 0 because det(M_z₀) ≠ 0 and det(M_z₁) ≠ 0 (by IH)
    -- Expand definition of foldMatrix for n+1
    dsimp [foldMatrix]
    -- Determinant of product
    rw [Matrix.det_mul]
    let midIdx : Fin r := ⟨i + n, by omega⟩
    let fiberMap := qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx)
      (steps := 1) (destIdx := destIdx) (h_destIdx := by dsimp only [midIdx]; omega)
      (h_destIdx_le := by omega) (y := y)
    let z₀ := fiberMap 0
    let z₁ := fiberMap 1
    apply mul_ne_zero
    -- 1. Butterfly Matrix part
    · -- ⊢ Δ(butterflyMatrix(n, z₀, z₁)) ≠ 0
      apply butterflyMatrix_det_ne_zero (L := L) (z₀ := z₀) (z₁ := z₁) (n := n)
      -- ⊢ ↑z₀ ≠ ↑z₁
      unfold z₀ z₁ fiberMap
      let z₀_eq := qMap_total_fiber_one_level_eq (i := ⟨midIdx, by dsimp [midIdx]; omega⟩)
        (destIdx := destIdx) (h_destIdx := by dsimp only [midIdx]; omega)
        (h_destIdx_le := by omega) (y := y) (k := 0)
      let z₁_eq := qMap_total_fiber_one_level_eq (i := ⟨midIdx, by dsimp [midIdx]; omega⟩)
        (destIdx := destIdx) (h_destIdx := by dsimp only [midIdx]; omega) (h_destIdx_le := by omega)
        (y := y) (k := 1)
      conv_lhs => rw [z₀_eq]
      conv_rhs => rw [z₁_eq]
      simp only [Fin.eta, Fin.isValue, Submodule.coe_add, SetLike.val_smul, ne_eq, add_left_inj]
      unfold Fin2ToF2
      rw [get_sDomain_first_basis_eq_1]
      simp only [Fin.isValue, ↓reduceIte, zero_smul, one_ne_zero, one_smul, zero_ne_one,
        not_false_eq_true]
    -- 2. Block Diagonal Part
    · dsimp only [blockDiagMatrix]
      rw [Matrix.det_reindex_self]
      rw [Matrix.det_from4Blocks_of_squareSubblocks_commute]
      -- Diagonal blocks: M_z₀ and M_z₁. Off-diagonal: 0.
      -- det(M) = det(M_z₀) * det(M_z₁) - 0*0
      · simp only [Fin.isValue, mul_zero, sub_zero, det_mul, ne_eq, _root_.mul_eq_zero, not_or]
       -- ⊢ `(Δ(M_z₀) ≠ 0 ∧ Δ(M_z₁) ≠ 0)`
        have h_det_M_z₀_ne_zero := ih (destIdx := midIdx) (by rfl)
          (h_destIdx_le := by dsimp only [midIdx]; omega) (y := z₀)
        have h_det_M_z₁_ne_zero := ih (destIdx := midIdx) (by rfl)
          (h_destIdx_le := by dsimp only [midIdx]; omega) (y := z₁)
        constructor
        · exact h_det_M_z₀_ne_zero
        · exact h_det_M_z₁_ne_zero
      · simp only [Fin.isValue, Commute.zero_left]

/-- **Definition 4.8**: Iterated fold over `steps` steps starting at domain index `i`. -/
def iterated_fold (i : Fin r) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps)
  (h_destIdx_le : destIdx ≤ ℓ)
  (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L) (r_challenges : Fin steps → L) :
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) → L := by
  let domain_type := sDomain 𝔽q β h_ℓ_add_R_rate
  let fold_func := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let α (j : Fin (steps + 1)) := domain_type (⟨i + j.val, by omega⟩) → L
  let fold_step (j : Fin steps) (f_acc : α ⟨j, by omega⟩) : α j.succ := by
    unfold α domain_type at *
    intro x
    -- ⊢ L => now fold `f_acc` and evaluate at `x`
    have fold_func := fold_func (i := ⟨i + j.val, by omega⟩)
      (destIdx := ⟨i + j.val + 1, by omega⟩)
      (h_destIdx := by simp only)
      (h_destIdx_le := by simp only; omega)
      (f := f_acc) (r_chal := r_challenges j)
    exact fold_func x
  let res : α (Fin.last steps) := Fin.dfoldl (n := steps) (α := α)
    (f := fun i (accF : α i.castSucc) =>
      have fSucc : α ⟨i.succ, by omega⟩ := fold_step i accF
      fSucc) (init := f)
  exact fun y => res ⟨y, by
    simp only [Fin.val_last]
    have h_eq : ⟨i + steps, by omega⟩ = destIdx := by
      apply Fin.eq_of_val_eq
      simp only
      exact h_destIdx.symm
    rw [h_eq]
    simp only [SetLike.coe_mem]
  ⟩

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Base Case**: Iterated fold with 0 steps is the identity
(returning the initial function `f`). -/
lemma iterated_fold_zero_steps (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val) (h_destIdx_le : destIdx ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges : Fin 0 → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := 0)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (f := f)
      (r_challenges := r_challenges) = fun y ↦ f (cast
        (congrArg (fun idx => ↥(sDomain 𝔽q β h_ℓ_add_R_rate (i := idx)))
          (Fin.ext h_destIdx)) y) := by
  have h_eq : destIdx = i := by omega
  subst destIdx
  dsimp only [iterated_fold]
  simp only [reduceAdd, Fin.val_castSucc, Fin.val_succ, id_eq, Fin.reduceLast, Fin.coe_ofNat_eq_mod,
    Subtype.coe_eta, Fin.dfoldl_zero, cast_eq]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma iterated_fold_last (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
    (h_midIdx : midIdx.val = i.val + steps) (h_destIdx : destIdx.val = i.val + steps + 1)
  (h_destIdx_le : destIdx ≤ ℓ)
  (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L) (r_challenges : Fin (steps + 1) → L) :
  let fold_full := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    (steps := steps + 1) h_destIdx h_destIdx_le (f := f) (r_challenges := r_challenges)
  let fold_init := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    (steps := steps) h_midIdx (h_destIdx_le := by omega) (f := f)
    (r_challenges := Fin.init r_challenges)
  let fold_init_fold := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx)
    (destIdx := destIdx) (h_destIdx := by omega) (h_destIdx_le := by omega)
    (f := fold_init) (r_chal := r_challenges (Fin.last steps))
  fold_full = fold_init_fold := by
  have h_bound_dest : i.val + steps + 1 < r := by omega
  have h_bound_mid : i.val + steps < r := by omega
  have h_mid_clean : midIdx = ⟨i.val + steps, h_bound_mid⟩ := Fin.eq_of_val_eq (by omega)
  have h_dest_clean : destIdx = ⟨i.val + steps + 1, h_bound_dest⟩ := Fin.eq_of_val_eq (by omega)
  subst h_mid_clean h_dest_clean
  simp only
  conv_lhs => unfold iterated_fold
  simp only
  erw [Fin.dfoldl_succ_last]
  simp only [Fin.succ_last, succ_eq_add_one, Fin.val_last, Function.comp_apply, Fin.val_castSucc,
    Fin.val_succ, id_eq]
  rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma iterated_fold_congr_source_index
    {i i' : Fin r} (h : i = i')
    (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx' : destIdx = i'.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges : Fin steps → L) :
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i)  steps h_destIdx  h_destIdx_le f r_challenges =
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i') steps h_destIdx' h_destIdx_le
    (fun x => f (cast (h := by rw [h]) x)) r_challenges := by
  subst h
  simp only [cast_eq]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma iterated_fold_congr_dest_index
    {i : Fin r} (steps : ℕ) {destIdx destIdx' : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ) (h_destIdx_eq_destIdx' : destIdx = destIdx')
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges : Fin steps → L) (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
    (i := i)  steps h_destIdx  h_destIdx_le f r_challenges y =
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx')
    (i := i) steps (by omega) (h_destIdx_le := by omega)
    (f) r_challenges (y := cast (h := by rw [h_destIdx_eq_destIdx']) y) := by
  subst h_destIdx_eq_destIdx'; rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma iterated_fold_congr_steps_index
    {i : Fin r} (steps steps' : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ) (h_steps_eq_steps' : steps = steps')
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges : Fin steps → L) (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
    (i := i)  steps h_destIdx  h_destIdx_le f r_challenges y =
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
    (i := i) steps' (by omega) (h_destIdx_le := by omega)
    (f) (fun (cIdx : Fin steps') => r_challenges ⟨cIdx, by omega⟩) (y := y) := by
  subst h_steps_eq_steps'; rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
private lemma fold_congr_source_dest_index
    {i i' destIdx destIdx' : Fin r}
    (hi : i = i')
    (hd : destIdx = destIdx')
    (h_destIdx : destIdx = i.val + 1)
    (h_destIdx' : destIdx' = i'.val + 1)
    (h_destIdx_le : destIdx ≤ ℓ)
    (h_destIdx_le' : destIdx' ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_chal : L) :
    fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (destIdx := destIdx) h_destIdx h_destIdx_le f r_chal =
    cast (congrArg (fun idx => sDomain 𝔽q β h_ℓ_add_R_rate (i := idx) → L) hd).symm
      (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i') (destIdx := destIdx') h_destIdx' h_destIdx_le'
        (cast (congrArg (fun idx => sDomain 𝔽q β h_ℓ_add_R_rate (i := idx) → L) hi) f)
        r_chal) := by
  subst hi
  subst hd
  simp only [cast_eq]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- Transitivity of iterated_fold : folding for `steps₁` and then for `steps₂`
equals folding for `steps₁ + steps₂` with concatenated challenges.
-/
lemma iterated_fold_transitivity
    (i : Fin r) {midIdx destIdx : Fin r} (steps₁ steps₂ : ℕ)
    (h_midIdx : midIdx.val = i.val + steps₁) (h_destIdx : destIdx.val = i.val + steps₁ + steps₂)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges₁ : Fin steps₁ → L) (r_challenges₂ : Fin steps₂ → L) :
    -- LHS : The nested fold (folding twice)
    have hi1 : i.val + steps₁ ≤ ℓ := by omega
    have _hi2 : i.val + steps₂ ≤ ℓ := by omega
    have _hi12 : steps₁ + steps₂ < ℓ + 1 := by omega
    let lhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := steps₂) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := by
        exact iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps₁)
          (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f)
          (r_challenges := r_challenges₁)
      ) r_challenges₂
    let rhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps₁ + steps₂) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := f) (r_challenges := Fin.append r_challenges₁ r_challenges₂)
    lhs = rhs := by
  revert destIdx h_destIdx h_destIdx_le r_challenges₂
  induction steps₂ with
  | zero =>
      intro destIdx h_destIdx h_destIdx_le r_challenges₂
      have h_dest_eq : destIdx = midIdx := by
        apply Fin.eq_of_val_eq
        omega
      subst h_dest_eq
      dsimp only
      rw [iterated_fold_zero_steps (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (destIdx := destIdx)
        (h_destIdx := by rfl) (h_destIdx_le := by omega)
        (f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
          (steps := steps₁) (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f)
          (r_challenges := r_challenges₁))
        (r_challenges := r_challenges₂)]
      simp only [cast_eq]
      have h_append_zero : Fin.append r_challenges₁ r_challenges₂ = r_challenges₁ := by
        funext j
        rw [show j = Fin.castAdd 0 j from rfl]
        rw [Fin.append_left]
        rfl
      rw [h_append_zero]
      change iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
          (steps := steps₁) (h_destIdx := h_midIdx) (h_destIdx_le := h_destIdx_le)
          (f := f) (r_challenges := r_challenges₁) =
        iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
          (steps := steps₁) (h_destIdx := h_midIdx) (h_destIdx_le := h_destIdx_le)
          (f := f) (r_challenges := r_challenges₁)
      rfl
  | succ n ih =>
      intro destIdx h_destIdx h_destIdx_le r_challenges₂
      let prevIdx : Fin r := ⟨i.val + steps₁ + n, by omega⟩
      have h_prev_from_i : prevIdx.val = i.val + steps₁ + n := by
        rfl
      have h_prev_from_mid : prevIdx.val = midIdx.val + n := by
        dsimp [prevIdx]
        omega
      have h_prev_le : prevIdx ≤ ℓ := by
        dsimp [prevIdx]
        omega
      dsimp only
      rw [iterated_fold_last (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (midIdx := prevIdx)
        (destIdx := destIdx) (steps := n) (h_midIdx := h_prev_from_mid)
        (h_destIdx := by
          calc
            destIdx.val = i.val + steps₁ + (n + 1) := h_destIdx
            _ = midIdx.val + n + 1 := by omega)
        (h_destIdx_le := h_destIdx_le)
        (f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
          (steps := steps₁) (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f)
          (r_challenges := r_challenges₁))
        (r_challenges := r_challenges₂)]
      have h_append_snoc :
          Fin.append r_challenges₁ r_challenges₂ =
            Fin.snoc (Fin.append r_challenges₁ (Fin.init r_challenges₂))
              (r_challenges₂ (Fin.last n)) := by
        ext j
        cases j using Fin.lastCases with
        | last =>
            rw [Fin.snoc_last]
            have hlast : Fin.last (steps₁.add n) = Fin.natAdd steps₁ (Fin.last n) := by
              apply Fin.eq_of_val_eq
              change steps₁.add n = steps₁ + n
              rfl
            rw [hlast, Fin.append_right]
        | cast j =>
            rw [Fin.snoc_castSucc]
            by_cases hj : j.val < steps₁
            · have hj_left :
                  j.castSucc = Fin.castAdd (n + 1) ⟨j.val, hj⟩ := by
                apply Fin.eq_of_val_eq
                rfl
              have hj_right :
                  j = Fin.castAdd n ⟨j.val, hj⟩ := by
                apply Fin.eq_of_val_eq
                rfl
              rw [hj_left, Fin.append_left]
              have h_app_right :
                  Fin.append r_challenges₁ (Fin.init r_challenges₂) j =
                    Fin.append r_challenges₁ (Fin.init r_challenges₂)
                      (Fin.castAdd n ⟨j.val, hj⟩) := by
                exact congrArg (Fin.append r_challenges₁ (Fin.init r_challenges₂)) hj_right
              rw [h_app_right, Fin.append_left]
            · have hj_total : j.val < steps₁ + n := by
                have hj' := j.isLt
                change j.val < steps₁ + n at hj'
                exact hj'
              have hle : steps₁ ≤ j.val := Nat.le_of_not_lt hj
              let k : Fin n := ⟨j.val - steps₁, by omega⟩
              have hj_left :
                  j.castSucc = Fin.natAdd steps₁ k.castSucc := by
                apply Fin.eq_of_val_eq
                simp only [k, Fin.val_natAdd, Fin.val_castSucc]
                rw [Nat.add_sub_of_le hle]
              have hj_right :
                  j = Fin.natAdd steps₁ k := by
                apply Fin.eq_of_val_eq
                simp only [k, Fin.val_natAdd]
                rw [Nat.add_sub_of_le hle]
              rw [hj_left, Fin.append_right]
              rw [hj_right, Fin.append_right]
              rfl
      rw [h_append_snoc]
      change fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) prevIdx
          (h_destIdx := by
            calc
              destIdx.val = i.val + steps₁ + (n + 1) := h_destIdx
              _ = i.val + steps₁ + n + 1 := by omega
              _ = prevIdx.val + 1 := by rw [h_prev_from_i])
          h_destIdx_le
          (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx n h_prev_from_mid
            (h_destIdx_le := by omega)
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps₁ h_midIdx
              (h_destIdx_le := by omega) f r_challenges₁) (Fin.init r_challenges₂))
          (r_challenges₂ (Fin.last n)) =
        iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ((steps₁ + n) + 1)
          (h_destIdx := by
            calc
              destIdx.val = i.val + steps₁ + (n + 1) := h_destIdx
              _ = i.val + (steps₁ + n) + 1 := by omega)
          h_destIdx_le f
          (Fin.snoc (Fin.append r_challenges₁ (Fin.init r_challenges₂))
            (r_challenges₂ (Fin.last n)))
      rw [iterated_fold_last (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (midIdx := prevIdx)
        (destIdx := destIdx) (steps := steps₁ + n) (h_midIdx := by
          calc
            prevIdx.val = i.val + steps₁ + n := h_prev_from_i
            _ = i.val + (steps₁ + n) := by omega)
        (h_destIdx := by
          calc
            destIdx.val = i.val + steps₁ + (n + 1) := h_destIdx
            _ = i.val + (steps₁ + n) + 1 := by omega)
        (h_destIdx_le := h_destIdx_le) (f := f)
        (r_challenges := Fin.snoc (Fin.append r_challenges₁ (Fin.init r_challenges₂))
          (r_challenges₂ (Fin.last n)))]
      simp only [Fin.init_snoc, Fin.snoc_last]
      rw [ih (destIdx := prevIdx) (h_destIdx := h_prev_from_i) (h_destIdx_le := h_prev_le)
        (r_challenges₂ := Fin.init r_challenges₂)]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **First-step decomposition**: `iterated_fold(i, steps+1, f, r₀ :: r_rest)` equals
`iterated_fold(i+1, steps, fold(f, r₀), r_rest)`.
Dual to `iterated_fold_last` which decomposes from the last step. -/
lemma iterated_fold_first (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
    (h_midIdx : midIdx.val = i.val + 1) (h_destIdx : destIdx.val = i.val + (steps + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges : Fin (steps + 1) → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps + 1) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_challenges) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := steps) (h_destIdx := by omega)
      (h_destIdx_le := h_destIdx_le)
      (f := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
        (destIdx := midIdx) (h_destIdx := h_midIdx)
        (h_destIdx_le := by omega) f (r_challenges 0))
      (r_challenges := fun j => r_challenges j.succ) := by
  have h_bound_mid : i.val + 1 < r := by omega
  have h_bound_dest : i.val + steps + 1 < r := by omega
  have h_mid_clean : midIdx = ⟨i.val + 1, h_bound_mid⟩ := by
    apply Fin.eq_of_val_eq
    exact h_midIdx
  have h_dest_clean : destIdx = ⟨i.val + steps + 1, h_bound_dest⟩ := by
    apply Fin.eq_of_val_eq
    calc
      destIdx.val = i.val + (steps + 1) := h_destIdx
      _ = i.val + steps + 1 := by omega
  subst h_mid_clean h_dest_clean
  have h_midIdx_le : (⟨i.val + 1, h_bound_mid⟩ : Fin r) ≤ ℓ := by omega
  have h_one_step :
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := 1) (destIdx := ⟨i.val + 1, h_bound_mid⟩) (h_destIdx := h_midIdx)
        (h_destIdx_le := h_midIdx_le) (f := f)
        (r_challenges := fun _ : Fin 1 => r_challenges 0) =
      fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
        (destIdx := ⟨i.val + 1, h_bound_mid⟩) (h_destIdx := h_midIdx)
        (h_destIdx_le := h_midIdx_le) f (r_challenges 0) := by
    funext y
    unfold iterated_fold
    rw [Fin.dfoldl_succ, Fin.dfoldl_zero]
    simp only [Fin.val_zero, Nat.add_zero, id_eq]
    rfl
  have h_challenges :
      Fin.append (fun _ : Fin 1 => r_challenges 0) (fun j => r_challenges j.succ) =
        fun cIdx : Fin (1 + steps) => r_challenges ⟨cIdx, by omega⟩ := by
    funext j
    by_cases hj : j.val = 0
    · have hj0 : j = 0 := Fin.eq_of_val_eq hj
      rw [hj0]
      rw [show (0 : Fin (1 + steps)) = Fin.castAdd steps 0 from rfl]
      rw [Fin.append_left]
      rfl
    · have hge : ¬ j.val < 1 := by omega
      rw [Fin.append_right_of_not_lt
        (u := fun _ : Fin 1 => r_challenges 0)
        (v := fun j => r_challenges j.succ)
        (j := j.val) (h := by omega) (hge := hge)]
      have hsucc :
          (⟨j.val - 1, by omega⟩ : Fin steps).succ = ⟨j, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [hsucc]
  have h_full_steps :
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps + 1) (h_destIdx := h_destIdx)
        (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_challenges) =
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := 1 + steps) (h_destIdx := by
          calc
            (⟨i.val + steps + 1, h_bound_dest⟩ : Fin r).val = i.val + (steps + 1) := h_destIdx
            _ = i.val + (1 + steps) := by omega)
        (h_destIdx_le := h_destIdx_le) (f := f)
        (r_challenges := fun cIdx : Fin (1 + steps) => r_challenges ⟨cIdx, by omega⟩) := by
    funext y
    exact iterated_fold_congr_steps_index 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps + 1) (steps' := 1 + steps) (destIdx := ⟨i.val + steps + 1, h_bound_dest⟩)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (h_steps_eq_steps' := by omega) (f := f) (r_challenges := r_challenges) (y := y)
  have h_trans := iterated_fold_transitivity (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (midIdx := ⟨i.val + 1, h_bound_mid⟩) (destIdx := ⟨i.val + steps + 1, h_bound_dest⟩)
      (steps₁ := 1) (steps₂ := steps) (h_midIdx := h_midIdx)
      (h_destIdx := by
        calc
          (⟨i.val + steps + 1, h_bound_dest⟩ : Fin r).val = i.val + (steps + 1) := h_destIdx
          _ = i.val + 1 + steps := by omega)
      (h_destIdx_le := h_destIdx_le) (f := f)
      (r_challenges₁ := fun _ : Fin 1 => r_challenges 0)
      (r_challenges₂ := fun j => r_challenges j.succ)
  dsimp only at h_trans
  rw [h_one_step] at h_trans
  rw [h_challenges] at h_trans
  exact h_full_steps.trans h_trans.symm

/-- **Definition 4.6** : the single-step vector-matrix-vector multiplication form of `fold` -/
def fold_single_matrix_mul_form (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
  (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
  (r_challenge : L) : (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) → L :=
  fun y => by
    let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      h_destIdx h_destIdx_le (y := y)
    let fiber_eval_mapping : (Fin 2) → L := fiberEvaluations 𝔽q β (steps := 1)
      (i := i) h_destIdx h_destIdx_le f y
    let z₀ : sDomain 𝔽q β h_ℓ_add_R_rate i := fiberMap 0
    let z₁ : sDomain 𝔽q β h_ℓ_add_R_rate i := fiberMap 1
    let challenge_vec : Fin (2 ^ 1) → L :=
      challengeTensorExpansion (n := 1) (r := fun _ => r_challenge)
    let fold_mat : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) L :=
      butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := 0) (z₀ := z₀) (z₁ := z₁)
    -- Matrix-vector multiplication : challenge_vec^T • (fold_mat • fiber_eval_mapping)
    let intermediate_fn := Matrix.mulVec fold_mat fiber_eval_mapping -- rhs Mat-Vec mul
    exact dotProduct challenge_vec intermediate_fn -- vec-vec dot product

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- The equality between the 1-step point-wise fold() operation vs the vec-mat-vec
multiplication form from **Definition 4.6** -/
lemma fold_eval_single_matrix_mul_form (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
  (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L) (r_challenge : L) :
  fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := destIdx)
    (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (f := f) (r_chal := r_challenge)
  = fold_single_matrix_mul_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    h_destIdx h_destIdx_le (f := f) (r_challenge := r_challenge) := by
  unfold fold_single_matrix_mul_form fold
  funext y
  simp only [Fin.isValue, reducePow, vec2_dotProduct]
  -- Approach: decompose the rhs into a flat sum expression
  have h_chal_tensor_vec_eq : challengeTensorExpansion (n := 1) (r := fun _ => r_challenge)
    = ![1 - r_challenge, r_challenge] := by
      unfold challengeTensorExpansion multilinearWeight
      simp only [reducePow, univ_unique, Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero,
        testBit_zero, decide_eq_true_eq, prod_ite_irrel, prod_const, card_singleton, pow_one,
        succ_eq_add_one, reduceAdd]
      funext i
      by_cases h : i = 0
      · simp only [h, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_ne_one, ↓reduceIte,
        cons_val_zero]
      · have h_i_eq_1 : i = 1 := by omega
        simp only [h_i_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, ↓reduceIte, cons_val_one,
          cons_val_fin_one]
  set fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
    h_destIdx h_destIdx_le (y := y)
  set z₀ := fiberMap 0
  set z₁ := fiberMap 1
  let butterflyMat0 := butterflyMatrix_zero_apply (L := L) (𝓡 := 𝓡) (ℓ := ℓ) (r := r)
    (z₀ := z₀) (z₁ := z₁)
  conv_rhs => rw [butterflyMat0];
  conv_rhs =>
    unfold fiberEvaluations
    rw [Matrix.mulVec, Matrix.mulVec]; dsimp only [dotProduct]
    simp only [Fin.isValue, Fin.sum_univ_two]
    rw [h_chal_tensor_vec_eq]
    simp only [succ_eq_add_one, reduceAdd, Fin.isValue, cons_val_zero, reindexSquareMatrix,
      reducePow, finCongr_refl, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, submatrix_apply,
      id_eq, cons_val_one, cons_val_fin_one]
  conv_rhs =>
    simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
      neg_mul, one_mul]
  unfold z₀ z₁ fiberMap -- this helps Lean understand the goal better
  ring_nf

/-- The single point vec-mat-vec form of `fold(...)` in **Lemma 4.9** -/
def single_point_localized_fold_matrix_form (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (r_challenges : Fin steps → L)
  (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
  (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  L := by
    let challenge_vec : Fin (2 ^ steps) → L :=
      challengeTensorExpansion (n := steps) (r := r_challenges)
    let fold_mat : Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L :=
      foldMatrix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y)
    -- Matrix-vector multiplication : challenge_vec^T • (fold_mat • fiber_eval_mapping)
    let intermediate_fn := Matrix.mulVec fold_mat fiber_eval_mapping -- rhs Mat-Vec mul
    exact dotProduct challenge_vec intermediate_fn -- vec-vec dot product

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma single_point_localized_fold_matrix_form_congr_source_index
    {i i' : Fin r} (h : i = i')
    (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx' : destIdx = i'.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (r_challenges : Fin steps → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps h_destIdx h_destIdx_le r_challenges y fiber_eval_mapping =
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i' steps h_destIdx' h_destIdx_le r_challenges y fiber_eval_mapping := by
  subst h; rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma single_point_localized_fold_matrix_form_congr_dest_index
    {i : Fin r} (steps : ℕ) {destIdx destIdx' : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ) (h_destIdx_eq_destIdx' : destIdx = destIdx')
    (r_challenges : Fin steps → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps h_destIdx h_destIdx_le r_challenges y fiber_eval_mapping =
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps (destIdx := destIdx') (by omega) (by omega) r_challenges
    (cast (by rw [h_destIdx_eq_destIdx']) y) fiber_eval_mapping := by
  subst h_destIdx_eq_destIdx'; rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma single_point_localized_fold_matrix_form_congr_steps_index
    {i : Fin r} (steps steps' : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ) (h_steps_eq_steps' : steps = steps')
    (r_challenges : Fin steps → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps h_destIdx h_destIdx_le r_challenges y fiber_eval_mapping =
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps' (by omega) h_destIdx_le
    (fun k ↦ r_challenges ⟨k, by omega⟩)
    y
    (fun k ↦ fiber_eval_mapping ⟨k, by subst h_steps_eq_steps'; exact k.is_lt⟩) := by
  subst h_steps_eq_steps'; rfl

/-- **From Lemma 4.9**: Matrix-vector multiplication form of iterated fold :
For a local `steps > 0`, `∀ i ∈ {0, ..., l-steps}`, `y ∈ S^(i+steps)`,
`fold(f^(i), r_0, ..., r_{steps-1})(y) = [⨂_{j=0}^{steps-1}(1-r_j, r_j)] • M_{steps, y}`
`• [f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T`,
where
- `M_{steps, y}` is the `steps`-step **foldMatrix** of point `y`.
- the right-hand vector's values `(x_0, ..., x_{2 ^ steps-1})` represent the fiber
`(q^(i+steps-1) ∘ ... ∘ q^(i))⁻¹({y}) ⊂ S^(i)`. -/
def localized_fold_matrix_form (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
  (r_challenges : Fin steps → L) : (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) → L :=
  fun y =>
    let fiber_eval_mapping := fiberEvaluations 𝔽q β (steps := steps)
        (i := i)
        h_destIdx h_destIdx_le f y
    single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le
      (r_challenges := r_challenges) (y := y) (fiber_eval_mapping := fiber_eval_mapping)

/-- The (2 x 1) vector `F₂(steps, r, z₀, z₁) = [fold(steps, r, z₀), fold(steps, r, z₁)]`.
This is the right-most vector when decomposing the outer single-step fold of **Lemma 4.9**.
NOTE: `h_F₂_y_eq` in lemma `iterated_fold_eq_matrix_form` below shows it OG form in Lemma 4.9. -/
def fold_eval_fiber₂_vec (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
    (h_midIdx : midIdx = i + steps) (h_destIdx : destIdx = i + steps + 1)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L) (r_challenges : Fin steps → L) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (i := destIdx) → (Fin 2) → L := fun y => by
    -- Can also use fiberEvaluations instead
    let fiberMap := qMap_total_fiber 𝔽q β (i := midIdx) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx)
      (h_destIdx := by omega) (by omega) (y := y)
    exact fun rowIdx =>
      let zᵢ := fiberMap rowIdx
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
        (steps := steps) h_midIdx (h_destIdx_le := by omega)
        (f := f) (r_challenges := r_challenges) zᵢ

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Helper #1 for Lemma 4.9**: The vector `F₂(steps, r, y) = `
`MatrixCTensor(steps, r) * blockDiagMatrix(steps, M_z₀, M_z₁) * fiberEvaluations(steps+1, r, y)`.
where `z₀, z₁` are the fiber of `y`, `y` is in `S^(i+steps+1)`). -/
lemma fold_eval_fiber₂_eq_mat_mat_vec_mul (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
    (h_midIdx : midIdx = i + steps) (h_destIdx : destIdx = i + steps + 1)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L) (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
    (lemma_4_9_inductive_hypothesis :
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps) (i := i)
        h_midIdx (h_destIdx_le := by omega) (f := f) (r_challenges := r_challenges)
      = (localized_fold_matrix_form 𝔽q β (i := i) (steps := steps) h_midIdx
        (h_destIdx_le := by omega) (f := f) (r_challenges := r_challenges))) :
    let F₂_y : Fin 2 → L := (fold_eval_fiber₂_vec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
      h_midIdx h_destIdx h_destIdx_le f r_challenges) (y)
    let fiberMap := qMap_total_fiber 𝔽q β (i := midIdx) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := destIdx) (h_destIdx := by omega)
      (h_destIdx_le := h_destIdx_le) (y := y)
    let z₀ := fiberMap 0
    let z₁ := fiberMap 1
    let M_z₀ := foldMatrix 𝔽q β (i := i) (steps := steps) h_midIdx (h_destIdx_le := by omega)
      (y := z₀)
    let M_z₁ := foldMatrix 𝔽q β (i := i) (steps := steps) h_midIdx (h_destIdx_le := by omega)
      (y := z₁)
    let fiber_eval_mapping := fiberEvaluations 𝔽q β (steps := steps + 1)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) h_destIdx h_destIdx_le f y
    let decomposed_form := ((challengeTensorExpansionMatrix (n := steps) (r := r_challenges)) *
        (blockDiagMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := steps) (Mz₀ := M_z₀) (Mz₁ := M_z₁)))
          *ᵥ fiber_eval_mapping
    F₂_y = decomposed_form := by
  -- funext (halfIdx : Fin 2)
  dsimp only [fold_eval_fiber₂_vec]
  -- 3. Apply the previous main theorem: iterated_fold_eq_matrix_form
  let h_matrix_form := lemma_4_9_inductive_hypothesis
  -- 4. Rewrite LHS using the matrix form theorem: LHS at halfIdx is `iterated_fold ... z_halfIdx`
  conv_lhs => rw [h_matrix_form] -- now lhs is `localized_fold_matrix_form ... z_halfIdx`
  let fiberVec_y_eq_merge := fiberEvaluations_eq_merge_fiberEvaluations_of_one_step_fiber
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    h_midIdx h_destIdx (h_destIdx_le := by omega)  (f := f) (y := y)
  conv_rhs => rw [fiberVec_y_eq_merge]
  -- simp [Fin.isValue, Fin.eta]
  -- LHS is localized_fold_matrix_form ... z_halfIdx
  -- RHS is: (MatrixCTensor * BlockDiagMatrix *v (fiberEval(z₀) ++ fiberEval(z₁))) [halfIdx]
  conv_rhs =>
    rw [←Matrix.mulVec_mulVec] -- group BlockDiagMatrix with fiberEval(z₀) ++ fiberEval(z₁)
    rw [←blockDiagMatrix_mulVec_F₂_eq_Fin_merge_PO2] -- distribute the mat-vec multiplication
    rw [←challengeTensorExpansionMatrix_mulVec_F₂_eq_Fin_merge_PO2] -- distribute again
  --  Now both sides are `(Fin 2) → L`
  funext (halfIdx : Fin 2)
  conv_lhs => unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
  conv_rhs => unfold mergeFinMap_PO2_left_right
  by_cases hi : halfIdx.val < 2 ^ 0
  · simp only [reduceAdd, reducePow, pow_zero, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue,
    Nat.pow_zero, mulVec_mulVec]
    -- first row of F₂_y (LHS): fold(steps, r_challenges, z₀)
    have h_halfIdx_eq_0 : halfIdx = 0 := by omega
    simp only [h_halfIdx_eq_0, Fin.isValue, ↓reduceDIte, Fin.coe_ofNat_eq_mod, zero_mod,
      Fin.zero_eta]
    conv_lhs => rw [Matrix.dotProduct_mulVec]
    conv_rhs => rw [Matrix.mulVec]
    -- Both sides have form (... ⬝ᵥ (fiberEvaluations (z₀)))
    rfl
  · simp only [reduceAdd, reducePow, pow_zero, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue,
    Nat.pow_zero, mulVec_mulVec]
    -- second row of F₂_y (RHS): fold(steps, r_challenges, z₁)
    have h_halfIdx_eq_1 : halfIdx = 1 := by omega
    simp only [h_halfIdx_eq_1, Fin.isValue, one_ne_zero, ↓reduceDIte, Fin.coe_ofNat_eq_mod,
      mod_succ, tsub_self, Fin.zero_eta]
    conv_lhs => rw [Matrix.dotProduct_mulVec]
    conv_rhs => rw [Matrix.mulVec]
    -- Both sides have form (... ⬝ᵥ (fiberEvaluations (z₁)))
    rfl

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- **Helper #2 for Lemma 4.9**: the (middle) interchangibility transformation in the Lemma 4.9
`butterflyMstrix(0, z₀, z₁) * MatrixCTensor(n, r)`
`= MatrixCTensor(n, r) * butterflyMatrix(n, z₀, z₁)`. Both have size `2 x (2^(n + 1))` -/
lemma butterflyMatrix0_mul_matrixCTensor_eq_matrixCTensor_mul_butterflyMatrix (n : ℕ)
    (z₀ z₁ : L) (r_challenges : Fin n → L) :
    (butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := 0) z₀ z₁) *
      (challengeTensorExpansionMatrix (n := n) (r := r_challenges))
    = (challengeTensorExpansionMatrix (n := n) (r := r_challenges)) *
      (butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := n) z₀ z₁) := by
  unfold butterflyMatrix challengeTensorExpansionMatrix reindexSquareMatrix
  simp only
  conv_lhs => -- clear way for Matrix.reindex_mul_reindex in lhs
    simp only [reduceAdd, reducePow, Nat.pow_zero, finCongr_refl, neg_smul, one_smul,
    Equiv.refl_symm, Equiv.coe_refl, submatrix_id_id, finCongr_symm]
  conv_lhs => rw [Matrix.reindex_mul_reindex]; rw [Matrix.from4Blocks_mul_from4Blocks]
  conv_rhs => rw [Matrix.reindex_mul_reindex]; rw [Matrix.from4Blocks_mul_from4Blocks]
  simp only [reduceAdd, reducePow, smul_mul, Nat.pow_zero, Matrix.one_mul, smul_of, Matrix.mul_zero,
    add_zero, Matrix.neg_mul, neg_of, zero_add, reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
    finCongr_symm, finCongr_refl, Matrix.mul_smul, Matrix.mul_one, neg_smul, one_smul,
    Matrix.mul_neg, neg_zero, smul_zero]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Lemma 4.9.** The iterated fold equals the localized fold evaluation via matmul form -/
theorem iterated_fold_eq_matrix_form (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (r_challenges : Fin steps → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := steps)
      (i := i)
      h_destIdx h_destIdx_le f
      r_challenges =
    localized_fold_matrix_form 𝔽q β i (steps := steps) h_destIdx h_destIdx_le f
      r_challenges := by
  revert destIdx h_destIdx h_destIdx_le
  induction steps with
  | zero => -- Base Case: steps = 0
    intro destIdx h_destIdx h_destIdx_le
    have h_destIdx_eq_i: destIdx = i := by omega
    subst h_destIdx_eq_i
    unfold iterated_fold localized_fold_matrix_form single_point_localized_fold_matrix_form
    simp only [Nat.add_zero, Fin.dfoldl, reduceAdd, Fin.val_succ, id_eq, Fin.dfoldlM_zero,
      Fin.isValue, Fin.coe_ofNat_eq_mod, reduceMod, Nat.pow_zero]
    -- The fold loop is empty, returns f(y)
    unfold challengeTensorExpansion foldMatrix fiberEvaluations qMap_total_fiber
    simp only [pure, Fin.reduceLast, Fin.coe_ofNat_eq_mod, reduceMod, Nat.add_zero, Fin.eta,
      Subtype.coe_eta, Nat.pow_zero, ↓reduceDIte, one_mulVec]
    unfold dotProduct
    simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, multilinearWeight, univ_eq_empty,
      Nat.pow_zero, Fin.val_eq_zero, zero_testBit, Bool.false_eq_true, ↓reduceIte, prod_empty,
      one_mul, sum_const, card_singleton, one_smul]
  | succ n ih =>
    intro destIdx h_destIdx h_destIdx_le
    -- Inductive Step: steps = n + 1
    -- 1. Unfold the definition of iterated_fold for n+1 steps.
    --    iterated_fold (n+1) is `fold` applied to `iterated_fold n`.
    let midIdx : Fin r := ⟨i + n, by omega⟩
    have h_midIdx : midIdx.val = i + n := by dsimp only [midIdx]
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := n)
      (midIdx := midIdx) (destIdx := destIdx) (h_midIdx := h_midIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_challenges)]
    -- simp only
    -- Let `prev_fold` be the result of folding n times.
    set prev_fold_fn := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := n) h_midIdx (h_destIdx_le := by omega) (f := f)
      (r_challenges := Fin.init r_challenges)
    funext (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
    -- ⊢ fold 𝔽q β ⟨↑i + n, ⋯⟩ ⋯ prev_fold_fn (r_challenges (Fin.last n)) y =
    -- localized_fold_matrix_form 𝔽q β i (n + 1) h_i_add_steps f r_challenges y
    set F₂_y := fold_eval_fiber₂_vec 𝔽q β i (steps := n) (midIdx := midIdx) (destIdx := destIdx)
      (h_midIdx := h_midIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
      (r_challenges := Fin.init r_challenges)
    have h_F₂_y_eq : ∀ yPoint, fiberEvaluations 𝔽q β (i := midIdx) (steps := 1)
      h_destIdx h_destIdx_le
      (f := prev_fold_fn) yPoint = F₂_y yPoint := fun yPoint => by rfl
    conv_lhs => -- use vec-matrix-vec form for the outer (single-step) fold()
      rw [fold_eval_single_matrix_mul_form 𝔽q β (i := midIdx)
        h_destIdx h_destIdx_le]; unfold fold_single_matrix_mul_form; simp only
      -- change the right-most multiplier term into F₂_y repr
      rw [h_F₂_y_eq]
      -- Now lhs has this form:` ((CTensor n=1)* butterflyMatrix(0, z₀(y), z₁(y))) * (F₂_y y)`,
        -- => we use **Helper #1** to expand the last term `F₂_y y` into product of 3 terms
      unfold F₂_y
      rw [fold_eval_fiber₂_eq_mat_mat_vec_mul (lemma_4_9_inductive_hypothesis := by
        let res := ih (r_challenges := Fin.init r_challenges) h_midIdx (h_destIdx_le := by omega)
        exact res
      )]
      -- Now LHS has this 5-term form: `(CTensor vec n=1) ⬝ᵥ butterflyMatrix(0, z₀(y), z₁(y))`
        -- `*ᵥ [ [ (MatrixCTensor n=n (Fin.init r_challenges)) * (blockDiagMatrix n Mz₀ Mz₁) ]`
              -- `*ᵥ (fiberEvaluations y)                                                    ] ]`
      -- Next, we group term 2 & 3
      rw [←Matrix.mulVec_mulVec] -- group term (4 * 5), split term 3
      rw [Matrix.mulVec_mulVec] -- group term (2 & 3)
      -- => Now we have 3 groups : (1) ⬝ᵥ (2 * 3) *ᵥ (4 *ᵥ 5)
      -- => We apply **Helper #2** to `swap positions of term 2 & 3`
      rw [butterflyMatrix0_mul_matrixCTensor_eq_matrixCTensor_mul_butterflyMatrix] -- Helper #2
      -- Now LHS has 5-term form: `(CTensor vec n=1) ⬝ᵥ (MatrixCTensor n=n (Fin.init r_challenges))`
        -- `butterflyMatrix(n := N, z₀(y), z₁(y)) * (blockDiagMatrix n Mz₀ Mz₁) ]`
          -- `*ᵥ (fiberEvaluations y)`
          -- where `Mz₀` and `Mz₁` are `n-step` foldMatrix of `z₀` and `z₁` respectively
    -- Now the last TWO jobs are to group * transform (term 1 & term 2), (term 3 & term 4)
    set multilinearWeight1step : (Fin 2 → L) := -- This is term 1 in the LHS
      (challengeTensorExpansion 1 fun x ↦ r_challenges (Fin.last n))
    have h_MLNWeight1step_eq: multilinearWeight1step
      = ![1 - r_challenges (Fin.last n), r_challenges (Fin.last n)] := by
        apply challengeTensorExpansion_one
    let h_merge_term1_term2_tensorExpand_for_n_plus_1 :=
      challengeTensorExpansion_decompose_succ (L := L) (n := n) (r := r_challenges)
    conv_lhs => -- JOB 1: group & transform (term 1 & term 2)
      -- => We need to convert `(CTensor 1) ⬝ᵥ (MatrixCTensor n)` into `(CTensor (n + 1))`
      rw [h_MLNWeight1step_eq]
      rw [←Matrix.mulVec_mulVec] -- group (term 3 4 5), split term 2
      rw [Matrix.dotProduct_mulVec] -- group (term 1 & term 2)
      rw [←h_merge_term1_term2_tensorExpand_for_n_plus_1] -- MERGING here
    conv_lhs => -- JOB 2: group & transform (term 3 & term 4), old term indices before JOB 1
      -- => We need to convert `butterflyMatrix(n := N, z₀(y), z₁(y)) * (blockDiagMatrix n Mz₀ Mz₁)`
        -- into `foldMatrix(n := n + 1, y)`
      rw [Matrix.mulVec_mulVec] -- group term (3 * 4)
      -- => We don't really have to do anything, cuz (term 3 * term 4) is
        -- definitionally equal to fold(n + 1, y)
    rfl

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Corollary of Lemma 4.9**: Direct connection between single-point
matrix form and iterated fold. This is a point-wise version of
`iterated_fold_eq_matrix_form` that directly connects
`single_point_localized_fold_matrix_form` with `fiberEvaluations` to `iterated_fold`.
This is useful when working with concrete fiber evaluation mappings rather than the
abstract `localized_fold_matrix_form` function. -/
lemma single_point_localized_fold_matrix_form_eq_iterated_fold
    (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (r_challenges : Fin steps → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_destIdx h_destIdx_le r_challenges y
    (fiber_eval_mapping := fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le f y) =
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    h_destIdx h_destIdx_le f r_challenges y := by
  rw [iterated_fold_eq_matrix_form]
  rfl

end FoldTheory

end Essentials

end
end Binius.BinaryBasefold
