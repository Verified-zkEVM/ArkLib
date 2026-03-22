/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
## Binary Basefold Soundness Lift

Tensor-expansion and lifting lemmas used by the Binary Basefold soundness development.
This file packages:
1. indicator-style identities for tensor expansions at binary challenges
2. the `preTensorCombine` and lift constructions connecting oracle words and interleaved words
3. disagreement isomorphisms and `preTensorCombine` proximity bridges that feed the
   Proposition 4.20 case analyses
4. the interleaved-distance lower bound of Lemma 4.21

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
-/

namespace Binius.BinaryBasefold

set_option maxHeartbeats 400000

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

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
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

omit [Fintype L] [DecidableEq L] [CharP L 2] in
lemma multilinearWeight_bitsOfIndex_eq_indicator {n : ℕ} (j k : Fin (2 ^ n)) :
  multilinearWeight (F := L) (r := bitsOfIndex k) (i := j) = if j = k then 1 else 0 := by
  set r_k := bitsOfIndex (L := L) k with h_r_k
  unfold multilinearWeight
  -- NOTE: maybe we can generalize this into a lemma?
  -- ⊢ (∏ j_1, if (↑j).testBit ↑j_1 = true then r_k j_1 else 1 - r_k j_1) = if j = k then 1 else 0
  dsimp only [bitsOfIndex, r_k]
  simp_rw [Nat.testBit_eq_getBit]
  by_cases h_eq : j = k
  · simp only [h_eq, ↓reduceIte]
    have h_eq: ∀ (x : Fin n),
      ((if (x.val).getBit ↑k = 1 then if (x.val).getBit ↑k = 1 then (1 : L) else (0 : L) else 1 - if (x.val).getBit ↑k = 1 then (1 : L) else (0 : L))) = (1 : L) := by
        intro x
        by_cases h_eq : (x.val).getBit ↑k = 1
        · simp only [h_eq, ↓reduceIte]
        · simp only [h_eq, ↓reduceIte, sub_zero]
    simp_rw [h_eq]
    simp only [prod_const_one]
  · simp only [h_eq, ↓reduceIte]
    -- ⊢ (∏ x, if (↑x).getBit ↑j = 1 then if (↑x).getBit ↑k = 1 then 1 else 0 else 1 - if (↑x).getBit ↑k = 1 then 1 else 0) = 0
    rw [Finset.prod_eq_zero_iff]
    --         ⊢ ∃ a ∈ univ,
    -- (if (↑a).getBit ↑j = 1 then if (↑a).getBit ↑k = 1 then 1 else 0 else 1 - if (↑a).getBit ↑k = 1 then 1 else 0) = 0
    let exists_bit_diff_idx := Nat.exist_bit_diff_if_diff (a := j) (b := k) (h_a_ne_b := h_eq)
    rcases exists_bit_diff_idx with ⟨bit_diff_idx, h_bit_diff_idx⟩
    have h_getBit_of_j_lt_2 : Nat.getBit (k := bit_diff_idx.val) (n := j) < 2 := by
      exact Nat.getBit_lt_2 (k := bit_diff_idx.val) (n := j)
    have h_getBit_of_k_lt_2 : Nat.getBit (k := bit_diff_idx.val) (n := k) < 2 := by
      exact Nat.getBit_lt_2 (k := bit_diff_idx.val) (n := k)
    use bit_diff_idx
    constructor
    · simp only [mem_univ]
    · by_cases h_bit_diff_of_j_eq_0 : Nat.getBit (k := bit_diff_idx.val) (n := j) = 0
      · simp only [h_bit_diff_of_j_eq_0, zero_ne_one, ↓reduceIte]
        -- ⊢ (1 - if (↑bit_diff_idx).getBit ↑k = 1 then 1 else 0) = 0
        have h_bit_diff_of_k_eq_1 : Nat.getBit (k := bit_diff_idx.val) (n := k) = 1 := by
          omega
        simp only [h_bit_diff_of_k_eq_1, ↓reduceIte, sub_self]
      · have h_bit_diff_of_j_eq_1 :
          Nat.getBit (k := bit_diff_idx.val) (n := j) = 1 := by
          omega
        have h_bit_diff_of_k_eq_0 : Nat.getBit (k := bit_diff_idx.val) (n := k) = 0 := by
          omega
        simp only [h_bit_diff_of_j_eq_1, ↓reduceIte, h_bit_diff_of_k_eq_0, zero_ne_one]

omit [Fintype L] [DecidableEq L] [CharP L 2] in
/-- **Key Property of Tensor Expansion with Binary Challenges**:
When `r = bitsOfIndex k`, the tensor expansion `challengeTensorExpansion n r`
is the indicator vector for index `k` (i.e., 1 at position `k`, 0 elsewhere).
This is a fundamental property used in both Proposition 4.20 and Lemma 4.21. -/
lemma challengeTensorExpansion_bitsOfIndex_is_eq_indicator {n : ℕ} (k : Fin (2 ^ n)) :
    -- Key Property: Tensor(r_k) is the indicator vector for k.
    -- Tensor(r_k)[j] = 1 if j=k, 0 if j≠k.
    challengeTensorExpansion n (r := bitsOfIndex (L := L) k) = fun j => if j = k then 1 else 0 := by
  -- Let r_k be the bit-vector corresponding to index k
  funext j
  unfold challengeTensorExpansion
  -- ⊢ multilinearWeight r_k j = if j = k then 1 else 0
  apply multilinearWeight_bitsOfIndex_eq_indicator

section Lift_PreTensorCombine

/-! **Interleaved Word Construction (Supporting definition for Lemma 4.21)**
Constructs the rows `f_j^{(i+steps)}` of the interleaved word.
For a fixed row index `j` and a domain point `y ∈ S^{i+steps}`,
the value is the `j`-th entry of the vector `M_y * fiber_vals`.
-- NOTE: the way we define `ι` as `sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩` instead of
`Fin` requires using the generic versions of code/proximity gap lemmas.
We don't have a unified mat-mul formula for this, because the `M_y` matrix varies over `y` -/
def preTensorCombine_WordStack (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    WordStack (A := L) (κ := Fin (2 ^ steps))
      (ι := sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := fun j y =>
    -- 1. Calculate the folding matrix M_y
    let M_y : Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L :=
      foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y)
    -- 2. Get the evaluation of f on the fiber of y
    let fiber_vals : Fin (2 ^ steps) → L :=
      fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i) (y := y)
    -- 3. The result is the j-th component of the matrix-vector product
    (M_y *ᵥ fiber_vals) j

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Folding with Binary Challenges selects a Matrix Row**
This lemma establishes the geometric link:
The `j`-th row of the `preTensorCombine` matrix product is exactly equal to
folding the function `f` using the bits of `j` as challenges.
This holds for ANY function `f`, not just codewords.
-/
lemma preTensorCombine_row_eq_fold_with_binary_row_challenges
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (rowIdx : Fin (2 ^ steps)) :
    ∀ y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx,
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) rowIdx y =
      iterated_fold 𝔽q β ⟨i, by omega⟩ steps
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
          (r_challenges := bitsOfIndex (L := L) (n := steps) rowIdx) (y := y) := by
  intro y
  -- 1. Expand the definition of preTensorCombine (The LHS)
  -- LHS = (M_y * f_vals)[rowIdx]
  dsimp [preTensorCombine_WordStack]
  -- 2. Expand the matrix form of iterated_fold (The RHS)
  -- RHS = Tensor(r) • (M_y * f_vals)
  rw [iterated_fold_eq_matrix_form 𝔽q β (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)]
  unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
  -- 3. Use the Tensor Property
  -- Tensor(bits(rowIdx)) is the indicator vector for rowIdx
  let tensor := challengeTensorExpansion (L := L) steps (bitsOfIndex rowIdx)
  have h_indicator : tensor = fun k => if k = rowIdx then 1 else 0 :=
    challengeTensorExpansion_bitsOfIndex_is_eq_indicator (L := L) rowIdx
  simp only
  -- 4. Simplify the Dot Product
  -- (Indicator • Vector) is exactly Vector[rowIdx]
  dsimp only [tensor] at h_indicator
  rw [h_indicator]
  rw [dotProduct]
  simp only [boole_mul]
  rw [Finset.sum_eq_single rowIdx]
  · -- The term at rowIdx is (1 * val)
    simp only [if_true]
  · -- All other terms are 0
    intro b _ hb_ne
    simp [hb_ne]
  · -- rowIdx is in the domain
    intro h_notin
    exact (h_notin (Finset.mem_univ rowIdx)).elim

omit [CharP L 2] in
lemma preTensorCombine_is_interleavedCodeword_of_codeword (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    (⋈|(preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f)) ∈
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ^⋈ (Fin (2 ^ steps))) := by
  -- 1. Interleaved Code Definition: "A word is in the interleaved code iff every row is in the base code"
  set S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx with h_S_next
  set u := (⋈|(preTensorCombine_WordStack 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f)) with h_u
  set C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
  simp only [InterleavedWord, InterleavedSymbol, ModuleCode,
    instCodeInterleavableModuleCodeInterleavedSymbol, ModuleCode.moduleInterleavedCode,
    interleavedCodeSet, SetLike.mem_coe, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  -- ⊢ ∀ (k : Fin (2 ^ steps)), uᵀ k ∈ C_next
  intro rowIdx
  -- 2. Setup: Define the specific challenge 'r' corresponding to row index 'rowIdx'
  let r_binary : Fin steps → L := bitsOfIndex rowIdx
  -- 3. Geometric Equivalence:
  -- Show that the `rowIdx`-th row of preTensorCombine is exactly `iterated_fold` of u with challenge r
  -- We rely on Lemma 4.9 (Matrix Form) which states: M_y * vals = iterated_fold(u, r, y)
  let preTensorCombine_Row: S_next → L := preTensorCombine_WordStack 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le (f_i := f) rowIdx
  let rowIdx_binary_folded_Row: S_next → L := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_binary)
  have h_row_eq_fold : preTensorCombine_Row = rowIdx_binary_folded_Row := by
    funext y
    exact preTensorCombine_row_eq_fold_with_binary_row_challenges 𝔽q β i
      steps h_destIdx h_destIdx_le f rowIdx y
  have h_row_of_u_eq: (uᵀ rowIdx) = preTensorCombine_Row := by rfl
  rw [←h_row_of_u_eq] at h_row_eq_fold
  rw [h_row_eq_fold]
  -- ⊢ rowIdx_binary_folded_Row ∈ C_next (i.e. lhs is of `fold(f, binary_rowIdx_challenges)` form)
  unfold rowIdx_binary_folded_Row
  exact iterated_fold_preserves_BBF_Code_membership 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_binary)

/-!
--------------------------------------------------------------------------------
   SECTION: THE LIFT INFRASTRUCTURE
   Constructing the inverse map from Interleaved Codewords back to Domain CodeWords
--------------------------------------------------------------------------------
-/


open Code.InterleavedCode in
def getRowPoly (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) : Fin (2 ^ steps) → L⦃<2^(ℓ-destIdx.val)⦄[X] := fun j => by
  -- 1. Extract polynomials P_j from V_codeword components
  set S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx with h_S_next
  set C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx with h_C_next
  let curRow := getRow (show InterleavedCodeword (A := L) (κ := Fin (2 ^ steps)) (ι := S_next) (C := C_next) from V_codeword) j
  have h_V_in_C_next : curRow.val ∈ (C_next) := by
    have h_V_mem := V_codeword.property
    let res := Code.InterleavedCode.getRowOfInterleavedCodeword_mem_code (C := (C_next : Set (S_next → L)))
      (κ := Fin (2 ^ steps)) (ι := S_next) (u := V_codeword) (rowIdx := j)
    exact res
  -- For each j, there exists a polynomial P_j of degree < 2^(ℓ - (i+steps))
  exact getBBF_Codeword_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) curRow

def getLiftCoeffs (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) : Fin (2^(ℓ - i)) → L := fun coeff_idx =>
    -- intertwining novel coeffs of the rows of V_codeword
    -- decompose `coeff_idx = colIdx * 2 ^ steps + rowIdx` as in paper,
      -- i.e. traverse column by column
    let colIdx : Fin (2 ^ (ℓ - destIdx.val)) := ⟨coeff_idx.val / (2 ^ steps), by
      apply Nat.div_lt_of_lt_mul;
      rw [← Nat.pow_add];
      convert coeff_idx.isLt using 2; omega
    ⟩
    let rowIdx : Fin (2 ^ steps) := ⟨coeff_idx.val % (2 ^ steps), by
      have h_coeff_idx_lt_two_pow_ℓ_i : coeff_idx.val < 2 ^ (ℓ - i) := by
        exact coeff_idx.isLt
      have h_coeff_idx_mod_two_pow_steps : coeff_idx.val % (2 ^ steps) < 2 ^ steps := by
        apply Nat.mod_lt; simp only [gt_iff_lt, ofNat_pos, pow_pos]
      exact h_coeff_idx_mod_two_pow_steps
    ⟩
    let coeff := getINovelCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (h_i := h_destIdx_le) (P := (getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i steps h_destIdx h_destIdx_le V_codeword) rowIdx) colIdx
    coeff

/-- Given an interleaved codeword `V ∈ C ⋈^ (2^steps)`, this method converts `2^steps` row polys
of `V` into a poly `P ∈ L[X]_(2^(ℓ-i))` that generates the fiber evaluator `g : S⁽ⁱ⁾ → L`
(this `g` produces the RHS vector in equality of **Lemma 4.9**). If we fold this function `g` using
**binary challenges** corresponding to each of the `2^steps` rows of `V`, let's say `j`,
we also folds `P` into the corresponding row polynomial `P_j` of the `j`-th row of `V`
(via **Lemma 4.13, aka iterated_fold_advances_evaluation_poly**). This works as a core engine for
proof of **Lemma 4.21**. -/
def getLiftPoly (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) : L⦃<2^(ℓ-i)⦄[X] := by
  have h_ℓ_lt_r : ℓ < r := by
    have h_pos : 0 < 𝓡 := Nat.pos_of_neZero (n := 𝓡)
    exact lt_trans (Nat.lt_add_of_pos_right (n := ℓ) (k := 𝓡) h_pos) h_ℓ_add_R_rate
  have h_i_lt_r : (i : Nat) < r := lt_trans i.isLt h_ℓ_lt_r
  let iR : Fin r := ⟨i, h_i_lt_r⟩
  refine ⟨intermediateEvaluationPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := iR) (h_i := by
        exact Nat.le_of_lt i.isLt)
      (coeffs := getLiftCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i steps h_destIdx h_destIdx_le V_codeword), ?_⟩
  apply Polynomial.mem_degreeLT.mpr
  exact degree_intermediateEvaluationPoly_lt (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := iR) (h_i := by
      exact Nat.le_of_lt i.isLt)
    (coeffs := getLiftCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le V_codeword)

/-- **Lift Function (Inverse Folding)**
Constructs a function `f` on the domain `S^{(i)}` from an interleaved word `W` on `S^{(i+steps)}`.
For any point `x` in the larger domain, we identify its quotient `y` and its index in the fiber.
We recover the fiber values by applying `M_y⁻¹` to the column `W(y)`.
-/
noncomputable def lift_interleavedCodeword (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) :
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ := by
  let P : L[X]_(2 ^ (ℓ - ↑i)) := getLiftPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le V_codeword
  -- 3. Define g as evaluation of P
  let g := getBBF_Codeword_of_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (h_i := by
      exact Nat.le_of_lt i.isLt) P
  exact g

omit [CharP L 2] in
/-- **Lemma 4.21 Helper**: Folding the "Lifted" polynomial `g` with binary challenges corresponding
to row index `j ∈ Fin(2^steps)`, results exactly in the `j`-th row polynomial `P_j`.
**Key insight**: **Binary folding** is a **(Row) Selector**
Proof strategy: applying `iterated_fold_advances_evaluation_poly` and
`intermediateEvaluationPoly_from_inovel_coeffs_eq_self`, then arithemetic equality for novel coeffs
computations in both sides. -/
lemma folded_lifted_IC_eq_IC_row_polyToOracleFunc (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)^⋈(Fin (2 ^ steps))))
    (j : Fin (2 ^ steps)) :
    let g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le V_codeword
    let P_j := (getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le
      V_codeword) j
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) g (bitsOfIndex j) =
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx) P_j := by
  -- 1. Unfold definitions to expose the underlying polynomials
  -- dsimp only [lift_interleavedCodeword, getLiftPoly]
  simp only
  set g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le V_codeword with h_g
  set P_j := (getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le V_codeword) j
  set P_G := getLiftPoly 𝔽q β i steps h_destIdx h_destIdx_le V_codeword with h_P_G -- due to def of `g`
  have h_g : g = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := ⟨i, by omega⟩) P_G := by rfl
  -- unfold getLiftPoly at h_P_G
  let novelCoeffs := getLiftCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le V_codeword
  -- have h_P_G_eq: P_G = intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
    -- (i := ⟨i, by omega⟩) novelCoeffs := by rfl
  let h_fold_g_advances_P_G := iterated_fold_advances_evaluation_poly 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (r_challenges := bitsOfIndex j) (coeffs := novelCoeffs)
  simp only at h_fold_g_advances_P_G
  conv_lhs at h_fold_g_advances_P_G => -- make it matches the lhs goal
    change iterated_fold 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := g) (bitsOfIndex j)
  conv_lhs => rw [h_fold_g_advances_P_G]
  -- ⊢ polyToOracleFunc 𝔽q β ⟨↑i + steps, ⋯⟩
  --   (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨↑i + steps, ⋯⟩ fun j_1 ↦
  --     ∑ x, multilinearWeight (bitsOfIndex j) x * novelCoeffs ⟨↑j_1 * 2 ^ steps + ↑x, ⋯⟩) =
  -- polyToOracleFunc 𝔽q β ⟨↑i + steps, ⋯⟩ ↑P_j
  have h_P_j_novel_form := intermediateEvaluationPoly_from_inovel_coeffs_eq_self 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := h_destIdx_le) (P := P_j) (hP_deg := by
        have h_mem := P_j.property
        rw [Polynomial.mem_degreeLT] at h_mem
        exact h_mem )
  conv_rhs => rw [←h_P_j_novel_form]
  -- polyToOracleFunc(intermediateEvaluationPoly(FOLDED novelCoeffs of P))) (via Lemma 4.13)
    -- = polyToOracleFunc(intermediateEvaluationPoly(inovelCoeffs of P_j))
  unfold polyToOracleFunc intermediateEvaluationPoly novelCoeffs
  simp only [map_sum, map_mul]
  funext y
  congr 1
  apply Finset.sum_congr rfl
  intro x hx_mem_univ
  rw [mul_eq_mul_right_iff]; left
  -- **Arithemetic reasoning**:
  -- ⊢ ∑ x_1, Polynomial.C (multilinearWeight (bitsOfIndex j) x_1) *
          --  Polynomial.C (getLiftCoeffs 𝔽q β i steps ⟨↑x * 2 ^ steps + ↑x_1, ⋯⟩) =
  -- Polynomial.C (getINovelCoeffs 𝔽q β h_ℓ_add_R_rate ⟨↑i + steps, ⋯⟩ (↑P_j) x)
  -- 1. Combine the Ring Homomorphisms to pull C outside the sum
  --    ∑ C(w) * C(v) -> C(∑ w * v)
  simp_rw [←Polynomial.C_mul]
  unfold getINovelCoeffs getLiftCoeffs
  simp only [mul_add_mod_self_right, map_mul]
  -- , ←Polynomial.C_sum]
  -- 2. Use the Indicator Property of multilinearWeight with binary challenges
  --    This logic should ideally be its own lemma: `weight_bits_eq_indicator`
  have h_indicator : ∀ m : Fin (2^steps), multilinearWeight (F := L) (r := bitsOfIndex j)
    (i := m) = if m = j then 1 else 0 := fun m => by
    apply multilinearWeight_bitsOfIndex_eq_indicator (j := m) (k := j)
  simp_rw [h_indicator]
  -- 3. Collapse the Sum using Finset.sum_eq_single
  rw [Finset.sum_eq_single j]
  · -- Case: The Match (x_1 = j)
    simp only [↓reduceIte, map_one, one_mul, Polynomial.C_inj]
    unfold getINovelCoeffs
    have h_idx_decomp : (x.val * 2 ^ steps + j.val) / 2^steps = x.val := by
      have h_j_div_2_pow_steps : j.val / 2^steps = 0 := by
        apply Nat.div_eq_of_lt; omega
      rw [mul_comm]
      have h_res := Nat.mul_add_div (m := 2 ^ steps) (x := x.val) (y := j.val) (m_pos := by
        simp only [gt_iff_lt, ofNat_pos, pow_pos])
      simp only [h_j_div_2_pow_steps, add_zero] at h_res
      exact h_res
    congr 1
    · funext k
      congr
      · apply Nat.mod_eq_of_lt; omega
    · simp_rw [h_idx_decomp]
  · -- Case: The Mismatch (x_1 ≠ j)
    intro m _ h_neq
    simp only [h_neq, ↓reduceIte, map_zero, zero_mul]
  · -- Case: Domain (Empty implies false, but we are in Fin (2^steps))
    intro h_absurd
    exfalso; exact h_absurd (Finset.mem_univ j)

omit [CharP L 2] in
open Code.InterleavedCode in
lemma preTensorCombine_of_lift_interleavedCodeword_eq_self (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) :
    let g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le V_codeword
    (⋈|(preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g)) = V_codeword.val := by
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  set g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (V_codeword := V_codeword)
  -- **FIRST**,
    -- `∀ j : Fin (2^ϑ), (V_codeword j)` and `fold(g, bitsOfIndex j)` agree identically
        -- over `S^{(i+ϑ)}`
    -- the dotproduct between `M_y's j'th ROW` and `G = g's restriction to the fiber of y`
        -- is actually the result of `fold(G, bitsOfIndex j)`
  have h_agree_with_fold := preTensorCombine_row_eq_fold_with_binary_row_challenges 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le g
  let eq_iff_all_rows_eq := (instInterleavedStructureInterleavedWord (A := L) (κ := Fin (2 ^ steps))
    (ι := S_next)).eq_iff_all_rows_eq (u := ⋈|preTensorCombine_WordStack 𝔽q β (i := i)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (↑g)) (v := V_codeword.val)
  simp only
  rw [eq_iff_all_rows_eq]
  intro j
  funext (y : S_next) -- compare the cells at (j, y)
  set G := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g) (y := y)
  simp only [InterleavedWord, Word, InterleavedSymbol, instInterleavedStructureInterleavedWord,
    InterleavedWord.getRowWord, InterleavedWord.getSymbol, transpose_apply, WordStack,
    instInterleavableWordStackInterleavedWord, interleave_wordStack_eq, ModuleCode,
    instCodeInterleavableModuleCodeInterleavedSymbol.eq_1, ModuleCode.moduleInterleavedCode.eq_1,
    interleavedCodeSet.eq_1]
  -- ⊢ preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le (↑g) j = (↑V_codeword)ᵀ j
  unfold preTensorCombine_WordStack
  simp only
  set M_y := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y
  -- ⊢ (foldMatrix 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ y *ᵥ fiberEvaluations 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ (↑g) y) j
    -- = ↑V_codeword y j
  change (M_y *ᵥ G) j = V_codeword.val y j
  let lhs_eq_fold := h_agree_with_fold j y
  unfold preTensorCombine_WordStack at lhs_eq_fold
  simp at lhs_eq_fold
  rw [lhs_eq_fold]
  -- ⊢ iterated_fold 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ (↑g) (bitsOfIndex j) y = ↑V_codeword y j
  -- **SECOND**, we prove that **the same row polynomial `P_j(X)` is used to generates** bot
    -- `fold(g, bitsOfIndex j)` and `j'th row of V_codeword`
  let curRow := getRow (show InterleavedCodeword (A := L) (κ := Fin (2 ^ steps))
    (ι := S_next) (C := C_next) from V_codeword) j
  let P_j := getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le V_codeword j
  let lhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g)
    (r_challenges := bitsOfIndex j)
  let rhs := curRow.val
  let generatedRow : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx) (P := P_j)
  have h_left_eq_P_j_gen: lhs = generatedRow := by
    unfold lhs generatedRow -- ⊢ iterated_fold 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ (↑g) (bitsOfIndex j)
      -- = polyToOracleFunc 𝔽q β ⟨↑i + steps, ⋯⟩ ↑P_j
    apply folded_lifted_IC_eq_IC_row_polyToOracleFunc
  have h_right_eq_P_j_eval: rhs = generatedRow := by
    unfold rhs generatedRow
    rw [getBBF_Codeword_poly_spec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (u := curRow)]; rfl
  conv_lhs => change lhs y
  conv_rhs => change rhs y
  rw [h_left_eq_P_j_gen, h_right_eq_P_j_eval]

/-- TODO: **Lifting Equivalence Lemma**: `lift(preTensorCombine(f)) = f`. -/

def fiberDiff (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : Prop :=
  ∃ x,
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (destIdx := destIdx)
      (k := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x = y ∧
    f x ≠ g x

/-- **Distance Isomorphism Lemma**
The crucial logic for Lemma 4.21:
Two functions `f, g` differ on a specific fiber `y` IF AND ONLY IF
their tensor-combinations `U, V` differ at the column `y`.
This holds because `M_y` is a bijection. -/
lemma fiberwise_disagreement_isomorphism (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    fiberDiff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f g y ↔
    WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) y ≠
    WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) y := by
  -- U_y = M_y * f_vals, V_y = M_y * g_vals
  let M_y := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y
  let f_vals := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f y
  let g_vals := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) g y
  have h_det : M_y.det ≠ 0 := foldMatrix_det_ne_zero 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y)
  constructor
  · -- Forward: Fiber different => Columns different
    intro h_diff
    -- If fiber is different, then vectors f_vals ≠ g_vals
    have h_vec_diff : f_vals ≠ g_vals := by
      rcases h_diff with ⟨x, h_gen_y, h_val_ne⟩ -- h_val_ne : f x ≠ g x
      intro h_eq
      let x_is_fiber_of_y := is_fiber_iff_generates_quotient_point 𝔽q β
        (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (x := x) (y := y).mp (by exact id (Eq.symm h_gen_y))
      let x_fiberIdx : Fin (2 ^ steps) :=
        pointToIterateQuotientIndex 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := x)
      have h_left_eval : f_vals x_fiberIdx = f x := by
        unfold f_vals fiberEvaluations
        rw [x_is_fiber_of_y]
      have h_right_eval : g_vals x_fiberIdx = g x := by
        unfold g_vals fiberEvaluations
        rw [x_is_fiber_of_y]
      let h_eval_eq := congrFun h_eq x_fiberIdx
      rw [h_left_eval, h_right_eval] at h_eval_eq -- f x = g x
      exact h_val_ne h_eval_eq
    -- M_y is invertible, so M_y * u = M_y * v => u = v. Contrapositive: u ≠ v => M_y * u ≠ M_y * v
    intro h_col_eq
    apply h_vec_diff
    -- ⊢ f_vals = g_vals
    -- h_col_eq: WordStack.getSymbol (preTensorCombine_WordStack ... f) y = WordStack.getSymbol (preTensorCombine_WordStack ... g) y
    -- This means: M_y *ᵥ f_vals = M_y *ᵥ g_vals
    -- Rewrite as: M_y *ᵥ (f_vals - g_vals) = 0
    have h_mulVec_sub_eq_zero : M_y *ᵥ (f_vals - g_vals) = 0 := by
      -- From h_col_eq and the definition of preTensorCombine_WordStack:
      -- WordStack.getSymbol (preTensorCombine_WordStack ... f) y = M_y *ᵥ f_vals
      -- WordStack.getSymbol (preTensorCombine_WordStack ... g) y = M_y *ᵥ g_vals
      have h_f_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) y = M_y *ᵥ f_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      have h_g_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) y = M_y *ᵥ g_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      -- ⊢ M_y *ᵥ (f_vals - g_vals) = 0
      rw [h_f_col, h_g_col] at h_col_eq
      -- Now h_col_eq: M_y *ᵥ f_vals = M_y *ᵥ g_vals
      rw [Matrix.mulVec_sub]
      -- Goal: M_y *ᵥ f_vals - M_y *ᵥ g_vals = 0
      rw [← h_col_eq]
      -- Goal: M_y *ᵥ f_vals - M_y *ᵥ f_vals = 0
      rw [sub_self]
    -- Apply eq_zero_of_mulVec_eq_zero to get f_vals - g_vals = 0
    have h_sub_eq_zero : f_vals - g_vals = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero h_det h_mulVec_sub_eq_zero -- `usage of M_y's nonsingularity`
    -- Convert to f_vals = g_vals
    exact sub_eq_zero.mp h_sub_eq_zero
  · -- Backward: Columns different => Fiber different
    intro h_col_diff
    by_contra h_fiber_eq
    -- h_fiber_eq: ¬fiberDiff, i.e., ∀ x, iteratedQuotientMap ... x = y → f x = g x
    -- If f and g agree on all points in the fiber of y, then f_vals = g_vals
    have h_vals_eq : f_vals = g_vals := by
      ext idx
      -- f_vals idx = f evaluated at the idx-th point in the fiber of y
      -- g_vals idx = g evaluated at the idx-th point in the fiber of y
      -- We need to show they're equal
      unfold f_vals g_vals fiberEvaluations
      -- fiberEvaluations f y idx = f (qMap_total_fiber ... y idx)
      -- fiberEvaluations g y idx = g (qMap_total_fiber ... y idx)
      let x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y) idx
      -- x is in the fiber of y, so iteratedQuotientMap ... x = y
      have h_x_in_fiber :
          iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (destIdx := destIdx)
            (k := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x = y := by
        -- This follows from generates_quotient_point_if_is_fiber_of_y
        have h := generates_quotient_point_if_is_fiber_of_y 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := x) (y := y) (hx_is_fiber := by use idx)
        exact h.symm
      -- Since h_fiber_eq says no point in the fiber has f x ≠ g x,
      -- we have f x = g x for all x in the fiber
      have h_fx_eq_gx : f x = g x := by
        -- h_fiber_eq: ¬fiberDiff, which is ¬(∃ x, iteratedQuotientMap ... x = y ∧ f x ≠ g x)
        -- By De Morgan: ∀ x, ¬(iteratedQuotientMap ... x = y ∧ f x ≠ g x)
        -- Which means: ∀ x, iteratedQuotientMap ... x = y → f x = g x
        -- h_fiber_eq is now: ∀ x, iteratedQuotientMap ... x = y → f x = g x
        unfold fiberDiff at h_fiber_eq
        simp only [ne_eq, Subtype.exists, not_exists, not_and, Decidable.not_not] at h_fiber_eq
        let res := h_fiber_eq x (by simp only [SetLike.coe_mem]) h_x_in_fiber
        exact res
      -- Now f_vals idx = f x = g x = g_vals idx
      exact h_fx_eq_gx
    -- If f_vals = g_vals, then M_y *ᵥ f_vals = M_y *ᵥ g_vals
    have h_col_eq : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) y =
                    WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) y := by
      -- From the forward direction, we know:
      -- WordStack.getSymbol (preTensorCombine_WordStack ... f) y = M_y *ᵥ f_vals
      -- WordStack.getSymbol (preTensorCombine_WordStack ... g) y = M_y *ᵥ g_vals
      have h_f_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) y = M_y *ᵥ f_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      have h_g_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) y = M_y *ᵥ g_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      rw [h_f_col, h_g_col]
      -- Goal: M_y *ᵥ f_vals = M_y *ᵥ g_vals
      rw [h_vals_eq]
    -- This contradicts h_col_diff
    exact h_col_diff h_col_eq

end Lift_PreTensorCombine

open Code.InterleavedCode in
/-- If `f_i` is fiberwise close to the destination code, then its
`preTensorCombine` word stack is jointly close to the corresponding interleaved code. -/
lemma preTensorCombine_jointProximityNat_of_fiberwiseClose (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let U := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i
    let C_next : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    jointProximityNat (C := C_next) (u := U) (e := Code.uniqueDecodingRadius (C := C_next)) := by
  intro U C_next
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  have h_close' := h_close
  unfold fiberwiseClose fiberwiseDistance at h_close'
  let dist_set := (fun (g : C_i) =>
    pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le (f := f_i) (g := g)) '' Set.univ
  have h_dist_set_nonempty : dist_set.Nonempty :=
    ⟨_, ⟨0, Set.mem_univ _, rfl⟩⟩
  have h_inf_mem : sInf dist_set ∈ dist_set := Nat.sInf_mem h_dist_set_nonempty
  obtain ⟨g, _, h_g_dist⟩ := h_inf_mem
  have h_g_close_nat : pair_fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx
      h_destIdx_le f_i g ≤ Code.uniqueDecodingRadius (C := C_next) := by
    have h_pfd_eq_sinf : pair_fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩)
        steps h_destIdx h_destIdx_le f_i g = sInf dist_set := h_g_dist
    have h_2pfd_lt_d : 2 * pair_fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩)
        steps h_destIdx h_destIdx_le f_i g <
        (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
      rw [h_pfd_eq_sinf]; exact_mod_cast h_close'
    have h_dist_eq_norm : (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        destIdx : ℕ) = ‖(C_next : Set _)‖₀ := by
      simp only [C_next, BBF_CodeDistance]
    have h_2pfd_lt_norm : 2 * pair_fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩)
        steps h_destIdx h_destIdx_le f_i g < ‖(C_next : Set _)‖₀ := by
      rw [← h_dist_eq_norm]; exact h_2pfd_lt_d
    haveI : NeZero ‖(C_next : Set _)‖₀ := ⟨by omega⟩
    exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR (C := C_next)).mpr h_2pfd_lt_norm
  let V := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g.val
  have h_V_codeword : (⋈|V) ∈ (C_next ^⋈ (Fin (2^steps))) :=
    preTensorCombine_is_interleavedCodeword_of_codeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le
      ⟨g.val, g.property⟩
  have h_dist_eq : Δ₀(⋈|U, ⋈|V) =
      pair_fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i g := by
    unfold hammingDist pair_fiberwiseDistance fiberwiseDisagreementSet
    congr 1; ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h_iso := fiberwise_disagreement_isomorphism 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_i) (g := g.val) (y := y)
    unfold fiberDiff at h_iso
    simp only [WordStack.getSymbol] at h_iso
    exact h_iso.symm
  unfold jointProximityNat
  calc Δ₀(⋈|U, (C_next ^⋈ (Fin (2^steps))))
      ≤ Δ₀(⋈|U, ⋈|V) := Code.distFromCode_le_dist_to_mem _ _ h_V_codeword
    _ = ↑(pair_fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i g) := by
        exact_mod_cast h_dist_eq
    _ ≤ ↑(Code.uniqueDecodingRadius (C := C_next)) := by
        exact_mod_cast h_g_close_nat

open Code.InterleavedCode in
/-- **Lemma 4.21** (Interleaved Distance Preservation):
If `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) ≥ d_{i+ϑ} / 2` (`f` is fiber-wise far wrt UDR),
then `d^{2^ϑ}( (f_j⁽ⁱ⁺ϑ⁾)_{j=0}^{2^ϑ - 1}, C^{(i+ϑ)^{2^ϑ}} ) ≥ d_{i+ϑ} / 2`
  (i.e. interleaved distance ≥ UDR distance).
* **Main Idea of Proof:** For an ARBITRARY interleaved codeword `(g_j⁽ⁱ⁺ϑ⁾)`,
a "lift" `g⁽ⁱ⁾ ∈ C⁽ⁱ⁾` is constructed. It's shown that `g⁽ⁱ⁾` relates to `(g_j⁽ⁱ⁺ϑ⁾)` (via
folding with basis vectors as challenges) similarly to how `f⁽ⁱ⁾` relates to `(f_j⁽ⁱ⁺ϑ⁾)` (via
Lemma 4.9 and matrix `M_y`). Since `f⁽ⁱ⁾` is far from `g⁽ⁱ⁾` on many fibers (by hypothesis), and
`M_y` is invertible, the columns `(f_j⁽ⁱ⁺ϑ⁾(y))` and `(g_j⁽ⁱ⁺ϑ⁾(y))` must differ for these `y`,
establishing the distance for the interleaved words. -/
lemma lemma_4_21_interleaved_word_UDR_far (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let U := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i
    let C_next : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    ¬(jointProximityNat (C := C_next) (u := U) (e := Code.uniqueDecodingRadius (C := C_next))) := by
  let m := 2^steps
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let C : Set (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ → L) :=
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let C_int := C_next ^⋈ (Fin m)
  let U_wordStack := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i
  let U_interleaved : InterleavedWord L (Fin m) S_next := ⋈|U_wordStack
  let d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := destIdx)
  let e_udr := Code.uniqueDecodingRadius (C := (C_next : Set (S_next → L)))
  have h_fiber_dist_ge : ∀ g : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩,
      2 * (fiberwiseDisagreementSet 𝔽q β ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i g).card
        ≥ d_next := by
    intro g
    unfold fiberwiseClose at h_far
    rw [not_lt] at h_far
    let dist_set := (fun (g' : C) =>
      (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i g').card) '' Set.univ
    have h_min_le_g : fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le
        f_i ≤
        (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i g).card := by
      apply csInf_le
      · use 0
        rintro _ ⟨_, _, rfl⟩
        simp only [_root_.zero_le]
      · use g
        simp only [Set.mem_univ, true_and]
        rfl
    calc
      d_next ≤ 2 * fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i := by
        norm_cast at h_far
      _ ≤ 2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le
            f_i g).card := by
        exact Nat.mul_le_mul_left 2 h_min_le_g
  simp only
  intro h_U_close
  obtain ⟨V_codeword, h_dist_U_V⟩ := jointProximityNat_iff_closeToInterleavedCodeword
    (u := U_wordStack) (e := e_udr) (C := C_next) |>.mp h_U_close
  let g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx
    h_destIdx_le V_codeword
  have h_g_is_lift_of_V : (⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le ↑g)
    = V_codeword.val := by
    apply preTensorCombine_of_lift_interleavedCodeword_eq_self 𝔽q β
  have h_disagreement_equiv : ∀ y : S_next,
      (∃ x,
        iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (destIdx := destIdx)
          (k := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x = y ∧
        f_i x ≠ g.val x) ↔
      getSymbol U_interleaved y ≠ getSymbol V_codeword y := by
    intro y
    let res := fiberwise_disagreement_isomorphism 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_i) (g := g.val) (y := y)
    unfold fiberDiff at res
    rw [res]
    have h_col_U_y_eq : (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i).getSymbol y
      = getSymbol U_interleaved y := by rfl
    have h_col_V_y_eq :
        (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g.val).getSymbol y
          = getSymbol V_codeword y := by
      have h_get_symbol_eq :
          (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g.val).getSymbol y
            = getSymbol (⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le ↑g) y := by
        rfl
      rw [h_get_symbol_eq]
      rw [h_g_is_lift_of_V]
      rfl
    rw [h_col_U_y_eq, h_col_V_y_eq]
  have h_dist_eq : Δ₀(U_interleaved, V_codeword.val) ≥
      (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i g).card := by
    apply le_of_eq
    unfold hammingDist
    unfold fiberwiseDisagreementSet
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h_disagreement_equiv]
    rfl
  have h_ineq_1 : ¬(2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps
        h_destIdx h_destIdx_le f_i g).card < d_next) := by
    simp only [not_lt, h_fiber_dist_ge (g := ⟨g, by simp only [SetLike.coe_mem]⟩)]
  have h_ineq_2 :
      2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps
        h_destIdx h_destIdx_le f_i g).card < d_next := by
    calc
      2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps
        h_destIdx h_destIdx_le f_i g).card
          ≤ 2 * Δ₀(U_interleaved, V_codeword.val) := by omega
      _ ≤ 2 * e_udr := by
        exact Nat.mul_le_mul_left 2 h_dist_U_V
      _ < d_next := by
        letI : NeZero (‖(C_next : Set (S_next → L))‖₀) := NeZero.of_pos (by
          have h_pos : 0 <
              BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
            simp [BBF_CodeDistance_eq (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := destIdx) (h_i := h_destIdx_le)]
          simp only [C_next, BBF_CodeDistance] at h_pos ⊢
          exact h_pos
        )
        let res := Code.UDRClose_iff_two_mul_proximity_lt_d_UDR
          (C := (C_next : Set (S_next → L))) (e := e_udr).mp (by omega)
        exact res
  exact h_ineq_1 h_ineq_2

end

end Binius.BinaryBasefold
