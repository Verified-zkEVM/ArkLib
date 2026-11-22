/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.InterleavedCode
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
# Binary Basefold: the tensor-combine word stack and its lift

For a block of `steps` folding rounds starting at index `i`, `preTensorCombine` arranges an
oracle `f : S⁽ⁱ⁾ → L` as a word stack of `2 ^ steps` rows over `S⁽ⁱ⁺ˢᵗᵉᵖˢ⁾`: its column at `y` is
`M_y` applied to the values of `f` on the fiber of `y`, where `M_y` is the fold matrix
(`foldMatrix`, the matrix of [DP24] Lemma 4.9). This is the interleaved word of [DP24]
equation (41); a fold of `f` is the tensor combination of its rows (equation (42)).

## Main definitions

* `preTensorCombine`: the word stack above.
* `liftInterleavedCodeword`: the lift of an interleaved codeword of the destination code to a
  codeword of the source code, assembled from the novel-basis coefficients of its rows (the lift
  `g⁽ⁱ⁾` in the proof of [DP24] Lemma 4.22).

## Main statements

* `preTensorCombine_apply_eq_iteratedFold`: row `j` of the stack is the fold at the binary
  challenges `bitsOfIndex j`.
* `preTensorCombine_mem_interleavedCode`, `preTensorCombine_liftInterleavedCodeword`: the stack of
  a codeword is an interleaved codeword, and the stack of a lift is the lifted interleaved
  codeword.
* `mem_fiberwiseDisagreementSet_iff_getSymbol_preTensorCombine_ne`: two oracles differ on the
fiber of `y` exactly
  when their stacks differ at column `y` (`M_y` is invertible).
* `preTensorCombine_jointProximityNat_of_fiberwiseClose` and
  `preTensorCombine_not_jointProximityNat_of_not_fiberwiseClose`: an oracle is fiberwise close to
  the source code exactly when its stack is within the unique-decoding radius of the interleaved
  destination code. The far direction is [DP24] Lemma 4.22.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Numbering follows the archived revision of [DP24].
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]

omit [Fintype 𝔽q] in
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) := ⟨CharP.prime_ringChar 𝔽q⟩
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section Lift_PreTensorCombine

/-- The tensor-combine word stack of `f_i` over a block of `steps` folds: the entry at row `j`
and column `y ∈ S⁽ⁱ⁺ˢᵗᵉᵖˢ⁾` is the `j`-th entry of `M_y` applied to the values of `f_i` on the
fiber of `y`, with `M_y` the fold matrix `foldMatrix`. The columns are indexed by the evaluation
domain itself (not by `Fin`), so the generic code and proximity-gap lemmas apply; since `M_y`
varies with `y`, the stack is not a single matrix product. -/
def preTensorCombine (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    WordStack (A := L) (κ := Fin (2 ^ steps))
      (ι := sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := fun j y =>
    let M_y : Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L :=
      foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y)
    let fiber_vals : Fin (2 ^ steps) → L :=
      fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i) (y := y)
    (M_y *ᵥ fiber_vals) j

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [SampleableType L] in
/-- Folding is the multilinear combination of the tensor-combine stack at the same challenges. -/
lemma iteratedFold_eq_multilinearCombine_preTensorCombine
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (challenges : Fin steps → L) :
    iteratedFold 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      h_destIdx h_destIdx_le f challenges =
      multilinearCombine (preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le f) challenges := by
  ext y
  rw [iteratedFold_eq_matrix_form]
  unfold iteratedFoldMatrixForm pointFoldMatrixForm multilinearCombine
  simp only [dotProduct, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => rfl

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
omit [SampleableType L] in
/-- Row `rowIdx` of the tensor-combine stack of any oracle `f` is the fold of `f` at the binary
challenges `bitsOfIndex rowIdx`. -/
lemma preTensorCombine_apply_eq_iteratedFold
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (rowIdx : Fin (2 ^ steps)) :
    ∀ y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx,
      (preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le f) rowIdx y =
      iteratedFold 𝔽q β ⟨i, by omega⟩ steps
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
          (r_challenges := bitsOfIndex (L := L) (n := steps) rowIdx) (y := y) := by
  intro y
  -- LHS = (M_y * f_vals)[rowIdx]
  dsimp [preTensorCombine]
  -- RHS = Tensor(r) • (M_y * f_vals)
  rw [iteratedFold_eq_matrix_form 𝔽q β (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)]
  unfold iteratedFoldMatrixForm pointFoldMatrixForm
  -- Tensor(bits(rowIdx)) is the indicator vector for rowIdx
  let tensor := multilinearWeight (ϑ := steps) (bitsOfIndex (L := L) rowIdx)
  have h_indicator : tensor = fun k => if k = rowIdx then 1 else 0 :=
    multilinearWeight_bitsOfIndex_fun (L := L) rowIdx
  simp only
  -- (Indicator • Vector) is exactly Vector[rowIdx]
  dsimp only [tensor] at h_indicator
  rw [h_indicator]
  rw [dotProduct]
  simp only [boole_mul]
  rw [Finset.sum_eq_single rowIdx]
  · -- The term at rowIdx is (1 * val)
    simp only [ite_true]
  · -- All other terms are 0
    intro b _ hb_ne
    simp [hb_ne]
  · -- rowIdx is in the domain
    intro h_notin
    exact (h_notin (Finset.mem_univ rowIdx)).elim

omit [DecidableEq 𝔽q] [NeZero ℓ] in
omit [SampleableType L] in
/-- The tensor-combine stack of a codeword is an interleaved codeword of the destination code:
each row is a fold of the codeword. -/
lemma preTensorCombine_mem_interleavedCode (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    (⋈|(preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le f)) ∈
      (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ^⋈ (Fin (2 ^ steps))) := by
  set S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx with h_S_next
  set u := (⋈|(preTensorCombine 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le f)) with h_u
  set C_next := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
  simp only [InterleavedWord, InterleavedSymbol, ModuleCode]
  intro rowIdx
  let r_binary : Fin steps → L := bitsOfIndex rowIdx
  -- Show that the `rowIdx`-th row of preTensorCombine is exactly `iteratedFold` of u with
  -- challenge r
  -- By the matrix form of folding: M_y * vals = iteratedFold(u, r, y)
  let preTensorCombine_Row: S_next → L := preTensorCombine 𝔽q β (h_ℓ_add_R_rate :=
    h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le (f_i := f) rowIdx
  let rowIdx_binary_folded_Row: S_next → L := iteratedFold 𝔽q β (h_ℓ_add_R_rate :=
    h_ℓ_add_R_rate) ⟨i, by omega⟩ steps (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f) (r_challenges := r_binary)
  have h_row_eq_fold : preTensorCombine_Row = rowIdx_binary_folded_Row := by
    funext y
    exact preTensorCombine_apply_eq_iteratedFold 𝔽q β i
      steps h_destIdx h_destIdx_le f rowIdx y
  have h_row_of_u_eq: (uᵀ rowIdx) = preTensorCombine_Row := by rfl
  rw [←h_row_of_u_eq] at h_row_eq_fold
  rw [h_row_eq_fold]
  unfold rowIdx_binary_folded_Row
  exact iteratedFold_mem_code 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_binary)

/-! ### The lift from interleaved codewords of the destination code to the source code -/

open Code.InterleavedCode in
/-- The message polynomials (in the novel basis of the destination index) of the rows of an
interleaved codeword of the destination code. -/
def rowPoly (steps : ℕ) {destIdx : Fin r}
    (V_codeword : ((code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)^⋈(Fin (2 ^
      steps)))) : Fin (2 ^ steps) → L⦃<2^(ℓ-destIdx.val)⦄[X] := fun j => by
  set S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx with h_S_next
  set C_next := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx with h_C_next
  let curRow := getRow (show InterleavedCodeword (A := L) (κ := Fin (2 ^ steps)) (ι := S_next) (C :=
      C_next) from V_codeword) j
  have h_V_in_C_next : curRow.val ∈ (C_next) := by
    have h_V_mem := V_codeword.property
    have res := Code.InterleavedCode.getRowOfInterleavedCodeword_mem_code (C := (C_next : Set
      (S_next → L)))
      (κ := Fin (2 ^ steps)) (ι := S_next) (u := V_codeword) (rowIdx := j)
    exact res
  -- For each j, there exists a polynomial P_j of degree < 2^(ℓ - (i+steps))
  exact codewordPolynomial 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) curRow

/-- The novel-basis coefficients of the lift: coefficient `colIdx * 2 ^ steps + rowIdx` is
coefficient `colIdx` of row polynomial `rowIdx`. -/
def liftCoeffs (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)^⋈(Fin (2 ^
      steps)))) : Fin (2^(ℓ - i)) → L := fun coeff_idx =>
    -- intertwining novel coeffs of the rows of V_codeword
    -- decompose `coeff_idx = colIdx * 2 ^ steps + rowIdx`,
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
        apply Nat.mod_lt; simp only [ofNat_pos, pow_pos]
      exact h_coeff_idx_mod_two_pow_steps
    ⟩
    let coeff := getINovelCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (h_i := h_destIdx_le) (P := (rowPoly 𝔽q β (h_ℓ_add_R_rate :=
        h_ℓ_add_R_rate)
        steps V_codeword) rowIdx) colIdx
    coeff

/-- The lift polynomial of an interleaved codeword `V` of the destination code: the polynomial of
degree `< 2 ^ (ℓ - i)` with novel-basis coefficients `liftCoeffs`. Folding its evaluation at
the binary challenges of row `j` gives the row polynomial `P_j` of `V`
(`iteratedFold_liftInterleavedCodeword_bitsOfIndex`, via
`iteratedFold_advances_evaluation_poly`). -/
def liftPoly (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)^⋈(Fin (2 ^
      steps)))) : L⦃<2^(ℓ-i)⦄[X] := by
  have h_ℓ_lt_r : ℓ < r := by
    have h_pos : 0 < 𝓡 := Nat.pos_of_neZero (n := 𝓡)
    exact lt_trans (Nat.lt_add_of_pos_right (n := ℓ) (k := 𝓡) h_pos) h_ℓ_add_R_rate
  have h_i_lt_r : (i : Nat) < r := lt_trans i.isLt h_ℓ_lt_r
  let iR : Fin r := ⟨i, h_i_lt_r⟩
  refine ⟨intermediateEvaluationPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := iR) (h_i := by
        exact Nat.le_of_lt i.isLt)
      (coeffs := liftCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i steps h_destIdx h_destIdx_le V_codeword), ?_⟩
  apply Polynomial.mem_degreeLT.mpr
  exact degree_intermediateEvaluationPoly_lt (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := iR) (h_i := by
      exact Nat.le_of_lt i.isLt)
    (coeffs := liftCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le V_codeword)

/-- The lift of an interleaved codeword `V` of the destination code: the source codeword that
encodes `liftPoly V`. Its tensor-combine stack is `V`
(`preTensorCombine_liftInterleavedCodeword`), so it inverts `preTensorCombine` on codewords. -/
noncomputable def liftInterleavedCodeword (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)^⋈(Fin (2 ^
      steps)))) :
    code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ := by
  let P : L[X]_(2 ^ (ℓ - ↑i)) := liftPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le V_codeword
  let g := polynomialCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩)  P
  exact g

omit [DecidableEq 𝔽q] [NeZero ℓ] in
omit [SampleableType L] in
/-- Folding the lift of `V` at the binary challenges of row `j` gives the evaluation of the
`j`-th row polynomial of `V`: at binary challenges, folding selects a row. The proof applies
`iteratedFold_advances_evaluation_poly` and compares novel-basis coefficients. -/
lemma iteratedFold_liftInterleavedCodeword_bitsOfIndex (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)^⋈(Fin (2 ^ steps))))
    (j : Fin (2 ^ steps)) :
    let g := liftInterleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le V_codeword
    let P_j := (rowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) steps V_codeword) j
    iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) g (bitsOfIndex j) =
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx) P_j := by
  simp only
  set g := liftInterleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le V_codeword with h_g
  set P_j := (rowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) steps V_codeword) j
  set P_G := liftPoly 𝔽q β i steps h_destIdx h_destIdx_le V_codeword with h_P_G
  have h_g : g = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := ⟨i, by omega⟩) P_G := by rfl
  let novelCoeffs := liftCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le V_codeword
  have h_fold_g_advances_P_G := iteratedFold_advances_evaluation_poly 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (r_challenges := bitsOfIndex j)
      (coeffs := novelCoeffs)
  simp only at h_fold_g_advances_P_G
  conv_lhs at h_fold_g_advances_P_G => -- make it matches the lhs goal
    change iteratedFold 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := g) (bitsOfIndex j)
  conv_lhs => rw [h_fold_g_advances_P_G]
  --   (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨↑i + steps, ⋯⟩ fun j_1 ↦
  --     ∑ x, multilinearWeight (bitsOfIndex j) x * novelCoeffs ⟨↑j_1 * 2 ^ steps + ↑x, ⋯⟩) =
  -- polyToOracleFunc 𝔽q β ⟨↑i + steps, ⋯⟩ ↑P_j
  have h_P_j_novel_form := intermediateEvaluationPoly_from_inovel_coeffs_eq_self 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := h_destIdx_le) (P := P_j)
      (hP_deg := by
        have h_mem := P_j.property
        rw [Polynomial.mem_degreeLT] at h_mem
        exact h_mem )
  conv_rhs => rw [←h_P_j_novel_form]
  -- polyToOracleFunc(intermediateEvaluationPoly(FOLDED novelCoeffs of P)))
  -- (via `iteratedFold_advances_evaluation_poly`)
    -- = polyToOracleFunc(intermediateEvaluationPoly(inovelCoeffs of P_j))
  unfold polyToOracleFunc intermediateEvaluationPoly novelCoeffs
  simp only [map_sum, map_mul]
  funext y
  congr 1
  apply Finset.sum_congr rfl
  intro x hx_mem_univ
  rw [mul_eq_mul_right_iff]; left
  -- Identify the row and coefficient indices in the lifted polynomial.
          --  Polynomial.C (liftCoeffs 𝔽q β i steps ⟨↑x * 2 ^ steps + ↑x_1, ⋯⟩) =
  -- Polynomial.C (getINovelCoeffs 𝔽q β h_ℓ_add_R_rate ⟨↑i + steps, ⋯⟩ (↑P_j) x)
  --    ∑ C(w) * C(v) -> C(∑ w * v)
  simp_rw [←Polynomial.C_mul]
  unfold getINovelCoeffs liftCoeffs
  simp only [mul_add_mod_self_right, map_mul]
  simp_rw [multilinearWeight_bitsOfIndex]
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

open Code.InterleavedCode in
omit [DecidableEq 𝔽q] in
omit [NeZero ℓ] in
omit [SampleableType L] in
/-- The tensor-combine stack of the lift of `V` is `V`. -/
lemma preTensorCombine_liftInterleavedCodeword (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)^⋈(Fin (2 ^
      steps)))) :
    let g := liftInterleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le V_codeword
    (⋈|(preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le g)) = V_codeword.val := by
  classical
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let C_next := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  set g := liftInterleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (V_codeword :=
      V_codeword)
    -- `∀ j : Fin (2^ϑ), (V_codeword j)` and `fold(g, bitsOfIndex j)` agree identically
        -- over `S^{(i+ϑ)}`
    -- the dotproduct between `M_y's j'th ROW` and `G = g's restriction to the fiber of y`
        -- is actually the result of `fold(G, bitsOfIndex j)`
  have h_agree_with_fold := preTensorCombine_apply_eq_iteratedFold 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le g
  let eq_iff_all_rows_eq := (instInterleavedStructureInterleavedWord (A := L) (κ := Fin (2 ^ steps))
    (ι := S_next)).eq_iff_all_rows_eq (u := ⋈|preTensorCombine 𝔽q β (i := i)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (↑g)) (v :=
        V_codeword.val)
  simp only
  rw [eq_iff_all_rows_eq]
  intro j
  funext (y : S_next) -- compare the cells at (j, y)
  set G := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g) (y := y)
  simp only [InterleavedWord, Word, InterleavedSymbol, WordStack,
    interleave_wordStack_eq, ModuleCode]
  unfold preTensorCombine
  simp only
  set M_y := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y
    -- = ↑V_codeword y j
  change (M_y *ᵥ G) j = V_codeword.val y j
  let lhs_eq_fold := h_agree_with_fold j y
  unfold preTensorCombine at lhs_eq_fold
  simp only at lhs_eq_fold
  rw [lhs_eq_fold]
    -- `fold(g, bitsOfIndex j)` and `j'th row of V_codeword`
  let curRow := getRow (show InterleavedCodeword (A := L) (κ := Fin (2 ^ steps))
    (ι := S_next) (C := C_next) from V_codeword) j
  let P_j := rowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) steps
    V_codeword j
  let lhs := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g)
    (r_challenges := bitsOfIndex j)
  let rhs := curRow.val
  let generatedRow : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx) (P := P_j)
  have h_left_eq_P_j_gen: lhs = generatedRow := by
    unfold lhs generatedRow -- ⊢ iteratedFold 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ (↑g) (bitsOfIndex j)
      -- = polyToOracleFunc 𝔽q β ⟨↑i + steps, ⋯⟩ ↑P_j
    apply iteratedFold_liftInterleavedCodeword_bitsOfIndex
  have h_right_eq_P_j_eval: rhs = generatedRow := by
    unfold rhs generatedRow
    rw [codewordPolynomial_spec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (u := curRow)]; rfl
  conv_lhs => change lhs y
  conv_rhs => change rhs y
  rw [h_left_eq_P_j_gen, h_right_eq_P_j_eval]

omit [NeZero ℓ] [SampleableType L] [DecidableEq 𝔽q] in
/-- Two oracles differ somewhere on the fiber of `y` exactly when their tensor-combine stacks
differ at column `y`, since the fold matrix `M_y` is invertible. -/
lemma mem_fiberwiseDisagreementSet_iff_getSymbol_preTensorCombine_ne (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    y ∈ fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f g ↔
    WordStack.getSymbol (preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le f) y ≠
    WordStack.getSymbol (preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le g) y := by
  classical
  let M := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y
  let values (word : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :=
    fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) word y
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero
      (foldMatrix_det_ne_zero 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y))
  have hmatrix : M *ᵥ values f ≠ M *ᵥ values g ↔ values f ≠ values g :=
    not_congr hinj.eq_iff
  simp only [mem_fiberwiseDisagreementSet_iff]
  dsimp only [WordStack.getSymbol, preTensorCombine]
  change (∃ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) (k := steps) h_destIdx h_destIdx_le x = y ∧ f x ≠ g x) ↔
    M *ᵥ values f ≠ M *ᵥ values g
  rw [hmatrix]
  constructor
  · rintro ⟨x, hx, hne⟩ heq
    have hpoint := (eq_iteratedQuotientMap_iff_quotientFiber_apply_eq 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x y).mp hx.symm
    have h := congr_fun heq (pointToIterateQuotientIndex 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x)
    exact hne (by simpa only [values, fiberEvaluations, hpoint] using h)
  · intro hne
    by_contra hnone
    apply hne
    funext j
    by_contra hj
    apply hnone
    refine ⟨quotientFiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y j, ?_, hj⟩
    exact (eq_iteratedQuotientMap_of_mem_quotientFiber_range 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (x := quotientFiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y j)
      (y := y) ⟨j, rfl⟩).symm

end Lift_PreTensorCombine

omit [NeZero ℓ] [SampleableType L] [DecidableEq 𝔽q] in
/-- Tensor-combine preserves the number of fibers on which two words disagree. -/
lemma hammingDist_preTensorCombine_eq_card_fiberwiseDisagreementSet
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    hammingDist (fun y j => preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le f j y)
      (fun y j => preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le g j y) =
      (fiberwiseDisagreementSet 𝔽q β ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f g).card := by
  classical
  rw [Code.hammingDist_eq_disagreementCols_card]
  congr 1
  ext y
  simp only [Code.mem_disagreementCols]
  exact (mem_fiberwiseDisagreementSet_iff_getSymbol_preTensorCombine_ne 𝔽q β i steps h_destIdx
    h_destIdx_le f g y).symm

open Code.InterleavedCode in
omit [DecidableEq 𝔽q] in
omit [NeZero ℓ] in
omit [SampleableType L] in
/-- If `f_i` is fiberwise close to the source code, then its tensor-combine stack is within the
unique-decoding radius of the interleaved destination code. -/
lemma preTensorCombine_jointProximityNat_of_fiberwiseClose (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_close : FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let U := preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le f_i
    let C_next : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
      code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    jointProximityNat (C := C_next) (u := U) (e := Code.uniqueDecodingRadius (C := C_next)) := by
  classical
  intro U C_next
  let C_i := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  have h_close' := h_close
  unfold FiberwiseClose fiberwiseDistance at h_close'
  let dist_set := (fun (g : C_i) =>
    pairFiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le (f := f_i) (g := g)) '' Set.univ
  have h_dist_set_nonempty : dist_set.Nonempty :=
    ⟨_, ⟨0, Set.mem_univ _, rfl⟩⟩
  have h_inf_mem : sInf dist_set ∈ dist_set := Nat.sInf_mem h_dist_set_nonempty
  obtain ⟨g, _, h_g_dist⟩ := h_inf_mem
  have h_g_close_nat : pairFiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx
      h_destIdx_le f_i g ≤ Code.uniqueDecodingRadius (C := C_next) := by
    have h_pfd_eq_sinf : pairFiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩)
        steps h_destIdx h_destIdx_le f_i g = sInf dist_set := h_g_dist
    have h_2pfd_lt_d : 2 * pairFiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩)
        steps h_destIdx h_destIdx_le f_i g <
        (codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
      rw [h_pfd_eq_sinf]; exact_mod_cast h_close'
    have h_dist_eq_norm : (codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        destIdx : ℕ) = ‖(C_next : Set _)‖₀ := by
      simp only [C_next, codeDistance]
    have h_2pfd_lt_norm : 2 * pairFiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩)
        steps h_destIdx h_destIdx_le f_i g < ‖(C_next : Set _)‖₀ := by
      rw [← h_dist_eq_norm]; exact h_2pfd_lt_d
    have : NeZero ‖(C_next : Set _)‖₀ := ⟨by omega⟩
    exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR (C := C_next)).mpr h_2pfd_lt_norm
  let V := preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le g.val
  have h_V_codeword : (⋈|V) ∈ (C_next ^⋈ (Fin (2^steps))) :=
    preTensorCombine_mem_interleavedCode 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le
      ⟨g.val, g.property⟩
  have h_dist_eq : Δ₀(⋈|U, ⋈|V) =
      pairFiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i g := by
    exact hammingDist_preTensorCombine_eq_card_fiberwiseDisagreementSet
      𝔽q β i steps h_destIdx h_destIdx_le f_i g
  unfold jointProximityNat
  calc Δ₀(⋈|U, (C_next ^⋈ (Fin (2^steps))))
      ≤ Δ₀(⋈|U, ⋈|V) := Code.distFromCode_le_dist_to_mem _ _ h_V_codeword
    _ = ↑(pairFiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i g) := by
        exact_mod_cast h_dist_eq
    _ ≤ ↑(Code.uniqueDecodingRadius (C := C_next)) := by
        exact_mod_cast h_g_close_nat

open Code.InterleavedCode in
omit [DecidableEq 𝔽q] in
omit [NeZero ℓ] in
omit [SampleableType L] in
/-- If `f_i` is not fiberwise close to the source code (its fiberwise distance is at least half
the destination distance), then its tensor-combine stack is not within the unique-decoding
radius of the interleaved destination code.

For an arbitrary interleaved codeword `V`, its lift `g` (`liftInterleavedCodeword`) has `V` as
its stack. Since `f_i` and `g` differ on at least half the destination distance of fibers, and
the fold matrices are invertible
(`mem_fiberwiseDisagreementSet_iff_getSymbol_preTensorCombine_ne`), the stack of
`f_i` differs from `V` in at least that many columns. -/
lemma preTensorCombine_not_jointProximityNat_of_not_fiberwiseClose (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let U := preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le f_i
    let C_next : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
      code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    ¬(jointProximityNat (C := C_next) (u := U) (e := Code.uniqueDecodingRadius (C := C_next))) := by
  classical
  let m := 2^steps
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let C : Set (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ → L) :=
      (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let C_next := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let C_int := C_next ^⋈ (Fin m)
  let U_wordStack := preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le f_i
  let U_interleaved : InterleavedWord L (Fin m) S_next := ⋈|U_wordStack
  let d_next := codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := destIdx)
  let e_udr := Code.uniqueDecodingRadius (C := (C_next : Set (S_next → L)))
  have h_fiber_dist_ge : ∀ g : code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩,
      2 * (fiberwiseDisagreementSet 𝔽q β ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i g).card
        ≥ d_next := by
    intro g
    unfold FiberwiseClose at h_far
    rw [not_lt] at h_far
    let dist_set := (fun (g' : C) =>
      (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i
        g').card) '' Set.univ
    have h_min_le_g : fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le
        f_i ≤
        (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i
          g).card := by
      apply csInf_le
      · use 0
        rintro _ ⟨_, _, rfl⟩
        simp only [_root_.zero_le]
      · use g
        simp only [Set.mem_univ, true_and]
        rfl
    calc
      d_next ≤ 2 * fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le
          f_i := by
        norm_cast at h_far
      _ ≤ 2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le
            f_i g).card := by
        exact Nat.mul_le_mul_left 2 h_min_le_g
  simp only
  intro h_U_close
  obtain ⟨V_codeword, h_dist_U_V⟩ := jointProximityNat_iff_closeToInterleavedCodeword
    (u := U_wordStack) (e := e_udr) (C := C_next) |>.mp h_U_close
  let g := liftInterleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx
    h_destIdx_le V_codeword
  have h_g_is_lift_of_V : (⋈|preTensorCombine 𝔽q β i steps h_destIdx h_destIdx_le ↑g)
    = V_codeword.val := by
    apply preTensorCombine_liftInterleavedCodeword 𝔽q β
  have h_dist_eq : Δ₀(U_interleaved, V_codeword.val) ≥
      (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i
        g).card := by
    rw [← h_g_is_lift_of_V]
    exact (hammingDist_preTensorCombine_eq_card_fiberwiseDisagreementSet
      𝔽q β i steps h_destIdx h_destIdx_le f_i g).ge
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
        let : NeZero (‖(C_next : Set (S_next → L))‖₀) := by
          simpa only [C_next, codeDistance] using
            codeDistance_neZero 𝔽q β destIdx
        have res := Code.UDRClose_iff_two_mul_proximity_lt_d_UDR
          (C := (C_next : Set (S_next → L))) (e := e_udr).mp (by omega)
        exact res
  exact h_ineq_1 h_ineq_2

end

end Binius.BinaryBasefold
