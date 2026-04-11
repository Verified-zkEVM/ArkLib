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
   Proposition 4.21 case analyses
4. the interleaved-distance lower bound of Lemma 4.22

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering below follows the archived revision of [DP24].
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
This is a fundamental property used in both Proposition 4.21 and Lemma 4.22. -/
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

/-! **Interleaved Word Construction (Supporting definition for Lemma 4.22)**
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
      (ι := AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
        (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  sorry

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
    ∀ y : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx,
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) rowIdx y =
      (iterated_fold 𝔽q β ⟨i, by omega⟩ steps
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
          (r_challenges := bitsOfIndex (L := L) (n := steps) rowIdx)) y := by
  sorry

lemma preTensorCombine_is_interleavedCodeword_of_codeword (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    (⋈|(preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f.val)) ∈
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ^⋈ (Fin (2 ^ steps))) := by
  sorry

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
      ^⋈(Fin (2 ^ steps)))) : Fin (2 ^ steps) → L⦃<2^(ℓ-destIdx.val)⦄[X] := by
  sorry

def getLiftCoeffs (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) : Fin (2^(ℓ - i)) → L := by
  sorry

/-- Given an interleaved codeword `V ∈ C ⋈^ (2^steps)`, this method converts `2^steps` row polys
of `V` into a poly `P ∈ L[X]_(2^(ℓ-i))` that generates the fiber evaluator `g : S⁽ⁱ⁾ → L`
(this `g` produces the RHS vector in equality of **Lemma 4.9**). If we fold this function `g` using
**binary challenges** corresponding to each of the `2^steps` rows of `V`, let's say `j`,
we also folds `P` into the corresponding row polynomial `P_j` of the `j`-th row of `V`
(via **Lemma 4.14, aka iterated_fold_advances_evaluation_poly**). This works as a core engine for
proof of **Lemma 4.22**. -/
def getLiftPoly (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) : L⦃<2^(ℓ-i)⦄[X] := by
  sorry

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
  sorry

omit [CharP L 2] in
/-- **Lemma 4.22 Helper**: Folding the "Lifted" polynomial `g` with binary challenges corresponding
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
  sorry

omit [CharP L 2] in
open Code.InterleavedCode in
lemma preTensorCombine_of_lift_interleavedCodeword_eq_self (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) :
    let g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le V_codeword
    (⋈|(preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g)) = V_codeword.val := by
  sorry

/-- TODO: **Lifting Equivalence Lemma**: `lift(preTensorCombine(f)) = f`. -/

def fiberDiff (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) : Prop :=
  ∃ x, ∃ k : Fin (2 ^ steps),
    x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y) k ∧
    f x ≠ g x

/-- **Distance Isomorphism Lemma**
The crucial logic for Lemma 4.22:
Two functions `f, g` differ on a specific fiber `y` IF AND ONLY IF
their tensor-combinations `U, V` differ at the column `y`.
This holds because `M_y` is a bijection. -/
lemma fiberwise_disagreement_isomorphism (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
    fiberDiff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f g y ↔
    WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) y ≠
    WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) y := by
  sorry

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
    let C_next : Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    jointProximityNat (C := C_next) (u := U) (e := Code.uniqueDecodingRadius (C := C_next)) := by
  sorry

open Code.InterleavedCode in
/-- **Lemma 4.22** (Interleaved Distance Preservation):
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
    let C_next : Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    ¬(jointProximityNat (C := C_next) (u := U) (e := Code.uniqueDecodingRadius (C := C_next))) := by
  sorry

end

end Binius.BinaryBasefold
