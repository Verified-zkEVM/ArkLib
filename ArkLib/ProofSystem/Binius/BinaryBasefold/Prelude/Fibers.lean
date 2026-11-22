/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.Prelims
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
public import ArkLib.Data.CodingTheory.ReedSolomon
public import CompPoly.Fields.Binary.AdditiveNTT.AdditiveNTT
public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.Data.MvPolynomial.RestrictDegree
public import CompPoly.Data.Vector.Basic
public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
public import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound
public import ArkLib.ToMathlib.InformationTheory.Hamming
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Binary Basefold fibers

The fibers of the iterated quotient maps `S⁽ⁱ⁾ → S⁽ʲ⁾` of the additive-NTT domains, and the
block-matrix and tensor-expansion helpers that the folding identities use.

## Main definitions

* `OracleFunction`: a function on the domain `S⁽ⁱ⁾`.
* `quotientFiber`: the `2 ^ steps` points of `S⁽ⁱ⁾` above a point of `S⁽ⁱ⁺ˢᵗᵉᵖˢ⁾`, with its
  coordinate (`quotientFiber_repr_coeff`), injectivity,
  cardinality and disjointness lemmas.
* `fiberEvaluations`: the vector of values of a function on a fiber.
* `multilinearWeight`, `challengeTensorExpansionMatrix`: the tensor `⨂ⱼ (1 - rⱼ, rⱼ)` and
  its block-diagonal form.
* `from4Blocks`: finite-ordinal reindexing of `Matrix.fromBlocks`.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Numbering follows the archived revision of [DP24].
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec ProtocolSpec Polynomial MvPolynomial Binius.BinaryBasefold
open scoped NNReal Polynomial
open Finset AdditiveNTT Nat Matrix

section Preliminaries

section BlockHelpers

/-- Merge two maps on `Fin (2 ^ n)` into one map on `Fin (2 ^ (n + 1))`: `left` on the lower half
of the indices and `right` on the upper half. -/
def appendPowTwo {L : Type*} {n : ℕ} (left : Fin (2 ^ n) → L)
    (right : Fin (2 ^ n) → L) : Fin (2 ^ (n + 1)) → L := fun i =>
  if hi : i.val < 2 ^ n then left ⟨i, by omega⟩
  else right ⟨i - 2 ^ n, by omega⟩

/-- The block matrix `[A B; C D]` over `Fin`-indexed blocks, indexed by `Fin (mTop + mBot)` and
`Fin (nLeft + nRight)`. -/
def from4Blocks {mTop nLeft mBot nRight : ℕ} {α : Type*}
    (A : Matrix (Fin mTop) (Fin nLeft) α) (B : Matrix (Fin mTop) (Fin nRight) α)
    (C : Matrix (Fin mBot) (Fin nLeft) α) (D : Matrix (Fin mBot) (Fin nRight) α) :
    Matrix (Fin (mTop + mBot)) (Fin (nLeft + nRight)) α := fun i j =>
  if isTop : i.val < mTop then
    if isLeft : j.val < nLeft then A ⟨i, by omega⟩ ⟨j, by omega⟩
    else B ⟨i, by omega⟩ ⟨j - nLeft, by omega⟩
  else
    if isLeft : j.val < nLeft then C ⟨i - mTop, by omega⟩ ⟨j, by omega⟩
    else D ⟨i - mTop, by omega⟩ ⟨j - nLeft, by omega⟩

/-- `from4Blocks` is `Matrix.fromBlocks` reindexed to finite ordinal indices. -/
lemma from4Blocks_eq_fromBlocks {mTop mBot nLeft nRight : ℕ} {α : Type*}
    (A : Matrix (Fin mTop) (Fin nLeft) α) (B : Matrix (Fin mTop) (Fin nRight) α)
    (C : Matrix (Fin mBot) (Fin nLeft) α) (D : Matrix (Fin mBot) (Fin nRight) α) :
    from4Blocks A B C D =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [from4Blocks, Matrix.fromBlocks]

/-- Block multiplication for `from4Blocks`:
`[A B; C D] * [E F; G H] = [AE + BG, AF + BH; CE + DG, CF + DH]`. -/
lemma from4Blocks_mul_from4Blocks {mTop mBot pLeft pRight nLeft nRight : ℕ} {α : Type*}
    [NonUnitalNonAssocSemiring α]
    (A : Matrix (Fin mTop) (Fin pLeft) α) (B : Matrix (Fin mTop) (Fin pRight) α)
    (C : Matrix (Fin mBot) (Fin pLeft) α) (D : Matrix (Fin mBot) (Fin pRight) α)
    (E : Matrix (Fin pLeft) (Fin nLeft) α) (F : Matrix (Fin pLeft) (Fin nRight) α)
    (G : Matrix (Fin pRight) (Fin nLeft) α) (H : Matrix (Fin pRight) (Fin nRight) α) :
    from4Blocks A B C D * from4Blocks E F G H =
      from4Blocks (A * E + B * G) (A * F + B * H) (C * E + D * G) (C * F + D * H) := by
  simp only [from4Blocks_eq_fromBlocks, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

end BlockHelpers

variable {L : Type*}

/-- A single challenge expands to the two weights `1 - r` and `r`. -/
lemma multilinearWeight_one [CommRing L] (r : L) :
    multilinearWeight (ϑ := 1) (r := fun _ => r) = ![1 - r, r] := by
  unfold multilinearWeight
  simp only [reducePow, univ_unique, Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero,
    testBit_zero, decide_eq_true_eq, prod_ite_irrel, prod_const, card_singleton, pow_one,
    succ_eq_add_one, reduceAdd]
  funext i
  by_cases hi_eq_0 : i = 0
  · simp only [hi_eq_0, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_ne_one, ↓reduceIte,
    cons_val_zero]
  · have hi_eq_1 : i = 1 := by omega
    simp only [hi_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, ↓reduceIte, cons_val_one,
      cons_val_fin_one]

/-- **Challenge Tensor Expansion Matrix**
Constructs the block-diagonal matrix containing the challenge tensor expansion of
size `n`: `MatrixCTensor(n, r) = [ CTensor(n, r)   0    ]`
                                `[   0     CTensor(n, r) ]` ,
which is used for decomposing `CTensor(n+1, r)` into a vector-matrix multiplication form. -/
def challengeTensorExpansionMatrix [CommRing L] (n : ℕ) (r : Fin n → L) :
    Matrix (Fin 2) (Fin (2 ^ (n + 1))) L :=
  let C_n_finmap := multilinearWeight (ϑ := n) r
  let C_n : Matrix (Fin (1)) (Fin (2 ^ n)) L := Matrix.of (fun _rowIdx colIdx => C_n_finmap colIdx)
  -- Create the block diagonal matrix using 1-row matrices
  let emptyBlock : Matrix (Fin 1) (Fin (2 ^ n)) L := 0
  let block := from4Blocks (C_n)      emptyBlock
                                 emptyBlock (C_n)
  Matrix.reindex (eₘ := finCongr (by omega)) (eₙ := finCongr (by omega)) block

/-- Challenge Tensor Expansion Matrix multiplication on top half returns M_top * v_top
-/
lemma appendPowTwo_mulVec_eq_challengeTensorExpansionMatrix_mulVec [CommRing L] (n : ℕ)
    (r : Fin n → L) (v_top : Fin (2 ^ n) → L) (v_bot : Fin (2 ^ n) → L) :
    let C_n_finmap := multilinearWeight (ϑ := n) (r := r)
    let C_n : Matrix (Fin (1)) (Fin (2 ^ n)) L :=
      Matrix.of (fun _rowIdx colIdx => C_n_finmap colIdx)
    (appendPowTwo (L := L) (n := 0) ((C_n *ᵥ v_top) : (Fin 1) → L)
      ((C_n *ᵥ v_bot) : (Fin 1) → L) : (Fin 2) → L)
    = (challengeTensorExpansionMatrix (n := n) (r := r)) *ᵥ
      appendPowTwo (n := n) v_top v_bot := by
  dsimp only [challengeTensorExpansionMatrix]
  conv_rhs =>
    -- Move reindexing from Matrix to Vector
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  funext k
  unfold appendPowTwo
  unfold from4Blocks Matrix.mulVec dotProduct
  -- Now unfold everything
  simp only [Matrix.zero_apply, finCongr_symm, Function.comp_apply, finCongr_apply,
    dite_mul, zero_mul,
    sum_dite_irrel, Fin.val_cast]
  simp_rw [Fin.sum_univ_add]
  simp_rw [←Finset.sum_add_distrib]
  simp only [reduceAdd, reducePow, pow_zero, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue,
    Nat.pow_zero, of_apply, dite_eq_ite, Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta,
    Fin.natAdd_eq_addNat, Fin.val_addNat, add_lt_iff_neg_right, _root_.not_lt_zero, add_zero,
    add_tsub_cancel_right, zero_add]

/-- **Challenge Tensor Expansion Decomposition Lemma (Vector-Matrix multiplication form)**
Prove that `CTensor(n+1, r_0, ..., r_n) = [1-r_n, r_n] * MatrixCTensor(n, r_0, ..., r_{n-1})` -/
lemma multilinearWeight_succ_eq_vecMul [CommRing L] (n : ℕ) (r : Fin (n + 1) → L) :
    multilinearWeight (ϑ := n + 1) (r := r) = ![1 - r (Fin.last n), r (Fin.last n)]
      ᵥ* (challengeTensorExpansionMatrix n (r := Fin.init r)) := by
  funext colIdx
  unfold challengeTensorExpansionMatrix
  simp only [succ_eq_add_one, reduceAdd, reindex_apply]
  simp only [vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply, submatrix_apply, smul_eq_mul,
    Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, cons_val_fin_one]
  dsimp only [finCongr_symm, finCongr_apply, Fin.cast_eq_self, Fin.isValue]
  unfold from4Blocks
  by_cases h_colIdx_lt_2_pow_n : colIdx.val < 2 ^ n
  · simp only [reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_lt_one, ↓reduceDIte,
    finCongr_apply_coe, h_colIdx_lt_2_pow_n, Fin.zero_eta, of_apply, mod_succ, lt_self_iff_false,
    Matrix.zero_apply, mul_zero, add_zero]
    rw [multilinearWeight_succ_lower_half (r := r) (i := colIdx)
      (h_lt := h_colIdx_lt_2_pow_n), mul_comm]
  · have h_ne_lt_2_pow_n : ¬(colIdx.val < 2 ^ n) := by exact h_colIdx_lt_2_pow_n
    simp only [reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_lt_one, ↓reduceDIte,
      finCongr_apply_coe, h_ne_lt_2_pow_n, Matrix.zero_apply, mul_zero, mod_succ,
      lt_self_iff_false, tsub_self,
      Fin.zero_eta, of_apply, zero_add]
    let u : Fin (2 ^ n) := ⟨colIdx.val - (2 ^ n), by omega⟩
    have h_eq: colIdx.val = u.val + (2 ^ n) := by dsimp only [u]; omega
    rw [multilinearWeight_succ_upper_half (r := r) (i := colIdx) (j := u)
      (h_eq := h_eq), mul_comm]

variable {L : Type} [CommRing L]

-- The multilinear polynomial types, `fixFirstVariablesOfMQP` and the round polynomial
-- `getSumcheckRoundPoly` are the structured sum-check's (`ArkLib.Data.MvPolynomial.RestrictDegree`,
-- `ArkLib.ProofSystem.Sumcheck.Structured`). They are re-exported under `Binius.BinaryBasefold`.
export MvPolynomial (fixFirstVariablesOfMQP fixFirstVariablesOfMQP_degreeLE)
export Sumcheck.Structured (MultilinearPoly MultiquadraticPoly getSumcheckRoundPoly)

/-- Helper to convert an index `k` into a vector of bits (as field elements). -/
def bitsOfIndex {n : ℕ} (k : Fin (2 ^ n)) : Fin n → L :=
  fun i => if Nat.testBit k i then 1 else 0

/-- The double coercion `Fin (2^n) → (Fin n → Fin 2) → (Fin n → L)` equals `bitsOfIndex`.
This connects the implicit coercion used in `polynomialFromNovelCoeffsF₂` with the explicit
bit extraction, which is essential for proving multilinear polynomial evaluation formulas. -/
lemma coe_fin_pow_two_eq_bitsOfIndex {n : ℕ} (k : Fin (2 ^ n)) :
    ((finFunctionFinEquiv.invFun k : Fin n → Fin 2) : Fin n → L) = bitsOfIndex k := by
  ext i
  simp only [bitsOfIndex]
  simp only [Equiv.invFun_as_coe, finFunctionFinEquiv_symm_apply_val]
  conv_lhs =>
    rw [←Nat.shiftRight_eq_div_pow, ←Nat.and_one_is_mod]
    change Nat.getBit (k := i) (n := k)
  rw [Nat.getBit_eq_testBit]
  split
  · simp only [cast_one]
  · simp only [cast_zero]

/-- The Boolean equality polynomial at a bit-index point evaluates to its multilinear weight. -/
lemma eval_eqPolynomial_bitsOfIndex {ℓ : ℕ}
    (challenges : Fin ℓ → L) (k : Fin (2 ^ ℓ)) :
    MvPolynomial.eval challenges (MvPolynomial.eqPolynomial (bitsOfIndex (L := L) k)) =
      multilinearWeight (r := challenges) (i := k) := by
  unfold MvPolynomial.eqPolynomial multilinearWeight bitsOfIndex
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hbit : k.val.testBit j.val
  · simp [hbit]
  · simp [hbit]

/-- A multilinear evaluation is the equality-weighted sum of its Boolean vertex evaluations. -/
theorem multilinear_eval_eq_sum_bool_hypercube {ℓ : ℕ}
    (challenges : Fin ℓ → L) (t : ↥L⦃≤ 1⦄[X Fin ℓ]) :
    t.val.eval challenges = ∑ (x : Fin (2^ℓ)),
      (multilinearWeight (r := challenges) (i := x)) * (t.val.eval (bitsOfIndex x) : L) := by
  have h_multilinear : MvPolynomial.MLE
      (fun x : Fin ℓ → Fin 2 => MvPolynomial.eval (x : Fin ℓ → L) t.val) = t.val := by
    exact (MvPolynomial.eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq _ t.val
      ((MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mp t.property)
      (fun _ => rfl)).symm
  calc
    t.val.eval challenges = MvPolynomial.eval challenges
        (MvPolynomial.MLE (fun x : Fin ℓ → Fin 2 => MvPolynomial.eval (x : Fin ℓ → L) t.val)) := by
      exact congrArg (MvPolynomial.eval challenges) h_multilinear.symm
    _ = ∑ x : Fin ℓ → Fin 2,
          MvPolynomial.eval challenges (MvPolynomial.eqPolynomial (x : Fin ℓ → L)) *
            MvPolynomial.eval (x : Fin ℓ → L) t.val := by
      exact MvPolynomial.MLE_eval challenges _
    _ = ∑ x : Fin (2 ^ ℓ),
          multilinearWeight (r := challenges) (i := x) *
            MvPolynomial.eval (bitsOfIndex x) t.val := by
      apply Fintype.sum_equiv finFunctionFinEquiv
      intro x
      have hx_bits : (x : Fin ℓ → L) = bitsOfIndex (L := L) (finFunctionFinEquiv x) := by
        rw [← coe_fin_pow_two_eq_bitsOfIndex (L := L) (k := finFunctionFinEquiv x)]
        simp
      calc
        MvPolynomial.eval challenges (MvPolynomial.eqPolynomial (x : Fin ℓ → L)) *
            MvPolynomial.eval (x : Fin ℓ → L) t.val
          = MvPolynomial.eval challenges
              (MvPolynomial.eqPolynomial (bitsOfIndex (L := L) (finFunctionFinEquiv x))) *
              MvPolynomial.eval (bitsOfIndex (L := L) (finFunctionFinEquiv x)) t.val := by
              rw [hx_bits]
        _ = multilinearWeight (r := challenges) (i := finFunctionFinEquiv x) *
              MvPolynomial.eval (bitsOfIndex (L := L) (finFunctionFinEquiv x)) t.val := by
              rw [eval_eqPolynomial_bitsOfIndex (L := L) (ℓ := ℓ)]

end Preliminaries

noncomputable section       -- expands with 𝔽q in front
/-- At the binary point `bitsOfIndex k`, the multilinear weight of index `j` is the indicator of
`j = k`. -/
lemma multilinearWeight_bitsOfIndex {L : Type} [CommRing L] {n : ℕ} (j k : Fin (2 ^ n)) :
    multilinearWeight (F := L) (r := bitsOfIndex k) (i := j) = if j = k then 1 else 0 := by
  set r_k := bitsOfIndex (L := L) k with h_r_k
  unfold multilinearWeight
  dsimp only [bitsOfIndex, r_k]
  simp_rw [Nat.testBit_eq_getBit]
  by_cases h_eq : j = k
  · simp only [h_eq, ↓reduceIte]
    have h_eq: ∀ (x : Fin n),
      ((if (x.val).getBit ↑k = 1 then if (x.val).getBit ↑k = 1 then (1 : L) else (0 : L) else 1 -
        if (x.val).getBit ↑k = 1 then (1 : L) else (0 : L))) = (1 : L) := by
        intro x
        by_cases h_eq : (x.val).getBit ↑k = 1
        · simp only [h_eq, ↓reduceIte]
        · simp only [h_eq, ↓reduceIte, sub_zero]
    simp_rw [h_eq]
    simp only [prod_const_one]
  · simp only [h_eq, ↓reduceIte]
    let exists_bit_diff_idx := Nat.exist_bit_diff_if_diff (a := j) (b := k) (h_a_ne_b := h_eq)
    rcases exists_bit_diff_idx with ⟨bit_diff_idx, h_bit_diff_idx⟩
    have h_getBit_of_j_lt_2 : Nat.getBit (k := bit_diff_idx.val) (n := j) < 2 := by
      exact Nat.getBit_lt_2 (k := bit_diff_idx.val) (n := j)
    have h_getBit_of_k_lt_2 : Nat.getBit (k := bit_diff_idx.val) (n := k) < 2 := by
      exact Nat.getBit_lt_2 (k := bit_diff_idx.val) (n := k)
    apply Finset.prod_eq_zero (Finset.mem_univ bit_diff_idx)
    by_cases h_bit_diff_of_j_eq_0 : Nat.getBit (k := bit_diff_idx.val) (n := j) = 0
    · simp only [h_bit_diff_of_j_eq_0, zero_ne_one, ↓reduceIte]
      have h_bit_diff_of_k_eq_1 : Nat.getBit (k := bit_diff_idx.val) (n := k) = 1 := by
        omega
      simp only [h_bit_diff_of_k_eq_1, ↓reduceIte, sub_self]
    · have h_bit_diff_of_j_eq_1 :
        Nat.getBit (k := bit_diff_idx.val) (n := j) = 1 := by
        omega
      have h_bit_diff_of_k_eq_0 : Nat.getBit (k := bit_diff_idx.val) (n := k) = 0 := by
        omega
      simp only [h_bit_diff_of_j_eq_1, ↓reduceIte, h_bit_diff_of_k_eq_0, zero_ne_one]

/-- At the binary point `bitsOfIndex k`, the tensor expansion `multilinearWeight (ϑ := n) r` is the
indicator vector of `k`. -/
lemma multilinearWeight_bitsOfIndex_fun {L : Type} [CommRing L] {n : ℕ} (k : Fin (2 ^ n)) :
    -- Key Property: Tensor(r_k) is the indicator vector for k.
    -- Tensor(r_k)[j] = 1 if j=k, 0 if j≠k.
    multilinearWeight (ϑ := n) (r := bitsOfIndex (L := L) k) = fun j => if j = k then 1 else 0 := by
  -- Let r_k be the bit-vector corresponding to index k
  funext j
  apply multilinearWeight_bitsOfIndex


variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
local instance instFactPrimeRingCharPreludeFibers [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}

section Essentials
-- In this section, we ue notation `ϑ` for the folding steps, along with `(hdiv : ϑ ∣ ℓ)`

/-- Oracle function type for round i.
f^(i) : S⁽ⁱ⁾ → L, where |S⁽ⁱ⁾| = 2^{ℓ + R - i} -/
abbrev OracleFunction (domainIdx : Fin r) := sDomain 𝔽q β h_ℓ_add_R_rate domainIdx → L

/-- Helper: Bound proof for the indices -/
lemma mul_pow_two_add_lt_pow_two_sub {ℓ i steps : ℕ} (j m : ℕ)
    (hj : j < 2 ^ (ℓ - (i + steps))) (hm : m < 2 ^ steps) (h_le : i + steps ≤ ℓ) :
    j * 2 ^ steps + m < 2 ^ (ℓ - i) := by
  -- Arithmetic proof: j * 2^s + m < (j+1) * 2^s <= 2^(L-i-s) * 2^s = 2^(L-i)
  calc
    j * 2 ^ steps + m
    _ < j * 2 ^ steps + 2 ^ steps := by apply Nat.add_lt_add_left hm
    _ = (j + 1) * 2 ^ steps := by ring
    _ ≤ (2 ^ (ℓ - (i + steps))) * 2 ^ steps := by
      apply Nat.mul_le_mul_right
      exact hj
    _ = 2 ^ (ℓ - i - steps + steps) := by
      rw [←Nat.pow_add]; simp only [ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
        pow_right_inj₀, Nat.add_right_cancel_iff]; omega
    _ = 2 ^ (ℓ - i) := by
      congr 1
      rw [Nat.sub_add_cancel]
      -- Proof that steps ≤ ℓ - i
      apply Nat.le_sub_of_add_le
      omega

omit [NeZero r]  in
/-- A round at or before `ℓ` lies strictly below `ℓ + 𝓡`. -/
lemma lt_rounds_add_rate_of_le_rounds {x : ℕ} (h_x : x ≤ ℓ) :
    x < ℓ + 𝓡 := by
  apply Nat.lt_add_of_pos_right_of_le; omega
section FiberMath
/-!
### The Fiber of the Quotient Map `qMap`

Utilities for constructing fibers and defining the fold operations used by Binary Basefold.
-/

def finTwoCast (𝔽q : Type*) [Ring 𝔽q] (k : Fin 2) : 𝔽q :=
  if k = 0 then 0 else 1

/-- Helper for the fiber coefficients used in `quotientFiber`.
It computes the coefficient of the `j`-th basis vector for a point (indexed by `elementIdx`)
in the fiber list of `y ∈ S^{i+steps}`.
- If `j < steps`, the coefficient comes from the binary expansion of `elementIdx`.
- If `j ≥ steps`, the coefficient comes from `y_coeffs` (coefficients of the target point `y`). -/
noncomputable def fiberCoeff
    (i : Fin r) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps)
    -- Input j is just an index in the source dimension
    (basisIdx : Fin (ℓ + 𝓡 - i))
    (elementIdx : Fin (2 ^ steps))
    -- y_coeffs now uses the clean 'destIdx'
    (y_coeffs : Fin (ℓ + 𝓡 - destIdx) →₀ 𝔽q) : 𝔽q :=
  if hj : basisIdx.val < steps then
    if Nat.getBit (k := basisIdx) (n := elementIdx) = 0 then 0 else 1
  else
    -- We need to access y_coeffs at (basisIdx - steps).
    -- We must prove (j - steps) < (ℓ + 𝓡 - destIdx).
    y_coeffs ⟨basisIdx.val - steps, by
      -- Clean proof using the equality h_dest
      rw [h_destIdx]
      rw [←Nat.sub_sub]
      apply Nat.sub_lt_sub_right
      · exact Nat.le_of_not_lt hj
      · exact basisIdx.isLt⟩

/-- Get the full fiber list `(x₀, ..., x_{2 ^ steps-1})` which represents the
joined fiber `(q⁽ⁱ⁺steps⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾)⁻¹({y}) ⊂ S⁽ⁱ⁾` over `y ∈ S^(i+steps)`,
in which the LSB represents the FIRST qMap `q⁽ⁱ⁾`, and the MSB represents the LAST `q⁽ⁱ⁺steps⁻¹⁾`
-/
noncomputable def quotientFiber
    -- S^i is source domain, S^{i + steps} is the target domain
    (i : Fin r) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps)
    (h_destIdx_le: destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    Fin (2 ^ steps) → sDomain 𝔽q β h_ℓ_add_R_rate i :=
  if h_steps : steps = 0 then by
    -- Base case : 0 steps, the fiber is just the point y itself.
    subst h_steps
    have h_i_eq_j : i = destIdx := by omega
    subst h_i_eq_j
    exact fun _ => y
  else by
    -- fun (k : 𝔽q) =>
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := destIdx)
      (h_i := lt_rounds_add_rate_of_le_rounds (by omega))
    let y_coeffs : Fin (ℓ + 𝓡 - destIdx) →₀ 𝔽q := basis_y.repr y
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (h_i := by omega)
    exact fun elementIdx => by
      let x_coeffs : Fin (ℓ + 𝓡 - i) → 𝔽q := fun j =>
        if hj_lt_steps : j.val < steps then
          if Nat.getBit (k := j) (n := elementIdx) = 0 then (0 : 𝔽q)
          else (1 : 𝔽q)
        else
          y_coeffs ⟨j.val - steps, by omega⟩  -- Shift indices to match y's basis
      exact basis_x.repr.symm ((Finsupp.equivFunOnFinite).symm x_coeffs)

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1  in
/-- Changing an equal fold count transports the fiber parametrization. -/
lemma quotientFiber_congr_steps
    {i : Fin r} (steps steps' : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (h_steps_eq : steps = steps')
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    quotientFiber 𝔽q β (i := i) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (y := y) =
    fun (x : Fin (2 ^ steps)) ↦
      quotientFiber 𝔽q β (i := i) (steps := steps') (h_destIdx := by omega)
        (h_destIdx_le := h_destIdx_le) (y := y)
        ⟨x.val, by subst h_steps_eq; exact x.is_lt⟩ := by
  subst h_steps_eq; rfl

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1  in
/-- Changing an equal source index transports each point in the fiber. -/
lemma quotientFiber_congr_source_apply
    {sourceIdx₁ sourceIdx₂ : Fin r} (steps : ℕ) {destIdx : Fin r}
    (h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂)
    (h_destIdx : destIdx = sourceIdx₁.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) (x : Fin (2 ^ steps)) :
    quotientFiber 𝔽q β (i := sourceIdx₁) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (y := y) x =
    cast (by subst h_sourceIdx_eq; rfl) (quotientFiber 𝔽q β (i := sourceIdx₂)
      (steps := steps) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (y := y) x) := by
  subst h_sourceIdx_eq; rfl

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1  in
/-- **qMap_fiber coefficient extraction**.
The coefficients of `x = quotientFiber(y, k)` with respect to `basis_x` are exactly
the function that puts binary coeffs corresponding to bits of `k` in
the first `steps` positions, and shifts `y`'s coefficients.
The first coordinates encode the fiber index and the remaining coordinates encode `y`.
-/
lemma quotientFiber_repr_coeff (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps)
  (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    (k : Fin (2 ^ steps)) :
    let x := quotientFiber 𝔽q β (i := i) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (y := y) k
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := destIdx)
      (h_i := lt_rounds_add_rate_of_le_rounds (by omega))
    let y_coeffs := basis_y.repr y
    ∀ j, -- j refers to bit index of the fiber point x
      ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := lt_rounds_add_rate_of_le_rounds (by
        omega))).repr x) j
      = fiberCoeff (i := i) (steps := steps) (destIdx := destIdx) (h_destIdx := h_destIdx)
        (basisIdx := j) (elementIdx := k) (y_coeffs := y_coeffs) := by
  unfold fiberCoeff
  simp only
  intro j
  by_cases h_steps_eq_0 : steps = 0
  · subst h_steps_eq_0
    have h_i_eq_destIdx : i = destIdx := by omega
    subst h_i_eq_destIdx
    rfl
  · simp only [quotientFiber, h_steps_eq_0, ↓reduceDIte, Module.Basis.repr_symm_apply,
    Module.Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_apply]

/-- The fiber bit-index records which of the first `steps` basis coefficients are nonzero. -/
def pointToIterateQuotientIndex (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := i)) : Fin (2 ^ steps) := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i)
    (h_i := lt_rounds_add_rate_of_le_rounds (by omega))
  let x_coeffs := basis_x.repr x
  let k_bits : Fin steps → Nat := fun j =>
    if x_coeffs ⟨j, by omega⟩ = 0 then 0 else 1
  let k := Nat.binaryFinMapToNat (n := steps) (m := k_bits) (h_binary := by
    intro j; simp only [k_bits]; split_ifs
    · norm_num
    · norm_num
  )
  exact k

omit  [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
/-- When ϑ = 1, quotientFiber maps k = 0 to an element with first coefficient 0
and k = 1 to an element with first coefficient 1. -/
lemma quotientFiber_one_level_eq (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) (k : Fin 2) :
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (h_i := by omega)
    let x : sDomain 𝔽q β h_ℓ_add_R_rate i := quotientFiber 𝔽q β (i := i)
      (steps := 1) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y) k
    let y_lifted : sDomain 𝔽q β h_ℓ_add_R_rate i := sDomain.lift 𝔽q β h_ℓ_add_R_rate
      (i := i) (j := destIdx)
      (h_j := by apply Nat.lt_add_of_pos_right_of_le; omega) (h_le := by omega) y
    let free_coeff_term : sDomain 𝔽q β h_ℓ_add_R_rate i :=
      (finTwoCast 𝔽q k) • (basis_x ⟨0, by omega⟩)
    x = free_coeff_term + y_lifted := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (h_i := by omega)
  apply basis_x.repr.injective
  simp only [map_add, map_smul]
  simp only [Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, basis_x]
  ext j
  have h_repr_x := quotientFiber_repr_coeff 𝔽q β i (steps := 1) (by omega)
    (y := y) (k := k) (j := j)
  simp only [h_repr_x, Finsupp.coe_add, Pi.add_apply]
  simp only [fiberCoeff, lt_one_iff, reducePow, finTwoCast, Fin.isValue]
  have h_i_lt_destIdx : i < destIdx := by omega
  by_cases hj : j = ⟨0, by omega⟩
  · simp only [hj, ↓reduceDIte, Fin.isValue, Finsupp.single_eq_same]
    by_cases hk : k = 0
    · simp only [getBit, hk, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, shiftRight_zero,
      and_one_is_mod, ↓reduceIte, zero_add]
      -- => Now use basis_repr_of_sDomain_lift
      rw [basis_repr_of_sDomain_lift]
      simp only [tsub_pos_iff_lt, Fin.val_fin_lt, h_i_lt_destIdx, ↓reduceDIte]
    · have h_k_eq_1 : k = 1 := by omega
      simp only [getBit, h_k_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, shiftRight_zero,
        Nat.and_self, one_ne_zero, ↓reduceIte, left_eq_add]
      have h : 0 < destIdx.val - i.val := by omega
      simp only [basis_repr_of_sDomain_lift, h, ↓reduceDIte]
  · have hj_ne_zero : j ≠ ⟨0, by omega⟩ := by omega
    have hj_val_ne_zero : j.val ≠ 0 := by
      change j.val ≠ ((⟨0, by omega⟩ :  Fin (ℓ + 𝓡 - ↑i)).val)
      apply Fin.val_ne_of_ne
      exact hj_ne_zero
    simp only [hj_val_ne_zero, ↓reduceDIte, Finsupp.single, Fin.isValue, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not, Pi.single, Finsupp.coe_mk, Function.update,
      hj_ne_zero, Pi.zero_apply, zero_add]
    have h_not_lt : ¬(j.val < destIdx.val - i.val) := by omega
    simp only [basis_repr_of_sDomain_lift, h_not_lt, ↓reduceDIte]
    congr 1
    simp only [Fin.mk.injEq]; rw [h_destIdx]; norm_num

omit [DecidableEq 𝔽q] hF₂  in
/-- `x` is in the fiber of `y` under `quotientFiber` iff `y` is the iterated
quotient of `x`. That is, for binary field, the fiber of `y` is exactly the set of
all `x` that map to `y` under the iterated quotient map. -/
theorem eq_iteratedQuotientMap_of_mem_quotientFiber_range
    (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := i))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx))
    (hx_is_fiber : ∃ (k : Fin (2 ^ steps)), x = quotientFiber 𝔽q β (i := i)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y) k) :
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps)
      (h_destIdx) (h_destIdx_le)  (x := x) := by
 -- Get the fiber index `k` and the equality from the hypothesis.
  rcases hx_is_fiber with ⟨k, hx_eq⟩
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := destIdx) (h_i := lt_rounds_add_rate_of_le_rounds (by omega))
  apply basis_y.repr.injective
  ext j
  conv_rhs =>
    rw [getSDomainBasisCoeff_of_iteratedQuotientMap]
  have h_repr_x := quotientFiber_repr_coeff 𝔽q β i (steps := steps)
    h_destIdx h_destIdx_le (y := y) (k := k) (j := ⟨j + steps, by omega⟩)
  rw [←hx_eq] at h_repr_x
  simp only [fiberCoeff, add_lt_iff_neg_right, _root_.not_lt_zero, ↓reduceDIte,
    add_tsub_cancel_right, Fin.eta] at h_repr_x
  exact h_repr_x.symm

/-- State the correspondence between the forward qMap and the backward quotientFiber -/
theorem eq_iteratedQuotientMap_iff_quotientFiber_apply_eq (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := i))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    let qMapFiber := quotientFiber 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le (y := y)
    let k := pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (x := x)
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps) h_destIdx h_destIdx_le x ↔
    qMapFiber k = x := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i
    (h_i := lt_rounds_add_rate_of_le_rounds (by omega))
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate destIdx
    (h_i := lt_rounds_add_rate_of_le_rounds (by omega))
  simp only
  set k := pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_destIdx h_destIdx_le (x := x)
  constructor
  · intro h_x_generates_y
    apply basis_x.repr.injective
    ext j
    let reConstructedX := basis_x.repr (quotientFiber 𝔽q β (i := i)
      (steps := steps) h_destIdx h_destIdx_le (y := y) k)
    have h_repr_of_reConstructedX := quotientFiber_repr_coeff 𝔽q β i (steps := steps)
      h_destIdx h_destIdx_le (y := y) (k := k) (j := j)
    rw [h_repr_of_reConstructedX]; dsimp [k, pointToIterateQuotientIndex, fiberCoeff];
    rw [getBit_of_binaryFinMapToNat]; simp only [Fin.eta, dite_eq_right_iff, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not]
    -- Now we only need to do case analysis
    by_cases h_j : j.val < steps
    · -- Case 1 : The first `steps` coefficients, determined by `k`.
      simp only [h_j, ↓reduceDIte, forall_const]
      by_cases h_coeff_j_of_x : basis_x.repr x j = 0
      · simp only [basis_x, h_coeff_j_of_x, ↓reduceIte];
      · simp only [basis_x, h_coeff_j_of_x, ↓reduceIte];
        have h_coeff := 𝔽q_element_eq_zero_or_eq_one 𝔽q (c := basis_x.repr x j)
        simp only [h_coeff_j_of_x, false_or] at h_coeff
        exact id (Eq.symm h_coeff)
    · -- Case 2 : The remaining coefficients, determined by `y`.
      simp only [h_j, ↓reduceDIte]
      simp only [basis_x]
      simp only [h_x_generates_y]
      have h_res := getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps)
        h_destIdx h_destIdx_le x (j := ⟨j - steps, by omega⟩) -- ⊢ ↑j - steps < ℓ + 𝓡 - (↑i + steps)
      have h_j_sub_add_steps : j - steps + steps = j := by omega
      simp only at h_res
      simp only [h_j_sub_add_steps, Fin.eta] at h_res
      exact h_res
  · intro h_x_is_fiber_of_y
    -- y is the quotient point of x over steps steps
    exact eq_iteratedQuotientMap_of_mem_quotientFiber_range 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (x := x) (y := y)
      (hx_is_fiber := by use k; exact h_x_is_fiber_of_y.symm)

omit hF₂ h_β₀_eq_1  in
/-- the pointToIterateQuotientIndex of quotientFiber -/
lemma pointToIterateQuotientIndex_quotientFiber_eq_self (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (i := destIdx)) (k : Fin (2 ^ steps)) :
    pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) h_destIdx h_destIdx_le (x := (quotientFiber 𝔽q β (i := i)
        (steps := steps) h_destIdx h_destIdx_le (y := y) k)) = k := by
  apply Fin.eq_mk_iff_val_eq.mpr
  apply eq_iff_eq_all_getBits.mpr
  intro j -- bit index j
  simp only [pointToIterateQuotientIndex, quotientFiber]
  rw [Nat.getBit_of_binaryFinMapToNat]
  simp only [Nat.add_zero, Nat.pow_zero, Module.Basis.repr_symm_apply]
  by_cases h_j : j < steps
  · simp only [h_j, ↓reduceDIte];
    by_cases hsteps : steps = 0
    · simp only [hsteps, ↓reduceDIte]; omega
    · simp only [hsteps, ↓reduceDIte, Module.Basis.repr_linearCombination,
      Finsupp.equivFunOnFinite_symm_apply_apply, h_j, ite_eq_left_iff, one_ne_zero,
      imp_false, Decidable.not_not]
      have h := Nat.getBit_eq_zero_or_one (k := j) (n := k)
      by_cases h_j_getBit_k_eq_0 : j.getBit ↑k = 0
      · simp only [h_j_getBit_k_eq_0, ↓reduceIte]
      · simp only [h_j_getBit_k_eq_0, false_or, ↓reduceIte] at h ⊢
        exact id (Eq.symm h)
  · rw [Nat.getBit_of_lt_two_pow];
    simp only [h_j, ↓reduceDIte, ↓reduceIte];

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1  in
/-- Distinct binary coordinate vectors give distinct points of a quotient fiber. -/
theorem quotientFiber_injective (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    Function.Injective (quotientFiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y)) := by
  intro k₁ k₂ h_eq
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (lt_rounds_add_rate_of_le_rounds (by omega))
  set fiberMap := quotientFiber 𝔽q β (i := i) (steps := steps)
    h_destIdx h_destIdx_le (y := y)
  have h_coeffs_eq : basis_x.repr (fiberMap k₁) = basis_x.repr (fiberMap k₂) := by
    rw [h_eq]
  have h_bits_eq : ∀ j : Fin steps,
      Nat.getBit (k := j) (n := k₁.val) = Nat.getBit (k := j) (n := k₂.val) := by
    intro j
    have h_coeff_j_eq : basis_x.repr (fiberMap k₁) ⟨j, by omega⟩
      = basis_x.repr (fiberMap k₂) ⟨j, by omega⟩ := by rw [h_coeffs_eq]
    rw [quotientFiber_repr_coeff 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y) (j := ⟨j, by omega⟩)]
      at h_coeff_j_eq
    rw [quotientFiber_repr_coeff 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le (y := y) (k := k₂) (j := ⟨j, by omega⟩)]
      at h_coeff_j_eq
    simp only [fiberCoeff, Fin.is_lt, ↓reduceDIte] at h_coeff_j_eq
    by_cases hbitj_k₁ : Nat.getBit (k := j) (n := k₁.val) = 0
    · simp only [hbitj_k₁, ↓reduceIte, left_eq_ite_iff, zero_ne_one, imp_false,
      Decidable.not_not] at ⊢ h_coeff_j_eq
      simp only [h_coeff_j_eq]
    · simp only [hbitj_k₁, ↓reduceIte, right_eq_ite_iff, one_ne_zero,
      imp_false] at ⊢ h_coeff_j_eq
      have b1 : Nat.getBit (k := j) (n := k₁.val) = 1 := by
        have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₁.val)
        simp only [hbitj_k₁, false_or] at h
        exact h
      have b2 : Nat.getBit (k := j) (n := k₂.val) = 1 := by
        have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₂.val)
        simp only [h_coeff_j_eq, false_or] at h
        exact h
      simp only [b1, b2]
  apply Fin.eq_of_val_eq
  apply eq_iff_eq_all_getBits.mpr
  intro k
  by_cases h_k : k < steps
  · simp only [h_bits_eq ⟨k, by omega⟩]
  · conv_lhs => rw [Nat.getBit_of_lt_two_pow]
    conv_rhs => rw [Nat.getBit_of_lt_two_pow]
    simp only [h_k, ↓reduceIte]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1  in
/-- The binary fiber parametrization has image cardinality `2 ^ steps`. -/
theorem card_quotientFiber (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := destIdx)) :
    Fintype.card (Set.image (quotientFiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le
      (y := y)) Set.univ) = 2 ^ steps := by
  rw [Set.card_image_of_injective Set.univ]
  · simp only [Fintype.card_setUniv, Fintype.card_fin]
  · exact quotientFiber_injective 𝔽q β i steps h_destIdx h_destIdx_le y

omit [DecidableEq 𝔽q]  hF₂ in
/-- The images of `quotientFiber` over distinct quotient points `y₁ ≠ y₂` are
disjoint -/
theorem quotientFiber_disjoint
    (i : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  {y₁ y₂ : sDomain 𝔽q β h_ℓ_add_R_rate destIdx}
  (hy_ne : y₁ ≠ y₂) :
  Disjoint
    ((quotientFiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le y₁ '' Set.univ).toFinset)
    ((quotientFiber 𝔽q β (i := i) (steps := steps)
      h_destIdx h_destIdx_le y₂ '' Set.univ).toFinset) := by
  classical
  refine Finset.disjoint_left.2 fun x hx₁ hx₂ => hy_ne ?_
  simp only [Set.mem_toFinset, Set.image_univ, Set.mem_range] at hx₁ hx₂
  obtain ⟨k₁, rfl⟩ := hx₁
  obtain ⟨k₂, hk₂⟩ := hx₂
  rw [eq_iteratedQuotientMap_of_mem_quotientFiber_range 𝔽q β i steps h_destIdx h_destIdx_le _ y₁
      ⟨k₁, rfl⟩,
    eq_iteratedQuotientMap_of_mem_quotientFiber_range 𝔽q β i steps h_destIdx h_destIdx_le _ y₂
      ⟨k₂, hk₂.symm⟩]


/-- Evaluation vector `[f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T` of `f` on the fiber of `y`,
the right-hand vector of the matrix form of the iterated fold (`iteratedFold_eq_matrix_form`). -/
def fiberEvaluations (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i + steps)
  (h_destIdx_le : destIdx ≤ ℓ)
  (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
  (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) : Fin (2 ^ steps) → L :=
  -- Get the fiber points
  let fiberMap := quotientFiber 𝔽q β (i := i) (steps := steps) (h_destIdx := h_destIdx)
    (h_destIdx_le := h_destIdx_le) (y := y)
  -- Evaluate f at each fiber point
  fun idx => f (fiberMap idx)

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
/-- A fiber evaluation vector splits into the vectors over its two one-step predecessor points. -/
lemma fiberEvaluations_succ
    (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ) (h_midIdx : midIdx = i + steps)
    (h_destIdx : destIdx = i + steps + 1)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :
    let fiberMap := quotientFiber 𝔽q β (i := midIdx) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by omega) h_destIdx_le (y := y)
    let z₀ := fiberMap 0
    let z₁ := fiberMap 1
    let fiber_eval_z₀ :=
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (steps := steps) (i := i) (destIdx := midIdx)
        (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f) z₀
    let fiber_eval_z₁ : Fin (2 ^ steps) → L :=
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps)
        (i := i) (destIdx := midIdx) (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f) z₁
    (fiberEvaluations 𝔽q β (steps := steps + 1) (i := i)
      h_destIdx h_destIdx_le f y) =
    appendPowTwo (n := steps) fiber_eval_z₀ fiber_eval_z₁ := by
  -- 1. Unfold definitions to expose `quotientFiber`
  unfold fiberEvaluations appendPowTwo
  simp only
  funext fiber_y_idx -- fiber_y_idx is index of the `steps`-step fiber point of y (y ∈ S^{i+steps})
  -- 2. We need to show that the fiber point mapping splits correctly.
  -- Split into cases based on the MSB of fiber_y_idx
  set fiberMap := quotientFiber 𝔽q β (i := midIdx) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_destIdx := by omega) h_destIdx_le (y := y)
  set z₀ := fiberMap 0
  set z₁ := fiberMap 1
  set left_point := (quotientFiber (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps + 1)
    h_destIdx h_destIdx_le) (y := y)
      fiber_y_idx
  let zᵢ : sDomain 𝔽q β h_ℓ_add_R_rate midIdx :=
    if h : fiber_y_idx.val < 2 ^ steps then z₀ else z₁
  let fiber_zᵢ_idx : Fin (2 ^ steps) :=
    if h : fiber_y_idx.val < 2 ^ steps then ⟨fiber_y_idx, by omega⟩
    else ⟨fiber_y_idx.val - 2 ^ steps, by omega⟩
  set right_point := quotientFiber (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_midIdx (h_destIdx_le := by omega)
    (y := zᵢ) fiber_zᵢ_idx
  have h_left_point_eq_right_point : left_point = right_point := by
    let basis := sDomain_basis 𝔽q β h_ℓ_add_R_rate i (lt_rounds_add_rate_of_le_rounds (by omega))
    apply basis.repr.injective
    ext (coeffIdx : Fin (ℓ + 𝓡 - i))
    rw [quotientFiber_repr_coeff 𝔽q β i (steps := steps + 1) (destIdx := destIdx)
      h_destIdx h_destIdx_le (y := y) (k := fiber_y_idx)]
    rw [quotientFiber_repr_coeff 𝔽q β i (steps := steps) (destIdx := midIdx)
      (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (y := zᵢ) (k := fiber_zᵢ_idx)]
    dsimp only [Fin.eta, fiberCoeff]
    unfold zᵢ fiber_zᵢ_idx
    have h_repr_z₀ := quotientFiber_repr_coeff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := 1) (h_destIdx := by omega) (h_destIdx_le := by omega)
      (y := y) (k := 0)
    have h_repr_z₁ := quotientFiber_repr_coeff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := 1) (h_destIdx := by omega) (h_destIdx_le := by omega)
      (y := y) (k := 1)
    by_cases h_fiber_y_idx_lt_2_pow_steps : fiber_y_idx.val < 2 ^ steps
    · -- right-point is quotientFiber(z₀, fiber_y_idx)
      simp only [h_fiber_y_idx_lt_2_pow_steps, ↓reduceDIte]
      by_cases h_coeffIdx_lt_steps : coeffIdx.val < steps
      · have h_lt_succ : coeffIdx.val < steps + 1 := by omega
        simp only [h_lt_succ, ↓reduceDIte, h_coeffIdx_lt_steps]
      · simp only [h_coeffIdx_lt_steps, ↓reduceDIte]
        by_cases h_lt_succ : coeffIdx.val < steps + 1
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₀_rhs := h_repr_z₀ ⟨coeffIdx.val - steps, by omega⟩
          conv_rhs => rw [h_repr_z₀_rhs]
          unfold fiberCoeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod]
          have h_coeffIdx_eq_steps : coeffIdx.val = steps := by omega
          simp only [h_coeffIdx_eq_steps, tsub_self, ↓reduceDIte]
          have h_steps_getBit_idx : Nat.getBit (n := fiber_y_idx) (k := steps) = 0 := by
            let res := Nat.getBit_of_lt_two_pow (k := steps) (n := steps)
              (a := ⟨fiber_y_idx, by omega⟩)
            simp only [lt_self_iff_false, ↓reduceIte] at res
            exact res
          rw [h_steps_getBit_idx, Nat.getBit]
          simp only [↓reduceIte, shiftRight_zero, and_one_is_mod, zero_mod]
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₀_rhs := h_repr_z₀ ⟨coeffIdx.val - steps, by omega⟩
          conv_rhs => rw [h_repr_z₀_rhs]
          unfold fiberCoeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod]
          have h_sub_gt_0: coeffIdx.val - steps ≠ 0 := by omega
          simp only [h_sub_gt_0, ↓reduceDIte]
          rfl
    · -- right-point is quotientFiber(z₁, fiber_y_idx - 2 ^ steps)
      have h_fiber_y_idx_ge_2_pow_steps : fiber_y_idx.val ≥ 2 ^ steps := by omega
      have h_fiber_y_idx_getBit_steps : Nat.getBit (k := steps) (n := fiber_y_idx) = 1 := by
        -- This is because 2^steps ≤ fiber_y_idx.val < 2^(steps + 1)
        have h_lt : fiber_y_idx.val < 2^(steps + 1) := by omega
        apply Nat.getBit_1_of_ge_two_pow_and_lt_two_pow_succ
        · omega
        · omega
      simp only [h_fiber_y_idx_lt_2_pow_steps, ↓reduceDIte]
      by_cases h_coeffIdx_lt_steps : coeffIdx.val < steps
      · have h_lt_succ : coeffIdx.val < steps + 1 := by omega
        simp only [h_lt_succ, ↓reduceDIte, h_coeffIdx_lt_steps]
        have h_getBit_eq: Nat.getBit (n := fiber_y_idx) (k := coeffIdx)
          = Nat.getBit (n := fiber_y_idx - 2 ^ steps) (k := coeffIdx) := by
          let getBit_Sub_2_pow_steps := Nat.getBit_of_sub_two_pow_of_bit_1 (n := fiber_y_idx)
            (i := steps) (h_getBit_eq_1 := h_fiber_y_idx_getBit_steps) (j := coeffIdx)
          rw [getBit_Sub_2_pow_steps]
          have h_ne : coeffIdx.val ≠ steps := by omega
          simp only [h_ne, ↓reduceIte]
        rw [h_getBit_eq]
      · simp only [h_coeffIdx_lt_steps, ↓reduceDIte]
        by_cases h_lt_succ : coeffIdx.val < steps + 1
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₁_rhs := h_repr_z₁ ⟨coeffIdx.val - steps, by omega⟩
          conv_rhs => rw [h_repr_z₁_rhs]
          unfold fiberCoeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ]
          have h_coeffIdx_eq_steps : coeffIdx.val = steps := by omega
          simp only [h_coeffIdx_eq_steps, tsub_self, ↓reduceDIte]
          simp only [h_fiber_y_idx_getBit_steps, one_ne_zero, ↓reduceIte, right_eq_ite_iff,
            imp_false, ne_eq];
          simp only [getBit, shiftRight_zero, Nat.and_self, one_ne_zero, not_false_eq_true]
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₁_rhs := h_repr_z₁ ⟨coeffIdx.val - steps, by omega⟩
          conv_rhs => rw [h_repr_z₁_rhs]
          unfold fiberCoeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod]
          have h_sub_gt_0: coeffIdx.val - steps ≠ 0 := by omega
          simp only [h_sub_gt_0, ↓reduceDIte]
          rfl
  rw [h_left_point_eq_right_point]
  unfold right_point zᵢ fiber_zᵢ_idx
  split_ifs with h_lt
  · simp only -- z₀
  · simp only -- z₁

end FiberMath

end Essentials

end
end Binius.BinaryBasefold
