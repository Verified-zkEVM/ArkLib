/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Chung Thai Nguyen, Quang Dao
-/
import ArkLib.Data.Nat.Bitwise
import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import ArkLib.Data.Probability.Instances
import ArkLib.Data.CodingTheory.Prelims
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.Henselian
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ENNReal.Inv

/-!
# Proximity Gaps in Interleaved Codes

This file formalizes the main results from the paper "Proximity Gaps in Interleaved Codes"
by Diamond and Gruen (DG25).

## Main Definitions

The core results from DG25 are the following:
1. `affine_gaps_lifted_to_interleaved_codes`: **Theorem 3.1 (DG25):** If a linear code `C` has
  proximity gaps for affine lines (up to unique decoding radius), then its interleavings `C^m`
  also do.
2. `interleaved_affine_gaps_imply_tensor_gaps`: **Theorem 3.6 (AER24):** If all interleavings `C^m`
  have proximity gaps for affine lines, then `C` exhibits tensor-style proximity gaps.
3. `reedSolomon_multilinearCorrelatedAgreement_Nat`, `reedSolomon_multilinearCorrelatedAgreement`:
  **Corollary 3.7 (DG25):** Reed-Solomon codes exhibit tensor-style proximity gaps (up to unique
  decoding radius).

This formalization assumes the availability of Theorem 2.2 (Ben+23 / BCIKS20 Thm 4.1) stating
that Reed-Solomon codes have proximity gaps for affine lines up to the unique decoding radius.

## TODOs
- Conjecture 4.3 proposes ε=n might hold for general linear codes.

## References

- [DG25] Benjamin E. Diamond and Angus Gruen. “Proximity Gaps in Interleaved Codes”. In: IACR
Communications in Cryptology 1.4 (Jan. 13, 2025). issn: 3006-5496. doi: 10.62056/a0ljbkrz.

- [AER24] Guillermo Angeris, Alex Evans, and Gyumin Roh. A Note on Ligero and Logarithmic
  Randomness. Cryptology ePrint Archive, Paper 2024/1399. 2024. url: https://eprint.iacr.org/2024/1399.
-/

noncomputable section

open Code LinearCode InterleavedCode ReedSolomonCode ProximityGap ProbabilityTheory Filter
open NNReal Finset Function
open scoped BigOperators LinearCode ProbabilityTheory
open Real

universe u v w k l
variable {κ : Type k} {ι : Type l} [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq κ]
variable {F : Type v} [Semiring F] [Fintype F]
variable {A : Type w} [Fintype A] [DecidableEq A] [AddCommMonoid A] [Module F A] -- Alphabet type

/-- Evaluation of an affine line across u₀ and u₁ at a point r -/
def affineLineEvaluation {F : Type v} [Ring F] [Module F A]
    (u₀ u₁ : Word A ι) (r : F) : Word A ι := (1 - r) • u₀ + r • u₁

----------------------------------------------------- Switch to (F : Type) for `Pr_{...}[...]` usage
variable {F : Type} [Ring F] [Module F A] [Fintype F] (C : Set (Word A ι))
/-
Definition 2.1. We say that `C ⊂ F^n` features proximity gaps for affine lines
with respect to the proximity parameter `e` and the false witness bound `ε` if, for
each pair of words `u_0` and `u_1` in `F^n`, if
`Pr_{r ∈ F}[d((1-r) · u_0 + r · u_1, C) ≤ e] > ε/q`
holds, then `d^2((u_i)_{i=0}^1, C^2) ≤ e` also does.
-/
def e_ε_correlatedAgreementAffineLinesNat
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Module F A]
    (C : Set (ι → A)) (e ε : ℕ) : Prop :=
  ∀ (u₀ u₁ : Word A ι),
    Pr_{let r ← $ᵖ F}[Δ₀(affineLineEvaluation (F := F) u₀ u₁ r, C) ≤ e]
      > ((ε: ℝ≥0) / (Fintype.card F : ℝ≥0)) →
      jointProximityNat₂ (A := A) (ι := ι) (u₀ := u₀) (u₁ := u₁) (e := e) (C := C)

omit [DecidableEq ι] [Nonempty ι] [Fintype A] [Fintype F] in
/-- **Lemma: Distance of Affine Combination is Bounded by Interleaved Distance** -/
theorem dist_affineCombination_le_dist_interleaved₂
    (u₀ u₁ v₀ v₁ : Word A ι) (r : F) :
    Δ₀( affineLineEvaluation (F := F) u₀ u₁ r, affineLineEvaluation (F := F) v₀ v₁ r) ≤
      Δ₀(u₀ ⋈₂ u₁, v₀ ⋈₂ v₁) := by
  -- The goal is to prove card(filter L) ≤ card(filter R)
  -- We prove this by showing filter L ⊆ filter R
  apply Finset.card_le_card
  -- Use `monotone_filter_right` or prove subset directly
  intro j
  -- Assume j is in the filter set on the LHS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hj_row_diff
  -- Goal: Show j is in the filter set on the RHS
  unfold affineLineEvaluation at hj_row_diff
  -- hj_row_diff : ((1 - r) • u₀ + r • u₁) j ≠ ((1 - r) • v₀ + r • v₁) j
  -- ⊢ (u₀⋈₂u₁) j ≠ (v₀⋈₂v₁) j
  -- We prove this by contradiction
  by_contra h_cols_eq
  -- h_cols_eq : (u₀ ⋈₂ u₁) j = (v₀ ⋈₂ v₁) j
  -- `h_cols_eq` is a function equality. Apply it to row indices 0 and 1
  have h_row0_eq : (u₀ ⋈₂ u₁) j = (v₀ ⋈₂ v₁) j := by exact h_cols_eq
  simp only [Pi.add_apply, Pi.smul_apply, ne_eq] at hj_row_diff
  have h_row0_eq : (u₀ ⋈₂ u₁) j 0 = (v₀ ⋈₂ v₁) j 0 := congrFun h_cols_eq 0
  have h_row1_eq : (u₀ ⋈₂ u₁) j 1 = (v₀ ⋈₂ v₁) j 1 := congrFun h_cols_eq 1
  have h_row0 : u₀ j = v₀ j := by exact h_row0_eq
  have h_row1 : u₁ j = v₁ j := by exact h_row1_eq
  rw [h_row0, h_row1] at hj_row_diff
  exact hj_row_diff rfl -- since hj_row_diff has form : ¬(x = x)

section TensorProximityGapDefinitions -- CommRing scalar set
variable {F : Type} [CommRing F] [Module F A] [Fintype F]

def δ_ε_multilinearCorrelatedAgreement_Nat [CommRing F]
  {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Module F A]
  (C : Set (ι → A)) (ϑ : ℕ) (e : ℕ) (ε : ℕ) : Prop :=
  ∀ (u : WordStack A (Fin (2^ϑ)) ι),
    Pr_{let r ← $ᵖ (Fin ϑ → F)}[ -- This syntax only works with (A : Type 0)
      Δ₀(r |⨂| u, C) ≤ e
    ] > (ϑ : ℝ≥0) * ε / (Fintype.card F : ℝ≥0) →
    jointProximityNat (u := u) (e := e) (C := C)

def multilinearCombine_affineLineEvaluation {ϑ : ℕ}
  (U₀ U₁ : WordStack A (Fin (2 ^ ϑ)) ι) (r : Fin ϑ → F) (r_affine_combine : F) : (Word A ι) :=
  multilinearCombine  (u := affineLineEvaluation (F := F) U₀ U₁ r_affine_combine) (r := r)

def splitHalfRowWiseInterleavedWords {ϑ : ℕ} (u : WordStack A (Fin (2 ^ (ϑ + 1))) ι) :
  (WordStack A (Fin (2 ^ (ϑ))) ι) × (WordStack A (Fin (2 ^ (ϑ))) ι) := by
  have h_pow_lt: 2 ^ (ϑ) < 2 ^ (ϑ + 1) := by
    apply Nat.pow_lt_pow_succ (by omega)
  let u₀ : WordStack A (Fin (2 ^ (ϑ))) ι := fun rowIdx => u ⟨rowIdx, by omega⟩
  let u₁ : WordStack A (Fin (2 ^ (ϑ))) ι := fun rowIdx => u ⟨rowIdx + 2 ^ (ϑ), by
    calc _ < 2 ^ (ϑ) + 2 ^ (ϑ) := by omega
      _ = 2 ^ (ϑ + 1) := by omega
  ⟩
  use u₀, u₁

def mergeHalfRowWiseInterleavedWords {ϑ : ℕ}
  (u₀ : WordStack A (Fin (2 ^ (ϑ))) ι)
  (u₁ : WordStack A (Fin (2 ^ (ϑ))) ι) :
  WordStack A (Fin (2 ^ (ϑ + 1))) ι := fun k =>
    if hk : k.val < 2 ^ ϑ then
      u₀ ⟨k, by omega⟩
    else
      u₁ ⟨k - 2 ^ ϑ, by omega⟩

omit [Fintype ι] [Nonempty ι] [Fintype A] [DecidableEq A] [AddCommMonoid A] [DecidableEq ι] in
lemma eq_splitHalf_iff_merge_eq {ϑ : ℕ}
  (u : WordStack A (Fin (2 ^ (ϑ + 1))) ι)
  (u₀ : WordStack A (Fin (2 ^ (ϑ))) ι)
  (u₁ : WordStack A (Fin (2 ^ (ϑ))) ι) :
  (u₀ = splitHalfRowWiseInterleavedWords (u := u).1
  ∧ u₁ = splitHalfRowWiseInterleavedWords (u := u).2)
  ↔ mergeHalfRowWiseInterleavedWords u₀ u₁ = u := by
  constructor
  · intro h_split_eq_merge
    funext rowIdx
    -- funext colIdx
    simp only [mergeHalfRowWiseInterleavedWords]
    simp only [splitHalfRowWiseInterleavedWords] at h_split_eq_merge
    by_cases hk : rowIdx.val < 2 ^ ϑ
    · simp only [hk, ↓reduceDIte]
      have h_eq := h_split_eq_merge.1
      rw [funext_iff] at h_eq
      let res := h_eq ⟨rowIdx, by omega⟩
      simp only at res
      exact res
    · simp only [hk, ↓reduceDIte]
      have h_eq := h_split_eq_merge.2
      rw [funext_iff] at h_eq
      let res := h_eq ⟨rowIdx - 2 ^ ϑ, by omega⟩
      simp only at res
      rw! (castMode:=.all) [Nat.sub_add_cancel (h := by omega)] at res
      exact res
  · intro h_merge_eq_split
    simp only [splitHalfRowWiseInterleavedWords]
    unfold mergeHalfRowWiseInterleavedWords at h_merge_eq_split
    rw [funext_iff] at h_merge_eq_split
    constructor
    · funext rowIdx
      let res := h_merge_eq_split ⟨rowIdx, by omega⟩
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at res
      exact res
    · funext rowIdx
      let res := h_merge_eq_split ⟨rowIdx + 2 ^ ϑ, by omega⟩
      simp only [add_lt_iff_neg_right, not_lt_zero', ↓reduceDIte, add_tsub_cancel_right,
        Fin.eta] at res
      exact res

omit [Nonempty ι] [DecidableEq ι] [Fintype A] [AddCommMonoid A] in
/-- NOTE: This could be generalized to 2 * N instead of 2 ^ (ϑ + 1).
Also, this can be proved for `↔` instead of `→`. -/
theorem CA_split_rowwise_implies_CA
    {ϑ : ℕ} (u : WordStack A (Fin (2 ^ (ϑ + 1))) ι) (e : ℕ) :
    let U₀ : WordStack A (Fin (2^ϑ)) ι := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
    let U₁ : WordStack A (Fin (2^ϑ)) ι := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
    jointProximityNat₂ (u₀ := ⋈|U₀) (u₁ := ⋈|U₁) (e := e) (C := C ^⋈ (Fin (2 ^ ϑ)))
      → jointProximityNat (u := u) (e := e) (C := C) := by
  -- 1. Unfold definitions
  unfold jointProximityNat₂ jointProximityNat
  simp only
  set U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
  set U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
  conv_lhs => rw [Code.closeToCode_iff_closeToCodeword_of_minDist]
  intro hCA_split_rowwise
  rcases hCA_split_rowwise with ⟨vSplit, hvSplit_mem, hvSplit_dist_le_e⟩
  -- ⊢ Δ₀(⋈|u, ↑(C ^⋈ (Fin (2 ^ (ϑ + 1))))) ≤ ↑e
  rw [closeToWord_iff_exists_possibleDisagreeCols] at hvSplit_dist_le_e
  rcases hvSplit_dist_le_e with ⟨D, hD_card_le_e, h_agree_outside_D⟩
  conv_lhs => rw [←interleavedCode_eq_interleavedCodeSet (C := C)]
  rw [Code.closeToCode_iff_closeToCodeword_of_minDist
    (u := ⋈|u) (e := e) (C := C ^⋈ (Fin (2 ^ (ϑ + 1))))]
  simp_rw [closeToWord_iff_exists_possibleDisagreeCols]
  let VSplit_rowwise := Matrix.transpose vSplit
  let VSplit₀_rowwise := Matrix.transpose (VSplit_rowwise 0)
  let VSplit₁_rowwise := Matrix.transpose (VSplit_rowwise 1)
  let v_rowwise_finmap : WordStack A (Fin (2 ^ (ϑ + 1))) ι :=
    mergeHalfRowWiseInterleavedWords VSplit₀_rowwise VSplit₁_rowwise
  let v_IC := ⋈| v_rowwise_finmap
  use v_IC
  constructor
  · -- v_IC ∈ ↑(C ^⋈ (Fin (2 ^ (ϑ + 1))))
    -- rw [interleavedCode_eq_interleavedCodeSet]
    -- simp only [SetLike.mem_coe, mem_interleavedCode_iff]
    intro rowIdx
    have h_vSplit_rows_mem : ∀ (i : Fin 2) (j : Fin (2 ^ ϑ)), (fun col ↦ vSplit col i j) ∈ C := by
      intro i
      specialize hvSplit_mem i
      exact hvSplit_mem
    -- Now we prove `v_rowwise_finmap rowIdx ∈ C` by cases on rowIdx.
    dsimp only [v_IC]
    by_cases hk : rowIdx.val < 2 ^ ϑ
    · -- Case 1: rowIdx is in the first half
      -- exact h_vSplit_rows_mem 0 ⟨rowIdx.val, hk⟩
      let hRes₀ := h_vSplit_rows_mem 0 ⟨rowIdx.val, hk⟩
      simp only [Fin.isValue] at hRes₀
      convert hRes₀
      rename_i colIdx
      -- ⊢ getRow (⋈|v_rowwise_finmap) rowIdx colIdx = vSplit colIdx 0 ⟨↑rowIdx, hk⟩
      unfold v_rowwise_finmap mergeHalfRowWiseInterleavedWords VSplit₀_rowwise
       VSplit_rowwise -- unfold them all
      simp only [WordStack, InterleavedWord, instInterleavableWordStackInterleavedWord,
        Fin.isValue, interleaveWordStack, Matrix.transpose_apply, hk, ↓reduceDIte]
    · -- Case 2: rowIdx is in the second half
      let hRes₁ := h_vSplit_rows_mem 1 ⟨rowIdx.val - 2 ^ ϑ, by omega⟩
      simp only [Fin.isValue] at hRes₁
      convert hRes₁
      rename_i colIdx
      -- ⊢ getRow (⋈|v_rowwise_finmap) rowIdx colIdx = vSplit colIdx 1 ⟨↑rowIdx - 2 ^ ϑ, by omega⟩
      unfold v_rowwise_finmap mergeHalfRowWiseInterleavedWords VSplit₁_rowwise
        VSplit_rowwise -- unfold them all
      simp only [WordStack, InterleavedWord, instInterleavableWordStackInterleavedWord,
        Fin.isValue, interleaveWordStack, Matrix.transpose_apply, hk, ↓reduceDIte]
    -- END OF MODIFIED SECTION
  · use D
    constructor
    · exact hD_card_le_e
    · intro colIdx h_colIdx_notin_D
      funext rowIdx
      -- simp only [interleaveWords]
      dsimp only [v_IC]
      have hRes := h_agree_outside_D colIdx (h_colIdx_notin_D)
      -- hRes : (⋈|finMapTwoWords (⋈|U₀) (⋈|U₁)) colIdx = vSplit colIdx
      -- ⊢ u rowIdx colIdx = (⋈|v_rowwise_finmap) colIdx rowIdx
      simp_rw [funext_iff] at hRes
      -- unfold finMapTwoWords at hRes
      by_cases hk : rowIdx.val < 2 ^ ϑ
      · -- Case 1: We are in the "U₀" half
        unfold v_rowwise_finmap mergeHalfRowWiseInterleavedWords VSplit₀_rowwise
          VSplit_rowwise
        simp only [WordStack, InterleavedWord, instInterleavableWordStackInterleavedWord,
          interleaveWordStack, Matrix.transpose_apply, Fin.isValue, hk,
          ↓reduceDIte]
        -- ⊢ u rowIdx colIdx = vSplit colIdx 0 ⟨↑rowIdx, ⋯⟩
        have hRes₀ := hRes 0 ⟨rowIdx, by omega⟩
        simp only [Fin.isValue] at hRes₀
        exact hRes₀
      · -- Case 2: We are in the "U₁" half
        unfold v_rowwise_finmap mergeHalfRowWiseInterleavedWords VSplit₁_rowwise
          VSplit_rowwise
        simp only [WordStack, InterleavedWord, instInterleavableWordStackInterleavedWord,
          interleaveWordStack, Matrix.transpose_apply, Fin.isValue, hk,
          ↓reduceDIte]
        -- ⊢ u rowIdx colIdx = vSplit colIdx 1 ⟨↑rowIdx - 2 ^ ϑ, ⋯⟩
        have hRes₁ := hRes 1 ⟨rowIdx - 2 ^ ϑ, by omega⟩
        simp only [Fin.isValue] at hRes₁
        ---
        dsimp only [splitHalfRowWiseInterleavedWords, Fin.isValue, U₁] at hRes₁
        rw [←hRes₁]
        conv_rhs =>
          unfold finMapTwoWords
          simp only [InterleavedSymbol, WordStack, InterleavedWord,
            instInterleavableWordStackInterleavedWord, interleaveWordStack, Fin.isValue,
            Matrix.transpose_apply]
          rw! [Nat.sub_add_cancel (h := by omega)]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype A] [DecidableEq A] [Fintype F] in
/-- `[⊗_{i=0}^{ϑ-1}(1-r_i, r_i)] · [ - u₀ - ; ... ; - u_{2^ϑ-1} - ]`
`- [⊗_{i=0}^{ϑ-2}(1-r_i, r_i)] · ([(1-r_{ϑ-1}) · U₀] + [r_{ϑ-1} · U₁])` -/
lemma multilinearCombine_recursive_form
  {ϑ : ℕ} (u : WordStack A (Fin (2 ^ (ϑ + 1))) ι) (r : Fin (ϑ + 1) → F) :
  let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
  let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
  let r_init : Fin (ϑ) → F := Fin.init r
  multilinearCombine (u:=u) (r:=r) = multilinearCombine (ϑ := ϑ) (u:=
    affineLineEvaluation (F := F) (u₀ := U₀) (u₁ := U₁) (r := r (Fin.last ϑ))) (r:=r_init) := by
  -- 1. Unfold definitions and prove equality component-wise for each column index.
  funext colIdx
  simp only [multilinearCombine]
  have h_2_pow_ϑ_succ : 2 ^ (ϑ + 1) = 2 ^ (ϑ) + 2 ^ (ϑ) := by
    exact Nat.two_pow_succ ϑ
  rw! (castMode := .all) [h_2_pow_ϑ_succ]
  conv_lhs => -- split the sum in LHS over (fin (2 ^ (ϑ + 1))) into two sums over (fin (2 ^ (ϑ)))
    rw [Fin.sum_univ_add (a := 2 ^ (ϑ)) (b := 2 ^ (ϑ))]
    simp only [Fin.natAdd_eq_addNat]
    -- 2. Simplify LHS using definitions of U₀ and U₁
  simp only [splitHalfRowWiseInterleavedWords]
  -- We also need to unfold U₀ and U₁ on the RHS.
  -- 3. Unfold RHS and distribute the sum
  simp only [affineLineEvaluation, Pi.add_apply, Pi.smul_apply, smul_add, smul_smul,
    sum_add_distrib]
  -- 4. Combine sums on LHS & RHS
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- 5. Show equality inside the sum
  apply Finset.sum_congr rfl
  intro i _ -- `i` is the row index `Fin (2 ^ ϑ)`
  simp_rw [eqRec_eq_cast]
  rw! [←Fin.cast_eq_cast (h := by omega)]
  -- 6. Prove the two core multilinearWeight identities
  -- These are the key `Nat.getBit` facts.
  let r_init := Fin.init r
  -- 7. Apply the identities to finish the proof
  -- The goal is now `... • U₀ i colIdx + ... • U₁ i colIdx = ... • U₀ i colIdx + ... • U₁ i colIdx`
  have h_fin_cast_castAdd: Fin.cast (eq := by omega) (i := Fin.castAdd (n := 2 ^ ϑ)
    (m := 2 ^ ϑ) i) = (⟨i, by omega⟩ : Fin (2 ^ (ϑ + 1))) := by rfl
  have h_fin_cast_castAdd_2: Fin.cast (eq := by omega)
    (i := i.addNat (2 ^ ϑ)) = (⟨i + 2 ^ ϑ, by omega⟩ : Fin (2 ^ (ϑ + 1))) := by rfl
  rw [h_fin_cast_castAdd, h_fin_cast_castAdd_2]

  have h_getLastBit : Nat.getBit (Fin.last ϑ) i = 0 := by
    have h := Nat.getBit_of_lt_two_pow (a := i) (k := Fin.last ϑ)
    simp only [Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
    exact h
  have h_i_and_2_pow_ϑ : i.val &&& (2 ^ ϑ) = 0 := by
    apply Nat.and_two_pow_eq_zero_of_getBit_0 (n := i) (i := ϑ)
    exact h_getLastBit
  have h_i_add_2_pow_ϑ := Nat.sum_of_and_eq_zero_is_xor (n := i.val)
    (m := 2 ^ ϑ) (h_n_AND_m:=h_i_and_2_pow_ϑ)

  have h_getLastBit_add_pow_2 : Nat.getBit (Fin.last ϑ) (i + 2 ^ ϑ) = 1 := by
    rw [h_i_add_2_pow_ϑ]; rw [Nat.getBit_of_xor]
    rw [h_getLastBit]; rw [Nat.getBit_two_pow]
    simp only [Fin.val_last, BEq.rfl, ↓reduceIte, Nat.zero_xor]

  have h_tensor_split_0 :
    multilinearWeight r ⟨i, by omega⟩ = multilinearWeight r_init i * (1 - r (Fin.last ϑ)) := by
    dsimp only [multilinearWeight]
    rw [Fin.prod_univ_castSucc]
    simp_rw [Nat.testBit_true_eq_getBit_eq_1]
    simp_rw [h_getLastBit]
    simp only [Fin.coe_castSucc]
    congr 1

  have h_tensor_split_1 :
    multilinearWeight r ⟨i + 2 ^ ϑ, by omega⟩ = multilinearWeight r_init i * (r (Fin.last ϑ)) := by
    dsimp only [multilinearWeight]
    rw [Fin.prod_univ_castSucc]
    simp_rw [Nat.testBit_true_eq_getBit_eq_1]
    simp_rw [h_getLastBit_add_pow_2]
    simp only [Fin.coe_castSucc, ↓reduceIte]
    congr 1
    apply Finset.prod_congr rfl
    intro x hx_univ-- index of the product
    rw [h_i_add_2_pow_ϑ]
    simp_rw [Nat.getBit_of_xor, Nat.getBit_two_pow]
    simp only [beq_iff_eq]
    have h_x_ne_ϑ: ϑ ≠ x.val := by omega
    simp only [h_x_ne_ϑ, ↓reduceIte, Nat.xor_zero]
    rfl
  rw [h_tensor_split_0, h_tensor_split_1]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype A] [DecidableEq A] [Fintype F] in
lemma multilinearCombine₁_eq_affineLineEvaluation -- ϑ = 1 case
  (u : Fin (2) → (Word A ι)):
  ∀ (r : Fin 1 → F), multilinearCombine (u:=u) (r:=r)
    = affineLineEvaluation (F := F) (u₀ := u 0) (u₁ := u 1) (r 0) := by
  intro r
  unfold multilinearCombine affineLineEvaluation multilinearWeight
  simp only [Nat.reducePow, Fin.sum_univ_two, Fin.isValue]
  ext colIdx
  simp_rw [Nat.testBit_true_eq_getBit_eq_1]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, Nat.getBit_zero_eq_zero, zero_ne_one, ↓reduceIte, prod_singleton, Nat.mod_succ,
    Nat.getBit_zero_eq_self (n := 1) (h_n := by omega), Word, Pi.add_apply, Pi.smul_apply]

end TensorProximityGapDefinitions

section MainResults
variable {F : Type} [CommRing F] [Fintype F] [NoZeroDivisors F] [DecidableEq F]
  -- switch to Type for `Pr_{...}[...]` usage
  {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A] [Module.Free F A]
  -- Semiring.toModule (R := A) => Module A A, plus Ring A for `RS code` theorems?
variable (MC : ModuleCode ι F A) [Nontrivial MC]
  (C : Set (Word A ι)) [Nonempty C] -- todo: change to Nontrivial if needed

instance : NoZeroSMulDivisors (R := F) (M := A) := Module.Free.noZeroSMulDivisors F A

instance : NoZeroSMulDivisors (R := F) (M := Word A ι) := _root_.Function.noZeroSMulDivisors

instance : Nonempty MC := by exact instNonemptyOfInhabited

-- instance : ∀ (κ : Type*) [Fintype κ] [DecidableEq κ], Nonempty (C ^⋈ κ) := by
--   intro κ hκ hκ_dec
--   exact instNonemptyInterleavedCode A (κ := κ) (ι := ι) C

/-!
## Section 3: Main Results
-/

variable {m : Nat} -- Interleaving factor > 0 (Proof uses m>1 later)
variable {e ε : ℕ} -- Proximity parameter and false witness bound

/-- The set R* of parameters `r` for which `Uᵣ` is e-close to the interleaved code C^m
i.e. `R* := {r ∈ F | d^m(Uᵣ, C^m) ≤ e}` -/
def R_star (U₀ U₁ : InterleavedWord A (Fin m) ι) : Finset F :=
  Finset.filter (fun r : F =>
    Δ₀(affineLineEvaluation (F := F) (u₀ := U₀) (u₁ := U₁) r, C ^⋈ (Fin m)) ≤ e
  ) Finset.univ

open Classical in
/-- The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁. -/
def disagreementSet (U₀ U₁ V₀ V₁ : InterleavedWord A (κ := κ) (ι := ι)) : Finset ι :=
  Finset.filter (fun colIdx => (U₀ colIdx ≠ V₀ colIdx) ∨ (U₁ colIdx ≠ V₁ colIdx)) Finset.univ

/-- The set `R** = {(r, j) ∈ R* × {0..n-1} | (Uᵣ)ʲ = (Vᵣ)ʲ}.` -/
def R_star_star (U₀ U₁ V₀ V₁ : InterleavedWord A (Fin m) ι) : Finset (F × ι) :=
  (R_star C (m := m) (e := e) U₀ U₁) ×ˢ (Finset.univ (α := ι)) |>.filter (fun (r, j) =>
    let Uᵣ := affineLineEvaluation U₀ U₁ r
    let Vᵣ := affineLineEvaluation V₀ V₁ r
    Uᵣ j = Vᵣ j)

omit [Nonempty ι] [DecidableEq ι] [DecidableEq κ] [Fintype A] [AddCommGroup A] in
open Classical in
/-- Row-wise distance is bounded by interleaved distance.
i.e. `d((U)ᵢ, (M)ᵢ) ≤ d^m(U, M)` -/
lemma dist_row_le_dist_ToInterleavedWord (U : InterleavedWord A (κ := κ) (ι := ι))
    (M : InterleavedWord A (κ := κ) (ι := ι)) (rowIdx : κ) :
    Δ₀(getRow U rowIdx, getRow M rowIdx) ≤ Δ₀(U, M) := by
  apply Finset.card_le_card
  refine monotone_filter_right univ ?_
  stop
  refine Pi.le_def.mpr ?_
  intro colIdx
  by_cases hDiffCell : getRow U rowIdx colIdx ≠ getRow M rowIdx colIdx
  · have hDiffCol : U colIdx ≠ M colIdx := by
      by_contra hEqCol
      simp only [getRow, ne_eq] at hDiffCell
      exact hDiffCell (congrFun hEqCol rowIdx)
    simp only [ne_eq, hDiffCell, not_false_eq_true, hDiffCol, le_refl]
  · by_cases hDiffCol : U colIdx ≠ M colIdx
    · simp only [hDiffCell, ne_eq, hDiffCol, not_false_eq_true, le_Prop_eq, implies_true]
    · simp only [hDiffCell, hDiffCol, le_refl]

omit [DecidableEq ι] [AddCommGroup A] [Fintype F] [Nonempty ι] [Fintype A]
  [NoZeroDivisors F] [DecidableEq F] [Module.Free F A] in
/-- Helper Lemma relating row distance to interleaved distance (as derived from DG25):
  `d((Uᵣ)ᵢ, C) ≤ d^m(Uᵣ, C^m)` -/
lemma dist_row_le_dist_ToInterleavedCode (U : InterleavedWord A (Fin m) ι) :
    ∀ (rowIdx : Fin m), Δ₀((getRow U rowIdx), C) ≤ Δ₀(U, C ^⋈ (Fin m)) := by
  intro i
  let d_To_interleaved := Code.distFromCode (u := U) (C := C ^⋈ (Fin m))
  -- There exists M achieving this distance e_int
  letI :   Nonempty ↑(C ^⋈ (Fin m)) :=
    instNonemptyInterleavedCode A (κ := Fin m) (ι := ι) C
  have h_exists : ∃ M ∈ C ^⋈ (Fin m), Δ₀(U, M) = d_To_interleaved :=
    Code.exists_closest_codeword_of_Nonempty_Code (C := C ^⋈ (Fin m)) (u := U)
  rcases h_exists with ⟨M, hM_mem, hM_dist⟩
  let Uᵢ := getRow U i
  let iM : InterleavedCodeword (A := A) (κ := Fin m) (ι := ι) (C := C):= ⟨M, hM_mem⟩
  let Mᵢ : C := getRow iM i
  -- InterleavedCodeword.getRowCodeword (A := A) (κ := Fin m) (ι := ι) (C := C) (v := iM) i
  -- We know d(Uᵢ, C) ≤ d(Uᵢ, Mᵢ) because Mᵢ ∈ C (from h_rows M hM_mem i)
  have dist_le_dist : Δ₀(Uᵢ, C) ≤ Δ₀(Uᵢ, Mᵢ) := by
    apply csInf_le' -- Using sInf property
    --  ⊢ ↑Δ₀(Uᵢ, Mᵢ) ∈ {d | ∃ v ∈ ↑MC, ↑Δ₀(Uᵢ, v) ≤ d}
    simp only [Set.mem_setOf_eq, Nat.cast_le]
    -- ⊢ ∃ v ∈ C, Δ₀(Uᵢ, v) ≤ Δ₀(Uᵢ, Mᵢ)
    use Mᵢ
    simp only [Subtype.coe_prop, le_refl, and_self]
  apply le_trans dist_le_dist
  -- ⊢ ↑Δ₀(Uᵢ, ↑Mᵢ) ≤ Δ₀(U, ↑C_m)

  have h_dist_row_le_dist_interleaved : Δ₀(Uᵢ, Mᵢ) ≤ Δ₀(U, M) := by
    simp only [Uᵢ, Mᵢ]
    simp only [getRow]
    convert dist_row_le_dist_ToInterleavedWord U M i

  calc
    (Δ₀(Uᵢ, Mᵢ): ℕ∞) ≤ (Δ₀(U, M): ℕ∞) :=
      ENat.coe_le_coe.mpr h_dist_row_le_dist_interleaved
    _ ≤ Δ₀(U, C ^⋈ (Fin m)) := le_of_eq hM_dist

/-- Extracts the constructed codewords V₀, V₁ and their agreement properties.
Hypotheses: 1. more than ε affine combinations Uᵣ are close to C^m (`hR_star_card`),
2. the base code C features proximity gaps for affine lines (`hC_gap`)
=> This function constructs the corresponding `interleaved codewords` `V₀` and `V₁` in `C^m`
that exhibit correlated agreement with `U₀` and `U₁` row-by-row respectively.
It returns a tuple containing:
- `V₀`, `V₁` : Codewords in `C^m`
- `hRowWise_pair_CA`: `Δ₀((u₀ := getRow U₀ rowIdx) ⋈₂ (u₁ := getRow U₁ rowIdx),`
                          `(v₀ := getRow V₀ rowIdx) ⋈₂ (v₁ := getRow V₁ rowIdx)) ≤ e`
-/
def constructInterleavedCodewordsAndRowWiseCA
  (U₀ U₁ : InterleavedWord A (Fin m) ι)
  (hC_gap : e_ε_correlatedAgreementAffineLinesNat (F := F) (C := C) e ε)
  (hR_star_card : (R_star (F := F) (C := C) (m := m) (e := e) U₀ U₁).card > ε) :
  Σ' (V₀ V₁ : C ^⋈ (Fin m)), -- Σ' creates a dependent tuple
    ∀ rowIdx, pairJointProximity₂ (u₀ := getRow U₀ rowIdx)
      (u₁ := getRow U₁ rowIdx)
      (v₀ := getRow (show (InterleavedCodeword A (Fin m) ι C) from V₀) rowIdx)
      (v₁ := getRow (show (InterleavedCodeword A (Fin m) ι C) from V₁) rowIdx) e := by
  let V₀₁ : (rowIdx: Fin m)
    → Σ' (v₀ v₁ : C), pairJointProximity₂ (u₀ := getRow U₀ rowIdx)
    (u₁ := getRow U₁ rowIdx) (v₀ := v₀) (v₁ := v₁) e := fun rowIdx => by
    set u₀ := getRow U₀ rowIdx
    set u₁ := getRow U₁ rowIdx
    -- Need: Δ₀(u₀ ⋈₂ u₁, v₀ ⋈₂ v₁) ≤ e, this requires { r | (1 - r) • u₀ + r • u₁ ∈ C} > ε,
      -- which can be derived from hR_star_card
    -- For any row i, R_star_card implies the proximity gap property applies to that row
    have h_P_affineCombineRow:
      (Pr_{ let r ←$ᵖ F }[ -- Probability notation
        (Δ₀(affineLineEvaluation (F := F) u₀ u₁ r, C) ≤ e: Prop)
      ] > ((ε: ℝ≥0) / (Fintype.card F : ℝ≥0))) := by
      -- Goal: Show probability > ε / q
      -- We know: card R* > ε, where R* = {r | Δ₀(Uᵣ, C^m) ≤ e}
      -- Let R_line = {r | Δ₀((Uᵣ)ᵢ, C) ≤ e}
      -- We proved earlier: R* ⊆ R_line
      -- So, card R_line ≥ card R* > ε
      let R_star_set := R_star (F := F) (C := C) (m := m) (e := e) U₀ U₁
      let R_line_set := Finset.filter (fun r =>
          Δ₀(affineLineEvaluation (F := F) u₀ u₁ r, C) ≤ e) Finset.univ
      -- Prove R* ⊆ R_line
      have R_star_subset : R_star_set ⊆ R_line_set := by
        intro r hr_mem
        simp only [R_star, mem_filter, mem_univ, true_and, R_star_set] at hr_mem
        simp only [R_line_set, Finset.mem_filter, Finset.mem_univ, true_and]
        -- Use dist_row_le_dist_ToInterleavedCode
        let Uᵣ : InterleavedWord A (Fin m) ι := affineLineEvaluation U₀ U₁ r
        have h_dist_le := dist_row_le_dist_ToInterleavedCode C Uᵣ rowIdx
        have h_row_eq : affineLineEvaluation u₀ u₁ r = getRow Uᵣ rowIdx := by
          ext j;
          simp only [affineLineEvaluation, Word, Pi.add_apply, Pi.smul_apply, getRow,
            InterleavedWord.getRowWord, Matrix.transpose_apply, Uᵣ]
          have h_u₀_j : u₀ j = U₀ j rowIdx := by rfl
          have h_u₁_j : u₁ j = U₁ j rowIdx := by rfl
          rw [h_u₀_j, h_u₁_j]
        rw [←h_row_eq] at h_dist_le
        exact le_trans h_dist_le hr_mem
      -- Use cardinality argument
      have h_card_line_gt_eps : R_line_set.card > ε :=
        lt_of_lt_of_le hR_star_card (Finset.card_le_card R_star_subset)
      -- Convert cardinality to probability: `Pr[P r] = card {r | P r} / card F`
      simp only [ENNReal.coe_natCast]
      rw [prob_uniform_eq_card_filter_div_card]
      simp only [ENNReal.coe_natCast]
      rw [gt_iff_lt]
      apply ENNReal.div_lt_div_right
      · simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]
      · exact ENNReal.natCast_ne_top (Fintype.card F)
      · exact Nat.cast_lt.mpr h_card_line_gt_eps

    -- Apply proximity gap of C to get correlated agreement at this row
    have h_corr_agree_row: Δ₀(u₀ ⋈₂ u₁, C ^⋈ (Fin 2)) ≤ e := by
      exact hC_gap (u₀) (u₁) (h_P_affineCombineRow)

    letI : Nonempty (C ^⋈ (Fin 2)) := instNonemptyInterleavedCode A (κ := Fin 2) (ι := ι) C

    let V_rowIdx := Code.pickClosestCodeword_of_Nonempty_Code (C := C ^⋈ (Fin 2)) (u := u₀ ⋈₂ u₁)
    let v₀ := getRow (show (InterleavedCodeword A (Fin 2) ι C) from V_rowIdx) 0
    let v₁ := getRow (show (InterleavedCodeword A (Fin 2) ι C) from V_rowIdx) 1
    use v₀, v₁
    have h_dist_min := Code.distFromPickClosestCodeword_of_Nonempty_Code
      (C := C ^⋈ (Fin 2)) (u := u₀ ⋈₂ u₁)
    rw [h_dist_min] at h_corr_agree_row
    have h_v₀_interleaved_v₁ : (V_rowIdx).val = (v₀.val ⋈₂ v₁.val) := by
      -- apply Subtype.ext;
      funext colIdx rowIdx₀₁
      by_cases h : rowIdx₀₁ = 0
      · rw [h]; rfl
      · have h' : rowIdx₀₁ = 1 := by omega
        rw [h']; rfl
    rw [h_v₀_interleaved_v₁] at h_corr_agree_row
    unfold pairJointProximity₂
    simp only [Nat.cast_le] at h_corr_agree_row
    simp only
    exact h_corr_agree_row -- TODO: try using `exact`

  let V₀_wordStack : WordStack A (Fin m) ι := fun rowIdx => (V₀₁ rowIdx).1.val
  let V₁_wordStack : WordStack A (Fin m) ι := fun rowIdx => (V₀₁ rowIdx).2.1.val
  let V₀ : C ^⋈ (Fin m) := ⟨⋈| V₀_wordStack, by
    simp only [Word, instCodeInterleavableSetForallMatrix, interleavedCodeSet,
      interleavedCode_eq_interleavedCodeSet, WordStack, InterleavedWord,
      instInterleavableWordStackInterleavedWord, interleave_wordStack_eq, Set.mem_setOf_eq,
      Matrix.transpose_transpose]
    intro rowIdx; exact Subtype.coe_prop (V₀₁ rowIdx).fst
  ⟩
  let V₁ : C ^⋈ (Fin m) := ⟨⋈| V₁_wordStack, by
    simp only [Word, instCodeInterleavableSetForallMatrix, interleavedCodeSet,
      interleavedCode_eq_interleavedCodeSet, WordStack, InterleavedWord,
      instInterleavableWordStackInterleavedWord, interleave_wordStack_eq, Set.mem_setOf_eq,
      Matrix.transpose_transpose]
    intro rowIdx; exact Subtype.coe_prop (V₀₁ rowIdx).snd.fst
  ⟩
  use V₀, V₁
  intro rowIdx
  exact (V₀₁ rowIdx).2.2 -- definitional equality of V₀ V₁ according to V₀₁

open Classical in
omit [NoZeroDivisors F] [DecidableEq F] [Fintype A] [Module.Free F A] in
/-- **Lemma 3.2 (DG25): Closeness implies Closeness to Constructed Codeword**
Context:
- `C` is a linear code in `F^n` with proximity gaps for affine lines (params `e`, `ε`).
- `e` is within the unique decoding radius of `C`.
- `U₀, U₁` are ColWise-interleaved words.
- `R*` is the set of `r` in `F` such that `Uᵣ = (1-r)U₀ + rU₁` is `e`-close to `C^m`.
- `V₀, V₁` are specific codewords in `C^m` constructed row-by-row using `C`'s gap property,
  assuming `|R*| > ε`.
- `Vᵣ = (1-r)V₀ + rV₁`.
Statement: For any parameter `r` in `R*`, the matrix `Uᵣ` must be `e`-close to the codeword `Vᵣ`.
 Lemma 3.2: Given a linear code `C ⊂ F^n` with proximity gaps for affine lines
(parameters `e`, `ε`), its `m`-fold interleaving `C^m`, and two matrices
`U_0`, `U_1 ∈ F^{m × n}`, let `U_r = (1-r)U_0 + rU_1` be a point on the affine line between them,
and let `R* = { r ∈ F | d^m(U_r, C^m) ≤ e }` be the set of parameters yielding points close
to the interleaved code.
-/
lemma affineWord_close_to_affineInterleavedCodeword
  (U₀ U₁ : InterleavedWord A (Fin m) ι)
  (he : e ≤ (Code.uniqueDecodingRadius (F := A) (ι := ι) (C := MC)))
  (hC_gap : e_ε_correlatedAgreementAffineLinesNat (F := F) (C := (MC : Set (ι → A))) e ε)
  (hR_star_card : (R_star (C := (MC : Set (ι → A))) (m := m) (e := e) U₀ U₁).card > ε) :
    let ⟨V₀, V₁, _⟩ := constructInterleavedCodewordsAndRowWiseCA (F := F)
      (A := A) (ι := ι) (C := MC) (U₀ := U₀) (U₁ := U₁) (hC_gap := by exact hC_gap)
      (hR_star_card := hR_star_card)
    ∀ (r : R_star (C := MC) (m := m) (e := e) (U₀ := U₀) (U₁ := U₁)), -- Δ₀ (Uᵣ, Vᵣ) ≤ e
      Δ₀(
        affineLineEvaluation (F := F) (u₀ := U₀) (u₁ := U₁) (r := r),
        affineLineEvaluation (F := F) (u₀ := V₀.val) (u₁ := V₁.val) (r := r.val)
      ) ≤ e := by
-- 1. Setup: Define V₀, V₁, Vᵣ, r, Uᵣ
  let ⟨V₀, V₁, h_row_agreement⟩ :=
    constructInterleavedCodewordsAndRowWiseCA (F := F) (A := A) (ι := ι) (C := MC) (U₀ := U₀)
      (U₁ := U₁) (hC_gap := by exact hC_gap) (hR_star_card := hR_star_card)
  intro r_sub
  let r := r_sub.val
  set Uᵣ := affineLineEvaluation (F := F) U₀ U₁ r
  set Vᵣ := affineLineEvaluation (F := F) V₀.val V₁.val r

  -- 2. By definition of R*, there exists *some* codeword Vᵣ* close to Uᵣ
  have h_r_in_R_star := r_sub.property
  simp only [R_star, Finset.mem_filter, Finset.mem_univ, true_and] at h_r_in_R_star
  -- h_r_in_R_star is: Δ₀(Uᵣ, C ^⋈ (Fin m)) ≤ e
  -- Use `exists_closest_codeword` to get this Vᵣ*
  letI : Nonempty ↑(MC ^⋈ (Fin m)) := instNonemptyInterleavedCode A (κ := Fin m) (ι := ι) MC
  classical
  let Vᵣ_star : MC ^⋈ (Fin m) := Code.pickClosestCodeword_of_Nonempty_Code (C := MC ^⋈ (Fin m))
    (u := Uᵣ)
  have hVᵣ_star_dist : Δ₀(Uᵣ, Vᵣ_star) = Δ₀(Uᵣ, MC ^⋈ (Fin m)) := by
    dsimp only [Vᵣ_star]
    rw [Code.distFromPickClosestCodeword_of_Nonempty_Code]

  have h_dist_Uᵣ_Vᵣ_star_le_e : Δ₀(Uᵣ, Vᵣ_star) ≤ e := by
    rw [←ENat.coe_le_coe, hVᵣ_star_dist]; exact h_r_in_R_star

  -- We must show Vᵣ* = Vᵣ. We do this row-by-row.
  -- Goal is Δ₀(Uᵣ, Vᵣ) ≤ e. We will prove Vᵣ = Vᵣ_star, then rw.
  have h_Vᵣ_eq_Vᵣ_star : Vᵣ = Vᵣ_star.val := by
    rw [InterleavedCode.eq_iff_all_rows_eq (α := InterleavedWord A (Fin m) ι)]
    intro rowIdx
    -- Get the i-th rows of Vᵣ and Vᵣ*
    set Vᵣ_i := getRow (show (InterleavedWord A (Fin m) ι) from Vᵣ) rowIdx
    set Vᵣ_star_i := getRow (show (InterleavedWord A (Fin m) ι) from Vᵣ_star.val) rowIdx
    -- ⊢ Vᵣ_i = Vᵣ_star_i
    -- 3. Show (Uᵣ)ᵢ is e-close to (Vᵣ*)ᵢ
    have h_dist_Uᵣi_Vᵣstari :
      Δ₀(getRow (show (InterleavedWord A (Fin m) ι) from Uᵣ) rowIdx, Vᵣ_star_i) ≤ e := by
      have h_Δ₀_getrow_Uᵣ_Vᵣ := dist_row_le_dist_ToInterleavedWord Uᵣ Vᵣ_star.val rowIdx
      apply le_trans (h_Δ₀_getrow_Uᵣ_Vᵣ)
      convert h_dist_Uᵣ_Vᵣ_star_le_e -- can't use exact here

    -- 4. Show (Uᵣ)ᵢ is e-close to (Vᵣ)ᵢ
    -- Get the row-wise agreement for row i from the constructor
    have h_agree_i := h_row_agreement rowIdx
    unfold pairJointProximity₂ at h_agree_i
    -- h_agree_i : Δ₀(getRow U₀ i ⋈₂ getRow U₁ i, getRow V₀.val i ⋈₂ getRow V₁.val i) ≤ e
    -- Show (Vᵣ)ᵢ is the affine combo of the rows of V₀, V₁
    have h_Vᵣ_i_eq_affine : Vᵣ_i =
      affineLineEvaluation (getRow V₀.val rowIdx) (getRow V₁.val rowIdx) r := by rfl
    -- Show (Uᵣ)ᵢ is the affine combo of the rows of U₀, U₁
    have h_Uᵣ_i_eq_affine : getRow (show (InterleavedWord A (Fin m) ι) from Uᵣ) rowIdx
      = affineLineEvaluation (getRow U₀ rowIdx) (getRow U₁ rowIdx) r := by rfl
    -- We need Δ₀((Uᵣ)ᵢ, (Vᵣ)ᵢ) ≤ e
    have h_dist_Uᵣi_Vᵣi : Δ₀(getRow (show (InterleavedWord A (Fin m) ι) from Uᵣ) rowIdx, Vᵣ_i) ≤ e
      := by -- ⊢ Δ₀(getRow (affineLineEvaluation U₀ U₁ r) rowIdx, getRow Vᵣ rowIdx) ≤ e
      have h_dist_row_le_dist_interleaved := dist_row_le_dist_ToInterleavedWord Uᵣ Vᵣ rowIdx
      -- apply le_trans h_dist_row_le_dist_interleaved
      -- ⊢ Δ₀(Uᵣ, Vᵣ) ≤ e
      -- Use the correlated agreement `h_agree_i`
      rw [h_Uᵣ_i_eq_affine, h_Vᵣ_i_eq_affine]
      apply le_trans (dist_affineCombination_le_dist_interleaved₂ _ _ _ _ _)
      -- ⊢ Δ₀(getRow U₀ rowIdx ⋈₂ getRow U₁ rowIdx, getRow (↑V₀) rowIdx ⋈₂ getRow (↑V₁) rowIdx) ≤ e
      exact h_agree_i

    -- 5. Use Unique Decoding to show (Vᵣ*)ᵢ = (Vᵣ)ᵢ
    -- We need the minimum distance d of the base code C
    let d: ℕ := ‖(MC : Set (ι → A))‖₀
    have h_d_pos : 0 < d := by
      -- Need to show d > 0. Usually codes have d ≥ 1 if not empty/trivial.
      -- Assuming d > 0 for non-trivial codes.
      rw [Code.uniqueDecodingRadius] at he
      let res :=  Code.dist_pos_of_Nontrivial (ι := ι) (F := A) (C := MC) (hC := by
        (expose_names; exact Set.nontrivial_coe_sort.mp inst_8))
      exact res

    -- We need 2e < d
    have h_2e_lt_d : 2 * e < d := by
      rw [Code.uniqueDecodingRadius] at he
      letI : NeZero ‖(MC : Set (ι → A))‖₀ := NeZero.of_pos h_d_pos
      have h_2e_lt_d := UDRClose_iff_two_mul_proximity_lt_d_UDR (C := MC) (e := e).mp (by exact he)
      exact h_2e_lt_d
    -- Apply unique decoding:
    -- Vᵣ_star_i is a codeword because it's a row of Vᵣ_star ∈ C^m
    have hVᵣ_star_i_mem : Vᵣ_star_i ∈ MC := by
      have hVᵣ_star := Vᵣ_star.property
      dsimp only [Word, instCodeInterleavableSetForallMatrix,
        CodeInterleavable.interleaveCode] at hVᵣ_star -- this is quite long
      rw [mem_moduleInterleavedCode_iff (F := F) (A := A) (κ := Fin m) (ι := ι) (MC := MC)
        (v := Vᵣ_star.val)] at hVᵣ_star
      exact hVᵣ_star rowIdx
    -- Vᵣ_i is a codeword because it's an affine combo of rows from V₀, V₁ ∈ C^m
    have hVᵣ_i_mem : Vᵣ_i ∈ MC := by
      rw [h_Vᵣ_i_eq_affine]
      apply MC.add_mem
      · apply MC.smul_mem;
        exact getRowOfInterleavedCodeword_mem_code (A := A) (κ := Fin m) (ι := ι) (C := MC)
          (u := V₀) rowIdx
      · apply MC.smul_mem;
        exact getRowOfInterleavedCodeword_mem_code (A := A) (κ := Fin m) (ι := ι) (C := MC)
          (u := V₁) rowIdx

    -- Apply the triangle inequality: d(Vᵣ_i, Vᵣ_star_i) ≤ d(Vᵣ_i, Uᵣ_i) + d(Uᵣ_i, Vᵣ_star_i)
    have h_dist_v_vstar : Δ₀(Vᵣ_i, Vᵣ_star_i) ≤
      Δ₀(Vᵣ_i, getRow (show (InterleavedWord A (Fin m) ι) from Uᵣ) rowIdx)
      + Δ₀(getRow (show (InterleavedWord A (Fin m) ι) from Uᵣ) rowIdx, Vᵣ_star_i) := by
        apply hammingDist_triangle

    -- We need to convert from ℕ∞ (Δ₀) to ℕ (hammingDist) for Code.eq_of_lt_dist
    have h_dist_v_vstar_nat : hammingDist Vᵣ_i Vᵣ_star_i < d := by
      -- Convert ℕ∞ inequalities to ℕ inequalities
      have h1_nat : Δ₀((getRow (show (InterleavedWord A (Fin m) ι) from Uᵣ) rowIdx), Vᵣ_i) ≤ e :=
        ENat.coe_le_coe.mp (ENat.coe_le_coe.mpr h_dist_Uᵣi_Vᵣi)
      have h2_nat : Δ₀((getRow (show (InterleavedWord A (Fin m) ι) from Uᵣ) rowIdx), Vᵣ_star_i) ≤ e
        := ENat.coe_le_coe.mp (ENat.coe_le_coe.mpr h_dist_Uᵣi_Vᵣstari)
      -- Apply triangle inequality for hammingDist
      calc
        Δ₀(Vᵣ_i, Vᵣ_star_i) ≤ Δ₀(Vᵣ_i, getRow (show (InterleavedWord A (Fin m) ι) from Uᵣ) rowIdx)
          + Δ₀(getRow (show (InterleavedWord A (Fin m) ι) from Uᵣ) rowIdx, Vᵣ_star_i) :=
            hammingDist_triangle _ _ _
        _ = Δ₀(getRow (show (InterleavedWord A (Fin m) ι) from Uᵣ) rowIdx, Vᵣ_i) +
          Δ₀(getRow (show (InterleavedWord A (Fin m) ι) from Uᵣ) rowIdx, Vᵣ_star_i)
          := by rw [hammingDist_comm]
        _ ≤ e + e := Nat.add_le_add h1_nat h2_nat
        _ = 2 * e := by rw [two_mul]
        _ < d := h_2e_lt_d

    -- Now apply unique decoding
    exact Code.eq_of_lt_dist hVᵣ_i_mem hVᵣ_star_i_mem h_dist_v_vstar_nat

  -- 8. Conclude Vᵣ = Vᵣ_star and return the distance
  rw [h_Vᵣ_eq_Vᵣ_star]
  exact h_dist_Uᵣ_Vᵣ_star_le_e

open Classical in
def R_star_star_filter_columns_in_D (U₀ U₁ : InterleavedWord A (Fin m) ι)
  (V₀ V₁ : MC^⋈(Fin m)) (e : ℕ) (D : Finset ι) : Finset (F × ι) :=
  (R_star_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁ V₀.val V₁.val).filter
    (fun p => p.2 ∈ D) in

def R_star_star_filter_columns_not_in_D (U₀ U₁ : InterleavedWord A (Fin m) ι)
  (V₀ V₁ : MC ^⋈ (Fin m)) (e : ℕ) (D : Finset ι) : Finset (F × ι) :=
  (R_star_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁ V₀.val V₁.val).filter
    (fun p => p.2 ∉ D) in

omit [Nonempty ι] [NoZeroDivisors F] [Fintype A] [Module.Free F A] [Nontrivial ↥MC] in
lemma R_star_star_eq_union (U₀ U₁ : InterleavedWord A (Fin m) ι)
  (V₀ V₁ : MC ^⋈ (Fin m)) (e : ℕ) (D : Finset ι):
  (R_star_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁ V₀.val V₁.val) =
    (R_star_star_filter_columns_not_in_D MC U₀ U₁ V₀ V₁ (e := e) D)
    ∪ (R_star_star_filter_columns_in_D MC U₀ U₁ V₀ V₁ (e := e) D) := by
  dsimp only [R_star_star, Lean.Elab.WF.paramLet, R_star_star_filter_columns_not_in_D,
    R_star_star_filter_columns_in_D]
  rw [Finset.union_comm]
  rw [Finset.filter_union_filter_neg_eq]

omit [Nonempty ι] [NoZeroDivisors F] [DecidableEq F] [Fintype A]
  [Module.Free F A] [Nontrivial ↥MC] in
open Classical in
lemma disjoint_R_star_star_filter_columns_in_D_not_in_D (U₀ U₁ : InterleavedWord A (Fin m) ι)
    (V₀ V₁ : MC^⋈(Fin m)) (e : ℕ) (D : Finset ι) :
  Disjoint (R_star_star_filter_columns_in_D MC U₀ U₁ V₀ V₁ (e := e) D)
    (R_star_star_filter_columns_not_in_D MC U₀ U₁ V₀ V₁ (e := e) D) := by
-- 1. Unfold the definitions to reveal the underlying `filter` structure
  unfold R_star_star_filter_columns_in_D R_star_star_filter_columns_not_in_D
  -- The goal is now `Disjoint (R_ss.filter P) (R_ss.filter (¬P))`
  apply disjoint_filter_filter_neg

omit [NoZeroDivisors F] [DecidableEq F] [Fintype A] [Module.Free F A] in
lemma D_card_le_e_implies_interleaved_correlatedAgreement₂
  (U₀ U₁ : InterleavedWord A (Fin m) ι)
  (hC_gap : e_ε_correlatedAgreementAffineLinesNat (F := F) (C := MC) e ε)
  (hR_star_card : (R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card > ε) :
    let V₀ := (constructInterleavedCodewordsAndRowWiseCA (F := F)
      (A := A) (ι := ι) (C := MC) (U₀ := U₀) (U₁ := U₁) (hC_gap := by exact hC_gap)
      (hR_star_card := hR_star_card)).1
    let V₁ := (constructInterleavedCodewordsAndRowWiseCA (F := F)
      (A := A) (ι := ι) (C := MC) (U₀ := U₀) (U₁ := U₁) (hC_gap := by exact hC_gap)
      (hR_star_card := hR_star_card)).2.1
    (disagreementSet U₀ U₁ V₀ V₁).card ≤ e
    → jointProximityNat₂ (C := MC ^⋈ (Fin m)) U₀ U₁ e := by
  -- 1. Unfold definitions and simplify
  set C_m := MC ^⋈ (Fin m)
  set U_rowwise := finMapTwoWords U₀ U₁
  set U_colwise := ⋈| U_rowwise
  set C_m_2 := C_m ^⋈ (Fin 2)
  -- Unfold the goal
  unfold jointProximityNat₂
  -- Goal: (let ⟨V₀, V₁, _⟩ := ... in (disagreementSet ...).card ≤ e) → (Δ₀(U_comb, C_m_2) ≤ e)
  simp only
  -- 2. Introduce the bindings and the hypothesis
  intro hDisagreeementCard_Le_e -- The assumption: (disagreementSet U₀ U₁ V₀ V₁).card ≤ e
  set V₀ := (constructInterleavedCodewordsAndRowWiseCA (F := F)
    (A := A) (ι := ι) (C := MC) (U₀ := U₀) (U₁ := U₁) (hC_gap := by exact hC_gap)
    (hR_star_card := hR_star_card)).1
  set V₁ := (constructInterleavedCodewordsAndRowWiseCA (F := F)
    (A := A) (ι := ι) (C := MC) (U₀ := U₀) (U₁ := U₁) (hC_gap := by exact hC_gap)
    (hR_star_card := hR_star_card)).2.1
  set hRowPairCA_U_V := (constructInterleavedCodewordsAndRowWiseCA
    (F := F) (A := A) (ι := ι) (C := MC) (U₀ := U₀) (U₁ := U₁) (hC_gap := by exact hC_gap)
    (hR_star_card := hR_star_card)).2.2
  have hD_card_le_e : #(disagreementSet U₀ U₁ V₀ V₁) ≤ e :=
    hDisagreeementCard_Le_e
  -- 3. Show LHS assumption is equal to Δ₀(U_comb, V_constructed) ≤ e
  set V_rowwise := finMapTwoWords V₀.val V₁.val
  set V_colwise := ⋈| V_rowwise
  have h_LHS_eq_dist : (disagreementSet U₀ U₁ V₀ V₁).card = Δ₀(U_colwise, V_colwise) := by
    unfold disagreementSet U_colwise V_colwise
    unfold Interleavable.interleave U_rowwise V_rowwise hammingDist Finset.filter
    congr 1
    simp only [ne_eq]
    congr 1
    congr 1
    funext colIdx
    simp only [eq_iff_iff]
    constructor
    · intro hleft
      simp only at hleft ⊢
      by_contra h_fun_eq
      rw [funext_iff] at h_fun_eq
      by_cases h_left_1: ¬U₀ colIdx = V₀.val colIdx
      · simp only [h_left_1, not_false_eq_true, true_or] at hleft
        have h_U₀_eq_V₀ := h_fun_eq 0
        simp only at h_U₀_eq_V₀
        exact h_left_1 h_U₀_eq_V₀
      · simp only [h_left_1, false_or] at hleft
        have h_U₁_eq_V₁ := h_fun_eq 1
        simp only at h_U₁_eq_V₁
        exact h_left_1 fun a ↦ hleft h_U₁_eq_V₁
    · intro h_fun_ne
      rw [funext_iff] at h_fun_ne
      rw [not_forall] at h_fun_ne
      rcases h_fun_ne with ⟨i_fin2, h_fun_ne_i⟩
      fin_cases i_fin2
      · simp only at h_fun_ne_i
        left
        exact h_fun_ne_i
      · simp only at h_fun_ne_i
        right
        exact h_fun_ne_i
  -- Our assumption `h_LHS` is now: Δ₀(U_comb, V_constructed) ≤ e
  simp_rw [h_LHS_eq_dist] at hD_card_le_e
  -- 4. Prove the RHS: Δ₀(U_comb, C_m_2) ≤ e
  rw [jointProximityNat]
  rw [Code.closeToCode_iff_closeToCodeword_of_minDist]
  -- ⊢ ∃ v ∈ ↑(C ^⋈ (Fin 2) ^⋈ (Fin m)),
  -- Δ₀(⋈|finMapTwoWords U₀ U₁, v) ≤ e
  use V_colwise
  constructor
  · rw [mem_interleavedCode_iff]
    intro k
    match k with
    | ⟨0, _⟩ => exact V₀.property
    | ⟨1, _⟩ => exact V₁.property
  · exact hD_card_le_e

omit [Nonempty ι] [NoZeroDivisors F] [DecidableEq F] [Fintype A] [Module.Free F A]
[Nontrivial ↥MC] in
/-- **Lemma 3.3 (Part 1): Bound on agreeing cells outside D**
    The set of agreeing cells `(r, j)` where `j ∉ D` is exactly the
    Cartesian product of `R*` and `Dᶜ` (the columns not in D).
-/
lemma card_agreeing_cells_notin_D {U₀ U₁ : InterleavedWord A (Fin m) ι} {V₀ V₁ : MC^⋈(Fin m)}
    {e : ℕ} (D : Finset ι)
    (h_D_def : D = disagreementSet U₀ U₁ V₀.val V₁.val) :
    (R_star_star_filter_columns_not_in_D MC U₀ U₁ V₀ V₁ e D).card
    = (R_star (A := A) (F := F) (ι := ι) (C := MC) (e := e) U₀ U₁).card
      * (Fintype.card ι - D.card) := by
  stop
  classical
  let n := Fintype.card ι
  let D_compl := Finset.univ \ D
-- Define local abbreviations
  let n := Fintype.card ι
  let D_compl := Finset.univ \ D
  let R_s := R_star (F := F) (A := A) (ι := ι) (C := MC) (e := e) U₀ U₁
  let R_ss_not_D := R_star_star_filter_columns_not_in_D MC U₀ U₁ V₀ V₁ e D
  -- 1. Prove that R_ss_not_D is equal to the product R_s ×ˢ D_compl
  have h_set_eq : R_ss_not_D = R_s ×ˢ D_compl := by
    -- We prove equality by showing element-wise equivalence
    ext p
    rcases p with ⟨r, j⟩
    -- Unfold all definitions
    simp only [R_star_star_filter_columns_not_in_D, R_star_star, mem_filter, mem_product, mem_univ,
      and_true, mem_sdiff, true_and, and_congr_left_iff, and_iff_left_iff_imp, R_ss_not_D, R_s,
      D_compl]
    intro j_memD r_mem_Rstar
    -- 1. Unfold the definition of `j ∉ D` to get the core equalities.
    have h_agree_at_j : U₀ j = V₀.val j ∧ U₁ j = V₁.val j := by
      -- Use the hypothesis `h_D_def` from the outer lemma
      simp only [h_D_def, disagreementSet, Finset.mem_filter, Finset.mem_univ, true_and,
                not_or, not_not] at j_memD
      -- j_memD is now `U₀ j = V₀.val j ∧ U₁ j = V₁.val j`
      exact j_memD
    -- 2. Unfold the goal (the affineLineEvaluation)
    unfold affineLineEvaluation
    simp only [Pi.add_apply, Pi.smul_apply]
    -- ⊢ (1 - r) • U₀ j + r • U₁ j = (1 - r) • ↑V₀ j + r • ↑V₁ j
    -- 3. Rewrite the goal using the equalities from h_agree_at_j
    rw [h_agree_at_j.1] -- Replaces U₀ j with V₀.val j
    rw [h_agree_at_j.2] -- Replaces U₁ j with V₁.val j
  have h_set_card_eq : R_ss_not_D.card = R_s.card * D_compl.card := by
    rw [h_set_eq]
    simp only [card_product]
  -- 2. Now calculate the cardinality using the set equality
  rw [h_set_card_eq]
  rw [Finset.card_sdiff (Finset.subset_univ D)]
  rw [Finset.card_univ]

omit [Nonempty ι] [DecidableEq F] [Fintype A] [Nontrivial ↥MC] in
/-- **Lemma 3.3 (Part 2): Bound on agreeing cells inside D**
For any column `j` that *is* in the disagreement set `D`, there is at most one
parameter `r` in `R*` such that the columns `Uᵣ j` and `Vᵣ j` agree.
Therefore, the total number of agreeing cells `(r, j)` with `j ∈ D` is at most `|D|`.
-/
lemma card_agreeing_cells_in_D_le
    {U₀ U₁ : InterleavedWord A (Fin m) ι}
    {V₀ V₁ : MC^⋈(Fin m)}
    {e : ℕ} (D : Finset ι)
    (h_D_def : D = disagreementSet U₀ U₁ V₀.val V₁.val) :
    (R_star_star_filter_columns_in_D MC U₀ U₁ V₀ V₁ e D).card ≤ D.card := by
  classical
  -- Let R_ss_in_D be the set of agreeing cells (r, j) with j ∈ D
  let R_ss_in_D := R_star_star_filter_columns_in_D MC U₀ U₁ V₀ V₁ e D
  -- 1. The card of a set is bounded by the sum of the cardinalities of its fibers
  --    (We are "slicing" the set by its second component, the column index j)
  have h_card_eq_sum_fibers : R_ss_in_D.card
    = ∑ j ∈ D, ((R_ss_in_D.filter (fun p => p.2 = j)).card) := by
      apply Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := D)
      -- We must show that every element in R_ss_in_D maps to an element in D
      -- Goal: `Set.MapsTo (Prod.snd) R_ss_in_D D`, this means: `∀ p ∈ R_ss_in_D, p.2 ∈ D`
      intro p hp_in_Rss
      -- This is true by the very definition of R_ss_in_D!
      unfold R_ss_in_D R_star_star_filter_columns_in_D at hp_in_Rss
      simp only [coe_filter, Set.mem_setOf_eq] at hp_in_Rss
      -- hp_in_Rss is `p ∈ R_star_star ∧ p.2 ∈ D`
      exact hp_in_Rss.2
  -- 2. We prove that each fiber (for a fixed j) has cardinality at most 1
  have h_fibers_le_one_sum :
    ∑ j ∈ D, ((R_ss_in_D.filter (fun p => p.2 = j)).card) ≤ ∑ j ∈ D, 1 := by
    apply Finset.sum_le_sum
    intro j hj_in_D -- For any column j that is in the disagreement set D
    -- Goal for this term: (R_ss_in_D.filter (fun p => p.2 = j)).card ≤ 1
    apply Finset.card_le_one_iff.mpr
    -- Goal: ∀ p1 p2, p1 ∈ ... → p2 ∈ ... → p1 = p2
    -- We MUST introduce two elements (p1, p2) and their two proofs (hp1, hp2)
    intro p1 p2 hp1 hp2
    rcases p1 with ⟨r₁, j₁⟩
    rcases p2 with ⟨r₂, j₂⟩
    -- ⊢ (r₁, j₁) = (r₂, j₂)
    apply Prod.ext
    · -- Goal 1: Prove r₁ = r₂: We need to extract the agreement properties from the hypotheses
      have h1_in_Rss : (r₁, j₁) ∈ R_ss_in_D := (Finset.mem_filter.mp hp1).1
      have h1_j_eq : j₁ = j := (Finset.mem_filter.mp hp1).2
      have h2_in_Rss : (r₂, j₂) ∈ R_ss_in_D := (Finset.mem_filter.mp hp2).1
      have h2_j_eq : j₂ = j := (Finset.mem_filter.mp hp2).2
      -- Get the agreement properties from R_ss_in_D
      have h1_agree : affineLineEvaluation U₀ U₁ r₁ j = affineLineEvaluation (↑V₀) (↑V₁) r₁ j := by
        -- Unfold R_ss_in_D and R_star_star to find the agreement
        unfold R_ss_in_D R_star_star_filter_columns_in_D at h1_in_Rss
        simp only [R_star_star, mem_filter, mem_product, mem_univ, and_true] at h1_in_Rss
        rw [← h1_j_eq] -- Use j₁ = j
        exact h1_in_Rss.1.2
      have h2_agree : affineLineEvaluation U₀ U₁ r₂ j = affineLineEvaluation (↑V₀) (↑V₁) r₂ j := by
        unfold R_ss_in_D R_star_star_filter_columns_in_D at h2_in_Rss
        simp only [R_star_star, mem_filter, mem_product, mem_univ, and_true] at h2_in_Rss
        rw [← h2_j_eq] -- Use j₂ = j
        exact h2_in_Rss.1.2 -- This is the `Uᵣ j = Vᵣ j` part
      -- linear algebra argument
      let W₀ := U₀ j - V₀.val j
      let W₁ := U₁ j - V₁.val j
      have h_eq_r1 : W₀ + r₁ • (W₁ - W₀) = 0 := by
        unfold affineLineEvaluation at h1_agree
        rw [← sub_eq_zero] at h1_agree
        rw [← h1_agree]
        unfold W₀ W₁
        -- ⊢ U₀ j - ↑V₀ j + r₁ • (U₁ j - ↑V₁ j - (U₀ j - ↑V₀ j)) = ((1 - r₁) • U₀ + r₁ • U₁) j
          -- - ((1 - r₁) • ↑V₀ + r₁ • ↑V₁) j
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [sub_smul, sub_smul]; rw [smul_sub, smul_sub, smul_sub]
        simp only [one_smul]
        abel_nf
      have h_eq_r2 : W₀ + r₂ • (W₁ - W₀) = 0 := by
        unfold affineLineEvaluation at h2_agree
        rw [← sub_eq_zero] at h2_agree
        rw [← h2_agree]
        unfold W₀ W₁
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [sub_smul, sub_smul]; rw [smul_sub, smul_sub, smul_sub]
        simp only [one_smul]
        abel_nf
      have h_j_in_D : W₀ ≠ 0 ∨ W₁ ≠ 0 := by
        simp only [h_D_def, disagreementSet, ne_eq, mem_filter, mem_univ, true_and] at hj_in_D
        by_cases h₀_ne: ¬U₀ j = V₀.val j
        · left
          dsimp only [W₀]
          exact sub_ne_zero_of_ne h₀_ne
        · simp only [h₀_ne, false_or] at hj_in_D
          right
          dsimp only [W₁]
          exact sub_ne_zero_of_ne hj_in_D
      by_cases h_diff_eq_zero : W₁ - W₀ = 0
      · -- Case 1: W₁ - W₀ = 0
        have h_W₀_zero : W₀ = 0 := by rwa [h_diff_eq_zero, smul_zero, add_zero] at h_eq_r1
        have h_W₁_zero : W₁ = 0 := by
          rw [←h_diff_eq_zero, h_W₀_zero];
          exact Eq.symm (sub_zero W₁)
        by_cases h_W₀_ne_zero : W₀ ≠ 0
        · exact False.elim (h_W₀_ne_zero h_W₀_zero)
        · have h_W₁_ne_0 : W₁ ≠ 0 := by
            exact h_j_in_D.resolve_left h_W₀_ne_zero
          exact False.elim (h_W₀_ne_zero fun a ↦ h_W₁_ne_0 h_W₁_zero)
      · -- Case 2: W₁ - W₀ ≠ 0 (this is `h_diff_eq_zero : ¬W₁ - W₀ = 0`)
        -- 2 hypotheses: h_eq_r1 : W₀ + r₁ • (W₁ - W₀) = 0, h_eq_r2 : W₀ + r₂ • (W₁ - W₀) = 0
        have h_eq_both : W₀ + r₁ • (W₁ - W₀) = W₀ + r₂ • (W₁ - W₀) := by
          rw [h_eq_r1, h_eq_r2]
        have h_smul_eq : r₁ • (W₁ - W₀) = r₂ • (W₁ - W₀) :=
          (add_right_inj W₀).mp h_eq_both
        have h_sub_smul_eq_zero : (r₁ - r₂) • (W₁ - W₀) = 0 := by
          rw [sub_smul, sub_eq_zero]
          exact h_smul_eq
        rw [smul_eq_zero] at h_sub_smul_eq_zero
        have h_r_sub_eq_zero : r₁ - r₂ = 0 := by
          exact h_sub_smul_eq_zero.resolve_right h_diff_eq_zero
        exact sub_eq_zero.mp h_r_sub_eq_zero
    · -- Goal 2: Prove j₁ = j₂: This follows directly from the fiber proofs
      have h1_j_eq : j₁ = j := (Finset.mem_filter.mp hp1).2
      have h2_j_eq : j₂ = j := (Finset.mem_filter.mp hp2).2
      rw [h1_j_eq, h2_j_eq]
  -- 3. Chain the inequalities: R_ss_in_D.card ≤ (∑ j in D, 1) ≤ D.card
  simp only [sum_const, smul_eq_mul, mul_one] at h_fibers_le_one_sum
  exact le_trans (Nat.le_of_eq h_card_eq_sum_fibers) h_fibers_le_one_sum

omit [Fintype A] in
/-- **Lemma 3.3 (DG25): Upper Bound on R** Cardinality**
Context:
- `U₀, U₁` are columnWise words; `V₀, V₁` are columnWise codewords
- `R_star` is the set where affine combinations `Uᵣ` are close to `C^m`.
- `D` is the set of columns where `U₀` differs from `V₀` OR `U₁` differs from `V₁`.
- `R_star_star` is the set of pairs `(r, j)` where `r ∈ R_star` and column `j` of `Uᵣ`
equals column `j` of `Vᵣ` (set of `agreeing linearComb columns`)
Statement: The number of agreeing column pairs `(r, j)` is bounded by the number
of parameters in `R_star` times the number of columns *outside* `D`, plus the
number of columns *inside* `D`.
`|R**| ≤ |R*| * (n - |D|) + |D|`
-/
lemma R_star_star_upper_bound
    (U₀ U₁ : InterleavedWord A (Fin m) ι)
    (hC_gap : e_ε_correlatedAgreementAffineLinesNat (A := A) (ι := ι) (C := MC) e ε)
    (hR_star_card : (R_star (A := A) (F := F) (ι := ι) (C := MC)
      (m := m) (e := e) U₀ U₁).card > ε) :
      let ⟨V₀, V₁, _⟩ := constructInterleavedCodewordsAndRowWiseCA (F := F)
        (A := A) (ι := ι) (C := MC) (U₀ := U₀) (U₁ := U₁) (hC_gap := by exact hC_gap)
        (hR_star_card := hR_star_card)
      let D : Finset ι := disagreementSet U₀ U₁ V₀ V₁
      (R_star_star (A := A) (ι := ι) (F := F) (C := MC) (m := m) (e := e) U₀ U₁ V₀ V₁).card
        ≤ (R_star (A := A) (ι := ι) (F := F) (C := MC) (m := m) (e := e) U₀ U₁).card *
          (Fintype.card ι - D.card) + D.card
      := by
  classical -- Use classical logic for decidable predicates on filters
  -- 1. Define local variables
  let ⟨V₀, V₁, _⟩ := constructInterleavedCodewordsAndRowWiseCA (F := F)
        (A := A) (ι := ι) (C := MC) (U₀ := U₀) (U₁ := U₁) (hC_gap := by exact hC_gap)
        (hR_star_card := hR_star_card)
  let n := Fintype.card ι
  let R_s := R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁
  let D := disagreementSet U₀ U₁ V₀.val V₁.val
  set R_ss := R_star_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁ V₀.val V₁.val
  set R_ss_in_D    := (R_star_star_filter_columns_in_D MC U₀ U₁ V₀ V₁ e D)
  set R_ss_notin_D := (R_star_star_filter_columns_not_in_D MC U₀ U₁ V₀ V₁ e D)

  -- 3. The card of R_ss is the sum of the cards of the disjoint partition.
  have h_card_split : R_ss.card = R_ss_notin_D.card + R_ss_in_D.card := by
    rw [← Finset.card_union_of_disjoint]
    congr
    · exact R_star_star_eq_union MC U₀ U₁ V₀ V₁ e D
    · exact Disjoint.symm (disjoint_R_star_star_filter_columns_in_D_not_in_D MC U₀ U₁ V₀ V₁ e D)

  simp only [ge_iff_le]
  -- 4. Apply the split
  rw [h_card_split]
  -- Goal: R_ss_notin_D.card + R_ss_in_D.card ≤ R_s.card * (n - D.card) + D.card

  -- 5. Apply the two new lemmas
  apply add_le_add
  · -- Prove R_ss_notin_D.card ≤ R_s.card * (n - D.card)
    have h_notin_D := card_agreeing_cells_notin_D MC (m := m) (e := e) (U₀ := U₀) (U₁ := U₁)
      (V₀ := V₀) (V₁ := V₁) D (by rfl)
    exact Nat.le_of_eq h_notin_D
  · -- Prove R_ss_in_D.card ≤ D.card
    have h_in_D := card_agreeing_cells_in_D_le MC (m := m) (e := e) (U₀ := U₀) (U₁ := U₁)
      (V₀ := V₀) (V₁ := V₁) D (by rfl)
    exact h_in_D

omit [NoZeroDivisors F] [DecidableEq F] [Fintype A] [Module.Free F A] in
/-- **Lemma 3.4 (DG25): Lower Bound on R** Cardinality**
Context:
- Same as Lemma 3.2, including hypotheses on `C`, `e`, `V₀`, `V₁`, `R_star`.
- `R_star_star` is the set of pairs `(r, j)` where `r ∈ R_star` and column `j` of `Uᵣ`
equals column `j` of `Vᵣ`.
Statement: The number of agreeing column pairs `(r, j)` is at least the number
of parameters in `R_star` times the number of columns guaranteed to agree (`n - e`)
for each `r` (using Lemma 3.2), i.e. `|R**| ≥ (n - e) * |R*|`
-/
lemma R_star_star_lower_bound
    (U₀ U₁ : InterleavedWord A (Fin m) ι)
    (he : e ≤ (Code.uniqueDecodingRadius (F := A) (ι := ι) (C := MC)))
    (hC_gap : e_ε_correlatedAgreementAffineLinesNat (A := A) (ι := ι) (C := MC) e ε)
    (hR_star_card : (R_star (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card > ε) :
      let ⟨V₀, V₁, _⟩ := constructInterleavedCodewordsAndRowWiseCA (F := F)
        (A := A) (ι := ι) (C := MC) (U₀ := U₀) (U₁ := U₁) (hC_gap := by exact hC_gap)
        (hR_star_card := hR_star_card)
      (R_star_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁ V₀ V₁).card
        >= (Fintype.card ι - e) *
          (R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card := by
  classical
  /- DG25 Proof Sketch:
     Sum over r ∈ R*. For each such r:
     Apply Lemma 3.2 (using h_agree, he_udr, hR_star): Δ^m(Uᵣ, Vᵣ) ≤ e.
     By definition of Δ^m, this means Uᵣ and Vᵣ agree on ≥ n - e columns j.
     So, row r contributes ≥ n - e to |R**|.
     Summing gives |R**| ≥ |R*| * (n - e).
  -/
  -- 1. Define local variables
  let V₀ := (constructInterleavedCodewordsAndRowWiseCA (F := F)
        (A := A) (ι := ι) (C := MC) (U₀ := U₀) (U₁ := U₁) (hC_gap := by exact hC_gap)
        (hR_star_card := hR_star_card)).1
  let V₁ := (constructInterleavedCodewordsAndRowWiseCA (F := F)
        (A := A) (ι := ι) (C := MC) (U₀ := U₀) (U₁ := U₁) (hC_gap := by exact hC_gap)
        (hR_star_card := hR_star_card)).2.1
  let n := Fintype.card ι
  let R_s := R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁
  let R_ss := R_star_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁ V₀.val V₁.val

  simp only [ge_iff_le]
  simp only [R_star_star]
  rw [Finset.card_filter]
  rw [Finset.sum_product]

  have h_card_ge_per_r: ∀ r : R_star (A := A) (F := F) (ι := ι) (C := MC)
    (e := e) U₀ U₁, (Fintype.card ι - e) ≤ (∑ j, if
      affineLineEvaluation (F := F) U₀ U₁ (r, j).1 (r, j).2
      = affineLineEvaluation (F := F) V₀.val V₁.val (r, j).1 (r, j).2 then 1 else 0) := by
    intro r
      -- Let Uᵣ and Vᵣ be the affine points for this r
    let Uᵣ := affineLineEvaluation (F := F) U₀ U₁ r
    let Vᵣ := affineLineEvaluation (F := F) V₀.val V₁.val r

    -- The sum is the number of agreeing columns, which is `n - hammingDist(Uᵣ, Vᵣ)`
    have h_sum_eq_agreeing_cols :
        (∑ j, if Uᵣ j = Vᵣ j then 1 else 0) = n - Δ₀(Uᵣ, Vᵣ) := by
      -- 1. `∑ j, if P j then 1 else 0` is the definition of `(Finset.filter P Finset.univ).card`
      rw [Finset.sum_boole]

      -- 2. Unfold the notation
      -- `n` is `(Finset.univ : Finset ι).card`
      dsimp only [Nat.cast_id, n]
      rw [←Finset.card_univ]
      -- `Δ₀(Uᵣ, Vᵣ)` is `hammingDist Uᵣ Vᵣ`
      unfold hammingDist
      apply Nat.eq_sub_of_add_eq
      rw [Finset.card_filter, Finset.card_filter]

      change ((∑ i, if Uᵣ i = Vᵣ i then 1 else 0) + ∑ i, if Uᵣ i ≠ Vᵣ i then 1 else 0) = #univ
      rw [← Finset.sum_add_distrib]
      simp_rw [ne_eq]
      -- simp will solve the `ite` logic and apply `sum_const_one`
      simp only [ite_not, card_univ]
      have h_inner : ∀ x, ((if Uᵣ x = Vᵣ x then 1 else 0) + if Uᵣ x = Vᵣ x then 0 else 1) = 1
        := fun x => by
        by_cases h : Uᵣ x = Vᵣ x
        · simp only [h, if_true]
        · simp only [h, if_false]
      simp_rw [h_inner]
      simp only [sum_const, card_univ, smul_eq_mul, mul_one]
    rw [h_sum_eq_agreeing_cols]
    -- Goal: n - e ≤ n - hammingDist Uᵣ Vᵣ
    -- This is equivalent to `hammingDist Uᵣ Vᵣ ≤ e`
    -- We use `Nat.sub_le_sub_left_iff` which requires `hammingDist Uᵣ Vᵣ ≤ n`
    have h_dist_le_n : hammingDist Uᵣ Vᵣ ≤ e := by
    -- This is exactly the conclusion of Lemma 3.2 (affineWord_close_to_affineInterleavedCodeword)
      let res := affineWord_close_to_affineInterleavedCodeword (U₀ := U₀) (U₁ := U₁)
        (he := he) (hC_gap := by exact hC_gap) (hR_star_card := hR_star_card) (r := r)
      simp only [Fin.isValue, eq_mpr_eq_cast, cast_eq, ENNReal.coe_natCast,
        Lean.Elab.WF.paramLet] at res
      exact res
    exact Nat.sub_le_sub_left h_dist_le_n (Fintype.card ι)

  have h_left : (Fintype.card ι - e) * #(R_star (A := A) (F := F) (ι := ι) (C := MC) (e := e) U₀ U₁)
    = ∑ r ∈ R_star (A := A) (F := F) (ι := ι) (C := MC) (e := e) U₀ U₁, (Fintype.card ι - e) := by
    rw [Finset.sum_const]
    simp only [smul_eq_mul]
    exact Nat.mul_comm (Fintype.card ι - e) #(R_star (A := A) (F := F) (ι := ι) (C := MC) U₀ U₁)
  rw [h_left]
  apply Finset.sum_le_sum
  intro r hr_mem
  exact h_card_ge_per_r (Subtype.mk r hr_mem)

omit [NoZeroDivisors F] [Module.Free F A] [Nonempty ι] [Fintype A] [DecidableEq F]
  [DecidableEq ι] [Nontrivial ↥MC] in
lemma probShadedAffineCombInterleavedCodeword_gt_threshold_iff
  (U₀ U₁ : InterleavedWord A (Fin m) ι) :
  Pr_{ let r ←$ᵖ F }[
    Δ₀(affineLineEvaluation (F := F) U₀ U₁ r,
      MC ^⋈ (Fin m)) ≤ e ] > ((ε: ℝ≥0) / (Fintype.card F : ℝ≥0))
  ↔ (R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card > ε := by
  conv_lhs =>
    rw [prob_uniform_eq_card_filter_div_card]
    rw [gt_iff_lt]
    simp only [ENNReal.coe_natCast]
    simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
      ENNReal.natCast_ne_top, ENNReal.div_lt_div_iff_left (c := ((Fintype.card F) : ENNReal)),
      Nat.cast_lt]
    rw [←gt_iff_lt]
  rfl

/--
This lemma proves the final algebraic step in the DG25 Theorem 3.1 proof.
It shows that if `R > e + 1`, then `e * (R / (R - 1)) < e + 1`.

The intuition is that the fraction `R / (R - 1)` is always greater than 1,
but as `R` gets larger, it gets closer to 1. The hypothesis `R > e + 1`
provides a strong enough bound to ensure the product `e * (fraction)`
doesn't "overshoot" `e + 1`.
-/
lemma e_mul_R_div_R_sub_1_lt_e_add_1_real {e R : ℕ} (hR_gt_e_add_1 : e + 1 < R) :
    ((e : ℝ) * (R : ℝ)) / ((R : ℝ) - 1) < (e : ℝ) + 1 := by
  have hR_gt_one : R > 1 := by omega
  have hR_Real_gt_one : (R : ℝ) > 1 := by exact Nat.cast_gt_Real_one R hR_gt_one
  have h_R_gt_e_add_1_real : ((e + 1) : ℝ) < (R : ℝ) := by
    rw [←Nat.cast_add_one (n := e)]
    apply Nat.cast_lt (α := ℝ) (m := e + 1) (n := R).mpr hR_gt_e_add_1
  have h_denom_pos : (R : ℝ) - 1 > 0 := by
    -- `linarith` solves this from the hypothesis
    linarith [hR_Real_gt_one]
  -- 3. Use `div_lt_iff` to multiply the denominator across
  -- This is the `ℝ` lemma for `a / b < c ↔ a < c * b` (since `b > 0`)
  rw [div_lt_iff₀ (hc := h_denom_pos)]
  -- Goal: ⊢ ↑e * ↑R < (↑e + 1) * (↑R - 1)
  -- 4. THIS IS THE KEY STEP
  -- Don't use `rw`. `linarith` will:
  --   a) Expand the RHS to: `e*R - e + R - 1`
  --   b) See the goal: `e*R < e*R - e + R - 1`
  --   c) Cancel `e*R` from both sides: `0 < R - e - 1`
  --   d) Rearrange: `e + 1 < R`
  --   e) See this is exactly your hypothesis `h_R_gt_e_add_1_real`
  linarith [h_R_gt_e_add_1_real]

open Classical in
omit [Fintype A] in
/- **Theorem 3.1**. If `C` features proximity gaps for affine lines with respect to the
proximity parameter `e ∈ {0, ..., ⌊(d-1)/2⌋}` and the false witness bound
`ε ≥ e+1`, then, for each `m > 1`, `C`'s interleaving `C^m` also does.
-/
theorem affine_gaps_lifted_to_interleaved_codes {m : ℕ} {ε : ℕ}
    {e : ℕ} (he : e ≤ (Code.uniqueDecodingRadius (F := A) (ι := ι) (C := MC))) (hε : ε ≥ e + 1)
    (hProximityGapAffineLines :
      e_ε_correlatedAgreementAffineLinesNat (F := F) (C := (MC : Set (ι → A))) (e := e) (ε := ε)) :
    e_ε_correlatedAgreementAffineLinesNat (ι := ι) (F := F) (A := InterleavedSymbol A (Fin m))
      (C := ((MC^⋈(Fin m)) : Set (ι → (InterleavedSymbol A (Fin m))))) (e := e) (ε := ε) := by
  -- 1. Unfold the definition of e_ε_correlatedAgreementAffineLinesNat for the interleaved code C^m.
  -- We must show that for any two words U₀, U₁, if the set of "close" affine
  -- combinations (R*) is large, then U₀ and U₁ have correlated agreement with C^m.
  intro U₀ U₁ hR_prob_shaded_affine_comb_gt_threshold
  -- `⊢ ModuleCode.correlatedAgreement₂ U₀ U₁ ↑e, i.e. |D| ≤ e`

  -- 2. Assume the hypothesis: |R*| > ε
  let hR_star_card_gt_ε := probShadedAffineCombInterleavedCodeword_gt_threshold_iff
    (F := F) (A := A) (ι := ι) (MC := MC) (m := m)
    (U₀ := U₀) (U₁ := U₁) (ε := ε) (e := e).mp hR_prob_shaded_affine_comb_gt_threshold

  have hR_star_card_gt1 : (R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m)
    (e := e) U₀ U₁).card > 1 := by omega  -- |R*| > ε ≥ e + 1 ≥ 1
  have hR_star_card_gt1_Real : ((R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m)
    (e := e) U₀ U₁).card : ℝ) > 1 := by
    exact Nat.cast_gt_Real_one (R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m)
      (e := e) U₀ U₁).card hR_star_card_gt1

  -- 3. Use the hypothesis on the base code C (hProximityGapAffineLines)
  -- and the fact that |R*| > ε to construct the candidate
  -- interleaved codewords V₀ and V₁ in C^m.
  set V := constructInterleavedCodewordsAndRowWiseCA (F := F) (A := A) (ι := ι) (C := MC) (m := m)
    (U₀ := U₀) (U₁ := U₁)
    hProximityGapAffineLines (hR_star_card_gt_ε)
  let V₀ := V.1; let V₁ := V.2.1; let h_row_agreement := V.2.2
  set D := disagreementSet U₀ U₁ V₀ V₁
  have h_D_card_le_n : D.card ≤ Fintype.card ι := by
    dsimp only [disagreementSet, ne_eq, D]
    let res := Finset.card_filter_le (s := Finset.univ (α := ι))
      (p := fun colIdx => ¬U₀ colIdx = V₀.val colIdx ∨ ¬U₁ colIdx = V₁.val colIdx)
    rw [Finset.card_univ] at res
    convert res
  have h_D_le_D_mul_R_star_card: D.card ≤ D.card * (R_star (A := A) (F := F) (ι := ι)
    (C := MC) (m := m) (e := e) U₀ U₁).card := by
    conv_lhs => rw [←Nat.mul_one D.card]
    apply Nat.mul_le_mul_left; exact Nat.one_le_of_lt hR_star_card_gt_ε

  -- `e · |R*| ≥ |D| · (|R*| - 1)
  have h_e_mul_Rstar_card_ge:
    e * (R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card
      ≥ D.card * (R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card
        - D.card := by
    -- This comes from lemma 3.3: |R**| ≤ |R*|(n - |D|) + |D|
    -- and lemma 3.4: |R**| ≥ (n - e)|R*|
    have h_lemma_3_3 := R_star_star_upper_bound (MC := MC) (ε := ε) (m := m) (e := e)
      U₀ U₁ hProximityGapAffineLines hR_star_card_gt_ε
    have h_lemma_3_4 := R_star_star_lower_bound (MC := MC) (ε := ε) (m := m) (e := e)
      (U₀ := U₀) (U₁ := U₁) (he := he) hProximityGapAffineLines hR_star_card_gt_ε
    simp only [ge_iff_le] at h_lemma_3_3 h_lemma_3_4

    set n := Fintype.card ι
    -- So (n - e)|R*| ≤ |R**| ≤ |R*|(n - |D|) + |D|
    have h_le_trans := le_trans h_lemma_3_4 h_lemma_3_3
    -- ↔ n * |R*| - e * |R*| ≤ n * |R*| - |D| * |R*| + |D|
    rw [Nat.sub_mul (n := n) (m := e), Nat.mul_sub (n := (R_star (A := A) (F := F)
      (ι := ι) (C := MC) U₀ U₁).card), Nat.mul_comm (n := (R_star (A := A) (F := F) (ι := ι)
        (C := MC) U₀ U₁).card) (m := D.card)] at h_le_trans
    -- ↔ e * |R*| ≥ |D| * (|R*| - 1) (Q.E.D)
    have h_le_trans: n * #(R_star (A := A) (F := F) (ι := ι) (C := MC) (e := e) U₀ U₁)
      - e * #(R_star (A := A) (F := F) (ι := ι) (C := MC) (e := e) U₀ U₁)
      ≤ n * #(R_star (A := A) (F := F) (ι := ι) (C := MC) (e := e) U₀ U₁)
        - #D * #(R_star (A := A) (F := F) (ι := ι) (C := MC) (e := e) U₀ U₁) + #D := by
      conv_rhs =>
        rw [Nat.mul_comm n (#(R_star (A := A) (F := F) (ι := ι) (C := MC) (e := e) U₀ U₁))]
      exact h_le_trans
    -- conv_rhs at h_le_trans => enter [2]; rw [←Nat.mul_one #D]
    rw [Nat.sub_add_eq_sub_sub_rev (a := n * #(R_star (A := A) (F := F) (ι := ι) (C := MC) U₀ U₁))
      (b :=  #D * #(R_star (A := A) (F := F) (ι := ι) (C := MC) U₀ U₁)) (c := #D)
        (h1 := h_D_le_D_mul_R_star_card)
      (h2 := Nat.mul_le_mul_right (#(R_star (A := A) (F := F) (ι := ι) (C := MC) U₀ U₁))
        h_D_card_le_n)] at h_le_trans
    have h_le: #D * #(R_star (A := A) (F := F) (ι := ι) (C := MC) (e := e) U₀ U₁) - #D
      ≤ n * #(R_star (A := A) (F := F) (ι := ι) (C := MC) (e := e) U₀ U₁) := by
      apply Nat.sub_le_of_le_add; apply le_add_of_le_left;
      exact
        Nat.mul_le_mul_right (#(R_star (A := A) (F := F) (ι := ι) (C := MC) U₀ U₁)) h_D_card_le_n
    rw [Nat.sub_le_sub_iff_left (k := n * #(R_star (A := A) (F := F) (ι := ι) (C := MC) U₀ U₁))
      (h := h_le)] at h_le_trans
    exact h_le_trans

  have h_e_mul_Rstar_card_ge_Real: (e : ℝ) * (R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m)
    (e := e) U₀ U₁).card ≥ D.card * (R_star (A := A) (F := F) (ι := ι) (C := MC)
      (m := m) (e := e) U₀ U₁).card - D.card := by
    rw [←Nat.cast_mul, ←Nat.cast_mul, ←Nat.cast_sub (h := h_D_le_D_mul_R_star_card)]
    rw [ge_iff_le]
    rw [Nat.cast_le]
    exact h_e_mul_Rstar_card_ge

  -- `|D| ≤ e * (|R*| / (|R*| - 1))
  have h_D_card_le_e_mul_R_div_R_succ: D.card ≤ e *
    ((R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card : ℝ) /
    ((R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card - 1) := by
    rw [le_div_iff₀ (hc := by rw [sub_pos]; exact hR_star_card_gt1_Real)]
    rw [mul_sub, mul_one]
    exact h_e_mul_Rstar_card_ge_Real

  -- e * (|R*| / (|R*| - 1)) < e + 1 ↔ e * |R*| < e * |R*| - (e + 1) + |R*|
    -- ↔ 0 < |R*| - (e + 1) ↔ e + 1 < |R*|
  have h_e_mul_R_div_R_succ_lt: e * ((R_star (A := A) (F := F) (ι := ι) (C := MC)
    (m := m) (e := e) U₀ U₁).card : ℝ)
    / ((R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card - 1) < e + 1 := by
    exact e_mul_R_div_R_sub_1_lt_e_add_1_real (e := e) (R := (R_star (A := A)
      (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card) (hR_gt_e_add_1 := by omega)

  have h_D_card_le_e: D.card ≤ e := by
    apply Nat.le_of_lt_succ;
    have res := lt_of_le_of_lt (a := (#D : ℝ))
      (b := e * ((R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card : ℝ)
        / ((R_star (A := A) (F := F) (ι := ι) (C := MC) (m := m) (e := e) U₀ U₁).card - 1))
        (c := (e + 1 : ℝ)) (hab := h_D_card_le_e_mul_R_div_R_succ) (hbc := h_e_mul_R_div_R_succ_lt)
    rw [←Nat.cast_add_one, Nat.cast_lt] at res
    exact res

  dsimp only [D] at h_D_card_le_e
  exact (D_card_le_e_implies_interleaved_correlatedAgreement₂ (MC := MC)
    (m := m) (e := e) (ε := ε) U₀ U₁ hProximityGapAffineLines hR_star_card_gt_ε) (h_D_card_le_e)

/-- For each `r_{ϑ-1} ∈ 𝔽_q`, we abbreviate:
`p(r_{ϑ-1}) := Pr_{(r_0, ..., r_{ϑ-2}) ∈ 𝔽_q^{ϑ-1}} [`
  `d([⊗_{i=0}^{ϑ-2}(1-r_i, r_i)] · [(1-r_{ϑ-1}) · U₀ + r_{ϑ-1} · U₁], C) ≤ e]`
We define `R* := {r_{ϑ-1} ∈ 𝔽_q | p(r_{ϑ-1}) > (ϑ-1) · ε/q}`. We note that
`R*` is precisely the set of parameters `r_{ϑ-1} ∈ 𝔽_q` for which the half-length
matrix `(1-r_{ϑ-1}) · U₀ + r_{ϑ-1} · U₁` fulfills the inductive hypothesis (that is,
the hypothesis of Definition 2.3, with respect to the smaller list size parameter) -/
def R_star_tensor_filter (U₀ U₁ : (Fin (2 ^ m)) → Word A ι) (r_affine_combine : F) : Prop :=
  (Pr_{let r ← $ᵖ (Fin m → F)}[ -- This syntax only works with (A : Type 0)
    Δ₀(multilinearCombine_affineLineEvaluation (U₀ := U₀) (U₁ := U₁)
      (r := r) (r_affine_combine := r_affine_combine), MC) ≤ e
  ] > (m * ε: ℝ≥0) / (Fintype.card F : ℝ≥0))

open Classical in
def R_star_tensor (U₀ U₁ : (Fin (2 ^ m)) → Word A ι) : Finset F :=
  Finset.filter (fun r_affine_combine : F =>
    R_star_tensor_filter MC (m := m) (e := e) (ε := ε) U₀ U₁ r_affine_combine
  ) Finset.univ

omit [NoZeroDivisors F] [DecidableEq F] [Fintype A] [Module.Free F A] [Nontrivial ↥MC] in
open Classical in
/-- inductively to each such matrix, we conclude that,
for each `r_{ϑ-1} ∈ R*`, `d^{2^{ϑ-1}}((1-r_{ϑ-1}) · U₀ + r_{ϑ-1} · U₁, C^{2^{ϑ-1}}) ≤ e`
-/
lemma correlatedAgreement_of_mem_R_star_tensor
    {ϑ_pred : ℕ}
    (ih : δ_ε_multilinearCorrelatedAgreement_Nat (F := F) (A := A) (ι := ι) (C := MC) (ϑ := ϑ_pred)
      (e := e) (ε := ε))
    (u : Fin (2 ^ (ϑ_pred + 1)) → (Word A ι)) :
    -- This hypothesis comes from the main theorem's inductive step
    let ⟨U₀, U₁⟩ := splitHalfRowWiseInterleavedWords (ϑ := ϑ_pred) u
    ∀ (r : R_star_tensor MC (e := e) (ε := ε) U₀ U₁),
    jointProximityNat (u := affineLineEvaluation U₀ U₁ r.val) (e := e) (C := MC) := by
  -- simp only [Nat.add_one_sub_one, Subtype.forall]
  intro r
  apply ih
  -- ⊢ Pr_{ r ← Fin (ϑ_pred) → F}[ Δ₀(multilinearCombine Uᵣ (r := r), MC) ≤ e ] > (ϑ_pred * ε) / |𝔽|
  -- i.e. these r must satisfy (tensor-folding with the affine random combination)
    -- must be close to individual-row code MC
  set U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ_pred) u).1
  set U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ_pred) u).2

  unfold R_star_tensor at r
  -- Now, just state that the proof is `r.property`
  have hr:  R_star_tensor_filter MC U₀ U₁ ↑r :=
    (Finset.mem_filter (s := Finset.univ (α := F)) (a := r)
      (p := R_star_tensor_filter MC (e := e) (ε := ε) U₀ U₁).mp (coe_mem r)).2
  unfold R_star_tensor_filter at hr
  exact hr

def multilinearCombine_affineComb_split_last_close {ϑ : ℕ}
  (u : WordStack A (Fin (2 ^ (ϑ + 1))) ι) (e : ℕ) (r_last : F) (r_init : Fin (ϑ) → F) : Prop :=
    let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
    let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
    Δ₀(multilinearCombine (F := F) (A := A) (ι := ι)
      (affineLineEvaluation U₀ U₁ r_last) r_init, ↑MC) ≤ (e : ℕ∞)

omit [Nonempty ι] [NoZeroDivisors F] [Fintype A] [Module.Free F A] [Nontrivial ↥MC]
  [DecidableEq ι] in
open Classical in
lemma prob_R_star_gt_threshold
  {ϑ : ℕ}
  (u : WordStack A (Fin (2 ^ (ϑ + 1))) ι) (e : ℕ)
  (hP_multilinearCombine_affine_close_gt :
    Pr_{ let r_last ← $ᵖ F; let r_init ← $ᵖ (Fin (ϑ) → F)}[
      multilinearCombine_affineComb_split_last_close (MC := MC) (u := u) (e := e) r_last r_init]
    > (((Nat.cast (R := ℝ≥0) (ϑ + 1)) * ε : ℝ≥0) / ((Fintype.card F : ℝ≥0) : ℝ≥0))) :
    let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
    let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
    let R_star_set := R_star_tensor MC (e := e) (ε := ε) U₀ U₁
  Pr_{ let r ← $ᵖ F }[ r ∈ R_star_set ] > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
  -- 1. Setup abbreviations for clarity
  set U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
  set U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
  set R_star_set := R_star_tensor MC (m := ϑ) (e := e) (ε := ε) U₀ U₁

  let q := (Fintype.card F : ENNReal)
  let ε_enn := (ε : ENNReal)
  let ϑ_enn := (ϑ : ENNReal)
  have hq_ne_zero : q ≠ 0 := Ne.symm (NeZero.ne' q)
  --  ENNReal.natCast_ne_zero.mpr Fintype.card_ne_zero
  have hq_ne_top : q ≠ ⊤ := ENNReal.natCast_ne_top (Fintype.card F)
  have h_finite : (↑(Nat.cast (R := ℝ≥0) ϑ) * ↑ε / q) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top) ENNReal.coe_ne_top)
      (Ne.symm (NeZero.ne' q))

  -- Define the thresholds from the paper
  let cur_false_witness_threshold := (((Nat.cast (R := ℝ≥0) (ϑ+1)) * ε: ℝ≥0) : ENNReal) / q
  let prev_false_witness_threshold := (((Nat.cast (R := ℝ≥0) ϑ) * ε: ℝ≥0) : ENNReal) / q
  let goal_threshold := (ε_enn / q)

  -- 2. Define the combined distribution and the two predicates
  let D : PMF (F × (Fin (ϑ) → F)) := do
    let r_last ← $ᵖ F
    let r_init ← $ᵖ (Fin (ϑ) → F)
    pure (r_last, r_init)
  set f := fun (r : F × (Fin ϑ → F)) =>
    multilinearCombine_affineComb_split_last_close (MC := MC) (u := u) (e := e) r.1 r.2
  set g := fun (r : F × (Fin ϑ → F)) => r.1 ∈ R_star_set

  -- 3. Rewrite the hypothesis `hP...` using the combined distribution `D`
  have h_D_eq_prod : D = $ᵖ (F × (Fin ϑ → F)) := by
    rw [←do_two_uniform_sampling_eq_uniform_prod]
  rw [Pr_multi_let_equiv_single_let] at hP_multilinearCombine_affine_close_gt

  -- `hP_f_gt` is the hypothesis `Pr[f] > cur_false_witness_threshold`
  have h_P_f_gt : Pr_{let r ← D}[f r] > cur_false_witness_threshold := by
    exact hP_multilinearCombine_affine_close_gt

  -- 4. Apply the Law of Total Probability: Pr[f] = Pr[f ∧ g] + Pr[f ∧ ¬g]
  have h_split : Pr_{let r ← D}[f r] =
    Pr_{let r ← D}[g r ∧ f r] + Pr_{let r ← D}[¬(g r) ∧ f r] := by
    apply Pr_add_split_by_complement

  -- 5. Bound the two terms on the RHS
  -- 5a. Pr[f ∧ g] ≤ Pr[g]
  have h_Pr_f_and_g_le_Pr_g : Pr_{let r ← D}[g r ∧ f r] ≤ Pr_{let r ← D}[g r] := by
    apply Pr_le_Pr_of_implies
    intro r h_imp; exact h_imp.1

  -- 5b. Pr[f ∧ ¬g] ≤ prev_false_witness_threshold (i.e., ϑε/q) (This is the "false positive" bound)
  -- Proof sketch: Pr_{let r ← D}[¬(g r) ∧ f r]
    -- = (1/q) * ∑' r_last, Pr_{r_init}[ r_last ∉ R_star_set ∧ f (r_init||r_last)]
  -- (1/q) * ∑' r_last, (if r_last ∉ R* then Pr_{r_init}[f(r_last, r_init)] else 0)
  -- ≤ (1/q) * ∑' r_last, (if r_last ∉ R* then (ϑ * ε/q) else 0)
  -- ≤ (1/q) * ∑' r_last, (ϑ * ε/q) = (1/q) * (ϑ * ε/q * q) = ϑ*ε/q (Q.E.D)
  have h_bound_not_g : Pr_{let r ← D}[¬(g r) ∧ f r] ≤ prev_false_witness_threshold := by
    dsimp only [D]
    rw [do_two_uniform_sampling_eq_uniform_prod (α := F) (β := (Fin ϑ → F))]
    rw [prob_split_uniform_sampling_of_prod]
    -- ⊢ Pr_{ x ← $ᵖ F; y ← $ᵖ (Fin ϑ → F)}[¬g (x, y) ∧ f (x, y)] ≤ prev_false_witness_threshold
    rw [prob_tsum_form_split_first (D := $ᵖ F) (D_rest :=
      fun r_last => (do let r_init ← $ᵖ (Fin ϑ → F); pure (¬(r_last ∈ R_star_set)
        ∧ f (r_last, r_init))))]
    conv_lhs =>
      simp only [PMF.uniformOfFintype_apply]; rw [ENNReal.tsum_mul_left]
      simp only [prob_const_and_prop_eq_ite]
    -- (1/q) * ∑' r_last, (if r_last ∉ R* then Pr_{r_init}[f(r_last, r_init)] else 0)
    have h_inner_le : ∀ (i: F), (if i ∉ R_star_set then
      Pr_{let r_init ← $ᵖ (Fin ϑ → F)}[f (i, r_init)] else 0)
        ≤ prev_false_witness_threshold := fun i => by
      by_cases hi_mem: i ∈ R_star_set
      · simp only [hi_mem, not_true_eq_false, ↓reduceIte, zero_le]
      · simp only [hi_mem, not_false_eq_true, ↓reduceIte]
        have h_i_mem_iff := Finset.mem_filter (s := Finset.univ (α := F)) (a := i)
          (p := fun r_last => R_star_tensor_filter MC (e := e) (ε := ε) U₀ U₁ r_last
      )
        simp only [R_star_set] at hi_mem
        have h_i_ne_mem_and_close := (Iff.not h_i_mem_iff).mp hi_mem
        have h_i_mem_univ: i ∈ Finset.univ (α := F) := by
          simp only [mem_univ]
        simp only [h_i_mem_univ, true_and] at h_i_ne_mem_and_close
        unfold R_star_tensor_filter at h_i_ne_mem_and_close
        simp only [gt_iff_lt, not_lt] at h_i_ne_mem_and_close
        exact h_i_ne_mem_and_close

    calc
      _ ≤ (((Fintype.card F): ENNReal)⁻¹ * ∑' (i : F), prev_false_witness_threshold) := by
        apply ENNReal.mul_le_mul_left (h0 := ENNReal.inv_ne_zero.mpr hq_ne_top)
          (hinf := ENNReal.inv_ne_top.mpr hq_ne_zero).mpr
        apply ENNReal.tsum_le_tsum h_inner_le
      _ ≤ _ := by
        simp only [ENNReal.tsum_const, ENat.card_eq_coe_fintype_card, ENat.toENNReal_coe]
        rw [←mul_assoc]
        simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
          ENNReal.natCast_ne_top, ENNReal.inv_mul_cancel, one_mul, le_refl]
  stop
  -- 6. Chain the inequalities: `(ϑ+1)ε/q < Pr[f] ≤ Pr[g] + Pr[f ∧ ¬g] ≤ Pr[g] + ϑε/q`
  have h_total_lt_Pr_g_add_term : cur_false_witness_threshold
    < Pr_{let r ← D}[g r] + prev_false_witness_threshold := by
    calc cur_false_witness_threshold
      < Pr_{let r ← D}[f r] := h_P_f_gt
      _ = Pr_{let r ← D}[g r ∧ f r] + Pr_{let r ← D}[¬(g r) ∧ f r] := by rw [h_split]
      _ ≤ Pr_{let r ← D}[g r] + Pr_{let r ← D}[¬(g r) ∧ f r] :=
        add_le_add_right h_Pr_f_and_g_le_Pr_g _
      _ ≤ Pr_{let r ← D}[g r] + prev_false_witness_threshold := add_le_add_left h_bound_not_g _
      _ ≤ _ := by simp only [bind_pure_comp, le_refl]

  -- 7. Prove Pr[g] is equal to the goal probability (marginalization)
  have h_Pr_g_eq : Pr_{let r ← D}[g r] = Pr_{let r ← $ᵖ F}[ r ∈ R_star_set ] := by
    have h_D_rw : D = (do { let x ← $ᵖ F; let y ← $ᵖ (Fin ϑ → F); pure (x, y)}) := rfl
    rw [h_D_rw]
    rw [do_two_uniform_sampling_eq_uniform_prod]
    rw [prob_marginalization_first_of_prod]

  -- 8. Rearrange to get the final result
  -- We have: cur_false_witness_threshold < Pr[g] + prev_false_witness_threshold
  -- We want: goal_threshold < Pr[g]
  -- This is: cur_false_witness_threshold - prev_false_witness_threshold < Pr[g]
  rw [h_Pr_g_eq] at h_total_lt_Pr_g_add_term
  have h_lt_sub : cur_false_witness_threshold - prev_false_witness_threshold
    < Pr_{let r ← $ᵖ F}[r ∈ R_star_set] := by
    rw [ENNReal.sub_lt_iff_lt_right]
    · omega
    · exact h_finite
    · dsimp only [ENNReal.coe_mul, ENNReal.coe_natCast, prev_false_witness_threshold,
      cur_false_witness_threshold]
      apply ENNReal.div_le_div
      · by_cases h_ε_ne_zero : ε ≠ 0
        · let mul_right_le:= (ENNReal.mul_le_mul_right (a := ϑ) (b := Nat.cast (R := ENNReal)
            (ϑ + 1)) (c := ε) (Nat.cast_ne_zero.mpr h_ε_ne_zero) (ENNReal.natCast_ne_top ε)).mpr
          apply mul_right_le
          simp only [Nat.cast_add, Nat.cast_one, self_le_add_right]
        · have h_ε_eq_zero : ε = 0 := by omega
          rw [h_ε_eq_zero]; simp only [CharP.cast_eq_zero, mul_zero, Nat.cast_add, Nat.cast_one,
            le_refl]
      · exact Preorder.le_refl q

  have h_sub_eq_goal : cur_false_witness_threshold - prev_false_witness_threshold
    = goal_threshold := by
    unfold cur_false_witness_threshold prev_false_witness_threshold goal_threshold
    simp only [Nat.cast_add, Nat.cast_one, ENNReal.coe_add, ENNReal.coe_one,
      ENNReal.coe_mul, ENNReal.coe_natCast, ε_enn]
    rw [add_mul]
    simp only [one_mul]
    rw [ENNReal.add_div]
    rw [add_comm, ENNReal.add_sub_cancel_right]
    omega

  rw [h_sub_eq_goal] at h_lt_sub
  exact h_lt_sub

omit [NoZeroDivisors F] [Fintype A] [Module.Free F A] [Nontrivial ↥MC] in
/- **Theorem 3.6 (Angeris-Evans-Roh AER24): Interleaved Affine Gaps -> Tensor Gaps**
If, for **every** interleaving factor `m ≥ 1`, the `m`-fold interleaved code `C^m`
features proximity gaps for affine lines with respect to parameters `e` and `ε`,
then the original code `C` also features tensor-style proximity gaps with respect
to the same parameters `e` and `ε`.
-/
theorem interleaved_affine_gaps_imply_tensor_gaps
    (hC_proximityGapAffineLines : e_ε_correlatedAgreementAffineLinesNat
      (F := F) (A := A) (ι := ι) (C := MC) (e := e) (ε := ε))
    (h_interleaved_gaps : ∀ m : ℕ, m ≥ 1 →
      e_ε_correlatedAgreementAffineLinesNat (F := F)
        (A := InterleavedSymbol A (Fin m)) (ι := ι) (C := MC ^⋈ (Fin m)) e ε) :
    ∀ (ϑ : ℕ), (hϑ_gt_0 : ϑ > 0) → δ_ε_multilinearCorrelatedAgreement_Nat (F := F) (A := A)
      (ι := ι) (C := MC) (ϑ := ϑ) (e := e) (ε := ε) := by
    intro ϑ
    induction ϑ with
    | zero =>
      intro u
      contradiction
    | succ ϑ_sub_1 ih =>
      cases ϑ_sub_1 with
      | zero =>
        -- `ϑ = 1`
        simp only [zero_add, gt_iff_lt, zero_lt_one, ModuleCode, forall_const]
        intro u
        let toAffineLineEval := multilinearCombine₁_eq_affineLineEvaluation (F := F) (u := u)
        intro hprob_gt
        simp_rw [toAffineLineEval] at hprob_gt
        let prob_eq := prob_uniform_singleton_finFun_eq (F := F)
          (P := fun r => Δ₀(affineLineEvaluation (u 0) (u 1) r, MC) ≤ e)
        -- Convert sampling (r ← (Fin 1 → F)) into sampling (r ← F)

        simp_rw [prob_eq, Nat.cast_one, ENNReal.coe_one, one_mul] at hprob_gt
        have h_correlated_agreement := hC_proximityGapAffineLines (u 0) (u 1) hprob_gt
        simp only [jointProximityNat₂, Fin.isValue] at h_correlated_agreement
        have h_u_eq: u = finMapTwoWords (u 0) (u 1) := by
          funext rowIdx
          match rowIdx with
          | 0 => rfl
          | 1 => rfl
        rw [h_u_eq.symm] at h_correlated_agreement
        exact h_correlated_agreement
      | succ ϑ_sub_2 =>
        intro hϑ_gt_0 u hP_multilinearCombine_close_gt
        -- `ϑ ≥ 2`
        -- set ϑ_sub_1 := ϑ_sub_2 + 1
        let ϑ := ϑ_sub_2 + 1 + 1
        have hϑ : ϑ = ϑ_sub_2 + 1 + 1 := by rfl
        -- have hfinϑ : Fin ϑ = Fin (ϑ_sub_2 + 1 + 1) := by rfl
        set U₀ : Fin (2 ^ (ϑ_sub_2 + 1)) → Word A ι :=
          (splitHalfRowWiseInterleavedWords (ϑ := ϑ_sub_2 + 1) u).1
        set U₁ : Fin (2 ^ (ϑ_sub_2 + 1)) → Word A ι :=
          (splitHalfRowWiseInterleavedWords (ϑ := ϑ_sub_2 + 1) u).2
        unfold jointProximityNat
        simp only
        -- intro hP_multilinearCombine_close_gt

        have h_finsnoc_eq_r: ∀ r: Fin (ϑ_sub_2 + 1 + 1) → F,
          Fin.snoc (fun (i : Fin (ϑ_sub_2 + 1)) ↦ r i.castSucc)
            (r (Fin.last (ϑ_sub_2 + 1))) = r := fun r => by
          funext i
          have hi_le_lt := i.isLt
          by_cases h : i = Fin.last (ϑ_sub_2 + 1)
          · simp only [h, Fin.snoc_last]
          · have h_i_ne_last: i ≠ Fin.last (ϑ_sub_2 + 1) := by omega
            have h_i_ne_last_val: i.val ≠ Fin.last (ϑ_sub_2 + 1) := by omega
            rw [Fin.val_last] at h_i_ne_last_val
            have h_i_lt: i.val < (ϑ_sub_2 + 1) := by omega
            simp only [Fin.snoc, Fin.castSucc_castLT, cast_eq, dite_eq_ite, ite_eq_left_iff, not_lt]
            simp only [isEmpty_Prop, not_le, h_i_lt, IsEmpty.forall_iff]
        let P : F → (Fin (ϑ_sub_2 + 1) → F) → Prop := fun r_last r_init =>
          Δ₀(multilinearCombine (u:=u) (r:=Fin.snoc r_init r_last), MC) ≤ e

        let hP_split_r_last := prob_split_last_uniform_sampling_of_finFun
          (ϑ := ϑ_sub_2 + 1) (F := F) (P := P)
        unfold P at hP_split_r_last
        simp_rw [h_finsnoc_eq_r] at hP_split_r_last

        rw [hP_split_r_last] at hP_multilinearCombine_close_gt

        -- Now we have two randomness sampling in hP_multilinearCombine_close_gt :
        -- `((ϑ_sub_2 + 1 + 1) * ε) / |𝔽|
          -- < Pr_{ r_last; r_init }[  Δ₀((Fin.snoc r_init r_last)|⨂|u, ↑MC) ≤ ↑e)) ]` (0)
        -- We need to achieve the upperbound for hP_multilinearCombine_close_gt probability by:
        -- i.e. `Pr_{ r_last; r_init }[  Δ₀((Fin.snoc r_init r_last)|⨂|u, ↑MC) ≤ ↑e)) ]`
        -- `= Pr_{ r_last; r_init }[ Δ₀((r_init)|⨂|affineCombine(U₀, U₁, r_last), ↑MC) ≤ ↑e)) ]`
        -- `= PR_{ r_last }[ r_init; Δ₀((r_init)|⨂|affineCombine(U₀, U₁, r_last), ↑MC) ≤ ↑e)) ]`
        -- Divide into two cases: r_last ∈ R* and r_last ∉ R*
        -- `= Pr_{ r_last }[ r_last ∈ R* ∧
          -- Pr_{ r_init }[ Δ₀((r_init)|⨂|affineCombine(U₀, U₁, r_last), ↑MC) ≤ ↑e)) ]` (1)
        -- `+ Pr_{ r_last }[ r_last ∉ R* ∧
          -- Pr_{ r_init }[ Δ₀((r_init)|⨂|affineCombine(U₀, U₁, r_last), ↑MC) ≤ ↑e)) ]` (2)
        -- `(1) = Pr_{ r_last }[ r_last ∈ R* ]` (3)
        -- `(2): ∀ r ∉ R*, it's trivial that the probability
          -- ≤ ((ϑ_sub_2 + 1) * ε) / |𝔽|, due to definition of membership of R*` (4)

        -- Combine (0), (3), (4): we have `Pr_{ r_last }[ r_last ∈ R* ] > ε/|𝔽|` (5)

        -- Applying `correlatedAgreement_of_mem_R_star_tensor` to (5), we get
          -- `Δ₀((r_last)|⨂|affineCombine(U₀, U₁, r_last), ↑MC) ≤ ↑e)) ] > ε/|𝔽|` (6)
        -- This is premise for affineProxmityGaps of interleaved code (`h_interleaved_gaps`)
          -- for `m = 2^{ϑ_sub_2 + 1}`, which directly leads to Q.E.D.

        let  ϑ_pred := ϑ_sub_2 + 1
        have h_ϑ_pred : ϑ_pred = ϑ_sub_2 + 1 := by rfl
        have h_ϑ : ϑ = ϑ_pred + 1 := by rfl
        -- Step 1: Apply multilinearCombine recursive form
        -- We need the lemma `multilinearCombine u r = multilinearCombine`
          -- `(affineLineEvaluation U₀ U₁ r_last) r_init` where `r = Fin.snoc r_init r_last`
        have multilinearCombine_snoc_eq_multilinearCombine_affine
          (r_init : Fin ϑ_pred → F) (r_last : F) : multilinearCombine u (Fin.snoc r_init r_last) =
            multilinearCombine (affineLineEvaluation U₀ U₁ r_last) r_init := by
          rw [multilinearCombine_recursive_form]
          simp only [Fin.snoc_last, Fin.init_snoc]
          rfl

        -- Rewrite the probability using this identity
        simp_rw [multilinearCombine_snoc_eq_multilinearCombine_affine]
          at hP_multilinearCombine_close_gt
        -- hP_multilinearCombine_close_gt now looks like:
        -- Pr_{ r_last ← $ᵖ F; r_init ← $ᵖ (Fin ϑ_pred → F) }[ Δ₀(multilinearCombine
            -- (affineLineEvaluation U₀ U₁ r_last) r_init, ↑MC) ≤ ↑e ] > ↑(↑ϑ * ↑ε) / q
        -- Step 2 & 3: Define R* and apply Law of Total Probability
        let R_star_set := R_star_tensor MC (m:=ϑ_pred) (e:=e) (ε:=ε) U₀ U₁

        -- Step 5: Show Pr[R*] > ε / q
        have h_prob_Rstar_gt_eps_div_q : Pr_{ let r ← $ᵖ F }[ r ∈ R_star_set ]
          > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
          let res := prob_R_star_gt_threshold (MC := MC) (ε := ε) (ϑ := ϑ_sub_2 + 1) (u := u)
            (e := e) (hP_multilinearCombine_close_gt)
          exact res
        -- Convert Pr_{}[] to cardinality
        have h_R_star_card_gt_eps : R_star_set.card > ε := by
          rw [prob_uniform_eq_card_filter_div_card] at h_prob_Rstar_gt_eps_div_q -- Needs NNReal
          simp only [ENNReal.coe_natCast] at h_prob_Rstar_gt_eps_div_q
          rw [gt_iff_lt] at h_prob_Rstar_gt_eps_div_q
          have h_cancel_q_denom := ENNReal.div_lt_div_iff_left
            (a := (ε : ENNReal))
            (b := (#(filter (fun r => r ∈ R_star_set) Finset.univ)))
            (c := (Fintype.card F : ENNReal)) (hc₀ := by simp only [ne_eq,
            Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]) (hc := by simp only [ne_eq,
              ENNReal.natCast_ne_top, not_false_eq_true])

          rw [h_cancel_q_denom] at h_prob_Rstar_gt_eps_div_q
          simp only [filter_univ_mem, Nat.cast_lt] at h_prob_Rstar_gt_eps_div_q
          exact h_prob_Rstar_gt_eps_div_q

        -- Step 6: Apply Inductive Hypothesis for r_last ∈ R*
        have h_line_close_to_C_m : ∀ (r : R_star_set),
          jointProximityNat (u := affineLineEvaluation U₀ U₁ r.val) (e := e) (C := MC) := by
          intro r_in_Rstar
          -- Use the lemma proven earlier
          apply correlatedAgreement_of_mem_R_star_tensor
            (ih := fun u_prev => ih (by omega) u_prev ) (u := u)
        -- Step 7: Apply Affine Gap of Interleaved Code C^(m = 2^(ϑ_sub_2 + 1))
        have h_C_m_gap := h_interleaved_gaps (2^(ϑ_sub_2 + 1)) (Nat.one_le_two_pow)

        -- Need the hypothesis Pr[...] > ε/q for h_C_m_gap
        have h_prob_line_gt_eps_div_q :
          Pr_{ let r ← $ᵖ F }[
            Δ₀(affineLineEvaluation (u₀ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₀))
              (u₁ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₁)) (r := r),
              ((MC ^⋈ (Fin (2 ^ (ϑ_sub_2 + 1)))))) ≤ e
          ] > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            -- This is implied by h_prob_Rstar_gt_eps_div_q becuz R* is a subset of the success set
            apply lt_of_le_of_lt' _ h_prob_Rstar_gt_eps_div_q
            have h_r_implies: ∀ (r : F), r ∈ R_star_set →
              Δ₀(affineLineEvaluation
                (u₀ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₀))
                (u₁ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₁)) (r := r),
                ((MC ^⋈ (Fin (2 ^ (ϑ_sub_2 + 1)))))) ≤ e := by
              intro r hr_in_Rstar
              specialize h_line_close_to_C_m ⟨r, hr_in_Rstar⟩
              unfold jointProximityNat at h_line_close_to_C_m
              exact h_line_close_to_C_m
            let Pr_le := Pr_le_Pr_of_implies (D := $ᵖ F)
              (g := fun r => Δ₀(affineLineEvaluation
                (u₀ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₀))
                (u₁ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₁)) (r := r),
                ((MC ^⋈ (Fin (2 ^ (ϑ_sub_2 + 1)))))) ≤ e)
              (f := fun r => r ∈ R_star_set) (h_imp := h_r_implies)
            simp only at Pr_le
            exact Pr_le

        -- Apply the gap property of C^m
        have h_final_gap : jointProximityNat₂
          (u₀ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₀))
          (u₁ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₁)) (e := e)
          (C := (MC ^⋈ (Fin (2^(ϑ_sub_2 + 1))))) := by
          apply h_C_m_gap (u₀ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₀))
            (u₁ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₁))
            (h_prob_line_gt_eps_div_q)

        apply CA_split_rowwise_implies_CA (u := u) (e := e)
        exact h_final_gap

omit [Fintype F] [NoZeroDivisors F] [DecidableEq F] [Fintype A] [Module.Free F A]
  [Nontrivial ↥MC] in
lemma jointProximity₂_affineShift_implies_jointProximity₂ (u₀ u₁ : Word A ι) (δ : ℝ≥0) :
  jointProximity₂ (C := MC) (u₀ := u₀) (u₁ := u₁ - u₀) (δ := δ) →
    jointProximity₂ (C := MC) (u₀ := u₀) (u₁ := u₁) (δ := δ) := by
  intro h_shifted_jointProximity₂
  unfold jointProximity₂ at h_shifted_jointProximity₂ ⊢
  rw [←jointAgreement_iff_jointProximity] at h_shifted_jointProximity₂ ⊢
  unfold jointAgreement at h_shifted_jointProximity₂ ⊢
  rcases h_shifted_jointProximity₂ with ⟨S, hS_card_ge_1_minus_δ, v, hv_agree_u₀_u₁_on_S⟩
  use S
  have h_S_card_ge : ↑(#S) ≥ (1 - δ) * ↑(Fintype.card ι) := hS_card_ge_1_minus_δ
  use h_S_card_ge
  let v₀ := v 0
  let v₁ := v 1
  let v' : Fin 2 → Word A ι := fun i =>
    match i with
    | 0 => v₀
    | 1 => v₀ + v₁
  use v'
  intro i
  -- ⊢ v' i ∈ ↑MC ∧ S ⊆ {j | v' i j = finMapTwoWords u₀ u₁ i j}
  constructor
  · -- Show v' i ∈ MC
    match i with
    | 0 =>
      simp only [v', Fin.isValue]
      exact (hv_agree_u₀_u₁_on_S 0).1
    | 1 =>
      simp only [v', Fin.isValue]
      apply MC.add_mem
      · exact (hv_agree_u₀_u₁_on_S 0).1
      · exact (hv_agree_u₀_u₁_on_S 1).1
  · -- Show agreement on S
    match i with
    | 0 =>
      simp only [v', Fin.isValue]
      have h_subset := (hv_agree_u₀_u₁_on_S 0).2
      intro j hj
      specialize h_subset hj
      simp only [mem_filter, mem_univ, true_and] at h_subset
      simp only [mem_filter, mem_univ, true_and, finMapTwoWords]
      exact h_subset
    | 1 =>
      simp only [v', Fin.isValue]
      intro j hj
      simp only [mem_filter, mem_univ, true_and, finMapTwoWords]
      -- v' 1 j = v₀ j + v₁ j
      -- We know v₀ j = u₀ j and v₁ j = (u₁ - u₀) j
      have h_agree_0 := (hv_agree_u₀_u₁_on_S 0).2 hj
      have h_agree_1 := (hv_agree_u₀_u₁_on_S 1).2 hj
      simp only [mem_filter, mem_univ, true_and, finMapTwoWords, Fin.isValue] at h_agree_0 h_agree_1
      rw [Pi.add_apply]
      dsimp only [v₀, v₁]
      rw [h_agree_0, h_agree_1]
      simp only [Pi.sub_apply]
      abel

end MainResults

section RSCode_Corollaries
variable {n k : ℕ} {A : Type} [NeZero n] [NeZero k] (hk : k ≤ n)
  {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq F] {α : ι ↪ A}
    (h_deg_le_length : k ≤ Fintype.card ι)
  {domain : (Fin n) ↪ A} [DecidableEq A] [Field A] [Fintype A]

/-
Theorem 2.2 (Ben-Sasson, et al. [Ben+23, Thm. 4.1]). For each `e ∈ {0, ..., ⌊(d-1)/2⌋}`,
`RS_{F, S}[k, n]` exhibits proximity gaps for affine lines with respect to the
proximity parameter `e` and the false witness bound `ε := n`.
-/
theorem ReedSolomon_ProximityGapAffineLines_UniqueDecoding [Nontrivial (ReedSolomon.code α k)]
    (hk : k ≤ Fintype.card ι) :
    ∀ e ≤ (Code.uniqueDecodingRadius (C := (ReedSolomon.code α k : Set (ι → A)))),
      e_ε_correlatedAgreementAffineLinesNat (F := A) (A := A) (ι := ι)
        (C := (ReedSolomon.code α k : Set (ι → A)))
        (e := e) (ε := Fintype.card (ι)) := by
  set n := Fintype.card ι
  intro e he_unique_decoding_radius
  intro u₀ u₁
  intro h_prob_affine_line_close_gt
  -- Apply theorem 4.1 (BCIKS20)
  let δ : ℝ≥0 := (e : ℝ≥0) / (Fintype.card (ι) : ℝ≥0)
  have h_δ_mul_n_eq_e: Nat.floor (δ * Fintype.card (ι)) = e := by
    dsimp only [Fin.isValue, δ]
    rw [div_mul]
    rw [div_self (h := by simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
      not_false_eq_true]), div_one]
    simp only [Nat.floor_natCast]
  set CRS := ReedSolomon.code α k
  have h_dist_RS := ReedSolomonCode.dist_eq' (F := A) (α := α)
    (n := k) (ι := ι) (h := hk)
  have h_dist_CRS : ‖(CRS : Set (ι → A))‖₀ = n - k + 1 := h_dist_RS
  have he_le_NNReal : (e : ℝ≥0)
    ≤ (((Code.dist (R := A) (n := ι) (C := CRS)) - 1) : ℝ≥0) / 2 := by
    rw [uniqueDecodingRadius_eq_floor_div_2] at he_unique_decoding_radius
    rw [Nat.le_floor_iff (ha := by simp only [zero_le])] at he_unique_decoding_radius
    exact he_unique_decoding_radius
  have h_δ_within_rel_URD : δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := A)
    (C := ReedSolomon.code α k) := by
    dsimp [δ, Code.relativeUniqueDecodingRadius]
    rw [div_le_iff₀ (hc := by simp only [Nat.cast_pos, Fintype.zero_lt_card])]
    rw [div_mul]
    simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true, div_self, div_one]
    exact he_le_NNReal
  have h_rewrite_prob : Pr_{let z ← $ᵖ A}[Δ₀((1 - z) • u₀ + z • u₁, CRS) ≤ e]
    = Pr_{let z ← $ᵖ A}[Δ₀(u₀ + z • (u₁ - u₀), CRS) ≤ e] := by
    congr  -- Peel away the Pr_{...} wrapper
    funext z
    congr! 1 -- Focus on the term inside Δ₀
    -- Apply the algebra derived above
    rw [sub_smul, one_smul, smul_sub]
    abel_nf
  have h_correlated_agreement := RS_correlatedAgreement_affineLines_uniqueDecodingRegime (deg := k)
    (domain := α) (ι := ι) (F := A) (δ := δ) (hδ := by exact h_δ_within_rel_URD)
  unfold affineLineEvaluation at h_prob_affine_line_close_gt
  rw [h_rewrite_prob] at h_prob_affine_line_close_gt
  -- now we can apply RS_correlatedAgreement_affineLines_uniqueDecodingRegime
  let uShifted := finMapTwoWords u₀ (u₁ - u₀)
  have h_errorBound_UDR_eq : (errorBound δ k α)
    = (Fintype.card (ι) : ℝ≥0) / (Fintype.card A : ℝ≥0) := by
    unfold errorBound
    have h_δ_mem : δ ∈ Set.Icc 0 (((1 : ℝ≥0) - (rate (ReedSolomon.code α k))) / 2) := by
      simp only [Set.mem_Icc, zero_le, true_and]
      rw [rateOfLinearCode_eq_div' (h := by omega)]
      simp only [NNRat.cast_div, NNRat.cast_natCast]
      rw [←ReedSolomonCode.relativeUniqueDecodingRadius_RS_eq' (F := A)
        (ι := ι) (h := by omega)]
      rw [dist_le_UDR_iff_relDist_le_relUDR] at he_unique_decoding_radius
      exact he_unique_decoding_radius
    simp only [h_δ_mem, ↓reduceIte]
  rw [h_errorBound_UDR_eq] at h_correlated_agreement
  -- convert h_correlated_agreement into absolute distance bound
  unfold  δ_ε_correlatedAgreementAffineLines at h_correlated_agreement
  simp_rw [relDistFromCode_le_iff_distFromCode_le] at h_correlated_agreement

  let h_u₀_and_u₁_sub_u₀_CA := h_correlated_agreement uShifted (by
    rw [h_δ_mul_n_eq_e]
    simp only [Fin.isValue, bind_pure_comp, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
      not_false_eq_true, ENNReal.coe_div, ENNReal.coe_natCast, gt_iff_lt]
    simp only [ENNReal.coe_natCast] at h_prob_affine_line_close_gt

    exact h_prob_affine_line_close_gt
  )

  rw [jointAgreement_iff_jointProximity] at h_u₀_and_u₁_sub_u₀_CA
  -- we have jointProximity₂ (u₀ := u₀) (u₁ := u₁ - u₀) (δ := δ) at h_u₀_and_u₁_sub_u₀_CA
  have h_jointProximity₂ : jointProximity₂ (C := CRS) (u₀ := u₀) (u₁ := u₁ - u₀) (δ := δ) := by
    exact h_u₀_and_u₁_sub_u₀_CA

  letI : Nontrivial (CRS) := by infer_instance

  let jointProximity₂_u₀_u₁ := jointProximity₂_affineShift_implies_jointProximity₂ (ι := ι)
    (MC := CRS) (u₀ := u₀) (u₁ := u₁) (δ := δ) (h_jointProximity₂)
  unfold jointProximity₂ jointProximity at jointProximity₂_u₀_u₁
  rw [relDistFromCode_le_iff_distFromCode_le] at jointProximity₂_u₀_u₁
  rw [h_δ_mul_n_eq_e] at jointProximity₂_u₀_u₁
  exact jointProximity₂_u₀_u₁

/-- **Corollary 3.7**: RS Codes have Tensor-Style Proximity Gaps (Unique Decoding)
Example 4.1 shows that ε=n is tight for RS codes (Ben+23 Thm 4.1 is sharp). -/
theorem reedSolomon_multilinearCorrelatedAgreement_Nat [Nontrivial (ReedSolomon.code α k)]
    {e : ℕ} (hk : k ≤ Fintype.card ι)
    (he : e ≤ (Code.uniqueDecodingRadius (C := (ReedSolomon.code α k : Set (ι → A))))) :
    ∀ (ϑ : ℕ), (hϑ_gt_0 : ϑ > 0) → δ_ε_multilinearCorrelatedAgreement_Nat (F := A) (A := A)
      (ι := ι) (C := (ReedSolomon.code α k : Set (ι → A)))
      (ϑ := ϑ) (e := e) (ε := Fintype.card ι) := by
    set n := Fintype.card ι
    intro ϑ hϑ_gt_0
    intro u h_prob_tensor_gt
    set C_RS: ModuleCode ι A A := ReedSolomon.code α k
    have h_dist_RS := ReedSolomonCode.dist_eq'  (F := A) (α := α)
      (n := k) (ι := ι) (h := hk)
    have h_dist_CRS : ‖(C_RS : Set (ι → A))‖₀ = n - k + 1 := h_dist_RS
    -- 1. Apply ReedSolomon_ProximityGapAffineLines_UniqueDecoding (BCIKS20 Thm 4.1)
    have h_fincard_n : Fintype.card (ι) = n := by rfl
    have h_affine_gap_base : e_ε_correlatedAgreementAffineLinesNat (F := A) (A := A) (ι := ι)
      (C := C_RS) (e := e) (ε := n) := by
      let res := ReedSolomon_ProximityGapAffineLines_UniqueDecoding (A := A)
        (hk := by omega) (e := e) he
      rw [h_fincard_n] at res
      exact res
    -- 2. Check condition ε ≥ e + 1 for Theorem 3.1
    have h_eps_ge_e1 : n ≥ e + 1 := by
      simp only [uniqueDecodingRadius] at he
      simp_rw [h_dist_CRS] at he
      simp only [add_tsub_cancel_right] at he
      rw [ge_iff_le];
      apply Nat.le_of_lt_succ;
      have h_lt : e + 1 < (n - k) / 2 + 1 + 1 := by omega
      have h_le : (n - k) / 2 + 1 ≤ n := by
        exact Nat.sub_div_two_add_one_le n k hk
      omega
    -- 3. Apply Theorem 3.1 inductively (or just state it's needed for Thm 3.6)
    have h_affine_gap_interleaved : ∀ m, (hm: m ≥ 1) →
        letI : Nonempty (Fin m × (ι)) := by
          apply nonempty_prod.mpr
          constructor
          · exact Fin.pos_iff_nonempty.mp hm
          · omega
        e_ε_correlatedAgreementAffineLinesNat
          (F := A) (A := InterleavedSymbol A (Fin m)) (ι := ι) (C := C_RS ^⋈ (Fin m))
          e (Fintype.card (ι)) := by
      intro m hm
      let res := affine_gaps_lifted_to_interleaved_codes (MC := C_RS)
        (F := A) (A := A) (hε := h_eps_ge_e1) (e := e)
        (m := m) (hProximityGapAffineLines := h_affine_gap_base) (he := he)
      rw [h_fincard_n]
      exact res
    -- 4. Apply Theorem 3.6 (AER24)
    let RS_tensor_gap := interleaved_affine_gaps_imply_tensor_gaps
      (MC := C_RS) (h_interleaved_gaps := by
      rw [h_fincard_n] at h_affine_gap_interleaved
      exact h_affine_gap_interleaved) h_affine_gap_base
    exact RS_tensor_gap ϑ hϑ_gt_0 u h_prob_tensor_gt

theorem reedSolomon_multilinearCorrelatedAgreement [Nontrivial (ReedSolomon.code α k)]
    (hk : k ≤ Fintype.card ι) {δ : ℝ≥0} (he : δ ≤ (Code.relativeUniqueDecodingRadius
      (C := (ReedSolomon.code α k : Set (ι → A))))) :
    ∀ (ϑ : ℕ), (hϑ_gt_0 : ϑ > 0) →
      δ_ε_multilinearCorrelatedAgreement (F := A) (A := A) (ι := ι) (ϑ := ϑ) (δ := δ)
      (C := (ReedSolomon.code α k : Set (ι → A))) (ε := ((Fintype.card ι) : ℝ≥0) / (Fintype.card A))
    := by
  set n := Fintype.card ι
  intro ϑ hϑ_gt_0
  intro u h_prob_u_close_gt
  let e : ℕ := Nat.floor (δ * n)
  have h_δᵣ_close_iff_Δ₀_close : ∀ (r : Fin ϑ → A),
    (δᵣ(multilinearCombine u r, ↑(ReedSolomon.code α k)) ≤ ↑δ)
      ↔ (Δ₀(multilinearCombine u r, ↑(ReedSolomon.code α k)) ≤ e) := by
      intro r
      conv_lhs => rw [relDistFromCode_le_iff_distFromCode_le]
  simp_rw [h_δᵣ_close_iff_Δ₀_close] at h_prob_u_close_gt
  simp only [ENNReal.coe_natCast, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
    not_false_eq_true, ENNReal.coe_div, mul_div] at h_prob_u_close_gt
  letI : Nontrivial (ReedSolomon.code α k) := by infer_instance
  have hCA_Nat_if_then := reedSolomon_multilinearCorrelatedAgreement_Nat (A := A) (ι := ι) (α := α)
    (ϑ := ϑ) (hϑ_gt_0 := hϑ_gt_0) (hk := hk) (e := e) (he := by
    rw [dist_le_UDR_iff_relDist_le_relUDR]
    calc
      _ ≤ δ := by
        simp only [e]; rw [div_le_iff₀ (hc := by
          simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n)]
        apply Nat.floor_le;
        exact zero_le (δ * ↑n)
      _ ≤ _ := by exact he
  )
  let h_CA_Nat := hCA_Nat_if_then u (by
    simp only [ENNReal.coe_natCast]
    exact h_prob_u_close_gt
  )
  rw [jointAgreement_iff_jointProximity]
  unfold jointProximity
  rw [relDistFromCode_le_iff_distFromCode_le]
  unfold jointProximityNat at h_CA_Nat
  exact h_CA_Nat

end RSCode_Corollaries
