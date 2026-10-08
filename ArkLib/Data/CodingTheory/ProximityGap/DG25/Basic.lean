/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import CompPoly.Data.Nat.Bitwise
public import ArkLib.Data.CodingTheory.Basic.DecodingRadius
public import ArkLib.Data.CodingTheory.Basic.Distance
public import ArkLib.Data.CodingTheory.Basic.LinearCode
public import ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import ArkLib.Data.CodingTheory.InterleavedCode
public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.UniqueDecoding
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import ArkLib.Data.Probability.Instances
public import ArkLib.Data.CodingTheory.Prelims
public import ArkLib.ToMathlib.BigOperators.Fin
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Defs
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.RingTheory.Henselian
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Basic.ENNReal.Inv

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

@[expose] public section

noncomputable section

open Code LinearCode InterleavedCode ReedSolomon ProximityGap ProbabilityTheory Filter
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

----------------------------------------------------- Switch to (F : Type) for `Pr{...}[...]` usage
variable {F : Type} [Ring F] [Module F A] [Fintype F] [SampleableType F] (C : Set (Word A ι))
/-
Definition 2.1. We say that `C ⊂ F^n` features proximity gaps for affine lines
with respect to the proximity parameter `e` and the false witness bound `ε` if, for
each pair of words `u_0` and `u_1` in `F^n`, if
`Pr{r ∈ F}[d((1-r) · u_0 + r · u_1, C) ≤ e] > ε/q`
holds, then `d^2((u_i)_{i=0}^1, C^2) ≤ e` also does.
-/
def e_ε_correlatedAgreementAffineLinesNat
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C : Set (ι → A)) (e ε : ℕ) : Prop :=
  ∀ (u₀ u₁ : Word A ι),
    Pr{let r ← $ᵗ F}[Δ₀(affineLineEvaluation (F := F) u₀ u₁ r, C) ≤ e]
      > ((ε: ℝ≥0) / (Fintype.card F : ℝ≥0)) →
      jointProximityNat₂ (A := A) (ι := ι) (u₀ := u₀) (u₁ := u₁) (e := e) (C := C)

omit [DecidableEq ι] [Nonempty ι] [Fintype A] [Fintype F] in
omit [SampleableType F] in
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
variable {F : Type} [CommRing F] [Module F A] [Fintype F] [SampleableType F]

def δ_ε_multilinearCorrelatedAgreement_Nat
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  (C : Set (ι → A)) (ϑ : ℕ) (e : ℕ) (ε : ℕ) : Prop :=
  ∀ (u : WordStack A (Fin (2^ϑ)) ι),
    Pr{let r ← $ᵗ (Fin ϑ → F)}[ -- This syntax only works with (A : Type 0)
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
      have h_eq := congr_fun h_split_eq_merge.1 ⟨rowIdx, by omega⟩
      simp only at h_eq
      exact h_eq
    · simp only [hk, ↓reduceDIte]
      have h_eq := congr_fun h_split_eq_merge.2 ⟨rowIdx - 2 ^ ϑ, by omega⟩
      simp only at h_eq
      rw! (castMode:=.all) [Nat.sub_add_cancel (h := by omega)] at h_eq
      exact h_eq
  · intro h_merge_eq_split
    simp only [splitHalfRowWiseInterleavedWords]
    unfold mergeHalfRowWiseInterleavedWords at h_merge_eq_split
    constructor
    · funext rowIdx
      let res := congr_fun h_merge_eq_split ⟨rowIdx, by omega⟩
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at res
      exact res
    · funext rowIdx
      let res := congr_fun h_merge_eq_split ⟨rowIdx + 2 ^ ϑ, by omega⟩
      simp only [add_lt_iff_neg_right, not_lt_zero, ↓reduceDIte, add_tsub_cancel_right,
        Fin.eta] at res
      exact res

/-- Split a stack of `2 ^ (ϑ + 1)` rows into its even-indexed rows `u (2 * j)` and its
odd-indexed rows `u (2 * j + 1)`. Folding a multilinear combination along its first challenge
pairs exactly these two halves (`multilinearCombine_recursive_form_first`), whereas
`splitHalfRowWiseInterleavedWords` pairs the halves of the last challenge. -/
def splitEvenOddRowWiseInterleavedWords {ϑ : ℕ} (u : Fin (2 ^ (ϑ + 1)) → ι → A) :
    (Fin (2 ^ ϑ) → ι → A) × (Fin (2 ^ ϑ) → ι → A) :=
  (fun j => u ⟨2 * j.val, by omega⟩, fun j => u ⟨2 * j.val + 1, by omega⟩)

-- Preserve the public `Matrix` aliases for interleaved words. Lean v4.33 otherwise refuses
-- to unfold them while matching the proof's implicit word types.
set_option backward.isDefEq.respectTransparency false in
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
    dsimp only [v_IC]
    change v_rowwise_finmap rowIdx ∈ C
    unfold v_rowwise_finmap mergeHalfRowWiseInterleavedWords
    by_cases hk : rowIdx.val < 2 ^ ϑ
    · simp only [hk, ↓reduceDIte]
      exact h_vSplit_rows_mem 0 ⟨rowIdx.val, hk⟩
    · simp only [hk, ↓reduceDIte]
      exact h_vSplit_rows_mem 1 ⟨rowIdx.val - 2 ^ ϑ, by omega⟩
    -- END OF MODIFIED SECTION
  · use D
    constructor
    · exact hD_card_le_e
    · intro colIdx h_colIdx_notin_D
      funext rowIdx
      dsimp only [v_IC]
      change u rowIdx colIdx = v_rowwise_finmap rowIdx colIdx
      have hRes := h_agree_outside_D colIdx (h_colIdx_notin_D)
      simp_rw [funext_iff] at hRes
      unfold v_rowwise_finmap mergeHalfRowWiseInterleavedWords
      by_cases hk : rowIdx.val < 2 ^ ϑ
      · simp only [hk, ↓reduceDIte]
        exact hRes 0 ⟨rowIdx, by omega⟩
      · simp only [hk, ↓reduceDIte]
        change u rowIdx colIdx = vSplit colIdx 1 ⟨↑rowIdx - 2 ^ ϑ, by omega⟩
        have hRes₁ := hRes 1 ⟨rowIdx - 2 ^ ϑ, by omega⟩
        dsimp only [splitHalfRowWiseInterleavedWords, Fin.isValue, U₁] at hRes₁
        rw [←hRes₁]
        simp only [Interleavable.interleave, interleaveWordStack, Matrix.transpose_apply,
          finMapTwoWords]
        rw! [Nat.sub_add_cancel (h := by omega)]
        rfl

omit [Nonempty ι] [DecidableEq ι] [Fintype A] [AddCommMonoid A] [Fintype F] [SampleableType F] in
/-- The even/odd analogue of `CA_split_rowwise_implies_CA`: if the interleaved pair formed by
the even-indexed and the odd-indexed rows of `u` is `e`-close to `C ^⋈ Fin (2 ^ ϑ)`, then `u`
is `e`-close to `C ^⋈ Fin (2 ^ (ϑ + 1))`. -/
theorem jointProximityNat_of_jointProximityNat₂_splitEvenOdd
    {ϑ : ℕ} (u : WordStack A (Fin (2 ^ (ϑ + 1))) ι) (e : ℕ) :
    let U₀ : WordStack A (Fin (2 ^ ϑ)) ι := (splitEvenOddRowWiseInterleavedWords (ϑ := ϑ) u).1
    let U₁ : WordStack A (Fin (2 ^ ϑ)) ι := (splitEvenOddRowWiseInterleavedWords (ϑ := ϑ) u).2
    jointProximityNat₂ (u₀ := ⋈|U₀) (u₁ := ⋈|U₁) (e := e) (C := C ^⋈ (Fin (2 ^ ϑ)))
      → jointProximityNat (u := u) (e := e) (C := C) := by
  classical
  intro U₀ U₁ h_close
  unfold jointProximityNat₂ jointProximityNat at h_close
  simp only at h_close
  replace h_close := (Code.closeToCode_iff_closeToCodeword_of_minDist ..).1 h_close
  rcases h_close with ⟨vSplit, hvSplit_mem, hvSplit_dist_le_e⟩
  replace hvSplit_dist_le_e :=
    (closeToWord_iff_exists_possibleDisagreeCols ..).1 hvSplit_dist_le_e
  rcases hvSplit_dist_le_e with ⟨D, hD_card_le_e, h_agree_outside_D⟩
  unfold jointProximityNat
  rw [Code.closeToCode_iff_closeToCodeword_of_minDist
    (u := ⋈|u) (e := e) (C := interleavedCodeSet (κ := Fin (2 ^ (ϑ + 1))) C)]
  let VSplit_rowwise := Matrix.transpose vSplit
  let VSplit_even_rowwise := Matrix.transpose (VSplit_rowwise 0)
  let VSplit_odd_rowwise := Matrix.transpose (VSplit_rowwise 1)
  let v_rowwise_finmap : WordStack A (Fin (2 ^ (ϑ + 1))) ι := fun rowIdx =>
    if h_even : rowIdx.val % 2 = 0 then
      VSplit_even_rowwise ⟨rowIdx.val / 2, by omega⟩
    else
      VSplit_odd_rowwise ⟨rowIdx.val / 2, by omega⟩
  let v_IC := ⋈|v_rowwise_finmap
  use v_IC
  constructor
  · intro rowIdx
    have h_vSplit_rows_mem : ∀ (i : Fin 2) (j : Fin (2 ^ ϑ)), (fun col ↦ vSplit col i j) ∈ C := by
      intro i j
      exact hvSplit_mem i j
    dsimp only [v_IC]
    by_cases h_even : rowIdx.val % 2 = 0
    · let j : Fin (2 ^ ϑ) := ⟨rowIdx.val / 2, by omega⟩
      have hRes := h_vSplit_rows_mem 0 j
      change (fun col => v_rowwise_finmap rowIdx col) ∈ C
      have h_fun : (fun col => v_rowwise_finmap rowIdx col) = fun col => vSplit col 0 j := by
        funext col
        dsimp [v_rowwise_finmap, VSplit_even_rowwise, VSplit_rowwise, j]
        rw [dite_eq_left h_even]
        rfl
      rw [h_fun]
      exact hRes
    · let j : Fin (2 ^ ϑ) := ⟨rowIdx.val / 2, by omega⟩
      have hRes := h_vSplit_rows_mem 1 j
      change (fun col => v_rowwise_finmap rowIdx col) ∈ C
      have h_fun : (fun col => v_rowwise_finmap rowIdx col) = fun col => vSplit col 1 j := by
        funext col
        dsimp [v_rowwise_finmap, VSplit_odd_rowwise, VSplit_rowwise, j]
        rw [dite_eq_right h_even]
        rfl
      rw [h_fun]
      exact hRes
  · refine (closeToWord_iff_exists_possibleDisagreeCols _ _ _).2 ⟨D, hD_card_le_e, ?_⟩
    intro colIdx h_colIdx_notin_D
    funext rowIdx
    dsimp only [v_IC]
    have hRes0 :
        interleaveWordStack
            ((splitEvenOddRowWiseInterleavedWords (ϑ := ϑ) u).1)
            colIdx
          = vSplit colIdx 0 := by
      exact congrFun (h_agree_outside_D colIdx h_colIdx_notin_D) 0
    have hRes1 :
        interleaveWordStack
            ((splitEvenOddRowWiseInterleavedWords (ϑ := ϑ) u).2)
            colIdx
          = vSplit colIdx 1 := by
      exact congrFun (h_agree_outside_D colIdx h_colIdx_notin_D) 1
    by_cases h_even : rowIdx.val % 2 = 0
    · have h_row_val : rowIdx.val = 2 * (rowIdx.val / 2) := by
        have h_divmod := Nat.mod_add_div rowIdx.val 2
        omega
      have h_row_eq :
          (⟨2 * (rowIdx.val / 2), by omega⟩ : Fin (2 ^ (ϑ + 1))) = rowIdx := by
        apply Fin.eq_of_val_eq
        exact h_row_val.symm
      have hRes₀ := congrFun hRes0 ⟨rowIdx.val / 2, by omega⟩
      dsimp [splitEvenOddRowWiseInterleavedWords] at hRes₀
      change u rowIdx colIdx = v_rowwise_finmap rowIdx colIdx
      simpa [v_rowwise_finmap, h_even, VSplit_even_rowwise, VSplit_rowwise,
        Matrix.transpose, h_row_eq] using hRes₀
    · have h_row_val : rowIdx.val = 2 * (rowIdx.val / 2) + 1 := by
        have h_divmod := Nat.mod_add_div rowIdx.val 2
        omega
      have h_row_eq :
          (⟨2 * (rowIdx.val / 2) + 1, by omega⟩ : Fin (2 ^ (ϑ + 1))) = rowIdx := by
        apply Fin.eq_of_val_eq
        exact h_row_val.symm
      have hRes₁ := congrFun hRes1 ⟨rowIdx.val / 2, by omega⟩
      dsimp [splitEvenOddRowWiseInterleavedWords] at hRes₁
      change u rowIdx colIdx = v_rowwise_finmap rowIdx colIdx
      simpa [v_rowwise_finmap, h_even, VSplit_odd_rowwise, VSplit_rowwise,
        Matrix.transpose, h_row_eq] using hRes₁

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype A] [DecidableEq A] [Fintype F] in
omit [SampleableType F] in
/-- `[⊗_{i=0}^{ϑ-1}(1-r_i, r_i)] · [ - u₀ -; ...; - u_{2^ϑ-1} - ]`
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
    simp only [Fin.val_castSucc]
    congr 1
  have h_tensor_split_1 :
    multilinearWeight r ⟨i + 2 ^ ϑ, by omega⟩ = multilinearWeight r_init i * (r (Fin.last ϑ)) := by
    dsimp only [multilinearWeight]
    rw [Fin.prod_univ_castSucc]
    simp_rw [Nat.testBit_true_eq_getBit_eq_1]
    simp_rw [h_getLastBit_add_pow_2]
    simp only [Fin.val_castSucc, ↓reduceIte]
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
omit [SampleableType F] in
/-- The first-challenge analogue of `multilinearCombine_recursive_form`: a multilinear
combination over `2 ^ (ϑ + 1)` rows is the multilinear combination, over the remaining
challenges, of the affine line through the even- and the odd-indexed rows at the first
challenge. -/
lemma multilinearCombine_recursive_form_first {ϑ : ℕ}
    (u : WordStack A (Fin (2 ^ (ϑ + 1))) ι) (r_challenges : Fin (ϑ + 1) → F) :
    let U_even := (splitEvenOddRowWiseInterleavedWords (ϑ := ϑ) u).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (ϑ := ϑ) u).2
    let r_tail : Fin ϑ → F := fun j => r_challenges (Fin.succ j)
    multilinearCombine (F := F) u r_challenges =
    multilinearCombine (F := F)
      (affineLineEvaluation (F := F) U_even U_odd (r_challenges 0)) r_tail := by
  intro U_even U_odd r_tail
  funext colIdx
  unfold multilinearCombine
  let f : ℕ → A := fun j =>
    if hj : j < 2 ^ (ϑ + 1) then
      multilinearWeight r_challenges ⟨j, hj⟩ • u ⟨j, hj⟩ colIdx
    else 0
  have h_lhs_as_f :
      (∑ rowIdx : Fin (2 ^ (ϑ + 1)),
        multilinearWeight r_challenges rowIdx • u rowIdx colIdx)
      = ∑ rowIdx : Fin (2 ^ (ϑ + 1)), f rowIdx := by
    apply Finset.sum_congr rfl
    intro rowIdx _
    simp [f]
  rw [h_lhs_as_f]
  rw [show ∑ x : Fin (2 ^ (ϑ + 1)), f x =
      ∑ x : Fin (2 ^ ϑ), f (2 * x) + ∑ x : Fin (2 ^ ϑ), f (2 * x + 1) by
    rw [pow_succ]; exact (Fin.sum_even_add_odd _ f).symm]
  simp only [f]
  simp only [U_even, U_odd, splitEvenOddRowWiseInterleavedWords]
  have h_tensor_even : ∀ i : Fin (2 ^ ϑ),
      multilinearWeight r_challenges ⟨2 * i, by omega⟩ =
      multilinearWeight r_tail i * (1 - r_challenges 0) := by
    intro i
    unfold multilinearWeight
    rw [Fin.prod_univ_succ]
    have h_bit0 : (2 * i.val).testBit 0 = false := by
      rw [Nat.testBit_false_eq_getBit_eq_0]
      exact Nat.getBit_zero_of_two_mul (n := i.val)
    have h_bit0' : (2 * i.val).testBit (↑(0 : Fin (ϑ + 1))) = false := by
      change (2 * i.val).testBit 0 = false
      exact h_bit0
    have h_prod :
        (∏ x : Fin ϑ,
          if (2 * i.val).testBit x.succ = true then r_challenges x.succ
          else 1 - r_challenges x.succ)
        = ∏ j : Fin ϑ, if i.val.testBit j.val = true then r_tail j else 1 - r_tail j := by
      apply Finset.prod_congr rfl
      intro j _
      have h_test :
          ((2 * i.val).testBit (↑j.succ) = true) = (i.val.testBit j.val = true) := by
        rw [Nat.testBit_true_eq_getBit_eq_1, Nat.testBit_true_eq_getBit_eq_1]
        have h_getBit :
            Nat.getBit (j.val + 1) (2 * i.val) = Nat.getBit j.val i.val := by
          exact Nat.getBit_eq_succ_getBit_of_mul_two (n := i.val) (k := j.val)
        change (Nat.getBit (j.val + 1) (2 * i.val) = 1) = (Nat.getBit j.val i.val = 1)
        exact congrArg (fun t : ℕ => t = 1) h_getBit
      have h_succ : (↑j.succ : ℕ) = ↑j + 1 := by simp [Fin.succ]
      have h_test' :
          ((2 * i.val).testBit (↑j + 1) = true) = (i.val.testBit j.val = true) := by
        rw [← h_succ]
        exact h_test
      by_cases hcond : (2 * i.val).testBit (↑j + 1) = true
      · have hcond' : i.val.testBit j.val = true := h_test'.mp hcond
        simp [hcond, hcond', r_tail]
      · have hcond' : ¬ i.val.testBit j.val = true := by
          intro hbit
          exact hcond (h_test'.mpr hbit)
        simp [hcond, hcond', r_tail]
    rw [h_prod]
    simp
    ring
  have h_tensor_odd : ∀ i : Fin (2 ^ ϑ),
      multilinearWeight r_challenges ⟨2 * i + 1, by omega⟩ =
      multilinearWeight r_tail i * (r_challenges 0) := by
    intro i
    unfold multilinearWeight
    rw [Fin.prod_univ_succ]
    have h_bit0 : (2 * i.val + 1).testBit 0 = true := by
      rw [Nat.testBit_true_eq_getBit_eq_1]
      unfold Nat.getBit
      simp [Nat.and_one_is_mod]
    have h_bit0' : (2 * i.val + 1).testBit (↑(0 : Fin (ϑ + 1))) = true := by
      change (2 * i.val + 1).testBit 0 = true
      exact h_bit0
    have h_prod :
        (∏ x : Fin ϑ,
          if (2 * i.val + 1).testBit x.succ = true then r_challenges x.succ
          else 1 - r_challenges x.succ)
        = ∏ j : Fin ϑ, if i.val.testBit j.val = true then r_tail j else 1 - r_tail j := by
      apply Finset.prod_congr rfl
      intro j _
      have h_test :
          ((2 * i.val + 1).testBit (↑j.succ) = true) = (i.val.testBit j.val = true) := by
        rw [Nat.testBit_true_eq_getBit_eq_1, Nat.testBit_true_eq_getBit_eq_1]
        have h_test := congrArg (fun t : ℕ => t = 1)
          (Nat.getBit_eq_succ_getBit_of_mul_two_add_one (n := i.val) (k := j.val))
        simp only [Fin.succ, Nat.add_comm] at h_test ⊢
        exact h_test
      have h_succ : (↑j.succ : ℕ) = ↑j + 1 := by simp [Fin.succ]
      have h_test' :
          ((2 * i.val + 1).testBit (↑j + 1) = true) = (i.val.testBit j.val = true) := by
        rw [← h_succ]
        exact h_test
      simp only [Fin.val_succ, h_test', r_tail]
    rw [h_prod]
    simp
    ring
  simp_rw [h_tensor_even, h_tensor_odd]
  have h_even_lt : ∀ x : Fin (2 ^ ϑ), 2 * x.val < 2 ^ (ϑ + 1) := by
    intro x; omega
  have h_odd_lt : ∀ x : Fin (2 ^ ϑ), 2 * x.val + 1 < 2 ^ (ϑ + 1) := by
    intro x; omega
  simp only [h_even_lt, ↓reduceDIte, h_odd_lt]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [affineLineEvaluation, Pi.add_apply, Pi.smul_apply]
  simp only [Word, Pi.smul_apply, Pi.add_apply, smul_add]
  rw [←smul_assoc, ←smul_assoc]
  rw [smul_eq_mul, smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype A] [DecidableEq A] [Fintype F] in
omit [SampleableType F] in
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

end
