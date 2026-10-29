/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Binary Basefold: noncompliant blocks at the end of the protocol

At the last statement index, block `j` of the oracles is *bad* when its oracle is not compliant
with the next oracle (the final constant, for the last block) under the block's folding
challenges. The query-phase soundness analysis works with the highest bad block, above which
every block is compliant.

## Main definitions

* `IsBadBlock`: block `j` is not compliant.
* `badBlockSet`, `highestBadBlock`: the bad blocks, and the highest one when one exists.

## Main statements

* `isBadBlock_highestBadBlock`, `not_isBadBlock_of_highestBadBlock_lt`: the highest bad block
  is bad, and every block above it is not.
* `uniqueDecodingClose_of_not_isBadBlock`: the oracle of a block that is not bad is within the
  unique-decoding radius.
* `prob_extractSuffixFromChallenge_mem_eq`: for a uniform query point `v ∈ S⁽⁰⁾`, its suffix at
  any domain index is uniform.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Numbering follows the archived revision of [DP24]. A block that is not bad has a compliant
  oracle in the sense of Definition 4.18; the highest bad block is the index `i*` of the proof of
  Proposition 4.24.
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open Probability
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

section QueryPhaseSoundnessStatements

open QueryPhase

/-- Block `j` is *bad*: its oracle is not compliant, over the block's `ϑ` folding challenges,
with the oracle of block `j + 1`, or with the constant function of the final constant if `j` is
the last block. -/
def IsBadBlock
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) :
    Fin (nBlocks (ϑ := ϑ) (ℓ := ℓ)) → Prop := fun j =>
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := blockSize_le_rounds ℓ ϑ
  if hj : j.val + 1 < nBlocks then
    let curDomainIdx : Fin r := ⟨j.val * ϑ, by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := j.val * ϑ)
      have h := oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)
      exact (Nat.le_add_right _ _).trans h⟩
    let destIdx : Fin r := ⟨j.val * ϑ + ϑ, by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := j.val * ϑ + ϑ)
      exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)⟩
    ¬ IsCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := curDomainIdx) (steps := ϑ) (destIdx := destIdx)
        (h_destIdx := by rfl) (h_destIdx_le := by
          exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j))
        (f_i := oStmtIn j)
        (f_i_plus_steps :=
          getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
            (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j) (hj := by
              simp only [nBlocks] at hj ⊢
              exact hj) (destDomainIdx := destIdx) (h_destDomainIdx := by rfl))
        (challenges :=
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
            stmtIn.challenges (k := j.val * ϑ) (h := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)))
  else
    let j_last := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    let k := j_last.val * ϑ
    have h_k : k = ℓ - ϑ := by
      dsimp [j_last, k]
      simp only [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.div_mul_cancel (hdiv.out),
        one_mul]
    have hk_add : k + ϑ = ℓ := by
      simp only [h_k] at h_k ⊢
      exact Nat.sub_add_cancel (by omega)
    have hk_le : k ≤ ℓ := by omega
    ¬ IsCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k); omega
          ⟩) (steps := ϑ) (destIdx := ⟨k + ϑ, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k + ϑ); omega
          ⟩)
        (h_destIdx := by rfl)
        (h_destIdx_le := by
          -- k + ϑ = ℓ, so the bound holds
          simp only [hk_add, le_refl])
        (f_i := oStmtIn j_last)
        (f_i_plus_steps := fun _ => stmtIn.finalConstant)
        (challenges :=
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
            stmtIn.challenges (k := k) (h := by
              simp only [hk_add, Fin.val_last, le_refl]))

open Classical in
/-- The set of bad blocks. -/
def badBlockSet
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) :
    Finset (Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) :=
  Finset.filter (IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (stmtIn := stmtIn) (oStmtIn := oStmtIn)) Finset.univ

open Classical in
/-- The highest bad block, given that some block is bad. -/
noncomputable def highestBadBlock
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_exists : (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)).Nonempty) :
    Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) :=
  (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (stmtIn := stmtIn) (oStmtIn := oStmtIn)).max' h_exists

omit [SampleableType L] [DecidableEq 𝔽q] in
/-- The highest bad block is bad. -/
lemma isBadBlock_highestBadBlock
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_exists : (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)).Nonempty) :
    IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists) := by
  classical
  exact (Finset.mem_filter.mp (Finset.max'_mem _ h_exists)).2

omit [SampleableType L] [DecidableEq 𝔽q] in
/-- No block above the highest bad block is bad. -/
lemma not_isBadBlock_of_highestBadBlock_lt
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_exists : (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)).Nonempty)
    {j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))}
    (hlt : highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists < j) :
    ¬ IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) j := by
  classical
  intro hj_bad
  have hj_mem :
      j ∈ badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) := by
    exact (Finset.mem_filter.mpr ⟨by simp, hj_bad⟩)
  have hle : j ≤ highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists := by
      dsimp [highestBadBlock]
      exact
        Finset.le_max' (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (stmtIn := stmtIn) (oStmtIn := oStmtIn)) j hj_mem
  exact not_lt_of_ge hle hlt

omit [SampleableType L] [DecidableEq 𝔽q] in
/-- If block `j` is not bad, its oracle, read at any index equal to its domain index `j·ϑ`, is
within the unique-decoding radius: compliance gives fiberwise closeness, which implies
closeness. -/
lemma uniqueDecodingClose_of_not_isBadBlock
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_good : ¬ IsBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j)
    {destIdx : Fin r}
    (h_idx : (⟨j.val * ϑ, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((Nat.le_add_right _ _).trans
        (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
          (i := Fin.last ℓ) (j := j)))⟩ : Fin r) = destIdx) :
    UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      destIdx (fun y => (oStmtIn j) (cast (by rw [h_idx]) y)) := by
  subst h_idx; simp only [cast_eq]
  -- Unfold IsBadBlock: it's `¬IsCompliant` in both branches.
  simp only [IsBadBlock] at h_good
  by_cases h_last : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
  · -- Intermediate block: IsBadBlock = ¬IsCompliant
    simp only [h_last, ↓reduceDIte, not_not] at h_good
    obtain ⟨h_fw, _, _⟩ := h_good
    exact uniqueDecodingClose_of_fiberwiseClose 𝔽q β _ ϑ (by rfl)
      (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j))
      (oStmtIn j) h_fw
  · -- Final block: need getLastOraclePositionIndex = j
    simp only [h_last, ↓reduceDIte, not_not] at h_good
    have h_j_eq : getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ) = j := by
      apply Fin.ext
      simp only [getLastOraclePositionIndex, toOutCodewordsCount_last]
      have h_ge : nBlocks (ℓ := ℓ) (ϑ := ϑ) ≤ j.val + 1 := Nat.le_of_not_gt h_last
      simp only [nBlocks, toOutCodewordsCount_last] at h_ge
      have h_lt : j.val < nBlocks (ℓ := ℓ) (ϑ := ϑ) := j.isLt
      simp only [nBlocks, toOutCodewordsCount_last] at h_lt
      omega
    subst h_j_eq
    obtain ⟨h_fw, _, _⟩ := h_good
    exact uniqueDecodingClose_of_fiberwiseClose 𝔽q β _ ϑ (by rfl)
      (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
        (i := Fin.last ℓ) (j := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)))
      (oStmtIn (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ))) h_fw

omit [SampleableType L] [DecidableEq 𝔽q] [NeZero ℓ] in
open Classical in
/-- For a uniform query point `v ∈ S⁽⁰⁾`, its suffix at domain index `destIdx` lies in `D` with
probability `|D| / |S⁽ᵈᵉˢᵗᴵᵈˣ⁾|`: every fiber of the iterated quotient map has `2^destIdx`
points. -/
lemma prob_extractSuffixFromChallenge_mem_eq
    (destIdx : Fin r) (h_destIdx_le : destIdx ≤ ℓ)
    (D : Finset (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)) :
    Pr{ let v ←$ᵗ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∈ D
    ] = (D.card : ENNReal) /
        Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := by
  let suffix (v : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) :
      sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
    extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le)
  classical
  have hf (y) : Nat.card {v // suffix v = y} = 2 ^ destIdx.val := by
    let fiber := quotientFiber 𝔽q β (i := (0 : Fin r)) (steps := destIdx.val)
      (h_destIdx := by simp) (h_destIdx_le := h_destIdx_le) y
    let fiberPoint (j : Fin (2 ^ destIdx.val)) : {v // suffix v = y} :=
      ⟨fiber j, (eq_iteratedQuotientMap_of_mem_quotientFiber_range 𝔽q β
        (i := (0 : Fin r)) (steps := destIdx.val) (h_destIdx := by simp)
        (h_destIdx_le := h_destIdx_le) (x := fiber j) (y := y) ⟨j, rfl⟩).symm⟩
    have hfiber : Function.Bijective fiberPoint := by
      constructor
      · intro j j' h
        exact quotientFiber_injective 𝔽q β (0 : Fin r) destIdx.val
          (by simp) h_destIdx_le y (congrArg Subtype.val h)
      · intro v
        refine ⟨pointToIterateQuotientIndex 𝔽q β (i := (0 : Fin r))
          (steps := destIdx.val) (h_destIdx := by simp) (h_destIdx_le := h_destIdx_le) v.val, ?_⟩
        apply Subtype.ext
        exact (eq_iteratedQuotientMap_iff_quotientFiber_apply_eq 𝔽q β (i := (0 : Fin r))
          (steps := destIdx.val) (h_destIdx := by simp) (h_destIdx_le := h_destIdx_le) v.val y).mp
          v.property.symm
    rw [← Nat.card_congr (Equiv.ofBijective fiberPoint hfiber), Nat.card_fin]
  have hfiber (y) : (Finset.univ.filter (fun v => suffix v = y)).card =
      2 ^ destIdx.val := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact hf y
  have hpre (T : Finset (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)) :
      (Finset.univ.filter (fun v => suffix v ∈ T)).card = T.card * 2 ^ destIdx.val := by
    rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ T suffix]
    exact Finset.sum_const_nat (fun y _ => hfiber y)
  have hcard : Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate 0) =
      Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) * 2 ^ destIdx.val := by
    simpa only [Finset.mem_univ, Finset.filter_true, Finset.card_univ] using hpre Finset.univ
  rw [SampleableType.prEvent_uniformSample, hpre, hcard, Nat.cast_mul, Nat.cast_mul]
  rw [mul_comm (D.card : ENNReal),
    mul_comm (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : ENNReal)]
  exact ENNReal.mul_div_mul_left (a := (D.card : ENNReal))
    (b := (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : ENNReal))
    (c := ((2 ^ destIdx.val : ℕ) : ENNReal)) (by positivity) (by simp)

end QueryPhaseSoundnessStatements

end

end Binius.BinaryBasefold
