/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations

/-!
# Binary Basefold: decoding at the final sum-check step

If the oracles are fold-consistent through the final constant, the first oracle decodes to a
multilinear polynomial `t` (`exists_extractMlp_eq_some_of_finalSumcheckOracleConsistent`),
and the final constant is `t` evaluated at the challenges
(`eval_eq_final_constant_of_extractMlp_eq_some`): by induction along the oracles, each decoded
oracle is the honest fold of the decoded first oracle. The final sum-check step's knowledge-state
function uses both across its message.
-/

@[expose] public section

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
  [SampleableType L]
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
variable [hdiv : Fact (ϑ ∣ ℓ)]

omit [SampleableType L] in
/-- Fiberwise closeness at a source index equal to zero yields successful extraction. -/
private lemma extractMLP_some_of_fiberwiseClose_at_zero
    {zeroIdx destIdx : Fin r} (steps : ℕ) (hzero : zeroIdx = 0)
    (hdest : destIdx.val = zeroIdx.val + steps) (hle : destIdx.val ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) zeroIdx)
    (hfw : FiberwiseClose 𝔽q β zeroIdx steps hdest hle f) :
    ∃ tpoly, extractMlp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
      (fun x => f (cast (by cases hzero; rfl) x)) = some tpoly := by
  cases hzero
  exact extractMlp_zero_isSome_of_fiberwiseClose 𝔽q β
    (h_destIdx := by simpa using hdest) (h_destIdx_le := hle) f hfw


omit [SampleableType L] in
/-- If the oracles are fold-consistent through the final constant, the first oracle is
unique-decoding close to the code, so decoding it succeeds. -/
lemma exists_extractMlp_eq_some_of_finalSumcheckOracleConsistent
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (h_oracle_consistency : FinalSumcheckOracleConsistent 𝔽q β
      (stmtOut := stmtOut) (oStmtOut := oStmt)) :
    -- extractMlp is used in `finalSumcheckRbrExtractor`
    ∃ tpoly, extractMlp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (f := getFirstOracle 𝔽q β oStmt) = some tpoly := by
  -- Proof strategy: the first oracle must be fiberwise-close due to IsCompliant
    -- constraint, hence it is UDR-close.
  have h_le : ϑ ≤ ℓ := blockSize_le_rounds ℓ ϑ
  have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  dsimp only [FinalSumcheckOracleConsistent] at h_oracle_consistency
  rcases h_oracle_consistency with ⟨h_oracle_cons, h_final_cons⟩
  let j0 : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) := ⟨0, by
    exact Nat.pos_of_neZero (toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
  ⟩
  by_cases h_ℓ_eq_ϑ : ℓ = ϑ
  · -- We reason on h_final_cons
    have h_div : ℓ / ϑ = 1 := by
      rw [h_ℓ_eq_ϑ]; rw [Nat.div_self (n := ϑ) (H := by omega)]
    have h_getLastOraclePositionIndex_last : getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ) = 0 := by
      dsimp only [getLastOraclePositionIndex]
      simp only [toOutCodewordsCount_last, Fin.mk_eq_zero, h_div]
    let jLast : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    have h_jLast_eq_zero : jLast = 0 := by
      dsimp only [jLast]
      exact h_getLastOraclePositionIndex_last
    have h_jLast_val : jLast.val = 0 := by
      exact congrArg Fin.val h_jLast_eq_zero
    let zeroIdxLast : Fin r := ⟨↑jLast * ϑ, by
      have h_r_pos : 0 < r := Nat.pos_of_neZero r
      rw [h_jLast_val, zero_mul]
      exact h_r_pos⟩
    let destIdxLast : Fin r := ⟨↑jLast * ϑ + ϑ, by
      have h_ℓ_lt_r : ℓ < r := by omega
      have h_ϑ_lt_r : ϑ < r := by
        rw [← h_ℓ_eq_ϑ]
        exact h_ℓ_lt_r
      rw [h_jLast_val, zero_mul, zero_add]
      exact h_ϑ_lt_r⟩
    let challengesLast : Fin ϑ → L := fun cId =>
      stmtOut.challenges ⟨↑jLast * ϑ + ↑cId, by
        simp only [h_jLast_eq_zero, Fin.coe_ofNat_eq_mod, toOutCodewordsCount_last, h_ℓ_eq_ϑ,
          Nat.zero_mod, zero_mul, zero_add, Fin.val_last, cId.isLt]⟩
    have h_zeroIdxLast : zeroIdxLast.val = 0 := by
      simp [zeroIdxLast, h_jLast_eq_zero]
    have h_zeroIdxLast_eq : zeroIdxLast = 0 := Fin.eq_of_val_eq h_zeroIdxLast
    have h_destIdxLast : destIdxLast = 0 + ϑ := by
      simp [destIdxLast, h_jLast_eq_zero]
    have h_destIdxLast_le : destIdxLast ≤ ℓ := by
      simp only [h_jLast_eq_zero, Fin.coe_ofNat_eq_mod, toOutCodewordsCount_last, h_ℓ_eq_ϑ,
        Nat.zero_mod, zero_mul, zero_add, le_refl, destIdxLast]
    have h_compl0 :
        IsCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := zeroIdxLast)
          (steps := ϑ)
          (destIdx := destIdxLast)
          (h_destIdx := by
            rw [h_zeroIdxLast_eq]
            exact h_destIdxLast)
          (h_destIdx_le := h_destIdxLast_le)
          (f_i := oStmt jLast)
          (f_i_plus_steps := fun _ => stmtOut.finalConstant)
          (challenges := challengesLast) := by
      have h_final_cons' := h_final_cons
      simp only [jLast, zeroIdxLast, destIdxLast, challengesLast] at h_final_cons' ⊢
      exact h_final_cons'
    rcases (extractMLP_some_of_fiberwiseClose_at_zero 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ϑ)
      (zeroIdx := zeroIdxLast)
      (hzero := Fin.ext (by simpa using h_zeroIdxLast))
      (destIdx := destIdxLast)
      (hdest := by simpa only [h_zeroIdxLast] using h_destIdxLast)
      (hle := h_destIdxLast_le)
      (f := oStmt jLast)
      (hfw := h_compl0.1)) with
      ⟨tpoly, h_extract⟩
    refine ⟨tpoly, ?_⟩
    convert h_extract using 1
    apply congrArg (fun f => extractMlp 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) f)
    funext x
    dsimp [getFirstOracle]
    refine OracleStatement.oracle_eval_congr (oStmtIn := oStmt)
      (h_j := h_jLast_eq_zero.symm) (h_x := ?_)
    simp only [Fin.coe_ofNat_eq_mod]
    exact (cast_cast _ _ _).symm
  · -- We reason on h_oracle_cons
    dsimp only [OracleFoldingConsistent] at h_oracle_cons
    have h_lt : ϑ < ℓ := by omega
    have h_div_gt_1 : ℓ / ϑ > 1 := by
      have h_res := (Nat.div_lt_div_right (a := ϑ) (b := ϑ) (c := ℓ) (ha := by omega)
        hdiv.out).mpr h_lt
      rw [Nat.div_self (n := ϑ) (H := by omega)] at h_res
      exact h_res
    have h_j0_next_lt : ↑j0 + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ) := by
      dsimp only [j0]
      rw [toOutCodewordsCount_last]
      exact h_div_gt_1
    let zeroIdx0 : Fin r := ⟨↑j0 * ϑ, by
      have h_r_pos : 0 < r := Nat.pos_of_neZero r
      dsimp only [j0]
      rw [zero_mul]
      exact h_r_pos⟩
    let destIdx0 : Fin r := ⟨↑j0 * ϑ + ϑ, by
      have h_ℓ_lt_r : ℓ < r := by omega
      have h_ϑ_lt_r : ϑ < r := lt_of_le_of_lt h_le h_ℓ_lt_r
      dsimp only [j0]
      rw [zero_mul, zero_add]
      exact h_ϑ_lt_r⟩
    have h_zeroIdx0 : zeroIdx0.val = 0 := by
      simp [zeroIdx0, j0]
    have h_destIdx0 : destIdx0 = 0 + ϑ := by
      simp [destIdx0, j0]
    have h_destIdx0_le : destIdx0 ≤ ℓ := by
      dsimp only [destIdx0, j0]
      rw [zero_mul, zero_add]
      exact h_le
    have h_k_next_le_last : ↑j0 * ϑ + ϑ ≤ Fin.last ℓ := by
      exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
        (i := Fin.last ℓ) (j := j0) (hj := h_j0_next_lt)
    let fNext0 : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx0 :=
      getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := Fin.last ℓ)
        oStmt j0 h_j0_next_lt
        (destDomainIdx := destIdx0)
        (h_destDomainIdx := by simp only [destIdx0])
    let challenges0 : Fin ϑ → L :=
      getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
        (challenges := stmtOut.challenges) (k := ↑j0 * ϑ) (h := h_k_next_le_last)
    have h_isCompliant_f₀ :
        IsCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := zeroIdx0) (steps := ϑ)
          (destIdx := destIdx0)
          (h_destIdx := by
            rw [h_zeroIdx0]
            exact h_destIdx0)
          (h_destIdx_le := h_destIdx0_le)
          (f_i := oStmt ⟨↑j0, by exact j0.isLt⟩)
          (f_i_plus_steps := fNext0)
          (challenges := challenges0) := by
      have h_oracle_cons' := h_oracle_cons j0 h_j0_next_lt
      simp only [zeroIdx0, destIdx0, fNext0, challenges0] at h_oracle_cons' ⊢
      exact h_oracle_cons'
    rcases (extractMLP_some_of_fiberwiseClose_at_zero 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ϑ)
      (zeroIdx := zeroIdx0)
      (hzero := Fin.ext (by simpa using h_zeroIdx0))
      (destIdx := destIdx0)
      (hdest := by simpa only [h_zeroIdx0] using h_destIdx0)
      (hle := h_destIdx0_le)
      (f := oStmt ⟨↑j0, by exact j0.isLt⟩)
      (hfw := h_isCompliant_f₀.1)) with
      ⟨tpoly, h_extract⟩
    refine ⟨tpoly, ?_⟩
    dsimp only [getFirstOracle, j0] at h_extract ⊢
    exact h_extract

/-! ### Decoded oracles along the folding chain

Under fold-consistency through the final constant, the unique-decoding codeword of each oracle is
the fold of the decoded first oracle by the challenges so far. -/
omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
private theorem uniqueDecodingCodeword_heq_of_fin_eq
    {i j : Fin r} (hij : i = j)
    (h_i : i ≤ ℓ) (h_j : j ≤ ℓ)
    {f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i}
    {g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j}
    (hfg : HEq f g)
    (h₁ : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (f := f))
    (h₂ : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := j) (f := g)) :
    HEq
      (uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (h_i := h_i) (f := f) (h_within_radius := h₁))
      (uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := j) (h_i := h_j) (f := g) (h_within_radius := h₂)) := by
  cases hij
  cases hfg
  rfl


private def finalOracleBlockIdx
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Fin r :=
  ⟨t * ϑ, by
    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ)
    exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩)⟩

private def finalPrefixChallenges
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    Fin (t * ϑ) → L := fun cId =>
  stmtOut.challenges ⟨cId, by
    exact lt_of_lt_of_le cId.isLt
      (oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))⟩

private def finalBlockChallenges
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    Fin ϑ → L := fun cId =>
  stmtOut.challenges ⟨t * ϑ + cId, by
    have h_lt : t * ϑ + cId.val < t * ϑ + ϑ := by
      omega
    exact lt_of_lt_of_le h_lt
      (oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))⟩

private def finalDecodedPrefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (finalOracleBlockIdx (ℓ := ℓ)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := 0) (steps := t * ϑ)
    (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_destIdx := by
      dsimp [finalOracleBlockIdx]
      simp only [zero_add])
    (h_destIdx_le := by
      dsimp [finalOracleBlockIdx]
      exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))
    (f := f₀)
    (r_challenges := finalPrefixChallenges stmtOut t ht)

private def finalOracleRaw
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) := by
  change OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (ϑ := ϑ) (i := Fin.last ℓ) ⟨t, ht⟩
  exact oStmtOut ⟨t, ht⟩

private def finalOracleDecoded
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
      (f := finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_i := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))
    (f := finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)
    (h_within_radius := h_close)


omit [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] in
private theorem finalOracleBlockIdx_zero
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht = 0 := by
  apply Fin.eq_of_val_eq
  dsimp [finalOracleBlockIdx]
  simp only [zero_mul]

private def FinalOracleClose
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Prop :=
  UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (f := oStmtOut ⟨t, ht⟩)


omit [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero ϑ] in
private theorem finalDecodedPrefixFold_step
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        t (Nat.lt_of_succ_lt ht))
      (steps := ϑ)
      (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (t + 1) ht)
      (h_destIdx := by
        dsimp [finalOracleBlockIdx]
        rw [Nat.add_mul, Nat.one_mul])
      (h_destIdx_le := by
        dsimp [finalOracleBlockIdx]
        rw [Nat.add_mul, Nat.one_mul]
        exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
      (f := finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t (Nat.lt_of_succ_lt ht))
      (r_challenges := finalBlockChallenges
        (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht) =
    finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ (t + 1) ht := by
  dsimp [finalDecodedPrefixFold]
  have h_transitivity := iteratedFold_iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (0 : Fin r))
    (midIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t (Nat.lt_of_succ_lt ht))
    (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t + 1) ht)
    (steps₁ := t * ϑ) (steps₂ := ϑ)
    (h_midIdx := by
      dsimp [finalOracleBlockIdx]
      simp only [zero_add])
    (h_destIdx := by
      dsimp [finalOracleBlockIdx]
      simp only [zero_add]
      rw [Nat.add_mul, Nat.one_mul])
    (h_destIdx_le := by
      dsimp [finalOracleBlockIdx]
      rw [Nat.add_mul, Nat.one_mul]
      exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
    (f := f₀)
    (r_challenges₁ := finalPrefixChallenges
      (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut t (Nat.lt_of_succ_lt ht))
    (r_challenges₂ := finalBlockChallenges
      (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht)
  rw [h_transitivity]
  funext y
  have h_steps_eq : t * ϑ + ϑ = (t + 1) * ϑ := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [iteratedFold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (0 : Fin r)) (steps := t * ϑ + ϑ) (steps' := (t + 1) * ϑ)
    (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t + 1) ht)
    (h_destIdx := by
      dsimp [finalOracleBlockIdx]
      simp only [zero_add]
      rw [Nat.add_mul, Nat.one_mul])
    (h_destIdx_le := by
      dsimp [finalOracleBlockIdx]
      rw [Nat.add_mul, Nat.one_mul]
      exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
    (h_steps_eq_steps' := h_steps_eq)
    (f := f₀)
    (r_challenges := Fin.append
      (finalPrefixChallenges
        (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut t (Nat.lt_of_succ_lt ht))
      (finalBlockChallenges
        (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht))
    (y := y)]
  have h_challenges_eq :
      (fun cId : Fin ((t + 1) * ϑ) =>
        Fin.append
          (finalPrefixChallenges
            (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut t (Nat.lt_of_succ_lt ht))
          (finalBlockChallenges
            (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht)
          ⟨cId, by
            have h_cast_lt : cId.val < t * ϑ + ϑ := by
              have h_lt' : cId.val < (t + 1) * ϑ := cId.isLt
              omega
            exact h_cast_lt⟩) =
      finalPrefixChallenges (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut (t + 1) ht := by
    funext cId
    dsimp only [finalPrefixChallenges, finalBlockChallenges, Fin.append, Fin.addCases]
    by_cases h : cId.val < t * ϑ
    · simp only [h, ↓reduceDIte, Fin.castLT_mk]
    · simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, eq_rec_constant]
      congr 1
      simp only [Fin.mk.injEq]
      omega
  rw [h_challenges_eq]

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
private theorem firstOracleDecoded_eq_f₀
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_close_first : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (f := getFirstOracle 𝔽q β oStmtOut))
    (h_dec0_eq_f0 :
      uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀)
    (h_close0 : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (f := getFirstOracle 𝔽q β oStmtOut)) :
    uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
      (h_within_radius := h_close0) = f₀ := by
  exact h_dec0_eq_f0

omit [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
private theorem finalOracleRaw_zero_heq_getFirstOracle
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    HEq
      (finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht)
      (getFirstOracle 𝔽q β oStmtOut) := by
  have h_idx0 := finalOracleBlockIdx_zero
    (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ht
  have h_dom :
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate
        (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)) =
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) := by
    exact congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i)) h_idx0
  have h_j0 :
      (⟨0, ht⟩ : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ))) =
      ⟨0, by
        let := instNeZeroNatToOutCodewordsCount ℓ ϑ (Fin.last ℓ)
        exact Nat.pos_of_neZero (toOutCodewordsCount ℓ ϑ (Fin.last ℓ))⟩ := by
    apply Fin.eq_of_val_eq
    rfl
  exact funext_heq h_dom (fun _ => rfl) (by
    intro y
    apply heq_of_eq
    cases h_j0
    dsimp [finalOracleRaw, getFirstOracle]
    exact congrArg (oStmtOut 0) ((cast_cast _ _ y).trans (cast_eq _ y)).symm)

omit [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
private theorem finalOracleClose_zero_eq_first
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close0 : FinalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht) :
    UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (f := getFirstOracle 𝔽q β oStmtOut) := by
  classical
  have h_idx0 := finalOracleBlockIdx_zero
    (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ht
  change UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)
      (f := finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht) at h_close0
  exact uniqueDecodingClose_congr (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_idx0
    (finalOracleRaw_zero_heq_getFirstOracle (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut ht)
    h_close0

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
private theorem finalOracleDecoded_zero_eq_prefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_close_first : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (f := getFirstOracle 𝔽q β oStmtOut))
    (h_dec0_eq_f0 :
      uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀)
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close0 : FinalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht) :
    finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht h_close0 =
    finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ 0 ht := by
  classical
  have h_idx0 := finalOracleBlockIdx_zero
    (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ht
  have h_raw0_heq :
      HEq
        (finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht)
        (getFirstOracle 𝔽q β oStmtOut) :=
    finalOracleRaw_zero_heq_getFirstOracle (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut ht
  have h_close0_first :
      UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (f := getFirstOracle 𝔽q β oStmtOut) := by
    exact finalOracleClose_zero_eq_first (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut ht h_close0
  have h_decoded0_heq_f₀ :
      HEq
        (finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht h_close0)
        f₀ := by
    have h_decoded0_heq_first :
        HEq
          (finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht h_close0)
          (uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
            (h_within_radius := h_close0_first)) := by
      exact uniqueDecodingCodeword_heq_of_fin_eq (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_idx0
        (oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨0, ht⟩))
        (by simp) h_raw0_heq h_close0 h_close0_first
    exact h_decoded0_heq_first.trans
      (heq_of_eq (firstOracleDecoded_eq_f₀ (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut f₀ h_close_first h_dec0_eq_f0 h_close0_first))
  have h_prefix_zero_heq :
      HEq
        (finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ 0 ht)
        f₀ := by
    have h_dom0 :
        ↥(sDomain 𝔽q β h_ℓ_add_R_rate
          (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)) =
        ↥(sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) := by
      exact congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i)) h_idx0
    exact funext_heq h_dom0 (fun _ => rfl) (by
      intro y
      apply heq_of_eq
      dsimp [finalDecodedPrefixFold]
      rw [iteratedFold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (steps := 0 * ϑ) (steps' := 0)
        (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)
        (h_destIdx := by
          dsimp [finalOracleBlockIdx]
          simp only [zero_mul, add_zero])
        (h_destIdx_le := by
          exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨0, ht⟩))
        (h_steps_eq_steps' := by simp only [zero_mul]) (f := f₀)
        (r_challenges := finalPrefixChallenges
          (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut 0 ht) (y := y)]
      rw [iteratedFold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r))
        (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)
        (h_destIdx := by
          dsimp [finalOracleBlockIdx]
          simp only [zero_mul])
        (h_destIdx_le := by
          exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨0, ht⟩))
        (f := f₀)
        (r_challenges := fun cId => finalPrefixChallenges
          (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut 0 ht ⟨cId, by omega⟩)])
  exact eq_of_heq (h_decoded0_heq_f₀.trans h_prefix_zero_heq.symm)

omit [SampleableType L] [DecidableEq 𝔽q] in
private theorem finalOracleClose_curr
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (h_oracle_cons : OracleFoldingConsistent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) (challenges := stmtOut.challenges) (oStmt := oStmtOut))
    (t : ℕ)
    (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    FinalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t (Nat.lt_of_succ_lt ht) := by
  let jCurr : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) := ⟨t, Nat.lt_of_succ_lt ht⟩
  have h_complCurr := h_oracle_cons jCurr ht
  rcases h_complCurr with ⟨h_fw_curr, _, _⟩
  exact uniqueDecodingClose_of_fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t (Nat.lt_of_succ_lt ht))
    (steps := ϑ)
    (h_destIdx := by
      dsimp [finalOracleBlockIdx, jCurr, oraclePositionToDomainIndex])
    (h_destIdx_le := by
      have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := jCurr)
      dsimp [finalOracleBlockIdx, jCurr, oraclePositionToDomainIndex] at h_le ⊢
      omega)
    (f := oStmtOut jCurr)
    h_fw_curr

private def finalOracleDecodedAt
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close : FinalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close

private def finalDecodedPrefixAt
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht

private def finalOracleNextIdxOrig
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Fin r :=
  ⟨t * ϑ + ϑ, by
    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
    exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩)⟩

private def finalOracleNextRaw
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (Fin.last ℓ) oStmtOut ⟨t, Nat.lt_of_succ_lt ht⟩ ht
    (destDomainIdx := finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_destDomainIdx := by rfl)

private def FinalOracleNextClose
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Prop :=
  UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (f := finalOracleNextRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)

private def finalOracleNextCodeword
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close : FinalOracleNextClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_i := by
      have h_le := oracle_block_k_next_le_i ℓ ϑ
        (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht)
      change (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) ≤ ℓ
      dsimp [finalOracleNextIdxOrig]
      have h_eq : (t + 1) * ϑ = t * ϑ + ϑ := by
        rw [Nat.add_mul, one_mul]
      exact h_eq ▸ h_le)
    (f := finalOracleNextRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)
    (h_within_radius := h_close)

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
private theorem finalOracleDecoded_next_heq
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ)
    (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close_next : FinalOracleNextClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)
    (h_close_next_final : FinalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht) :
    HEq
      (finalOracleNextCodeword (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close_next)
      (finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht h_close_next_final) := by
  classical
  dsimp only [finalOracleNextCodeword, finalOracleDecodedAt, finalOracleDecoded]
  have h_idx :
      finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht =
      finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t + 1) ht := by
    apply Fin.ext
    dsimp [finalOracleNextIdxOrig, finalOracleBlockIdx]
    rw [Nat.add_mul, Nat.one_mul]
  have h_dom :
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate
        (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)) =
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate
        (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t + 1) ht)) := by
    exact congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i)) h_idx
  have h_raw_heq :
      HEq
        (finalOracleNextRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)
        (finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht) := by
    exact funext_heq h_dom (fun _ => rfl) (by
      intro y
      apply heq_of_eq
      dsimp [finalOracleNextRaw, getNextOracle, finalOracleRaw,
        finalOracleNextIdxOrig, finalOracleBlockIdx])
  exact uniqueDecodingCodeword_heq_of_fin_eq (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_idx
    (by
      have h_le := oracle_block_k_next_le_i ℓ ϑ
        (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht)
      change
        (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) ≤ ℓ
      dsimp [finalOracleNextIdxOrig]
      have h_eq : (t + 1) * ϑ = t * ϑ + ϑ := by
        rw [Nat.add_mul, Nat.one_mul]
      exact h_eq ▸ h_le)
    (by
      exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
        (i := Fin.last ℓ) (j := ⟨t + 1, ht⟩))
    h_raw_heq h_close_next h_close_next_final

omit [SampleableType L] [DecidableEq 𝔽q] in
private theorem finalOracleDecoded_nat_eq_prefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (h_oracle_cons : OracleFoldingConsistent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) (challenges := stmtOut.challenges) (oStmt := oStmtOut))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_close_first : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (f := getFirstOracle 𝔽q β oStmtOut))
    (h_dec0_eq_f0 :
      uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀) :
    ∀ t, ∀ ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ),
      ∀ h_close : FinalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht,
        finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close =
        finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht := by
  classical
  intro t
  induction t with
  | zero =>
      intro ht h_close
      exact finalOracleDecoded_zero_eq_prefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut f₀
        h_close_first h_dec0_eq_f0 ht h_close
  | succ t ih =>
      intro ht h_close
      have ht_prev : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ) := Nat.lt_of_succ_lt ht
      have h_close_curr :
          FinalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev :=
        finalOracleClose_curr (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut h_oracle_cons t ht
      have h_curr_eq :
          finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev h_close_curr =
          finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht_prev :=
        ih ht_prev h_close_curr
      let jCurr : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) := ⟨t, ht_prev⟩
      have h_complCurr := h_oracle_cons jCurr ht
      rcases h_complCurr with ⟨h_fw_curr, h_close_next, h_fold_curr⟩
      dsimp [finalOracleDecodedAt, finalDecodedPrefixAt, finalOracleDecoded, finalOracleRaw, jCurr,
        oraclePositionToDomainIndex, getFoldingChallenges, finalOracleBlockIdx]
        at h_fold_curr h_curr_eq
      rw [h_curr_eq] at h_fold_curr
      change
        iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨t * ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ)
            exact oracle_block_k_le_i (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := jCurr)⟩)
          (steps := ϑ)
          (destIdx := ⟨t * ϑ + ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
            exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := jCurr) (hj := ht)⟩)
          (h_destIdx := by rfl)
          (h_destIdx_le := by
            exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := jCurr) (hj := ht))
          (f := finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht_prev)
          (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
            (i := Fin.last ℓ) (challenges := stmtOut.challenges) (t * ϑ)
            (h := by
              exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := jCurr) (hj := ht))) =
        finalOracleNextCodeword (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close_next at h_fold_curr
      have h_rhs_heq :
          HEq
            (finalOracleNextCodeword (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close_next)
            (finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht h_close) := by
        exact finalOracleDecoded_next_heq (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close_next h_close
      have h_fold_curr_heq := (heq_of_eq h_fold_curr).trans h_rhs_heq
      have h_blockChallenges_eq :
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
            (challenges := stmtOut.challenges) (t * ϑ)
            (h := by
              exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := jCurr) (hj := ht)) =
          finalBlockChallenges
            (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht := by
        funext cId
        dsimp [getFoldingChallenges, finalBlockChallenges, jCurr, oraclePositionToDomainIndex]
      rw [h_blockChallenges_eq] at h_fold_curr_heq
      have h_step_heq :
          HEq
            (finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ (t + 1) ht)
            (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := ⟨t * ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ)
                exact oracle_block_k_le_i (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩)⟩)
              (steps := ϑ)
              (destIdx := ⟨t * ϑ + ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
                exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht)⟩)
              (h_destIdx := by rfl)
              (h_destIdx_le := by
                exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht))
              (f := finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t (Nat.lt_of_succ_lt ht))
              (r_challenges := finalBlockChallenges
                (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht)) := by
        have h_step' := finalDecodedPrefixFold_step (𝔽q := 𝔽q) (β := β)
          (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht
        refine (heq_of_eq h_step').symm.trans ?_
        apply iteratedFold_heq_of_fin_eq
        apply Fin.ext
        simp only [finalOracleBlockIdx, Nat.add_mul, Nat.one_mul]
      have h_res :
          HEq
            (finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ (t + 1) ht)
            (finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht h_close) := by
        exact h_step_heq.trans h_fold_curr_heq
      exact eq_of_heq h_res.symm

omit [SampleableType L] in
/-- If the oracles are fold-consistent through the final constant and the first oracle decodes to
`tpoly`, then the final constant is `tpoly` evaluated at the challenges: the decoded oracles are
the honest folds of the decoded first oracle. -/
lemma eval_eq_final_constant_of_extractMlp_eq_some
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (tpoly : MultilinearPoly L ℓ)
    (h_extractMLP : extractMlp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (f := getFirstOracle 𝔽q β oStmtOut) = some tpoly)
    (h_finalSumcheckStepOracleConsistency : FinalSumcheckOracleConsistent 𝔽q β
      (stmtOut := stmtOut) (oStmtOut := oStmtOut)) :
    stmtOut.finalConstant = tpoly.val.eval stmtOut.challenges := by
  classical
  have h_final_consistency := h_finalSumcheckStepOracleConsistency
  dsimp only [FinalSumcheckOracleConsistent] at h_final_consistency
  rcases h_final_consistency with ⟨h_oracle_cons, h_final_cons⟩
  let P₀ : L⦃< 2^ℓ⦄[X] :=
    polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => tpoly.val.eval (bitsOfIndex ω))
  let f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := (0 : Fin r)) :=
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  have h_pair :
      PairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r))
        (f := getFirstOracle 𝔽q β oStmtOut) (g := f₀) := by
    have h_pair' :=
      (extractMlp_eq_some_iff_pairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (f := getFirstOracle 𝔽q β oStmtOut) (tpoly := tpoly)).1 h_extractMLP
    dsimp [f₀, P₀] at h_pair' ⊢
    exact h_pair'
  let C₀ : Set ((sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) → L) :=
    (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)))
  have h_f0_mem : f₀ ∈ C₀ := by
    dsimp [C₀, f₀]
    change polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := (0 : Fin r)) (P := P₀) ∈
      code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r))
    have h_codeword :=
      (polynomialCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r))  (P := P₀)).property
    unfold polynomialCodeword at h_codeword
    dsimp only at h_codeword
    exact h_codeword
  have h_close_first :
      UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (f := getFirstOracle 𝔽q β oStmtOut) := by
    unfold UniqueDecodingClose
    calc
      2 * Δ₀(getFirstOracle 𝔽q β oStmtOut, C₀) ≤
          2 * Δ₀(getFirstOracle 𝔽q β oStmtOut, f₀) := by
        rw [ENat.mul_le_mul_left_iff (ha := by
            simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
          (h_top := by simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true])]
        exact Code.distFromCode_le_dist_to_mem (C := C₀)
          (u := getFirstOracle 𝔽q β oStmtOut) (v := f₀) h_f0_mem
      _ < codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)) := by
        norm_cast
  have h_dec0_eq_f0 :
      uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := by simp) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀ :=
    uniqueDecodingCodeword_eq_of_extractMlp_eq_some 𝔽q β _ tpoly h_extractMLP h_close_first
  have h_oracle_cons' := h_oracle_cons
  dsimp only [OracleFoldingConsistent] at h_oracle_cons'
  rcases h_final_cons with ⟨h_fw_last, h_close_const, h_fold_last⟩
  -- The last decoded oracle equals the constant oracle fun _ => stmtOut.finalConstant.
  -- We apply the same unique-decoding argument as for the first oracle, but now at the
  -- last oracle index with code C_last and center u := oStmtOut jLast.
  let jLast : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
  let lastDomainIdx : Fin r :=
    ⟨jLast.val * ϑ, by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := jLast.val * ϑ)
      exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := jLast)⟩
  let k := lastDomainIdx.val
  have h_k: k = ℓ - ϑ := by
    dsimp only [k, lastDomainIdx, jLast]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := blockSize_le_rounds ℓ ϑ
  let finalDomainIdx : Fin r := ⟨k + ϑ, by
    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k + ϑ)
    rw [h_k]
    exact le_of_eq (Nat.sub_add_cancel h_ϑ_le_ℓ)⟩
    -- final virtual oracle's evaluation domain
  have h_finalDomainIdx_le : finalDomainIdx ≤ ℓ := by
    dsimp [finalDomainIdx]
    rw [h_k]
    exact le_of_eq (Nat.sub_add_cancel h_ϑ_le_ℓ)
  have h_lastDomainIdx_le : lastDomainIdx ≤ ℓ := by
    dsimp [lastDomainIdx, jLast]
    exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := jLast)
  let f_last_raw : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) lastDomainIdx := by
    change OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (i := Fin.last ℓ) jLast
    exact oStmtOut jLast
  have h_close_last :
      UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := lastDomainIdx)  (f := f_last_raw) := by
    have h_close_last' :=
      uniqueDecodingClose_of_fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := lastDomainIdx) (steps := ϑ) (h_destIdx := by rfl)
        (h_destIdx_le := by
          dsimp [lastDomainIdx, jLast]
          exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := jLast))
        (f := f_last_raw) h_fw_last
    dsimp [f_last_raw, lastDomainIdx, jLast] at h_close_last' ⊢
    exact h_close_last'
  let f_last : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) lastDomainIdx :=
    uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := lastDomainIdx) (h_i := h_lastDomainIdx_le) (f := f_last_raw)
      (h_within_radius := h_close_last)
  let f_final_virtual : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) finalDomainIdx :=
    uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalDomainIdx) (h_i := h_finalDomainIdx_le)
      (f := fun _ => stmtOut.finalConstant) (h_within_radius := h_close_const)
  let preFinalChallenges : (Fin k) → L := fun cId => stmtOut.challenges ⟨cId, by
    simp only [Fin.val_last]; omega⟩
  let finalChallenges : Fin ϑ → L := fun cId => stmtOut.challenges ⟨k + cId, by
      rw [h_k]
      have h_cId : cId.val < ϑ := cId.isLt
      have h_last : (Fin.last ℓ).val = ℓ := rfl
      simp only [Fin.val_last, gt_iff_lt]
      omega
    ⟩
  -- The last decoded oracle is the corresponding prefix fold.
  let f_f₀_folded_to_last := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := 0) (steps := k) (destIdx := lastDomainIdx) (h_destIdx := by
      dsimp only [k]; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
    (h_destIdx_le := by omega) (f := f₀) (r_challenges := preFinalChallenges)
  have h_f_last_eq_iterated_fold_f₀ :
    f_last = f_f₀_folded_to_last := by
    have h_last_decoded_eq_prefix :
        finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut jLast.val jLast.isLt h_close_last =
        finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ jLast.val jLast.isLt := by
      exact finalOracleDecoded_nat_eq_prefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut h_oracle_cons f₀
        h_close_first h_dec0_eq_f0 jLast.val jLast.isLt h_close_last
    have h_f_last_eq_decoded :
        f_last =
          finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut jLast.val jLast.isLt h_close_last := by
      rfl
    have h_preFinalChallenges_eq :
        finalPrefixChallenges (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut jLast.val jLast.isLt =
        preFinalChallenges := by
      funext cId
      dsimp [finalPrefixChallenges, preFinalChallenges, k, jLast]
    rw [h_f_last_eq_decoded, h_last_decoded_eq_prefix]
    dsimp [f_f₀_folded_to_last, finalDecodedPrefixFold, k, lastDomainIdx, jLast]
    rw [h_preFinalChallenges_eq]
    rfl
  -- The final decoded constant is the fold of the last decoded oracle.
  let f_last_folded_to_final := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := lastDomainIdx) (steps := ϑ) (destIdx := finalDomainIdx) (h_destIdx := by
      change finalDomainIdx.val = k + ϑ; rw [h_k]; dsimp only [finalDomainIdx]; omega
    )
    (h_destIdx_le := by
      dsimp only [finalDomainIdx]; omega
    ) (f := f_last)
    (r_challenges := finalChallenges)
  have h_f_final_virtual_eq :
    f_last_folded_to_final = f_final_virtual := by
    dsimp [f_last_folded_to_final, f_final_virtual, f_last, f_last_raw, finalChallenges,
      lastDomainIdx, finalDomainIdx, jLast]
    exact h_fold_last
  have h_f_final_virtual_eq_const :
      f_final_virtual = fun _ => stmtOut.finalConstant := by
    dsimp [f_final_virtual]
    exact uniqueDecodingCodeword_const (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := finalDomainIdx)
      h_finalDomainIdx_le stmtOut.finalConstant
  -- Compose the prefix and final-block folds.
  rw [h_f_final_virtual_eq_const] at h_f_final_virtual_eq
  dsimp only [f_last_folded_to_final] at h_f_final_virtual_eq
  rw [h_f_last_eq_iterated_fold_f₀] at h_f_final_virtual_eq
  dsimp only [f_f₀_folded_to_last] at h_f_final_virtual_eq
  have hjoin := iteratedFold_take_suffix_of_add_eq 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) k ϑ
    (N := ℓ) (by rw [h_k]; omega)
    (midIdx := lastDomainIdx) (destIdx := finalDomainIdx)
    (hmid := by simp [k])
    (hdest := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]
      dsimp only [finalDomainIdx]
      rw [h_k]
      omega)
    (hle := h_finalDomainIdx_le) f₀ stmtOut.challenges
  have heval := iteratedFold_to_level_ℓ_eval 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) tpoly finalDomainIdx
    (by dsimp [finalDomainIdx]; rw [h_k]; omega) stmtOut.challenges
  have hconstant := (hjoin.trans heval).symm.trans h_f_final_virtual_eq
  exact (congr_fun hconstant ⟨0, by simp only [zero_mem]⟩).symm

end
end Binius.BinaryBasefold.CoreInteraction
