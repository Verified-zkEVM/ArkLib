/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Protocol

/-!
# Binary Basefold query-phase folding lemmas

For a strictly consistent oracle family, the queried guard coordinate equals the preceding
iterated fold, and folding the queried fiber gives the next iterated fold. At the last block,
strict final consistency identifies the total fold with the claimed final constant.
-/

@[expose] public section

open OracleSpec

namespace Binius.BinaryBasefold.QueryPhase

noncomputable section
open OracleSpec OracleComp
open AdditiveNTT Polynomial MvPolynomial ProtocolSpec
open Probability

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]

variable (𝔽q : Type) [Field 𝔽q]
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section FinalQueryRoundIOR

omit [DecidableEq 𝔽q] hF₂ in
/-- Oracle-family simulation returns the vector of fiber evaluations. -/
theorem queryFiberPoints_simulate (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt messages)
      (queryFiberPoints 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v).run =
      pure (some ((⟨Array.finRange (2 ^ ϑ), by simp⟩ : Vector (Fin (2 ^ ϑ)) (2 ^ ϑ)).map
        (logicalQueryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt k v))) := by
  dsimp only [queryFiberPoints]
  apply simulateQ_optionT_vector_mapM_pure
  intro u
  rfl

/-- The queried coordinate of a strictly consistent oracle is the preceding total fold. -/
lemma iteratedFold_eq_queryFiberPoint_of_strictConsistency
    {k : Fin (ℓ / ϑ)} (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (t : MultilinearPoly L ℓ)
    (h_strictOracleFoldingConsistency : StrictOracleFoldingConsistent 𝔽q β
      (ϑ := ϑ) t (Fin.last ℓ) stmtIn.challenges oStmtIn) :
    iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := k.val * ϑ) (destIdx := ⟨k.val * ϑ, by
        have := k_mul_ϑ_lt_ℓ (k := k); omega⟩)
      (h_destIdx := by simp) (h_destIdx_le := by
        simp only; have := k_mul_ϑ_lt_ℓ (k := k); omega)
      (f := getFirstOracle 𝔽q β oStmtIn)
      (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ)
        stmtIn.challenges 0 (by have := k_mul_ϑ_lt_ℓ (k := k); simp; omega))
      (y := extractSuffixFromChallenge 𝔽q β v ⟨k.val * ϑ, by
        have := k_mul_ϑ_lt_ℓ (k := k); omega⟩ (by
        simp only; have := k_mul_ϑ_lt_ℓ (k := k); omega)) =
    logicalQueryFiberPoints 𝔽q β oStmtIn k v
      (extractMiddleFinMask 𝔽q β v ⟨k.val * ϑ, by
        have := k_mul_ϑ_lt_ℓ (k := k); omega⟩ ϑ) := by
  dsimp only [logicalQueryFiberPoints]
  have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k)
  set destIdx : Fin r := ⟨k.val * ϑ, by omega⟩ with h_destIdx_eq
  rcases t with ⟨t, h_t_mem_support⟩
  dsimp only [StrictOracleFoldingConsistent] at h_strictOracleFoldingConsistency
  -- Now extract the oStmtIn equality at position k
  have h_oStmtIn_k_eq := h_strictOracleFoldingConsistency ⟨k.val,
    by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩
  conv_rhs => rw [h_oStmtIn_k_eq]
  simp only
  have h_point_eq : extractSuffixFromChallenge 𝔽q β v ⟨↑k * ϑ, by omega⟩ (by simp only; omega) =
      getFiberPoint 𝔽q β k v (extractMiddleFinMask 𝔽q β v ⟨↑k * ϑ, by omega⟩ ϑ) := by
    -- The key insight: getFiberPoint reconstructs a point in S^i by:
    -- 1. Taking the suffix at i+ϑ
    -- 2. Joining it with the fiber index u (the middle ϑ bits)
    -- 3. Converting back to sDomain
    -- When u = extractMiddleFinMask v i ϑ, this reconstructs exactly the suffix at i
    -- Unfold definitions
    dsimp only [getFiberPoint, getChallengeSuffix, extractSuffixFromChallenge]
    -- Both sides use iteratedQuotientMap, so we need to show they're applied to the same element
    have h_aux := iteratedQuotientMap_eq_quotientFiber_extractMiddleFinMask
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨k.val * ϑ, by have := k_mul_ϑ_lt_ℓ (k := k); omega⟩) (steps := ϑ)
      (destIdx := ⟨k.val * ϑ + ϑ, by have := k_succ_mul_ϑ_le_ℓ_₂ (k := k); omega⟩)
      (h_destIdx := rfl) (h_destIdx_le := k_succ_mul_ϑ_le_ℓ_₂ (k := k)) (v := v)
    exact h_aux
  rw [h_point_eq]
  rw [polyToOracleFunc_eq_getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (t := ⟨t, h_t_mem_support⟩) (i := Fin.last ℓ)
    (challenges := stmtIn.challenges) (oStmt := oStmtIn)
    (h_consistency := h_strictOracleFoldingConsistency)]

omit [DecidableEq 𝔽q] in
/-- Folding a strictly consistent queried fiber returns the next total fold. -/
lemma logicalComputeFoldedValue_eq_totalFold_of_strictConsistency
    {k : Fin (ℓ / ϑ)} (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (t : MultilinearPoly L ℓ)
    (h_strictOracleFoldingConsistency : StrictOracleFoldingConsistent 𝔽q β
      (ϑ := ϑ) t (Fin.last ℓ) stmtIn.challenges oStmtIn) :
    logicalComputeFoldedValue 𝔽q β k v stmtIn
      (logicalQueryFiberPoints 𝔽q β oStmtIn k v) =
    iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := (k.val + 1) * ϑ) (destIdx := ⟨(k.val + 1) * ϑ, by
        have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩)
      (h_destIdx := by simp) (h_destIdx_le := k_succ_mul_ϑ_le_ℓ (k := k))
      (f := getFirstOracle 𝔽q β oStmtIn)
      (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ)
        stmtIn.challenges 0 (by
          simp only [zero_add, Fin.val_last]
          exact k_succ_mul_ϑ_le_ℓ (k := k)))
      (y := extractSuffixFromChallenge 𝔽q β v ⟨(k.val + 1) * ϑ, by
        have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩
        (k_succ_mul_ϑ_le_ℓ (k := k))) := by
  have h₁ := k_mul_ϑ_lt_ℓ (k := k)
  have h₂ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have hnext := k_succ_mul_ϑ_le_ℓ (k := k)
  rw [logicalComputeFoldedValue_eq_iteratedFold]
  dsimp only [getChallengeSuffix]
  let k_oracle_idx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k, by simpa only [toOutCodewordsCount_last] using k.isLt⟩
  let challenges_mid : Fin (k.val * ϑ) → L := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ)
    stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega)
  let challenges_last : Fin ϑ → L := fun j =>
    stmtIn.challenges ⟨k.val * ϑ + j.val, by simp only [Fin.val_last]; omega⟩
  let challenges_full : Fin ((k.val + 1) * ϑ) → L :=
    getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ)
    stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega)
  let y_left := extractSuffixFromChallenge 𝔽q β v ⟨k.val * ϑ + ϑ, by omega⟩ (by omega)
  let y_right := extractSuffixFromChallenge 𝔽q β v ⟨(k.val + 1) * ϑ, by omega⟩ (by omega)
  -- Extract t and StrictOracleFoldingConsistent from h_relIn
  rcases t with ⟨t, h_t_mem_support⟩
  dsimp only [StrictOracleFoldingConsistent] at h_strictOracleFoldingConsistency
  -- Get the equality for k_oracle_idx: oStmtIn k_oracle_idx = iteratedFold from 0 to k.val * ϑ
  have h_f_mid_eq_iterated_fold := h_strictOracleFoldingConsistency k_oracle_idx
  conv_lhs => rw [h_f_mid_eq_iterated_fold]
  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => t.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  conv_lhs => simp only [cast_eq, Fin.val_last]
  conv_lhs =>
    rw [iteratedFold_iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff,
        mul_eq_mul_right_iff]; left; rfl
    )]
  dsimp only [k_oracle_idx]
  -- Step 1: Align steps (k * ϑ + ϑ = (k + 1) * ϑ)
  have h_steps_eq : k.val * ϑ + ϑ = (k.val + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
  conv_lhs =>
    erw [iteratedFold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := k.val * ϑ + ϑ) (steps' := (k.val + 1) * ϑ)
      (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]) (h_destIdx_le := by omega)
      (h_steps_eq_steps' := h_steps_eq)
      (f := f₀) (r_challenges := Fin.append challenges_mid challenges_last)
      (y := y_left)]
  -- Step 2: Align destIdx (⟨k * ϑ + ϑ, ...⟩ = ⟨(k + 1) * ϑ, ...⟩)
  conv_lhs =>
    rw [iteratedFold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := (k.val + 1) * ϑ)
      (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (destIdx' := ⟨(k.val + 1) * ϑ, by omega⟩)
      (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by omega) (h_destIdx_eq_destIdx' := by apply Fin.eq_of_val_eq; omega)
      (f := f₀)]
  -- Step 3: Align function (f₀ = getFirstOracle)
  have h_f₀_eq_getFirstOracle : f₀ = getFirstOracle 𝔽q β oStmtIn := by
    exact polyToOracleFunc_eq_getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t := ⟨t, h_t_mem_support⟩) (i := Fin.last ℓ)
      (challenges := stmtIn.challenges) (oStmt := oStmtIn)
      (h_consistency := h_strictOracleFoldingConsistency)
  conv_lhs => rw [h_f₀_eq_getFirstOracle]
  -- Step 4: Align challenges
  have h_challenges_eq : (fun (cIdx : Fin ((↑k + 1) * ϑ)) => Fin.append challenges_mid
    challenges_last ⟨cIdx.val, by omega⟩) = challenges_full := by
    funext j
    dsimp only [Fin.append, Fin.addCases, challenges_full, challenges_mid, challenges_last]
    by_cases h : j.val < k.val * ϑ
    · -- Case 1: cId < k_steps, so it's from the first part
      simp only [h, ↓reduceDIte, Fin.castLT_mk]; rfl
    · -- Case 2: cId >= k_steps, so it's from the second part
      dsimp only [getFoldingChallenges]
      simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, Fin.val_last,
        eq_rec_constant]
      congr 1; simp only [Fin.val_last, zero_add, Fin.mk.injEq]; omega
  conv_lhs => rw [h_challenges_eq]
  have h_sDomain_eq : sDomain 𝔽q β h_ℓ_add_R_rate ⟨k.val * ϑ + ϑ, by omega⟩
    = sDomain 𝔽q β h_ℓ_add_R_rate ⟨(↑k + 1) * ϑ, by omega⟩ := by
    apply congrArg (sDomain 𝔽q β h_ℓ_add_R_rate)
    apply Fin.eq_of_val_eq
    simp only
    omega
  -- Step 5: Align points
  have h_y_eq : cast (by rw [h_sDomain_eq]) y_left = y_right := by
    dsimp only [y_left, y_right]
    rw [←extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_idx_eq := by apply Fin.eq_of_val_eq; simp only; omega)]
  conv_lhs => rw [h_y_eq]
-- The final fold compares the stored last-oracle accessor with a total-fold domain
-- their dependent domain casts require relaxed definitional unification.
set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq 𝔽q] in
/-- The total fold of a strictly consistent final input equals its claimed constant. -/
lemma iteratedFold_eq_finalConstant_of_strictFinalSumcheckRelOut
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (c : L)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    -- Hypothesis: x is the result of folding all the way to ℓ
    (h_c_correct :
      have h_mul_eq : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
      c = iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (ℓ / ϑ) * ϑ)
        (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega))
        (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add];)
    ) :
    c = stmtIn.finalConstant := by
  classical
  dsimp only [strictFinalSumcheckRelOut, StrictFinalSumcheckRelated,
    StrictFinalSumcheckFoldingState] at h_relIn
  simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn
  -- 2. Extract the existential witnesses
  rw [h_c_correct]
  rcases h_relIn with ⟨exists_t_MLP, h_final_oracle_fold_to_constant⟩
  have h_final_oracle_fold_to_const_at_0 := congr_fun h_final_oracle_fold_to_constant 0
  rw [h_final_oracle_fold_to_const_at_0.symm]
  rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
  dsimp only [StrictOracleFoldingConsistent] at h_strictOracleFoldingConsistency
  let lastOraclePositionIndex := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
  have h_last_oracle_eq_t_evals_folded := h_strictOracleFoldingConsistency lastOraclePositionIndex
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  have h_ℓ_div_mul_eq_ℓ : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have h_lastOraclePosIdx_mul_add :
    (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)).val * ϑ + ϑ = ℓ := by
    conv_rhs => rw [←h_ℓ_div_mul_eq_ℓ]
    rw [getLastOraclePositionIndex_last]; simp only
    rw [Nat.sub_mul, Nat.one_mul]; rw [Nat.sub_add_cancel (by rw [h_ℓ_div_mul_eq_ℓ]; omega)]
  have h_first_oracle_eq_t_evals_folded := h_strictOracleFoldingConsistency ⟨0, by
    simp only [toOutCodewordsCount_last, Nat.div_pos_iff]; omega⟩
  dsimp only [getFirstOracle]
  have h_getLastOracle_eq : oStmtIn lastOraclePositionIndex =
    getLastOracle (h_destIdx := by rfl) (oracleFrontierIdx := Fin.last ℓ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn) := by rfl
  rw [←h_getLastOracle_eq]
  rw [h_last_oracle_eq_t_evals_folded, h_first_oracle_eq_t_evals_folded]
  simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod]
  have h_zero_mod : 0 % toOutCodewordsCount ℓ ϑ (Fin.last ℓ) * ϑ = 0 := by
    rw [toOutCodewordsCount_last]
    simp only [Nat.zero_mod, zero_mul]
  rw [iteratedFold_iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff,
    mul_eq_mul_right_iff]
    rw [getLastOraclePositionIndex_last]
    dsimp only [lastOraclePositionIndex]
    rw [getLastOraclePositionIndex_last]
    simp only [true_or]
  )]
  set chalLeft := (getFoldingChallenges (i := Fin.last ℓ) (𝓡 := 𝓡) (r := r)
    (challenges := stmtIn.challenges) (k := 0) (ϑ := ℓ/ϑ * ϑ) (by
    simp only [zero_add, Fin.val_last]; omega)) with h_chalLeft
  set chalRight := Fin.append (getFoldingChallenges (i := Fin.last ℓ) (𝓡 := 𝓡) (r := r)
    (challenges := stmtIn.challenges) (k := 0) (ϑ := lastOraclePositionIndex.val * ϑ)
      (by simp only [zero_add, Fin.val_last, oracle_index_le_ℓ]))
      (fun (cId : Fin ϑ) ↦
        stmtIn.challenges ⟨(getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)) * ϑ + cId.val, by
          simp only [Fin.val_last, getLastOraclePositionIndex_last]
          simp only [lastBlockIdx_mul_ϑ_add_fin_lt_ℓ]⟩) with h_chalRight
  have h_chalLeft_eq_chalRight_cast : chalLeft = fun cIdx : Fin (ℓ / ϑ * ϑ) => chalRight ⟨cIdx, by
    dsimp only [lastOraclePositionIndex]
    simp only [getLastOraclePositionIndex_last]
    rw [Nat.sub_mul, Nat.one_mul]; omega
  ⟩ := by
    funext cIdx
    dsimp only [chalLeft, chalRight]
    by_cases h : cIdx.val < lastOraclePositionIndex.val * ϑ
    · -- Case 1: cId < k_steps, so it's from the first part
      simp only [Fin.val_last]
      dsimp only [Fin.append, Fin.addCases]
      simp only [h, ↓reduceDIte, getFoldingChallenges, Fin.val_last, Fin.val_castLT, zero_add]
    · -- Case 2: cId >= k_steps, so it's from the second part
      simp only [Fin.val_last]
      dsimp only [Fin.append, Fin.addCases]
      simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, eq_rec_constant]
      dsimp only [getFoldingChallenges]
      congr 1
      simp only [Fin.val_last, zero_add, Fin.mk.injEq]
      rw [add_comm]
      dsimp only [lastOraclePositionIndex, lastOraclePositionIndex] at ⊢ h
      rw [Nat.sub_add_cancel]
      rw [getLastOraclePositionIndex_last] at ⊢ h
      simp only [Nat.sub_mul, one_mul, not_lt, tsub_le_iff_right] at ⊢ h
      exact h
  rw [h_chalLeft_eq_chalRight_cast]
  conv_lhs =>
    -- 1. Locate the specific sub-term corresponding to the folding function
    --    This enters the folding-function lambda "fun y ↦ ..." (7th positional arg)
    enter [7, y]
    rw [iteratedFold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := 0 % toOutCodewordsCount ℓ ϑ (Fin.last ℓ) * ϑ) (steps' := 0) (h_destIdx := by
      simp only [toOutCodewordsCount_last, Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod, add_zero])
      (h_destIdx_le := by simp only [toOutCodewordsCount_last, Nat.zero_mod, zero_mul, zero_le])
      (h_steps_eq_steps' := by omega)]
    rw [iteratedFold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (h_destIdx := by simp only [toOutCodewordsCount_last,
      Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod])]
  conv_lhs => simp only [cast_cast, cast_eq]
  conv_lhs =>
    rw [←iteratedFold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := (ℓ / ϑ * ϑ)) (h_destIdx := by
      dsimp only [lastOraclePositionIndex]
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
    (h_destIdx_le := by simp only; omega) (h_steps_eq_steps' := by
      dsimp only [lastOraclePositionIndex]; omega)]
  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => t.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  set destIdx' : Fin r := ⟨(getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)).val + ϑ, by
    rw [getLastOracleDomainIndex]; simp only; omega⟩ with h_destIdx'
  let point := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
    (destIdx := ⟨ℓ / ϑ * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
  conv_lhs =>
    erw [iteratedFold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (destIdx := ⟨ℓ / ϑ * ϑ, by omega⟩)
      (destIdx' := destIdx') (h_destIdx := by
        dsimp only [lastOraclePositionIndex]
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by simp only; omega) (h_destIdx_eq_destIdx' := by
        dsimp only [destIdx']; simp only [Fin.mk.injEq]; omega)
      (r_challenges := chalRight) (y := point)]
  rw [iteratedFold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := ℓ) (h_destIdx := by
      dsimp only [destIdx']
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff,
      mul_eq_mul_right_iff]; omega)
    (h_destIdx_le := by dsimp only [destIdx']; simp only [oracle_index_add_steps_le_ℓ])
    (h_steps_eq_steps' := by omega)]
  rw [iteratedFold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := ℓ) (h_destIdx := by
    dsimp only [destIdx']
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add,
      Nat.add_right_cancel_iff, mul_eq_mul_right_iff]; omega)
    (h_destIdx_le := by dsimp only [destIdx']; simp only [oracle_index_add_steps_le_ℓ])
    (h_steps_eq_steps' := by omega)]
  have h_sDomain_eq : (sDomain 𝔽q β h_ℓ_add_R_rate ⟨ℓ/ϑ * ϑ, by omega⟩)
    = (sDomain 𝔽q β h_ℓ_add_R_rate destIdx') := by
    apply congrArg (sDomain 𝔽q β h_ℓ_add_R_rate)
    apply Fin.ext
    dsimp only [destIdx']
    omega
  let res := iteratedFold_to_level_ℓ_is_constant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (t := ⟨t, h_t_mem_support⟩) (destIdx := destIdx') (h_destIdx := by omega)
    (challenges := fun (cIdx : Fin ℓ) =>
      chalRight ⟨cIdx, by dsimp only [lastOraclePositionIndex]; omega⟩)
    (x := cast (by rw [h_sDomain_eq]) point) (y := 0)
  -- `res` matches up to η-expansion of the `f`-argument and a `cast ∘ cast` on the input
  -- (both `sDomain`s are equal, so the composite cast is the identity).
  convert res using 4

end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase
