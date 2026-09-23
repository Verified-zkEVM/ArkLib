/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Protocol
-- These probability proofs use the protocol module's private probability helpers.
import all ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Protocol

/-!
# Binary Basefold query-phase folding lemmas
-/

@[expose] public section

open OracleSpec
attribute [local instance] queryEmptySpecInhabited
noncomputable local instance foldingEmptyUniformSpec : IsUniformSpec []ₒ :=
  IsUniformSpec.ofFintypeInhabited _

namespace Binius.BinaryBasefold.QueryPhase

noncomputable section
open OracleSpec OracleComp
open AdditiveNTT Polynomial MvPolynomial ProtocolSpec
open Probability

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section FinalQueryRoundIOR

lemma OracleComp.liftM_query_eq_liftM_liftM.{u, v, z}
    {ι : Type u} {spec : OracleSpec ι} {m : Type v → Type z}
    [MonadLift (OracleComp spec) m] {α : Type v}
    (q : OracleQuery spec α) :
    (liftM q : m α) = liftM (liftM q : OracleComp spec α) := rfl

omit [CharP L 2] [SampleableType L] in
lemma mem_support_queryFiberPoints
    -- The number of oracles in query phase is toCodewordsCount(ℓ) = ℓ/ϑ
    {oraclePositionIdx : Fin (ℓ / ϑ)} (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (f_i_on_fiber : Vector L (2 ^ ϑ))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn :
      ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    -- Hypothesis: The fiber evaluations come from the simulated oracle query
    (h_fiber_mem :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      some (f_i_on_fiber) ∈
      support (simulateQ.{0, 0, 0} so
        ((queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oraclePositionIdx v)))) :
    let k_th_oracleIdx: Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      ⟨oraclePositionIdx, by simp only [toOutCodewordsCount, Fin.val_last,
        lt_self_iff_false, ↓reduceIte, add_zero, Fin.is_lt];⟩
    ∀ (fiberIndex : Fin (2 ^ ϑ)),
      f_i_on_fiber.get fiberIndex =
      (oStmtIn k_th_oracleIdx (getFiberPoint 𝔽q β oraclePositionIdx v fiberIndex)) := by
  simp only [MessageIdx] at h_fiber_mem
  set step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) with h_step
  set transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges with h_transcript
  set so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages with h_so
  -- rw [simulateQ_liftComp] at h_fiber_mem
  unfold queryFiberPoints at h_fiber_mem
  simp only at h_fiber_mem
  unfold queryCodeword at h_fiber_mem
  -- Simplify the simulation through liftComp/liftM
  -- simp_rw [← simulateQ_liftComp] at h_fiber_mem
  -- simp only [liftComp_eq_liftM] at h_fiber_mem
  -- Step 1: Unpack Vector.mapM membership
  erw [OptionT.simulateQ_vector_mapM] at h_fiber_mem
  erw [OptionT.mem_support_vector_mapM] at h_fiber_mem
  -- simp only [liftM, monadLift, MonadLift.monadLift] at h_fiber_mem
  conv_rhs at h_fiber_mem =>
    erw [simulateQ_liftComp]
    simp only [MessageIdx, Message, Fin.getElem_fin, Vector.getElem_mk, OptionT.run_monadLift,
      simulateQ_map, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      OptionT.mem_support_iff, toPFunctor_emptySpec, OptionT.support_run_eq, support_map,
      Set.mem_image, Option.some.injEq, exists_eq_right]
    erw [OptionT.run_monadLift, simulateQ_map, simulateQ_spec_query,
      simulateQ_simOracle2_liftM_query_T1]
  simp only
  intro fiberIndex
  have h_res := h_fiber_mem fiberIndex
  -- reduce `f_i_on_fiber[i] ∈ support (some <$> pure answer)` (OracleComp map on `Option`)
  -- to the equality: `some <$> pure a = pure (some a)` (defeq), whose support is `{some a}`,
  -- so membership defeq-reduces to `some f_i[i] = some (answer …)`.
  have key : (some f_i_on_fiber[fiberIndex.val] : Option L) =
      some (OracleInterface.answer (oStmtIn ⟨oraclePositionIdx.val, by
        simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
          Fin.is_lt]⟩)
        (getFiberPoint 𝔽q β oraclePositionIdx v (Array.finRange (2 ^ ϑ))[fiberIndex.val])) := h_res
  rw [Vector.get_eq_getElem]
  injection key with key'
  rw [key', Array.getElem_finRange]
  congr 1

/-! Simulated `queryFiberPoints` has zero failure probability. -/
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ in
set_option backward.isDefEq.respectTransparency false in
lemma probFailure_simulateQ_queryFiberPoints_eq_zero
    (so : QueryImpl
      ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ +
        [(pSpecQuery 𝔽q β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))
      (OracleComp []ₒ))
    (k : Fin (List.finRange (ℓ / ϑ)).length)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    Pr[⊥ |
      OptionT.mk
        (simulateQ.{0, 0, 0} so
          (queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((List.finRange (ℓ / ϑ)).get k) v))] = 0 := by
  dsimp only [queryFiberPoints, queryCodeword, OptionT.mk]
  erw [OptionT.simulateQ_vector_mapM_eq]
  apply OptionT.probFailure_vector_mapM_eq_zero
  intro x _
  erw [OptionT.probFailure_eq (m := OracleComp []ₒ)]
  simp only [probFailure_eq_zero, zero_add]
  rw [probOutput_eq_zero_iff]
  simp [OptionT.run, liftM, monadLift, MonadLift.monadLift, OptionT.mk,
    OptionT.lift, simulateQ_map]

lemma getBit_eq_testBit (n k : ℕ) : Nat.getBit k n = 1 ↔ Nat.testBit n k = true := by
  unfold Nat.getBit Nat.testBit
  have h : n >>> k &&& 1 = 1 &&& n >>> k := Nat.land_comm _ _
  rw [h]
  cases h_eq : 1 &&& n >>> k
  · simp
  · case succ m =>
    have h_le : m + 1 ≤ 1 := by
      calc m + 1 = 1 &&& n >>> k := h_eq.symm
        _ ≤ 1 := Nat.and_le_left
    have h_m_0 : m = 0 := by omega
    subst h_m_0
    simp

omit [CharP L 2] [SampleableType L] in
lemma iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask
    (i : Fin r) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps)
    (h_destIdx_le : destIdx.val ≤ ℓ)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, by omega⟩) (k := i.val)
      (h_destIdx := by simp only [zero_add])
      (h_destIdx_le := by omega) v =
    qMap_total_fiber 𝔽q β i steps h_destIdx h_destIdx_le
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, by omega⟩) (k := destIdx.val)
        (h_destIdx := by simp only [zero_add])
        (h_destIdx_le := h_destIdx_le) v)
      (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) := by
  have h_R_pos : 0 < 𝓡 := NeZero.pos 𝓡
  have h_i_le : i.val ≤ ℓ := by omega
  have h_i : i.val < ℓ + 𝓡 := Nat.lt_of_le_of_lt h_i_le (Nat.lt_add_of_pos_right h_R_pos)
  have h_zero : (0 : Fin r).val < ℓ + 𝓡 := by
    change 0 < ℓ + 𝓡
    exact Nat.lt_of_lt_of_le (NeZero.pos ℓ) (Nat.le_add_right ℓ 𝓡)
  apply LinearEquiv.injective (sDomain_basis 𝔽q β h_ℓ_add_R_rate i h_i).repr
  ext j
  rw [getSDomainBasisCoeff_of_iteratedQuotientMap]
  set y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, by omega⟩) (k := destIdx.val)
      (h_destIdx := by simp only [zero_add]) (h_destIdx_le := h_destIdx_le) v
  have h_repr_fiber := qMap_total_fiber_repr_coeff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_destIdx h_destIdx_le (y := y)
    (k := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) (j := j)
  simp only [y] at h_repr_fiber
  rw [h_repr_fiber]
  by_cases h_j : j.val < steps
  · unfold fiber_coeff
    rw [dif_pos h_j]
    set pointFinIdx :=
      sDomainToFin 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ h_zero v
    have h_j_shift : j.val + i.val < ℓ + 𝓡 := by
      omega
    have h_coeff_v := finToBinaryCoeffs_sDomainToFin 𝔽q β h_ℓ_add_R_rate
      ⟨0, by omega⟩ h_zero v
    simp only at h_coeff_v
    have h_coeff_vj := congrFun h_coeff_v ⟨j.val + i.val, h_j_shift⟩
    simp only [finToBinaryCoeffs] at h_coeff_vj
    rw [← h_coeff_vj]
    have h_middle_bit :
        Nat.getBit (k := j) (n := extractMiddleFinMask 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) =
          Nat.getBit (k := j.val + i.val) (n := pointFinIdx) := by
      dsimp [extractMiddleFinMask, pointFinIdx]
      rw [Nat.getBit_of_middleBits]
      simp only [h_j, ↓reduceIte]
      congr 1
    rw [← h_middle_bit]
    by_cases h_bit :
        Nat.getBit (k := j) (n := extractMiddleFinMask 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) = 0
    · simp [h_bit]
    · have h_bit_one :
          Nat.getBit (k := j) (n := extractMiddleFinMask 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) = 1 := by
        have h := Nat.getBit_eq_zero_or_one
          (k := j) (n := extractMiddleFinMask 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps)
        simp only [h_bit, false_or] at h
        exact h
      simp [h_bit_one]
  · unfold fiber_coeff
    rw [dif_neg h_j]
    have h_res := getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      ⟨0, by omega⟩ (k := destIdx.val) (h_destIdx := by simp only [zero_add])
      (h_destIdx_le := h_destIdx_le) (x := v) (j := ⟨j.val - steps, by omega⟩)
    simp only at h_res
    have h_idx :
        (⟨j.val + i.val, by omega⟩ : Fin (ℓ + 𝓡)) =
          ⟨j.val - steps + destIdx.val, by omega⟩ := by
      apply Fin.eq_of_val_eq
      simp only
      rw [h_destIdx]
      omega
    rw [h_idx]
    exact h_res.symm

omit [CharP L 2] [SampleableType L] in
/-- Lemma 1 (Safety):
Proves that if `c_k` is the result of `iterated_fold` up to step `k`,
it must match the oracle evaluation at that step (provided by `h_relIn`).
-/
lemma query_phase_consistency_guard_safe
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c_k : L)
    (f_i_on_fiber : Vector L (2 ^ ϑ))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    -- Hypothesis: c_k is the correct iterated fold value up to this point
    (h_c_k_correct :
      let := k_mul_ϑ_lt_ℓ (k := k)
      let := k_succ_mul_ϑ_le_ℓ (k := k)
      c_k = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k.val * ϑ)
        (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ)
          stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
        (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]))
    -- Hypothesis: We are at a step > 0 where a check actually happens
    (h_k_pos : k.val * ϑ > 0)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    -- Hypothesis: The fiber evaluations come from the simulated oracle query
    (h_fiber_mem :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      some (f_i_on_fiber) ∈
      support (simulateQ.{0, 0, 0} so
        ((queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v)))) :
  let := k_mul_ϑ_lt_ℓ (k := k)
  c_k = f_i_on_fiber.get (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (v := v) (i := ⟨k.val * ϑ, by omega⟩) (steps := ϑ)) := by
  have _ := h_k_pos
  have h_fiber_val := mem_support_queryFiberPoints 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v f_i_on_fiber stmtIn
    oStmtIn witIn challenges (h_fiber_mem := h_fiber_mem)
  simp only at h_fiber_val
  rw [h_c_k_correct]
  simp only
  have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k)
  set destIdx : Fin r := ⟨k.val * ϑ, by omega⟩ with h_destIdx_eq
  conv_rhs => rw [h_fiber_val]
  dsimp only [strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
    strictfinalSumcheckStepFoldingStateProp] at h_relIn
  simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn
  rcases h_relIn with ⟨exists_t_MLP, _⟩
  rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency
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
    dsimp only [getFiberPoint, getChallengeSuffix, challengeSuffixToFin, extractSuffixFromChallenge]
    -- Both sides use iteratedQuotientMap, so we need to show they're applied to the same element
    have h_aux := iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask
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

set_option backward.isDefEq.respectTransparency false in
omit [CharP L 2] [SampleableType L] in
/--
Lemma 2 (Preservation):
Proves that `checkSingleFoldingStep` computes the correct `iterated_fold` value at step `k+1`.

**Key insight**: This lemma does NOT require `c_k` to be the correct fold value as a hypothesis.
Why? Because `checkSingleFoldingStep` performs a **direct computation** from oracle queries:
  `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`

The output `s'` is computed via `single_point_localized_fold_matrix_form` using:
- Fresh oracle queries to `f^(i)` (the fiber evaluations)
- The folding challenges from position `i` to `i+ϑ`
- The suffix of the challenge `v` starting at `i+ϑ`

The input `c_k` is only used for the guard check (validating consistency when `i > 0`),
but it does NOT affect the computation of the output value `s'`.
-/
lemma query_phase_step_preserves_fold
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c_k : L) (s' : L) -- The next state (c_next)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), ()))
    (h_c_k_correct_of_k_pos :
      let := k_mul_ϑ_lt_ℓ (k := k)
      let := k_succ_mul_ϑ_le_ℓ (k := k)
      if _ : k.val > 0 then
        c_k = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k.val * ϑ)
          (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
          (f := getFirstOracle 𝔽q β oStmtIn)
          (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges
            0 (by simp only [zero_add, Fin.val_last]; omega))
          (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
            (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
          (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
      else True)
    -- Hypothesis: s' is a valid output of the simulated step function
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    (h_s'_mem :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let witIn : Unit := ()
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      s' ∈
      support (OptionT.mk
        (simulateQ.{0, 0, 0} so
          ((checkSingleFoldingStep 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k c_k v stmtIn))))) :
    let := k_succ_mul_ϑ_le_ℓ (k := k)
    s' = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (k.val + 1) * ϑ)
        (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega))
        (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
          (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add];) := by
  let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let witIn : Unit := ()
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages
  -- This is basically due to definition of s'
  -- First, convert h_s'_mem to equality form
  dsimp only [checkSingleFoldingStep] at h_s'_mem
  -- 2. Handle the conditional guard (k > 0 vs k = 0)
  --    In both cases, the core computation (query + fold) is the same.
  have h₁ := k_succ_mul_ϑ_le_ℓ (k := k)
  have h₂ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (by exact hdiv.out)
  let destIdx : Fin r := ⟨(k.val + 1) * ϑ, by omega⟩
  let midIdx : Fin r := ⟨k.val * ϑ, by omega⟩
  by_cases h_k_pos : k.val > 0
  · -- Case k > 0: The guard is present.
    -- **Simplify the monadic structure**
    -- fiber_vec is the vector of fiber evaluations at domain Sˆ{k * ϑ} of (y ∈ Sˆ{(k+1) * ϑ})
    -- Goal s'= fold (f^0)(r_0, ..., r_{(k+1)*ϑ-1})(y)
    simp only
    have h_mul_ϑ_gt_0 : k.val * ϑ > 0 := by
      simp only [gt_iff_lt, CanonicallyOrderedAdd.mul_pos]; omega
    simp only [MessageIdx, Message, gt_iff_lt, h_mul_ϑ_gt_0, ↓reduceDIte, guard_eq, Fin.val_last,
      bind_pure_comp, ReduceClaim.support_mk, Set.mem_ofPred_eq] at h_s'_mem
    erw [simulateQ_bind, support_bind] at h_s'_mem
    simp only [Set.mem_iUnion, exists_prop] at h_s'_mem
    rcases h_s'_mem with ⟨fiber_vec_Opt, h_fiber_vec_Opt_mem_support, h_s'_mem_support_guard⟩
    let k_fin_list : Fin (List.finRange (ℓ / ϑ)).length := ⟨k.val, by
      simp only [List.length_finRange, Fin.is_lt]⟩
    have h_k_fin_list_eq : k = ((List.finRange (ℓ / ϑ)).get k_fin_list) := by
      apply Fin.eq_of_val_eq; simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta,
        Fin.val_cast]; rfl
    have h_probFailure_queryFiberPoints_eq_zero := by
      apply probFailure_simulateQ_queryFiberPoints_eq_zero (γ_repetitions := γ_repetitions)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝔽q := 𝔽q) (β := β)
        (so := so) (k := k_fin_list) (v := v)
    rw [OptionT.probFailure_eq] at h_probFailure_queryFiberPoints_eq_zero
    have h_probOutput_none_queryFiberPoints_eq_zero :=
      (add_eq_zero.mp h_probFailure_queryFiberPoints_eq_zero).2
    have h_fiber_vec_Opt_mem_support_eq := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero
      (x := fiber_vec_Opt) (hx := h_fiber_vec_Opt_mem_support) (hnone := by
      have h_none := h_probOutput_none_queryFiberPoints_eq_zero
      simp only [so, transcript, h_k_fin_list_eq] at h_none ⊢
      exact h_none)
    rcases h_fiber_vec_Opt_mem_support_eq with ⟨fiber_vec, h_fiber_vec_Opt_mem_support_eq⟩
    rw [h_fiber_vec_Opt_mem_support_eq] at h_s'_mem_support_guard h_fiber_vec_Opt_mem_support
    -- h_s'_eq : s' = the evaluation at y of the folded function from fiber_vec
    -- simp only [OptionT.simulateQ_map] at h_s'_mem_support_guard
    have h_fiber_val := mem_support_queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v fiber_vec stmtIn
      oStmtIn () challenges (by exact h_fiber_vec_Opt_mem_support)
    erw [simulateQ_bind, support_bind] at h_s'_mem_support_guard
    simp only [Function.comp_apply, Set.mem_iUnion, exists_prop] at h_s'_mem_support_guard
    have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k)
    -- 1. Simplify failure probability to just the guard condition
    -- simp only [h_i_pos, ↓reduceIte, OptionT.simulateQ_map]
    have h_guard_pass : c_k = fiber_vec.get (extractMiddleFinMask 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (i := ⟨k.val * ϑ, by omega⟩) (steps := ϑ)) := by
      have h_mul_gt_0 : k.val * ϑ > 0 := by
        simp only [gt_iff_lt, CanonicallyOrderedAdd.mul_pos]
        omega
      have h_k_eq_fin_cast : k = Fin.cast (by simp only [List.length_finRange]) k_fin_list := by
        apply Fin.eq_of_val_eq; simp only [Fin.val_cast]; rfl
      -- 4. Apply the lemma
      have res := query_phase_consistency_guard_safe 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (k := k) (v := v) (c_k := c_k) (f_i_on_fiber := fiber_vec) (stmtIn := stmtIn)
        (oStmtIn := oStmtIn) (witIn := witIn) (h_relIn := h_relIn) (h_c_k_correct := by
        simp only at h_c_k_correct_of_k_pos
        simp only [gt_iff_lt, h_k_pos] at h_c_k_correct_of_k_pos
        exact h_c_k_correct_of_k_pos
      ) (h_k_pos := h_mul_gt_0) (γ_repetitions := γ_repetitions) (challenges := challenges)
        (h_fiber_mem := by simp only [witIn]; exact h_fiber_vec_Opt_mem_support)
      exact res
    simp only [h_guard_pass, ↓reduceIte] at h_s'_mem_support_guard
    erw [simulateQ_pure] at h_s'_mem_support_guard
    simp only [support_pure, Set.mem_singleton_iff, exists_eq_left,
      OptionT.pure, support_pure] at h_s'_mem_support_guard
    dsimp only [OptionT.mk] at h_s'_mem_support_guard
    erw [_root_.simulateQ_pure] at h_s'_mem_support_guard
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq]
      at h_s'_mem_support_guard
    -- Step 1: Use symmetry of h_s'_eq
    rw [h_s'_mem_support_guard]
    dsimp only [getChallengeSuffix] -- extractSuffixFromChallenge  arise here
    have h_destIdx_eq : destIdx.val = k.val * ϑ + ϑ := by
      dsimp only [destIdx]; rw [Nat.add_mul, Nat.one_mul]
  --  iterated_fold 𝔽q β 0 ((↑k + 1) * ϑ) ⋯ ⋯ (getFirstOracle 𝔽q β oStmtIn)
  --   (getFoldingChallenges (Fin.last ℓ) stmtIn.challenges 0 ⋯) (extractSuffixFromChallenge
    -- 𝔽q β v ⟨(↑k + 1) * ϑ, ⋯⟩ ⋯)
    set challenges_full := getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := (k.val + 1) * ϑ)
      (i := Fin.last ℓ) stmtIn.challenges (k := 0)
      (h := by simp only [zero_add, Fin.val_last, k_succ_mul_ϑ_le_ℓ]) with h_challenges_full_defs
    set challenges_mid := getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := k.val * ϑ)
      (i := Fin.last ℓ) stmtIn.challenges (k := 0)
      (h := by simp only [zero_add, Fin.val_last]; omega) with h_challenges_mid_defs
    set challenges_last : Fin ϑ → L := (fun j ↦ stmtIn.challenges ⟨↑k * ϑ + ↑j, by
      simp only [Fin.val_last]; omega⟩) with h_challenges_last_defs
    set y_left := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (h_destIdx_le := by omega) with hy_left_defs
    set y_right := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by omega) with hy_right_defs
    -- -- Step 2: Transform the RHS
    -- Define f_mid directly from oStmtIn k, which is simpler and aligns with fiber_vec.get
    let k_oracle_idx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      ⟨k, by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩
    -- Prove that oraclePositionToDomainIndex matches midIdx
    have h_domain_idx_eq : (oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ)
      (positionIdx := k_oracle_idx)).val = midIdx.val := by
      dsimp only [oraclePositionToDomainIndex, midIdx]
    have h_sDomain_midIdx_eq : sDomain 𝔽q β h_ℓ_add_R_rate midIdx = sDomain 𝔽q β h_ℓ_add_R_rate
      ⟨(oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ)
        (positionIdx := k_oracle_idx)).val, by omega⟩ := by
      apply congrArg (sDomain 𝔽q β h_ℓ_add_R_rate)
      apply Fin.eq_of_val_eq
      rw [h_domain_idx_eq]
    let f_mid : ↥(sDomain 𝔽q β h_ℓ_add_R_rate midIdx) → L :=
      fun x => oStmtIn k_oracle_idx (cast (by rw [h_sDomain_midIdx_eq]) x)
    set fiber_vec_actual_def := fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := ϑ) (destIdx := ⟨k * ϑ + ϑ, by omega⟩) (h_destIdx := by
        simp only [Nat.add_right_cancel_iff]; rfl)
      (h_destIdx_le := by omega) (f := f_mid)
      (y := y_left) with h_fiber_vec_actual_def
    have h_fiber_vec_get : fiber_vec.get = fiber_vec_actual_def := by
      dsimp only [fiber_vec_actual_def]; unfold fiberEvaluations
      funext x
      conv_lhs =>
        rw [h_fiber_val x]; dsimp only [getFiberPoint]
        dsimp only [getChallengeSuffix]
      conv_rhs =>
      dsimp only [f_mid]
      apply OracleStatement.oracle_eval_congr 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oStmtIn := oStmtIn) (j' := k_oracle_idx) (j := ⟨k, by
          simp only [toOutCodewordsCount_last, Fin.is_lt]⟩) (h_j := by rfl)
      rfl
    rw [h_fiber_vec_get]; dsimp only [fiber_vec_actual_def]
    have h_eq := single_point_localized_fold_matrix_form_eq_iterated_fold 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (steps := ϑ)
      (destIdx := ⟨k * ϑ + ϑ, by omega⟩) (h_destIdx := by simp only [Nat.add_right_cancel_iff]; rfl)
      (h_destIdx_le := by omega) (f := f_mid) (y := y_left) (r_challenges :=
        fun j => stmtIn.challenges ⟨k.val * ϑ + j.val, by simp only [Fin.val_last]; omega⟩)
    conv_lhs => erw [h_eq]
    dsimp only [f_mid]
    -- Now rw the oStmtIn k_oracle_idx into the iterated_fold of f⁽⁰⁾ form
    -- Extract t and strictOracleFoldingConsistencyProp from h_relIn
    dsimp only [strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
      strictfinalSumcheckStepFoldingStateProp] at h_relIn
    simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn
    rcases h_relIn with ⟨exists_t_MLP, _⟩
    rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
    dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency
    -- Get the equality for k_oracle_idx: oStmtIn k_oracle_idx = iterated_fold from 0 to k.val * ϑ
    have h_f_mid_eq_iterated_fold := h_strictOracleFoldingConsistency k_oracle_idx
    conv_lhs => rw [h_f_mid_eq_iterated_fold]
    let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => t.eval (bitsOfIndex ω))
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    conv_lhs => dsimp only [midIdx]
    conv_lhs => simp only [cast_eq, Fin.val_last]; rw [←fun_eta_expansion]
    conv_lhs =>
      rw [iterated_fold_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff,
          mul_eq_mul_right_iff]; left; rfl
      )]
    dsimp only [k_oracle_idx]
    -- Step 1: Align steps (k * ϑ + ϑ = (k + 1) * ϑ)
    have h_steps_eq : k.val * ϑ + ϑ = (k.val + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
    conv_lhs =>
      erw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
        (steps := k.val * ϑ + ϑ) (steps' := (k.val + 1) * ϑ)
        (h_destIdx := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]) (h_destIdx_le := by omega)
        (h_steps_eq_steps' := h_steps_eq)
        (f := f₀) (r_challenges := Fin.append challenges_mid challenges_last)
        (y := y_left)]
    -- Step 2: Align destIdx (⟨k * ϑ + ϑ, ...⟩ = ⟨(k + 1) * ϑ, ...⟩)
    conv_lhs =>
      rw [iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
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
      -- dsimp only [chalLeft, chalRight]
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
        (h_idx_eq := by apply Fin.eq_of_val_eq; omega)]
    conv_lhs => rw [h_y_eq]
  · -- Case k = 0: No guard.
    ---------------------------------------------------------------------
    -- First establish that k = 0
    simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h_k_pos
    have h_mul_eq_0 : ↑k * ϑ = 0 := by
      rw [h_k_pos]; simp only [zero_mul]
    have h_k_eq_0 : k.val = 0 := by
      by_contra h_ne
      have : k.val > 0 := Nat.pos_of_ne_zero h_ne
      have : k.val * ϑ > 0 := Nat.mul_pos this (Nat.pos_of_neZero ϑ)
      omega
    simp only [h_k_eq_0, zero_mul, zero_add] at h_s'_mem ⊢
    simp only [MessageIdx, Message, gt_iff_lt, lt_self_iff_false, ↓reduceDIte, Fin.mk_zero',
      Fin.val_last, bind_pure_comp, ReduceClaim.support_mk,
      Set.mem_ofPred_eq] at h_s'_mem
    erw [simulateQ_bind, support_bind] at h_s'_mem
    simp only [Set.mem_iUnion, exists_prop] at h_s'_mem
    rcases h_s'_mem with ⟨fiber_vec_Opt, h_fiber_vec_Opt_mem_support, h_s'_mem_support_guard⟩
    let k_fin_list : Fin (List.finRange (ℓ / ϑ)).length := ⟨k.val, by
      simp only [List.length_finRange, Fin.is_lt]⟩
    have h_k_fin_list_eq : k = ((List.finRange (ℓ / ϑ)).get k_fin_list) := by
      apply Fin.eq_of_val_eq; simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta,
        Fin.val_cast]; rfl
    have h_probFailure_queryFiberPoints_eq_zero := by
      apply probFailure_simulateQ_queryFiberPoints_eq_zero (γ_repetitions := γ_repetitions)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝔽q := 𝔽q) (β := β)
        (so := so) (k := k_fin_list) (v := v)
    rw [OptionT.probFailure_eq] at h_probFailure_queryFiberPoints_eq_zero
    have h_probOutput_none_queryFiberPoints_eq_zero :=
      (add_eq_zero.mp h_probFailure_queryFiberPoints_eq_zero).2
    have h_exists_some_fiber_vec_of_fiber_vec_Opt :=
      exists_eq_some_of_mem_support_of_probOutput_none_eq_zero
      (x := fiber_vec_Opt) (hx := h_fiber_vec_Opt_mem_support) (hnone := by
      have h_none := h_probOutput_none_queryFiberPoints_eq_zero
      simp only [so, transcript, h_k_fin_list_eq] at h_none ⊢
      exact h_none)
    rcases h_exists_some_fiber_vec_of_fiber_vec_Opt with ⟨fiber_vec, h_fiber_vec_Opt_eq_some⟩
    rw [h_fiber_vec_Opt_eq_some] at h_s'_mem_support_guard h_fiber_vec_Opt_mem_support
    -- **Simplify the monadic structure**
    simp only at h_s'_mem_support_guard
    erw [simulateQ_pure] at h_s'_mem_support_guard
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at h_s'_mem_support_guard
    -- h_s'_mem_support_guard : s' = single_point_localized_fold_matrix_form
    have h_fiber_val := mem_support_queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v fiber_vec stmtIn
      oStmtIn () challenges (by exact h_fiber_vec_Opt_mem_support)
    -- Step 1: Use symmetry of h_s'_eq
    rw [h_s'_mem_support_guard]
    -- ⊢ single_point_localized_fold_matrix_form ... = iterated_fold ...
    have h_destIdx_eq : destIdx.val = ϑ := by
      dsimp only [destIdx]; rw [h_k_eq_0, zero_add, one_mul]
  --  iterated_fold 𝔽q β 0 ((↑k + 1) * ϑ) ⋯ ⋯ (getFirstOracle 𝔽q β oStmtIn)
  --   (getFoldingChallenges (Fin.last ℓ) stmtIn.challenges 0 ⋯)
        -- (extractSuffixFromChallenge 𝔽q β v ⟨(↑k + 1) * ϑ, ⋯⟩ ⋯)
    let challenges_full := getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := (k.val + 1) * ϑ)
      (i := Fin.last ℓ) stmtIn.challenges
      (k := 0) (h := by simp only [zero_add, Fin.val_last]; omega)
    set y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by omega) with hy_def
    -- Step 2: Transform the RHS
    let rhs_to_mat_mul_form := iterated_fold_eq_matrix_form 𝔽q β (i := 0)
      (steps := (k.val + 1) * ϑ) (destIdx := destIdx) (h_destIdx := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
      (h_destIdx_le := by omega) (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := challenges_full)
    conv_rhs =>
      rw [rhs_to_mat_mul_form]
      dsimp only [localized_fold_matrix_form]
    -- Step 3: Unfold localized form
  -- 1. Simplify the index arithmetic for k=0
    --    (k+1)*ϑ becomes ϑ
    -- simp? [Fin.mk_zero', Fin.val_last]
    -- 2. Unfold your helper definition
    --    This reveals that LHS suffix is exactly the RHS suffix
    dsimp only [getChallengeSuffix]
    set fiber_vec_actual_def := fiberEvaluations 𝔽q β (i := 0) (steps := ϑ) (destIdx := destIdx)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by omega) (f := getFirstOracle 𝔽q β oStmtIn) (y := y) with hright_def
    have h_fiber_vec_get : fiber_vec.get = fiber_vec_actual_def := by
      dsimp only [fiber_vec_actual_def]; unfold fiberEvaluations
      funext x
      conv_lhs =>
        rw [h_fiber_val x]; dsimp only [getFiberPoint]
        dsimp only [getChallengeSuffix]
      conv_rhs =>
        dsimp only [getFirstOracle]
      simp only [Fin.mk_zero']
      -- symm
      apply OracleStatement.oracle_eval_congr 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oStmtIn := oStmtIn) (j' := 0) (j := ⟨k, by
          simp only [toOutCodewordsCount_last, Fin.is_lt]⟩) (h_j := by
          apply Fin.eq_of_val_eq
          exact h_k_eq_0)
      have h_destIdx_eq : (⟨k.val * ϑ + ϑ, by omega⟩ : Fin r) = ⟨(k.val + 1) * ϑ, by omega⟩ := by
        apply Fin.eq_of_val_eq
        simp only [Nat.add_mul, one_mul]
      simp only [Fin.coe_ofNat_eq_mod, cast_cast]
      have h_i_eq : (⟨k.val * ϑ, by omega⟩ : Fin r) = 0 := by
        apply Fin.eq_of_val_eq
        simp [h_mul_eq_0]
      have hsrc_fun := qMap_total_fiber_congr_source_apply 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (steps := ϑ) (destIdx := destIdx) (sourceIdx₁ := (⟨k.val * ϑ, by omega⟩ : Fin r))
        (sourceIdx₂ := 0) (h_sourceIdx_eq := h_i_eq)
        (h_destIdx := by dsimp only [destIdx]; rw [Nat.add_mul, Nat.one_mul])
        (h_destIdx_le := by omega) (y := y) (x := x)
      -- qMap_total_fiber source/dest congruence over `k*ϑ+ϑ` vs `(k+1)*ϑ`: the suffix and the
      -- extra `cast` are all heterogeneously equal (source indices agree, `cast_heq`).
      rw [hy_def]
      convert hsrc_fun using 3
    rw [h_fiber_vec_get]
    -- Step 4: Apply the congruence lemma of single_point_localized_fold_matrix_form
      -- 1. Establish that the step counts are equal
    have h_steps_eq : ϑ = (↑k + 1) * ϑ := by
      simp only [h_k_eq_0, zero_add, one_mul]
    -- 2. Apply the Step Congruence Lemma to the RHS
    --    We rewrite the RHS to use 'ϑ' instead of '(k+1)*ϑ'
    conv_rhs => rw [single_point_localized_fold_matrix_form_congr_steps_index 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps' := ϑ) (h_steps_eq_steps' := h_steps_eq.symm)]
    have h_challenges_eq :
      (fun (j : Fin ϑ) => stmtIn.challenges ⟨j.val, by simp only [Fin.val_last]; omega⟩)
      = fun (j : Fin ϑ) => challenges_full ⟨j.val, by omega⟩ := by
        funext j
        dsimp only [challenges_full, getFoldingChallenges]
        simp only [Fin.val_last, zero_add]
    conv_lhs => erw [h_challenges_eq]
    have h_sDomain_eq : (sDomain 𝔽q β h_ℓ_add_R_rate ⟨↑k * ϑ + ϑ, by omega⟩)
      = (sDomain 𝔽q β h_ℓ_add_R_rate ⟨(↑k + 1) * ϑ, by omega⟩) := by
      apply congrArg (sDomain 𝔽q β h_ℓ_add_R_rate)
      apply Fin.ext
      simp only [Nat.add_mul, Nat.one_mul]
    conv_lhs =>
      rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
      dsimp only [destIdx]; simp only [Nat.add_mul, Nat.one_mul])]
    have h_y_eq : y = cast (by rw [h_sDomain_eq]) (extractSuffixFromChallenge 𝔽q β (v := v)
      (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩)
      (h_destIdx_le := by simp only [k_succ_mul_ϑ_le_ℓ_₂])) := by
      rw [hy_def]
      rw [extractSuffixFromChallenge_congr_destIdx]
      simp only [Nat.add_mul, Nat.one_mul]
    rw [←h_y_eq]
    dsimp only [fiber_vec_actual_def, fiberEvaluations]
    rw [qMap_total_fiber_congr_steps 𝔽q β (i := 0) (steps := ϑ) (steps' := (↑k + 1) * ϑ)
      (h_steps_eq := h_steps_eq) (y := y)]

/-! Lemma 3 (Completeness):
Proves that the fully folded value (result of `iterated_fold` at `ℓ`)
equals the `final_constant` expected by the statement.
-/
omit [SampleableType L] [DecidableEq 𝔽q] in
set_option backward.isDefEq.respectTransparency false in
omit [CharP L 2] in
lemma query_phase_final_fold_eq_constant
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c : L)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    -- Hypothesis: x is the result of folding all the way to ℓ
    (h_c_correct :
      have h_mul_eq : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
      c = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (ℓ / ϑ) * ϑ)
        (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega))
        (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add];)
    ) :
    c = stmtIn.final_constant := by
  classical
  dsimp only [strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
    strictfinalSumcheckStepFoldingStateProp] at h_relIn
  simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn
  -- 2. Extract the existential witnesses
  rw [h_c_correct]
  rcases h_relIn with ⟨exists_t_MLP, h_final_oracle_fold_to_constant⟩
  have h_final_oracle_fold_to_const_at_0 := congr_fun h_final_oracle_fold_to_constant 0
  rw [h_final_oracle_fold_to_const_at_0.symm]
  rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency
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
    rw [toOutCodewordsCount_last];
    simp only [Nat.zero_mod, zero_mul]
  rw [iterated_fold_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff,
    mul_eq_mul_right_iff];
    rw [getLastOraclePositionIndex_last];
    dsimp only [lastOraclePositionIndex]
    rw [getLastOraclePositionIndex_last];
    simp only [true_or]
  )]
  set chalLeft := (getFoldingChallenges (i := Fin.last ℓ) (𝓡 := 𝓡) (r := r)
    (challenges := stmtIn.challenges) (k := 0) (ϑ := ℓ/ϑ * ϑ) (by
    simp only [zero_add, Fin.val_last]; omega)) with h_chalLeft
  -- have h_concat_challenges_eq :
  set chalRight := Fin.append (getFoldingChallenges (i := Fin.last ℓ) (𝓡 := 𝓡) (r := r)
    (challenges := stmtIn.challenges) (k := 0) (ϑ := lastOraclePositionIndex.val * ϑ)
      (by simp only [zero_add, Fin.val_last, oracle_index_le_ℓ]))
      (fun (cId : Fin ϑ) ↦
        stmtIn.challenges ⟨(getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)) * ϑ + cId.val, by
          simp only [Fin.val_last, getLastOraclePositionIndex_last];
          simp only [lastBlockIdx_mul_ϑ_add_fin_lt_ℓ]⟩) with h_chalLeft
  have h_chalLeft_eq_chalRight_cast : chalLeft = fun cIdx : Fin (ℓ / ϑ * ϑ) => chalRight ⟨cIdx, by
    dsimp only [lastOraclePositionIndex]
    simp only [getLastOraclePositionIndex_last];
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
      rw [add_comm];
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
    rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := 0 % toOutCodewordsCount ℓ ϑ (Fin.last ℓ) * ϑ) (steps' := 0) (h_destIdx := by
      simp only [toOutCodewordsCount_last, Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod, add_zero])
      (h_destIdx_le := by simp only [toOutCodewordsCount_last, Nat.zero_mod, zero_mul, zero_le])
      (h_steps_eq_steps' := by omega)]
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (h_destIdx := by simp only [toOutCodewordsCount_last,
      Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod])]
  conv_lhs => simp only [cast_cast, cast_eq]; simp only [←fun_eta_expansion]
  conv_lhs =>
    rw [←iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := (ℓ / ϑ * ϑ)) (h_destIdx := by
      dsimp only [lastOraclePositionIndex];
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
    erw [iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (destIdx := ⟨ℓ / ϑ * ϑ, by omega⟩)
      (destIdx' := destIdx') (h_destIdx := by
        dsimp only [lastOraclePositionIndex];
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by simp only; omega) (h_destIdx_eq_destIdx' := by
        dsimp only [destIdx']; simp only [Fin.mk.injEq]; omega)
      (r_challenges := chalRight) (y := point)]
  rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := ℓ) (h_destIdx := by
      dsimp only [destIdx'];
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff,
      mul_eq_mul_right_iff]; omega)
    (h_destIdx_le := by dsimp only [destIdx']; simp only [oracle_index_add_steps_le_ℓ])
    (h_steps_eq_steps' := by omega)]
  rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := ℓ) (h_destIdx := by
    dsimp only [destIdx'];
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
  let res := iterated_fold_to_level_ℓ_is_constant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
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
