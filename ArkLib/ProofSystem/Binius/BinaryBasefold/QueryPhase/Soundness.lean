/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Completeness
-- These probability proofs use the protocol module's private probability helpers.
import all ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Protocol

/-!
# Binary Basefold query-phase soundness
-/

@[expose] public section

open OracleSpec
attribute [local instance] queryEmptySpecInhabited
noncomputable local instance soundnessEmptyUniformSpec : IsUniformSpec []ₒ :=
  IsUniformSpec.ofFintypeInhabited _

namespace Binius.BinaryBasefold.QueryPhase

noncomputable section
open OracleSpec _root_.OracleComp
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

/-- Pair-support projection wrapper of `support_simulateQ_run'_eq`.
`Prod.fst` of the stateful run support matches the spec support. -/
lemma support_run_simulateQ_run_fst_eq {ι : Type}
    {oSpec : OracleSpec ι} [IsUniformSpec oSpec] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec (Option α)) (s : σ)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    Prod.fst <$> support (m := ProbComp) (α := Option α × σ) ((simulateQ impl oa) s) =
      support (m := OracleComp oSpec) (α := Option α) oa := by
  have h_support := support_simulateQ_run'_eq (impl := impl) (oa := oa) (s := s)
    (hImplSupp := hImplSupp)
  rw [StateT.run'_eq, support_map] at h_support
  exact h_support
/-! **Per-repetition support → logical** (extracted for reuse from completeness-style reasoning).
**Counterpart** of `checkSingleRepetition_probFailure_eq_zero` for the `OracleComp.support` case.
If `(ForInStep.yield PUnit.unit, state_post)` lies in the support of one iteration of the
  verifier's forIn body (for a given `rep`), then the logical proximity check holds for that
  repetition: `logical_checkSingleRepetition 𝔽q β oStmtIn (tr.challenges ⟨0, rfl⟩ rep) stmtIn
    stmtIn.final_constant`.
-/
omit [CharP L 2] [SampleableType L] in
lemma logical_checkSingleRepetition_of_mem_support_forIn_body {σ : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (stmtIn : FinalSumcheckStatementOut)
    (rep : Fin γ_repetitions)
    (state_pre : σ)
    (forIn_body : Fin γ_repetitions → PUnit → StateT σ ProbComp (Option (ForInStep PUnit)))
    (h_forIn_body_eq : forIn_body =
      fun (a : Fin γ_repetitions) (_ : PUnit.{1}) =>
      OptionT.mk (simulateQ impl ((((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$>
          ((simulateQ.{0, 0, 0} (impl := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
            ((checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ a)
              stmtIn stmtIn.final_constant) :
                OptionT (OracleComp
                  ([]ₒ + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ +
                    [(pSpecQuery 𝔽q β γ_repetitions).Message]ₒ))) Unit).run) :
            OracleComp []ₒ (Option Unit))) :
          OptionT (OracleComp []ₒ) (ForInStep PUnit.{1})))))
    (h_mem : ∃ (res : ForInStep PUnit.{1} × σ), (some res.1, res.2) ∈
     support ((forIn_body rep PUnit.unit).run state_pre)) :
    logical_checkSingleRepetition 𝔽q β oStmtIn (tr.challenges ⟨0, rfl⟩ rep) stmtIn
      stmtIn.final_constant := by
  -- 1. Extract the witness res = (control_flow, state_post)
  rcases h_mem with ⟨⟨res_flow, state_post_single_outer_repetition⟩, h_support⟩
  -- 2. Unfold the body definition
  rw [h_forIn_body_eq] at h_support
  set v := tr.challenges ⟨0, rfl⟩ rep with h_v
  let Rel := checkSingleRepetition_foldRel 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)
  dsimp only [logical_checkSingleRepetition]
  conv at h_support =>
    -- 1. Expand definition to expose the `forIn` and `guard`
    dsimp only [checkSingleRepetition]
    -- 2. Distribute simulateQ and liftM over the Bind (>>=)
    --    This splits `simulateQ (Loop >>= Guard)` into `simulateQ Loop >>= simulateQ Guard`
    erw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
    erw [support_bind]
    dsimp only [Function.comp_def]
    simp only [Fin.isValue, id_map',
      guard_eq, map_bind, simulateQ_bind, simulateQ_liftComp, StateT.run_bind, Function.comp_apply,
      simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure,
      StateT.run_map, support_bind,
      support_map, Set.mem_iUnion, Set.mem_image, Prod.mk.injEq, Prod.exists, exists_eq_right_right,
      exists_and_right, exists_and_left, exists_prop]
    erw [support_bind]
    simp only [Fin.isValue, id_map',
      guard_eq, map_bind, simulateQ_bind, simulateQ_liftComp, StateT.run_bind, Function.comp_apply,
      simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure,
      StateT.run_map, support_bind,
      support_map, Set.mem_iUnion, Set.mem_image, Prod.mk.injEq, Prod.exists, exists_eq_right_right,
      exists_and_right, exists_and_left, exists_prop]
  obtain ⟨output_final_guard, output_state_final_guard, exists_c_last,
    h_final_yield_support_mem⟩ := h_support
  -- c_last is the yielded folded value from the last inner iteration (i.e. γ_repetitions-1)
  rcases exists_c_last with ⟨c_last, output_state_inner_forIn, ⟨h_mem_forIn_support,
    h_mem_final_guard_support⟩⟩
  conv at h_mem_forIn_support =>
    erw [OptionT.simulateQ_forIn]
    erw [OptionT.simulateQ_forIn_stateful_comp]
  -- Bridge to the `OptionT` path lemma: extract a successful `c_last` from support.
  obtain ⟨c_last_val, h_c_last_eq_some⟩ : ∃ c_last_val : L, c_last = some c_last_val := by
    cases h_c : c_last with
    | none =>
      exfalso
      simp only [MessageIdx, h_c, Message, simulateQ_pure] at h_mem_final_guard_support
      erw [support_pure] at h_mem_final_guard_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h_mem_final_guard_support
      obtain ⟨h_guard_none, _⟩ := h_mem_final_guard_support
      have h_final_mem := h_final_yield_support_mem
      simp only [h_guard_none, simulateQ_pure] at h_final_mem
      erw [support_pure] at h_final_mem
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at h_final_mem
    | some a =>
      exact ⟨a, rfl⟩
  have h_mem_forIn_support_some := by
    have h_mem_forIn_support_some := h_mem_forIn_support
    simp only [h_c_last_eq_some] at h_mem_forIn_support_some ⊢
    exact h_mem_forIn_support_some
  have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  have h_ℓ_div_ϑ_ge_1 : ℓ/ϑ ≥ 1 := by exact (Nat.one_le_div_iff h_ϑ_pos).mpr h_ϑ_le_ℓ
  have h_0_lt : 0 < (ℓ / ϑ) := by omega
  have h_ℓ_div_mul_eq_ℓ : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have h_lastOraclePosIdx_mul_add :
    (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)).val * ϑ + ϑ = ℓ := by
    conv_rhs => rw [←h_ℓ_div_mul_eq_ℓ]
    rw [getLastOraclePositionIndex_last]; simp only
    rw [Nat.sub_mul, Nat.one_mul]; rw [Nat.sub_add_cancel (by rw [h_ℓ_div_mul_eq_ℓ]; omega)]
  -- **Applying indutive relation inference** for the inner `forIn` only
  let Rel' := fun (i : Fin ((List.finRange (ℓ / ϑ)).length + 1)) (c_next : Option L) (_s : σ) =>
    -- state i => at the end of the inner repetition `i-1`
    -- which means at `i = 0`, value = True since nothing meaningful to check
    logical_stepCondition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn)
      (k := ⟨i - 1, by
        have hi := i.isLt;
        simp only [List.length_finRange] at hi; omega
      ⟩) (v := v) (stmt := stmtIn) (final_constant := stmtIn.final_constant)
    ∧ (
      if hi : i > 0 then
        have hi_lt := i.isLt;
        have hi_lt₂ : i - 1 < ℓ / ϑ := by
          simp only [List.length_finRange] at hi_lt; omega
        let k : Fin (ℓ / ϑ) := ⟨i - 1, by omega⟩
        -- **NOTE**: At the end of repetition `k = i-1`, the value c_next which is
          -- the evaluation on `S^{(k+1)*ϑ}` of the folded oracle function must be computed
        -- let point := getChallengeSuffix 𝔽q β (List.finRange (ℓ / ϑ))[↑k] v; fiber_vec.get
        let point := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (k := k)
        let fiber_vec : Fin (2 ^ ϑ) → L := logical_queryFiberPoints 𝔽q β oStmtIn k v
        let output_of_iteration_k : L :=
          (single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨k.val * ϑ, by
            exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h := k_mul_ϑ_lt_ℓ (k := k))
          ⟩) (steps := ϑ) (destIdx := ⟨k.val * ϑ + ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            exact k_succ_mul_ϑ_le_ℓ_₂ (k := k)
          ⟩) (h_destIdx := by
            simp only)
          (h_destIdx_le := k_succ_mul_ϑ_le_ℓ_₂ (k := k))
          (r_challenges := fun j ↦ stmtIn.challenges ⟨↑k * ϑ + ↑j, by
            simp only [Fin.val_last]
            have h_le : k.val * ϑ + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
            omega
          ⟩)
          (y := point) (fiber_eval_mapping := fiber_vec))
        some output_of_iteration_k = c_next
      else True)
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  -- inductive relation inference for the intermediate folding steps
  have h_inductive_relations := _root_.OptionT.exists_rel_path_of_mem_support_forIn_stateful.{0}
    (spec := []ₒ) (l := List.finRange (ℓ / ϑ)) (init := 0) (σ := σ)
    (s := state_pre) (res := (c_last_val, output_state_inner_forIn))
    (h_mem := h_mem_forIn_support_some) (rel := Rel') (h_start := by
      simp only [logical_stepCondition, logical_checkSingleFoldingStep, gt_iff_lt,
        CanonicallyOrderedAdd.mul_pos, tsub_pos_iff_lt, dite_else_true, Fin.val_last,
        Fin.coe_ofNat_eq_mod, List.length_finRange, Nat.zero_mod, zero_tsub, h_0_lt, ↓reduceDIte,
        _root_.not_lt_zero, false_and, zero_mul, Fin.mk_zero', IsEmpty.forall_iff,
        lt_self_iff_false,
        zero_add, and_self, Rel']
    )
    (h_step := by
      intro k (c_cur : L) (s_curr : σ) h_rel_k res_step h_res_step_mem
      -- c_cur is the yielded folded value from the previous inner iteration (i.e. k-1)
      have h_k := k.isLt
      simp only [List.length_finRange] at h_k
      have h_k_succ_sub_1_lt : k.succ.val - 1 < ℓ / ϑ := by
        simp only [Fin.val_succ, add_tsub_cancel_right]; omega
      have h_k_sub_1_lt : k.val - 1 < ℓ / ϑ := by
        omega
      have h_k_succ_gt_0 : k.succ > 0 := by simp only [gt_iff_lt, Fin.succ_pos]
      dsimp only [Rel', logical_stepCondition] at h_rel_k
      simp only [Fin.val_castSucc, h_k_sub_1_lt, ↓reduceDIte] at h_rel_k
      -- **Nested simulateQ structure** (do not simp the outer impl):
      -- • Outer: `simulateQ impl (...)` comes from RoundByRound's toFun_full: the reduction runs
      --   the verifier with a stateful oracle impl (black box). We do NOT unfold impl; we only
      --   use that its support equals the spec (support_simulateQ_run'_eq).
      -- • Inner: `simulateQ (simOracle2 []ₒ oStmtIn tr.messages) (...)` comes
      --   from OracleVerifier.toVerifier (Basic.lean): verifier checks are run with
      --   simOracle2 so oStmtIn and transcript answer the oracle queries. This inner layer
      --   can be simplified further (unfold checkSingleFoldingStep, use simOracle2 lemmas).
      set inner_base : OracleComp []ₒ (Option L) :=
        simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
          (checkSingleFoldingStep 𝔽q β γ_repetitions ((List.finRange (ℓ / ϑ)).get k)
            c_cur v stmtIn).run
      set inner_oa : OptionT (OracleComp []ₒ) (ForInStep L) :=
        ForInStep.yield <$> (OptionT.mk inner_base)
      have h_run'_supp_eq := OptionT.support_run_simulateQ_run'_eq (impl := impl)
        (oa := inner_oa)
        (s := s_curr)
        (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
      -- res_step ∈ (run s).support → res_step.1 ∈ (run' s).support = inner_oa.support
      have h_fst_mem :
          some res_step.1 ∈ support ((simulateQ impl
            inner_oa).run' s_curr) := by
        have h_run_mem :
            (some res_step.1, res_step.2) ∈
              support ((simulateQ impl inner_oa).run s_curr) := by
          have h_run_mem := h_res_step_mem
          simp only [inner_oa, inner_base, h_v, bind_pure_comp,
            OptionT.simulateQ_map] at h_run_mem ⊢
          exact h_run_mem
        simp only [StateT.run', support_map, Set.mem_image]
        exact ⟨(some res_step.1, res_step.2), h_run_mem, rfl⟩
      rw [h_run'_supp_eq] at h_fst_mem
      have h_fst_mem_opt : res_step.1 ∈ support (inner_oa) := by
        exact (OptionT.mem_support_iff (mx := inner_oa) (x := res_step.1)).2 h_fst_mem
      have h_inner_step_mem :
          ∃ c_next,
            (some c_next) ∈ support inner_base ∧ ForInStep.yield c_next = res_step.1 := by
        have h_map_mem := h_fst_mem_opt
        change res_step.1 ∈ support (ForInStep.yield <$> OptionT.mk inner_base) at h_map_mem
        rw [support_map, Set.mem_image] at h_map_mem
        rcases h_map_mem with ⟨c_next, h_c_next_mem_mk, h_yield_eq⟩
        exact ⟨c_next, (OptionT.mem_support_iff _ _).mp h_c_next_mem_mk, h_yield_eq⟩
      rcases h_inner_step_mem with ⟨c_next, h_fst_mem, h_res_step1_eq⟩
      dsimp only [Rel', logical_stepCondition]
      dsimp only [inner_base] at h_fst_mem
      unfold checkSingleFoldingStep at h_fst_mem
      erw [simulateQ_bind] at h_fst_mem
      erw [support_bind] at h_fst_mem
      dsimp only [OptionT.run] at h_fst_mem
      simp only [Set.mem_iUnion, exists_prop] at h_fst_mem
      rcases h_fst_mem with ⟨fiber_vec_opt, h_fiber_vec_opt_mem_support, h_c_k_mem_output⟩
      have h_probFailure_queryFiberPoints_eq_zero := probFailure_simulateQ_queryFiberPoints_eq_zero
          (𝔽q := 𝔽q) (β := β) (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (so := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages) (k := k) (v := v)
      have h_probOutput_none_queryFiberPoints_eq_zero :=
        (add_eq_zero.mp ((OptionT.probFailure_eq _).symm.trans
          h_probFailure_queryFiberPoints_eq_zero)).2
      have h_fiber_vec_opt_mem_support_run :
          fiber_vec_opt ∈
            support (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
              (queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((List.finRange (ℓ / ϑ)).get k)
                v)) := by
        exact h_fiber_vec_opt_mem_support
      have h_fiber_vec_opt_eq_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero
        (x := fiber_vec_opt) (hx := h_fiber_vec_opt_mem_support_run)
        (hnone := h_probOutput_none_queryFiberPoints_eq_zero)
      rcases h_fiber_vec_opt_eq_some with ⟨fiber_vec, h_fiber_vec_opt_eq_some⟩
      rw [h_fiber_vec_opt_eq_some] at h_fiber_vec_opt_mem_support_run h_c_k_mem_output
      have h_fiber_val := mem_support_queryFiberPoints 𝔽q β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := ⟨k, h_k⟩) (v := v)
          (f_i_on_fiber := fiber_vec) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
            (witIn := ()) (challenges := tr.challenges)
        (h_fiber_mem := by
          dsimp only [queryPhaseLogicStep]
          have h_transcript : (FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (tr.challenges ⟨0, rfl⟩)).messages
              = tr.messages := by
            -- funext j
            simp only [MessageIdx, Fin.isValue, FullTranscript.mk1_eq_snoc]
            unfold FullTranscript.messages Transcript.concat
            funext x
            obtain ⟨i, hi⟩ := x; fin_cases i; simp at hi
          rw [h_transcript]
          have h_k_fin_eq : (List.finRange (ℓ / ϑ)).get k = ⟨k, h_k⟩ := by
            apply Fin.eq_of_val_eq
            simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast]
          have h_mem := h_fiber_vec_opt_mem_support_run
          simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta] at h_mem ⊢
          exact h_mem
        )
      simp only at h_fiber_val
      have h_fiber_val_eq : fiber_vec.get = fun (fiberIndex : Fin (2 ^ ϑ)) => oStmtIn ⟨k.val, by
        simp only [toOutCodewordsCount_last]; omega⟩
        (getFiberPoint 𝔽q β ⟨↑k, h_k⟩ v fiberIndex) := by
        funext fiberIndex
        exact h_fiber_val fiberIndex
      simp only [h_fiber_val] at h_c_k_mem_output
      simp only [h_k_succ_sub_1_lt, h_k_succ_gt_0, ↓reduceDIte]
      -- ⊢ logical_checkSingleFoldingStep 𝔽q β oStmtIn ⟨↑k.succ - 1, ⋯⟩ v stmtIn
      dsimp only [logical_checkSingleFoldingStep]
      by_cases h_k_gt_0 : k.val > 0
      · have h_gt : (k.succ.val - 1) * ϑ > 0 := by
          have hk' : k.succ.val - 1 > 0 := by
            rw [Fin.val_succ, add_tsub_cancel_right]
            exact h_k_gt_0
          exact Nat.mul_pos hk' h_ϑ_pos
        simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast,
          gt_iff_lt, h_k_gt_0, mul_pos_iff_of_pos_left, h_ϑ_pos, ↓reduceDIte, Message, guard_eq,
          Fin.val_last, bind_pure_comp, OptionT.simulateQ_map] at h_c_k_mem_output
        erw [simulateQ_ite] at h_c_k_mem_output
        set V_check := (c_cur = oStmtIn ⟨k, by
          simp only [toOutCodewordsCount_last]; omega⟩ (
            (getFiberPoint 𝔽q β ⟨↑k, h_k⟩ v (extractMiddleFinMask 𝔽q β v ⟨k.val * ϑ, by
              have h := oracle_index_le_ℓ (i := Fin.last ℓ)
                (j := ⟨k, by
                  rw [toOutCodewordsCount_last]
                  exact h_k⟩)
              simp only at h; omega⟩ ϑ))
          )) with h_V_check_def
        have h_V_check_passed : V_check := by
          by_contra h_V_check_false
          rw [h_V_check_def] at h_V_check_false
          simp only [h_V_check_false, ↓reduceIte, OptionT.simulateQ_failure, OptionT.map_failure,
            OptionT.support_failure_run, Set.mem_singleton_iff, reduceCtorEq] at h_c_k_mem_output
        rw [h_V_check_def] at h_V_check_passed
        simp only [h_V_check_passed, ↓reduceIte] at h_c_k_mem_output
        erw [simulateQ_pure, _root_.map_pure] at h_c_k_mem_output
        simp only [support_pure, Set.mem_singleton_iff,
          support_pure,
          Option.some.injEq] at h_c_k_mem_output
        -- dsimp only [Functor.map] at h_c_k_mem_output
        have h_k_cast_gt_0 : 0 < k.castSucc := by
          change 0 < k.val
          exact h_k_gt_0
        simp only [gt_iff_lt, h_k_cast_gt_0, ↓reduceDIte, Fin.val_last,
          Option.some.injEq] at h_rel_k
        simp only [h_gt, ↓reduceDIte]
        simp only [Fin.val_succ, add_tsub_cancel_right]
        -- Goal: LHS = RHS. We have h_c_k_mem_output.1 : b = (RHS as oStmtIn ... getFiberPoint ...).
        conv_rhs => dsimp only [logical_queryFiberPoints];
        dsimp only [logical_queryFiberPoints]
        -- ⊢ logical_computeFoldedValue 𝔽q β ⟨↑k - 1, ⋯⟩ v stmtIn (logical_queryFiberPoints 𝔽q β
          -- oStmtIn ⟨↑k - 1, ⋯⟩ v) = oStmtIn ⟨↑k, ⋯⟩ (getFiberPoint 𝔽q β ⟨↑k, ⋯⟩ v
            -- (extractMiddleFinMask 𝔽q β v ⟨↑k * ϑ, ⋯⟩ ϑ))
        dsimp only [logical_computeFoldedValue, logical_queryFiberPoints]
        constructor
        · -- V check in the current iteration passes
          rw [←h_V_check_passed]
          -- rw previous computation of c_cur (in previous iteration)
          simp only [Fin.val_last, h_rel_k.2.symm]
          rfl
        · -- prove equality relation for the output of the current iteration (i.e. c_next)
          simp only [ForInStep.state]
          rw [h_c_k_mem_output] at h_res_step1_eq
          rw [h_res_step1_eq.symm]
          dsimp only [ForInStep.state]
          rw [h_fiber_val_eq]
          simp only [Nat.add_one_sub_one, Fin.val_last]
          have h_k_fin_eq : (List.finRange (ℓ / ϑ)).get k = ⟨k, by omega⟩ := by
            apply Fin.eq_of_val_eq;
            simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast]
          let destIdx : Fin r := ⟨k.val * ϑ + ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            have h_le : k.val * ϑ + ϑ ≤ ℓ := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
                (j := ⟨k.val, by
                  rw [toOutCodewordsCount_last]
                  exact h_k⟩)
            exact h_le
          ⟩
          conv_lhs => erw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
            dsimp only [destIdx]; apply Fin.ext; simp only [add_tsub_cancel_right])]
          conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
            simp only [List.getElem_finRange, Fin.eta, Fin.val_cast]; dsimp only [destIdx])]
          congr 1; congr 1;
          -- only challenges equality left
          simp only [Nat.add_one_sub_one, cast_eq]
          dsimp only [getChallengeSuffix]
          apply extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (h_idx_eq := by
              simp only [List.getElem_finRange, Fin.eta, Fin.val_cast]) (h_le := by
              have h_main : k.val * ϑ + ϑ ≤ ℓ := by
                exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
                  (j := ⟨k.val, by
                    rw [toOutCodewordsCount_last]
                    exact h_k⟩)
              have h_main' := h_main
              change k.val * ϑ + ϑ ≤ ℓ at h_main' ⊢
              exact h_main'
            ) (h_le' := by
            have h_main : k.val * ϑ + ϑ ≤ ℓ := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
                (j := ⟨k.val, by
                  rw [toOutCodewordsCount_last]
                  exact h_k⟩)
            simp only [List.getElem_finRange, Fin.eta, Fin.val_cast] at h_main ⊢
            exact h_main
          )
      · have h_ne_gt : ¬ ((k.succ.val - 1) * ϑ > 0) := by
          intro h_gt
          have h_mul_pos : k.val * ϑ > 0 := by
            have h_gt' := h_gt
            simp only [Fin.val_succ, add_tsub_cancel_right] at h_gt'
            exact h_gt'
          have hk_pos : k.val > 0 := by
            exact Nat.pos_of_mul_pos_right h_mul_pos
          exact h_k_gt_0 hk_pos
        simp only [h_ne_gt, ↓reduceDIte, true_and]
        simp only [Fin.val_succ, add_tsub_cancel_right, Nat.add_one_sub_one, Fin.val_last,
          Option.some.injEq]
        -- ⊢ single_point_localized_fold_matrix_form 𝔽q β ⟨(↑k.succ - 1) * ϑ, ⋯⟩ ϑ ⋯ ⋯
        --     (fun j ↦ stmtIn.challenges ⟨(↑k.succ - 1) * ϑ + ↑j, ⋯⟩)
          -- (getChallengeSuffix 𝔽q β ⟨↑k.succ - 1, ⋯⟩ v)
        --     (logical_queryFiberPoints 𝔽q β oStmtIn ⟨↑k.succ - 1, ⋯⟩ v) =
        --   res_step.1.state
        simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast,
          gt_iff_lt, CanonicallyOrderedAdd.mul_pos, h_k_gt_0, false_and, ↓reduceDIte, Message,
          Fin.val_last] at h_c_k_mem_output
        erw [simulateQ_pure, support_pure] at h_c_k_mem_output
        simp only [Set.mem_singleton_iff, Option.some.injEq] at h_c_k_mem_output
        rw [h_c_k_mem_output] at h_res_step1_eq
        rw [h_res_step1_eq.symm]
        dsimp only [ForInStep.state]
        dsimp only [logical_queryFiberPoints]
        rw [h_fiber_val_eq]
        have h_k_fin_eq : (List.finRange (ℓ / ϑ)).get k = ⟨k, by omega⟩ := by
          apply Fin.eq_of_val_eq;
          simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast]
        let destIdx : Fin r := ⟨k.val * ϑ + ϑ, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          have h_le : k.val * ϑ + ϑ ≤ ℓ := by
            exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
              (j := ⟨k.val, by
                rw [toOutCodewordsCount_last]
                exact h_k⟩)
          exact h_le
        ⟩
        conv_lhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
          apply Fin.eq_of_val_eq;
          simp only; dsimp only [destIdx])]
        conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
          simp only [List.getElem_finRange, Fin.eta, Fin.val_cast]; dsimp only [destIdx])]
        congr 1;
        -- only challenges equality left
        simp only [cast_eq]
        dsimp only [getChallengeSuffix]
        apply extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h_idx_eq := by
            simp only [List.getElem_finRange, Fin.eta, Fin.val_cast]) (h_le := by
            have h_main : k.val * ϑ + ϑ ≤ ℓ := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
                (j := ⟨k.val, by
                  rw [toOutCodewordsCount_last]
                  exact h_k⟩)
            change k.val * ϑ + ϑ ≤ ℓ
            exact h_main
          ) (h_le' := by
            have h_main : k.val * ϑ + ϑ ≤ ℓ := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
                (j := ⟨k.val, by
                  rw [toOutCodewordsCount_last]
                  exact h_k⟩)
            simp only [List.getElem_finRange, Fin.eta, Fin.val_cast] at h_main ⊢
            exact h_main
          )
    )
    (h_yield := by
      intro k c_cur s_curr res_step h_res_step_mem
      -- erw [OptionT.support_run] at h_res_step_mem
      erw [simulateQ_bind] at h_res_step_mem
      erw [simulateQ_bind, support_bind] at h_res_step_mem
      dsimp only [OptionT.run] at h_res_step_mem
      simp only [MessageIdx, Fin.isValue, Message,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_res_step_mem
      rcases h_res_step_mem with
        ⟨c_next_opt, output_state_next, _h_mem_support_cur_folding_step, h_res_step_mem_yield⟩
      cases h_c : c_next_opt with
      | none =>
        have h_res_step1_mem :
            some res_step.1 ∈ support (m := OracleComp []ₒ) (α := Option (ForInStep L))
              (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                (pure (none : Option (ForInStep L)))) := by
          have h_proj_mem :
              some res_step.1 ∈ Prod.fst <$> support (m := ProbComp)
                (α := Option (ForInStep L) × σ)
                  ((simulateQ impl
                    (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                      (pure (none : Option (ForInStep L))))) output_state_next) := by
            refine ⟨(some res_step.1, res_step.2), ?_, rfl⟩
            have h_mem := h_res_step_mem_yield
            simp only [MessageIdx, simulateQ_pure, h_c] at h_mem ⊢
            exact h_mem
          have h_proj_eq := support_run_simulateQ_run_fst_eq (impl := impl)
            (oa := simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
              (pure (none : Option (ForInStep L))))
            (s := output_state_next)
            (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
          rw [h_proj_eq] at h_proj_mem
          exact h_proj_mem
        simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at h_res_step1_mem
        cases h_res_step1_mem
      | some next =>
        have h_res_step1_mem :
            some res_step.1 ∈ support (m := OracleComp []ₒ) (α := Option (ForInStep L))
              (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                (pure (some (ForInStep.yield next)))) := by
          have h_proj_mem :
              some res_step.1 ∈ Prod.fst <$> support (m := ProbComp)
                (α := Option (ForInStep L) × σ)
                  ((simulateQ impl
                    (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                      (pure (some (ForInStep.yield next))))) output_state_next) := by
            refine ⟨(some res_step.1, res_step.2), ?_, rfl⟩
            have h_mem := h_res_step_mem_yield
            simp only [h_c] at h_mem ⊢
            exact h_mem
          have h_proj_eq := support_run_simulateQ_run_fst_eq (impl := impl)
            (oa := simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
              (pure (some (ForInStep.yield next))))
            (s := output_state_next)
            (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
          rw [h_proj_eq] at h_proj_mem
          exact h_proj_mem
        simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at h_res_step1_mem
        injection h_res_step1_mem with h_yield
        exact ⟨next, h_yield⟩
    )
  -- extract the final guard relation from h_c_last_mem
  set v_challenge := (FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩
      with h_v_challenge
  intro (k : Fin (ℓ / ϑ + 1))
  dsimp only [logical_stepCondition]
  by_cases h_k_lt : ↑k < ℓ / ϑ
  · simp only [h_k_lt, ↓reduceDIte]
    have h_pred_lt : k.val + 1 - 1 < ℓ / ϑ := by omega
    have res := h_inductive_relations.2
    -- 1. Unpack the existence proof
    rcases res with ⟨bs, ss, h_init, h_s_init, h_final_b, h_final_s, h_steps, h_rel_all⟩
    -- 2. Specialize the relation for the 'input' to the k-th iteration
    -- Since k : Fin (ℓ / ϑ), it can be cast into Fin (ℓ / ϑ + 1)
    have h_rel_for_k_th_level_guard := h_rel_all ⟨k + 1, by simp only [List.length_finRange]; omega⟩
    dsimp only [Rel', checkSingleRepetition_foldRel] at h_rel_for_k_th_level_guard
    have h_res := h_rel_for_k_th_level_guard
    simp only [logical_stepCondition, h_pred_lt, ↓reduceDIte, gt_iff_lt, Fin.val_last,
      dite_else_true] at h_res
    -- rw [h_v] at h_res
    exact h_res.1
  · simp only [h_k_lt, ↓reduceDIte]
    --   ⊢ logical_computeFoldedValue 𝔽q β ⟨ℓ / ϑ - 1, ⋯⟩ v stmtIn
      -- (logical_queryFiberPoints 𝔽q β oStmtIn ⟨ℓ / ϑ - 1, ⋯⟩ v) = stmtIn.final_constant
    have h_last_guard_relation := h_inductive_relations.1.2
    dsimp only [Rel', Rel, checkSingleRepetition_foldRel] at h_last_guard_relation
    simp only [List.length_finRange, gt_iff_lt, Fin.val_last,
      dite_else_true] at h_last_guard_relation
    have h_lt : 0 < (⟨ℓ/ϑ, by simp only [List.length_finRange, lt_add_iff_pos_right,
      zero_lt_one]⟩ : Fin ((List.finRange (ℓ / ϑ)).length + 1)) := by
      change (0 : ℕ) < (ℓ / ϑ)
      exact h_0_lt
    dsimp only [logical_computeFoldedValue]
    simp only [h_lt, forall_true_left] at h_last_guard_relation
    obtain ⟨rfl⟩ := h_c_last_eq_some
    simp only [Option.some.injEq] at h_last_guard_relation
    simp only [MessageIdx, h_last_guard_relation.symm, Message] at h_mem_final_guard_support
    erw [simulateQ_ite, simulateQ_ite, simulateQ_pure, simulateQ_pure] at h_mem_final_guard_support
    have h_dest_le_final : (ℓ / ϑ - 1) * ϑ + ϑ ≤ ℓ := by
      have h_dest_eq_final : (ℓ / ϑ - 1) * ϑ + ϑ = ℓ := by
        calc
          (ℓ / ϑ - 1) * ϑ + ϑ = ((ℓ / ϑ - 1) + 1) * ϑ := by
            rw [Nat.add_mul, Nat.one_mul]
          _ = (ℓ / ϑ) * ϑ := by
            rw [Nat.sub_add_cancel (Nat.succ_le_of_lt h_0_lt)]
          _ = ℓ := h_ℓ_div_mul_eq_ℓ
      exact le_of_eq h_dest_eq_final
    let destIdx : Fin r := ⟨(ℓ / ϑ - 1) * ϑ + ϑ, by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      exact h_dest_le_final
    ⟩
    set fiber_vec := logical_queryFiberPoints 𝔽q β oStmtIn ⟨ℓ / ϑ - 1, by omega⟩ v
      with h_fiber_vec_def
    set single_point_localized_fold_matrix_form_val :=
      single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        _ _ _ _ _ _ _ with h_single_point_localized_fold_matrix_form_val_def
    conv at h_mem_final_guard_support =>
      rw [support_StateT_ite_apply]
      erw [support_pure, support_pure]
      enter [1]
      rw [h_last_guard_relation]
    have h_final_check_passed : c_last_val = stmtIn.final_constant := by
      by_contra h_neq
      simp only [h_neq, ↓reduceIte, Set.mem_singleton_iff,
        Prod.mk.injEq] at h_mem_final_guard_support
      -- h_mem_final_guard_support :
      -- output_final_guard = none ∧ output_state_final_guard = output_state_inner_forIn
      simp only [h_mem_final_guard_support, simulateQ_pure] at h_final_yield_support_mem
      erw [support_pure] at h_final_yield_support_mem
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq,
        false_and] at h_final_yield_support_mem
    simp only [h_final_check_passed, ↓reduceIte, Set.mem_singleton_iff,
      Prod.mk.injEq] at h_mem_final_guard_support -- pure equalities now
    -- h_mem_final_guard_support :
    -- output_final_guard = some () ∧ output_state_final_guard = output_state_inner_forIn
    rw [←h_final_check_passed]
    rw [←h_last_guard_relation]
    dsimp only [single_point_localized_fold_matrix_form_val]
    conv_lhs =>
      rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx)
        (h_destIdx_eq_destIdx' := by dsimp only [destIdx]) (fiber_eval_mapping := fiber_vec)]
    conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
        simp only [List.length_finRange]; dsimp only [destIdx]) (fiber_eval_mapping := fiber_vec)]
    congr 1
    -- only challenges equality left
    simp only [cast_eq]
    dsimp only [getChallengeSuffix]
    apply extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_idx_eq := by
        simp only [List.length_finRange]) (h_le := by
        exact h_dest_le_final) (h_le' := by
        have h_dest_le_final' := h_dest_le_final
        simp only [List.length_finRange] at h_dest_le_final' ⊢
        exact h_dest_le_final')

/-! Main lemma connecting verifier support to logical proximity checks.
    This is the key lemma used in toFun_full of queryKnowledgeStateFunction.
    The left side matches the hypothesis from StateT.run characterization:
      (stmtOut, oStmtOut) ∈ support ((fun x ↦ x.1) <$> simulateQ impl (Verifier.run ...) s)
    The right side gives us:
      1. stmtOut = true
      2. oStmtOut is the verifier's materialized output oracle family
      3. ∀ rep, logical_checkSingleRepetition ... (the proximity checks spec)
-/
omit [CharP L 2] [SampleableType L] in
set_option backward.isDefEq.respectTransparency false in
lemma logical_consistency_checks_passed_of_mem_support_V_run {σ : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmtIn : FinalSumcheckStatementOut)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (s : σ) (stmtOut : Bool) (oStmtOut : Empty → Unit)
    (h_mem_V_run_support :
      (stmtOut, oStmtOut) ∈
        support (OptionT.mk (Prod.fst <$> ((simulateQ.{0, 0, 0} impl
            (Verifier.run (stmtIn, oStmtIn) tr
              (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
                (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))) :
              StateT σ ProbComp (Option (Bool × (Empty → Unit)))).run s))) :
    (stmtOut = true ∧
      oStmtOut = OracleVerifier.materializeOutput
        (Oₛₒ := fun i : Empty => nomatch i)
        (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        tr.challenges oStmtIn tr.messages ∧
     ∀ (rep : Fin γ_repetitions),
       logical_checkSingleRepetition 𝔽q β oStmtIn
         (tr.challenges ⟨0, rfl⟩ rep) stmtIn stmtIn.final_constant) := by
  -- dsimp only [OptionT.mk] at h_mem_V_run_support
  conv at h_mem_V_run_support =>
    dsimp only [Verifier.run, OracleVerifier.toVerifier, queryOracleVerifier]
    dsimp only [queryPhaseLogicStep]
    -- Simplify the `(fun x ↦ x.1) <$> ...` part
    -- Group the last two `bind`
    simp only [OracleProofVerifier.ofVerify, OptionT.run_bind, OptionT.run_pure,
      OptionT.run_map, OptionT.run_mk, bind_assoc, pure_bind]
    -- Distribute `simulateQ` over the `bind`
    erw [simulateQ_bind]
    -- Resolve the constant mappings
    erw [OptionT.simulateQ_forIn]
    dsimp only [OptionT.mk]
    erw [simulateQ_map, simulateQ_bind]
    erw [OptionT.simulateQ_forIn_stateful_comp]
  conv at h_mem_V_run_support =>
    -- rw [simulateQ_forIn_stateful_comp (impl := impl)
      -- (l := List.finRange γ_repetitions) (init := PUnit.unit)]
    rw [OptionT.mem_support_iff]
    erw [support_map]
    erw [Set.mem_image]
    erw [support_bind]
    enter [1, x]
    simp only [MessageIdx, Message, Fin.isValue, FullTranscript.mk1_eq_snoc, bind_pure_comp,
      OptionT.simulateQ_map, id_map', Set.mem_iUnion,
      exists_prop, Prod.exists]
  obtain ⟨x, hx_mem, hx_1_eq_stmtOut_oStmtOut⟩ := h_mem_V_run_support
  -- Note: hx_mem now refers to the exact simulateQ (forIn ...) block
  -- after the conv with OptionT.simulateQ_forIn
  -- The structure is: hx_mem : ∃ a b, (a, b) ∈ (simulateQ impl (forIn ...)).support
  -- where the forIn is exactly: forIn (List.finRange γ_repetitions) PUnit.unit (fun a b => ...)
  let forIn_body : Fin γ_repetitions → PUnit.{1} →
      StateT σ ProbComp (Option (ForInStep PUnit.{1})) := fun (a : Fin γ_repetitions)
      (b : PUnit.{1}) =>
    simulateQ impl (
      (((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$>
        ((simulateQ.{0, 0, 0} (impl := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
          ((checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ a)
            stmtIn stmtIn.final_constant) :
              OptionT (OracleComp
                ([]ₒ + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ +
                  [(pSpecQuery 𝔽q β γ_repetitions).Message]ₒ))) Unit).run) :
            OracleComp []ₒ (Option Unit))) :
        OptionT (OracleComp []ₒ) (ForInStep PUnit.{1}))
    )
  let forIn_block : OptionT (StateT σ ProbComp) PUnit.{1} :=
    forIn (xs := List.finRange γ_repetitions) (b := PUnit.unit.{1}) (f := forIn_body)
  -- let simulateQ_forIn_block := simulateQ impl forIn_block
  -- Verify that hx_mem is about the exact simulateQ (forIn ...) block
  conv at hx_mem =>
    enter [1, x, 1, b, 1, 1, 1, 1]
    -- Unfold the set definitions to expose the structure
    change (forIn_block)
  conv at hx_mem =>
    enter [1, x_1, 1, b, 1]
    change ((x_1, b) ∈ support (((forIn_block >>=
      (fun (u : Option PUnit.{1}) => (_ : StateT σ ProbComp (Option Bool)))) :
        StateT σ ProbComp (Option Bool)).run s))
    rw [OptionT.mem_support_StateT_bind_run (ma := forIn_block) (x := (x_1, b))]
  rcases hx_mem with ⟨y, s', h_y_s'_mem_support_forIn_block, h_x_eq⟩
  -- simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h_x_eq -- TODO
  have h_y_ne_none : y ≠ none := by
    intro h_y_eq_none
    simp only [h_y_eq_none] at h_x_eq
    erw [support_pure] at h_x_eq
    simp only [Set.mem_singleton_iff] at h_x_eq
    rw [Prod.mk_inj] at h_x_eq
    rw [hx_1_eq_stmtOut_oStmtOut] at h_x_eq
    simp only [Option.map_none, reduceCtorEq, false_and] at h_x_eq
  obtain ⟨y_val, h_y_eq⟩ := Option.ne_none_iff_exists.mp h_y_ne_none
  obtain ⟨rfl⟩ := h_y_eq
  erw [support_pure] at h_x_eq
  rw [Set.mem_singleton_iff, Prod.mk_inj] at h_x_eq
  -- **Now we have pure equalities of x.1 and x.2**
  rcases h_y_s'_mem_support_forIn_block with ⟨z, s'', h_forIn_run_mem, h_pure⟩
  have h_z_ne_none : z ≠ none := by
    intro h_z_eq_none
    simp only [h_z_eq_none, Option.elim_none, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at h_pure
  obtain ⟨z_val, h_z_eq⟩ := Option.ne_none_iff_exists.mp h_z_ne_none
  obtain ⟨rfl⟩ := h_z_eq
  erw [simulateQ_pure, support_pure] at h_pure
  simp only [Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at h_pure
  -- **h_pure : y_val = true ∧ s' = s''**
  dsimp only [forIn_block] at h_forIn_run_mem
  -- 1. Apply the extraction lemma
  have h_independent_support_mem_exists := OptionT.exists_path_of_mem_support_forIn_unit.{0}
    (spec := []ₒ) (l := List.finRange γ_repetitions) (f := forIn_body) (s_init := s)
    (s_final := s'') (u := z_val)
    (h_yield := by
      intro rep s_pre res_step h_res_step_mem
      dsimp only [forIn_body] at h_res_step_mem
      set oa : OracleComp []ₒ (Option Unit) :=
       ((simulateQ.{0, 0, 0} (impl := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
          ((checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ rep)
            stmtIn stmtIn.final_constant) :
              OptionT (OracleComp
                ([]ₒ + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ +
                  [(pSpecQuery 𝔽q β γ_repetitions).Message]ₒ))) Unit).run) :
            OracleComp []ₒ (Option Unit))
      have h_fst_mem : some res_step.1 ∈ support ((simulateQ impl
          ((((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$> oa) :
            OptionT (OracleComp []ₒ) (ForInStep PUnit)))).run' s_pre) := by
        rw [StateT.run', support_map]
        exact Set.mem_image_of_mem Prod.fst h_res_step_mem
      have h_run'_supp_eq := support_simulateQ_run'_eq (impl := impl)
        (oa := ((((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$> oa) :
          OptionT (OracleComp []ₒ) (ForInStep PUnit))))
        (s := s_pre)
        (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
      rw [h_run'_supp_eq] at h_fst_mem
      have h_mem : res_step.1 ∈ support
          ((fun (_ : Unit) => ForInStep.yield PUnit.unit) <$> OptionT.mk oa) :=
        (OptionT.mem_support_iff _ _).mpr h_fst_mem
      rw [support_map, Set.mem_image] at h_mem
      obtain ⟨u, _h_u_mem, h_eq⟩ := h_mem
      exact h_eq.symm
    )
    (h_mem := h_forIn_run_mem)
  set γ_challenges : Fin γ_repetitions →
    sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ := tr.challenges ⟨0, rfl⟩ with h_γ_challenges_def
  rw [h_pure.1] at h_x_eq
  rw [h_x_eq.1] at hx_1_eq_stmtOut_oStmtOut
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Bool.true_eq]
    at hx_1_eq_stmtOut_oStmtOut
  constructor
  · exact hx_1_eq_stmtOut_oStmtOut.1
  · constructor
    · exact hx_1_eq_stmtOut_oStmtOut.2.symm
    · -- 2. Quantify over an arbitrary repetition
      intro rep
      -- ⊢ logical_checkSingleRepetition 𝔽q β oStmtIn (γ_challenges rep)
        -- stmtIn stmtIn.final_constant
      have h_rep_th_support_mem := h_independent_support_mem_exists rep
        (by simp only [List.mem_finRange])
      rcases h_rep_th_support_mem with ⟨state_pre_repetition, state_post_repetition,
        h_support_rep_ith_iteration⟩
      exact logical_checkSingleRepetition_of_mem_support_forIn_body 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (γ_repetitions := γ_repetitions) (σ := σ) (impl := impl)
        (oStmtIn := oStmtIn) (tr := tr) (stmtIn := stmtIn) (rep := rep)
        (state_pre := state_pre_repetition) (forIn_body := forIn_body) (h_forIn_body_eq := rfl)
        (h_mem := by
          use (ForInStep.yield PUnit.unit, state_post_repetition)
          exact h_support_rep_ith_iteration
        )

open scoped NNReal

/-- The round-by-round extractor for the query phase.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def queryRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
      × (∀ j, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j))
    (WitIn := Unit)
    Unit
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ _ => ()

def queryKStateProp (m : Fin (1 + 1))
    (tr : ProtocolSpec.Transcript m
      (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (witMid : Unit)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- Same as last KState of finalSumcheck reduction (= relIn)
    Binius.BinaryBasefold.finalSumcheckRelOutProp 𝔽q β
      (input := ⟨⟨stmtIn, oStmtIn⟩, witMid⟩)
  | ⟨1, _⟩ => -- After V sends γ challenges: proximity tests must pass
    let γ_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ :=
      tr.challenges ⟨0, rfl⟩
    let fold_challenges := stmtIn.challenges
    logical_proximityChecksSpec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (γ_repetitions := γ_repetitions) (γ_challenges := γ_challenges)
      (final_constant := stmtIn.final_constant) (oStmt := oStmtIn) (stmt := stmtIn)

set_option backward.isDefEq.respectTransparency false in
/-- The knowledge state function for the query phase -/
noncomputable def queryKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).KnowledgeStateFunction init impl
  (Oₛₒ := fun i : Empty => nomatch i)
  (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
  (relOut := acceptRejectOracleRel)
  (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ)
    γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    queryKStateProp 𝔽q β (ϑ:=ϑ) (γ_repetitions:=γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (m:=m) (tr:=tr) (stmtIn:=stmtIn) (witMid:=witMid) (oStmtIn:=oStmtIn)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by rfl
  toFun_next := fun m hDir ⟨stmtMid, oStmtMid⟩ tr msg witMid => by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_fin_one,
      Direction.not_V_to_P_eq_P_to_V] at hDir
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    -- h_relOut: ∃ stmtOut oStmtOut, verifier outputs (stmtOut, oStmtOut) with prob > 0
    --   and ((stmtOut, oStmtOut), witOut) ∈ foldStepRelOut
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          support (do
              let s ← init
              Prod.fst <$>
                (simulateQ impl
                  (Verifier.run (stmtIn, oStmtIn) tr
                    (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
                      (pSpec := pSpecQuery 𝔽q β γ_repetitions)
                      (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
                        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))).run s) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
                  (pSpec := pSpecQuery 𝔽q β γ_repetitions)
                  (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support_with_s⟩
    -- Apply the main lemma connecting verifier support to logical proximity checks
    have h_res := logical_consistency_checks_passed_of_mem_support_V_run
      (impl := impl) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (tr := tr)
      (s := s) (stmtOut := stmtOut) (oStmtOut := oStmtOut)
      (h_mem_V_run_support := by
        rw [OptionT.mem_support_iff]
        dsimp only [OptionT.mk, OptionT.run]
        exact h_output_mem_V_run_support_with_s
      )
    -- The lemma gives us:
    exact h_res.2.2

omit [CharP L 2] [SampleableType L] in
/-- **Single Repetition Proximity Check Bound (Proposition 4.24)**

For a single repetition of the proximity check, the probability that a non-compliant
oracle (not close to RS codeword) passes the fold consistency check is bounded by:
  `(1/2) + 1/(2 * 2^𝓡)`

**Preconditions (from Proposition 4.24 in the archived DP24 PDF):**
- `h_not_oracleFoldingConsistent`: At least one oracle is non-compliant
- `h_no_bad_event`: No bad folding events occurred (Definition 4.20)

This is the fundamental proximity testing bound used in the soundness proof. -/
theorem prop_4_24_singleRepetition_proximityCheck_bound
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_oracleFoldingConsistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad_event : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- Delegates to Soundness Prop 4.24 (Lemma 4.26 supplies the query-rejection property).
  have h_res :=
    (Binius.BinaryBasefold.prop_4_24_singleRepetition_proximityCheck_bound
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (h_not_consistent := h_not_oracleFoldingConsistent)
      (h_no_bad := h_no_bad_event)
      (h_le := by
        apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)))
  dsimp only [queryRbrKnowledgeError_singleRepetition]
  simp only [one_div, mul_inv_rev, ENNReal.coe_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat, ENNReal.coe_mul, pow_eq_zero_iff',
    false_and, ENNReal.coe_pow, ge_iff_le]
  simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv,
    ENNReal.coe_ofNat, ENNReal.coe_one] at h_res
  rw [ENNReal.mul_inv (ha := by
    left; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
    (hb := by
      left; simp only [ne_eq, ENNReal.ofNat_ne_top, not_false_eq_true]) , mul_comm] at h_res
  exact h_res

omit [CharP L 2] [SampleableType L] in
theorem singleRepetition_proximityCheck_bound
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_oracleFoldingConsistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad_event : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- This is Proposition 4.24 from the archived DP24 PDF specialized to a single repetition.
  exact
    prop_4_24_singleRepetition_proximityCheck_bound (𝔽q := 𝔽q) (β := β)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (h_not_oracleFoldingConsistent := h_not_oracleFoldingConsistent)
      (h_no_bad_event := h_no_bad_event)

open Classical in
/-! Round-by-round knowledge soundness for the oracle verifier (query phase).

**Proof Strategy (RBR Extraction Failure Event):**

The RBR extraction failure event is: `¬ KState(0) ∧ KState(1)`, i.e.,
  - `¬ finalSumcheckRelOutProp` (KState 0 = FALSE), AND
  - `proximityChecksSpec` (KState 1 = TRUE)

By De Morgan's law:
  `¬ finalSumcheckRelOutProp = ¬ (oracleFoldingConsistency ∨ badEvent)`
                             `= ¬ oracleFoldingConsistency ∧ ¬ badEvent`

This means:
  - `¬ oracleFoldingConsistency`: Some oracle is NOT compliant (not close to correct folding)
  - `¬ badEvent`: No bad events detected

**Proposition 4.24 (archived DP24 - assuming no bad events):**
If any of the adversary's oracles is not compliant (not close to RS codeword),
then the verifier accepts with at most negligible probability:
  `Pr[V accepts] ≤ ((1/2) + 1/(2 * 2^𝓡))^γ_repetitions`

This is exactly `queryRbrKnowledgeError`. -/
open scoped OracleSpec.PrimitiveQuery in
omit [CharP L 2] [SampleableType L] in
/-- Per-challenge extraction-failure ("doom") bound for the FRI query round: the honest-verifier
extraction event holds with probability at most `queryRbrKnowledgeError`.  Factored out of
`queryOracleVerifier_rbrKnowledgeSoundness` so the reducer call is a one-liner (mirrors
`foldStep_/iteratedSumcheck_/batching_doom_escape_probability_bound`). -/
lemma query_doom_escape_probability_bound {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmtIn_oStmtIn : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) ×
      (∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j))
    (transcript : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Transcript
      (⟨0, rfl⟩ : (pSpecQuery 𝔽q β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx).1.castSucc) :
    Pr_{ let y ← $ᵖ (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      rbrExtractionFailureEvent
        (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
        (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        ⟨0, rfl⟩ stmtIn_oStmtIn transcript y ] ≤
      queryRbrKnowledgeError 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, rfl⟩ := by
  classical
  change Pr_{ let y ← $ᵖ (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
    rbrExtractionFailureEvent
      (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
      (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      ⟨0, rfl⟩ stmtIn_oStmtIn transcript y ] ≤
    ↑(queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) ^ γ_repetitions)
  have hP_eq : ∀ y : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0,
      rbrExtractionFailureEvent
        (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
        (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        ⟨0, rfl⟩ stmtIn_oStmtIn transcript y ↔
        (¬ finalSumcheckRelOutProp 𝔽q β
            (input := ⟨⟨stmtIn_oStmtIn.1, stmtIn_oStmtIn.2⟩, ()⟩) ∧
          ∀ rep : Fin γ_repetitions,
            logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              stmtIn_oStmtIn.2 (y rep) stmtIn_oStmtIn.1 stmtIn_oStmtIn.1.final_constant) := by
    intro y
    simp only [rbrExtractionFailureEvent, queryRbrExtractor, queryKnowledgeStateFunction,
      queryKStateProp, logical_proximityChecksSpec, Fin.isValue,
      Fin.castSucc_zero, Fin.succ_zero_eq_one]
    simp only [FullTranscript.challenges, Transcript.concat, Fin.isValue]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨(), h⟩
  rw [Pr_congr (h := hP_eq)]
  -- Bound `A ∧ (∀ rep, B (y rep))` by dropping `A` and applying the γ-fold product bound.
  by_cases hA : finalSumcheckRelOutProp 𝔽q β
      (input := ⟨⟨stmtIn_oStmtIn.1, stmtIn_oStmtIn.2⟩, ()⟩)
  · -- `A` false: the extraction-failure event never holds, so the probability is `0`.
    have h_false : ∀ y : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0,
        (¬ finalSumcheckRelOutProp 𝔽q β
              (input := ⟨⟨stmtIn_oStmtIn.1, stmtIn_oStmtIn.2⟩, ()⟩) ∧
            ∀ rep : Fin γ_repetitions,
              logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                stmtIn_oStmtIn.2 (y rep) stmtIn_oStmtIn.1 stmtIn_oStmtIn.1.final_constant)
          ↔ False :=
      fun y => iff_false_intro (fun hy => hy.1 hA)
    rw [Pr_congr (h := h_false)]
    simp only [prob_tsum_form_singleton, ↓reduceIte, mul_zero, tsum_zero, zero_le]
  · -- `¬ A`: the two negated preconditions of Proposition 4.24 hold (De Morgan).
    rw [finalSumcheckRelOutProp, finalSumcheckStepFoldingStateProp, not_or] at hA
    obtain ⟨h_not_consistent, h_no_bad⟩ := hA
    -- Drop the constant conjunct `A` (which holds), reducing to the all-repetitions event.
    calc Pr_{ let y ← $ᵖ (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
            ¬ finalSumcheckRelOutProp 𝔽q β
                (input := ⟨⟨stmtIn_oStmtIn.1, stmtIn_oStmtIn.2⟩, ()⟩) ∧
              ∀ rep : Fin γ_repetitions,
                logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  stmtIn_oStmtIn.2 (y rep) stmtIn_oStmtIn.1 stmtIn_oStmtIn.1.final_constant ]
        ≤ Pr_{ let y ← $ᵖ (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
              ∀ rep : Fin γ_repetitions,
                logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  stmtIn_oStmtIn.2 (y rep) stmtIn_oStmtIn.1 stmtIn_oStmtIn.1.final_constant ] := by
          apply Pr_le_Pr_of_implies
          intro y hy
          exact hy.2
      _ ≤ (queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡)) ^ γ_repetitions := by
          apply prob_pow_bound_of_forall
            (A := sDomain 𝔽q β h_ℓ_add_R_rate 0)
            (n := γ_repetitions)
            (P := fun v => logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              stmtIn_oStmtIn.2 v stmtIn_oStmtIn.1 stmtIn_oStmtIn.1.final_constant)
            (ε := queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡))
          exact singleRepetition_proximityCheck_bound (𝔽q := 𝔽q) (β := β)
            (stmtIn := stmtIn_oStmtIn.1) (oStmtIn := stmtIn_oStmtIn.2)
            (h_not_oracleFoldingConsistent := h_not_consistent)
            (h_no_bad_event := h_no_bad)
      _ = ↑(queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) ^ γ_repetitions) := by
          rw [ENNReal.coe_pow]
omit [CharP L 2] [SampleableType L] in
theorem queryOracleVerifier_rbrKnowledgeSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).rbrKnowledgeSoundness init impl
    (Oₛₒ := fun i : Empty => nomatch i)
    (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := queryRbrKnowledgeError 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  classical
  -- The FRI query round is 1-message verifier-first; reduce r.b.r. knowledge soundness to the
  -- (now-extracted) per-challenge product bound — a one-liner like the other leaves.
  let p := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let : OracleSpec.Fintype [p.Challenge]ₒ :=
    { fintypeB := fun j => inferInstanceAs (Fintype (p.Challenge j.1)) }
  let : OracleSpec.Inhabited [p.Challenge]ₒ :=
    { inhabitedB := fun j => inferInstanceAs (Inhabited (p.Challenge j.1)) }
  let : IsUniformSpec ([]ₒ + [p.Challenge]ₒ) := IsUniformSpec.ofFintypeInhabited _
  exact OracleReduction.rbrKnowledgeSoundness_of_1msg_VtoP_uniformChallenge
    (WitMid := fun _ => Unit)
    (rbrKnowledgeError := queryRbrKnowledgeError 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
    (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (hDir0 := rfl)
    (hbound := fun stmtIn_oStmtIn transcript =>
      query_doom_escape_probability_bound (init := init) (impl := impl)
        (stmtIn_oStmtIn := stmtIn_oStmtIn) (transcript := transcript))

end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase
