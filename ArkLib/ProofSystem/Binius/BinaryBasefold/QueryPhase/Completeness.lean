/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Folding
-- These structural proofs use the protocol module's private support helpers.
import all ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Protocol

/-!
# Binary Basefold query-phase completeness
-/

@[expose] public section

open OracleSpec

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

/-- Relation used in the forIn loop of `checkSingleRepetition`: at index 0 the folded value is 0;
  at index `oraclePositionIdx > 0` it equals `iterated_fold` up to that position with challenges
    from `stmtIn` and suffix from `v`. -/
@[reducible]
def checkSingleRepetition_foldRel
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    Fin ((List.finRange (ℓ / ϑ)).length + 1) → L → Prop :=
  let f₀ := getFirstOracle 𝔽q β oStmtIn
  fun oraclePositionIdx val_folded_point =>
    if hk : oraclePositionIdx.val = 0 then
      val_folded_point = 0  -- Base case: initial value is 0
    else
      have h_toCodewordCount : toOutCodewordsCount ℓ ϑ (Fin.last ℓ) = ℓ / ϑ :=
        toOutCodewordsCount_last ℓ ϑ
      have h_le : oraclePositionIdx ≤ ℓ/ϑ := by
        have h := oraclePositionIdx.isLt
        simp only [List.length_finRange] at h
        exact Nat.le_of_lt_succ h
      have h_mul : (ℓ/ϑ) * ϑ = ℓ := by rw [Nat.div_mul_cancel (hdiv.out)]
      have h_mul_le : oraclePositionIdx * ϑ ≤ ℓ := by
        conv_rhs => rw [←h_mul]
        apply Nat.mul_le_mul_right; exact h_le
      let destIdx : Fin r := ⟨oraclePositionIdx * ϑ, by omega⟩
      let suffix_point_from_v : sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v:=v) (destIdx:=destIdx) (h_destIdx_le:=by omega)
      val_folded_point = iterated_fold
        (i := 0) (steps := oraclePositionIdx * ϑ) (destIdx := destIdx) (h_destIdx := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
        (h_destIdx_le := by
          rw [←h_mul]
          dsimp only [destIdx];
          apply Nat.mul_le_mul_right; exact h_le
        ) (f := f₀)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega)) (y := suffix_point_from_v)

omit [CharP L 2] [SampleableType L] in
/-- Safety of the simulated inner `forIn` loop used by
`checkSingleRepetition_none_not_mem_support`. -/
lemma checkSingleRepetition_inner_forIn_none_not_mem_support
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmtIn, oStmtIn), witIn))
    (rep : Fin γ_repetitions)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges) :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      let v := (FullTranscript.mk1 (challenges ⟨0, by rfl⟩)).challenges ⟨0, by rfl⟩ rep
      let f : Fin (ℓ / ϑ) → L → OracleComp []ₒ (Option (ForInStep L)) :=
        fun (a : Fin (ℓ / ϑ)) (b : L) ↦
          ((ForInStep.yield <$>
            (simulateQ.{0, 0, 0} so
                (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) a b v stmtIn
              ).run
            )) : OptionT (OracleComp []ₒ) (ForInStep L))
      let inner_forIn_block : OptionT (OracleComp []ₒ) L :=
        forIn (List.finRange (ℓ / ϑ)) (0 : L) f
      none ∉ support (inner_forIn_block).run := by
  intro step transcript so v f inner_forIn_block
  dsimp only [inner_forIn_block]
  let Rel : Fin ((List.finRange (ℓ / ϑ)).length + 1) → L → Prop :=
    checkSingleRepetition_foldRel 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)
  -- For this proof, we define a trivial relation since the real invariant
  -- is complex and involves the correctness of folding operations
  -- a. Push liftComp inside the forIn loop (twice, for the two layers)
  --    Goal: simulateQ so (liftComp (liftComp (forIn ...)))
  --    Becomes: simulateQ so (forIn ... (fun x s => liftComp ...))
  -- **Applying indutive relation inference**
  apply none_not_mem_support_forIn_of_relations_simplified (rel := Rel)
    (h_start := by rfl) (h_step := by
    -- Inductive step: any INNER repetition never fails
    intro (k : Fin (List.finRange (ℓ / ϑ)).length) (c_k : L) h_rel_k_c
    -- simp only [List.get_eq_getElem, List.getElem_finRange] at *
    -- Simplify k.succ ≠ 0 (always true)
    have h_succ_ne_zero : k.succ ≠ 0 := Fin.succ_ne_zero k
    constructor
    · -- Part 1: checkSingleFoldingStep is safe (never fails)
      -- where the forInStep.yield has spec
      -- `OracleComp [OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ (ForInStep L)`
      -- [⊥|simulateQ so
      --     ((ForInStep.yield <$> checkSingleFoldingStep 𝔽q β
      --       ((List.finRange (ℓ / ϑ)).get k) c_k v stmtIn).liftComp
      --       ([]ₒ ++ₒ
      --         ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ ++ₒ
      --           [fun i ↦ ![Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)] ↑i]ₒ)))] =
      -- 0
      dsimp only [f]
      -- rw [simulateQ_liftComp]
      rw [map_eq_bind_pure_comp]
      erw [OptionT.none_not_mem_support_map_iff]
      -- ⊢ none ∉ support (simulateQ so (checkSingleFoldingStep 𝔽q β γ_repetitions
      --   ((List.finRange (ℓ / ϑ)).get k) c_k v stmtIn).run).run
      dsimp only [checkSingleFoldingStep]
      erw [simulateQ_bind]
      erw [none_not_mem_support_mk_bind_iff.{0, 0}]
      have h_fiber_safe : none ∉ support (OptionT.mk
          (simulateQ so
            (queryFiberPoints 𝔽q β γ_repetitions ((List.finRange (ℓ / ϑ)).get k) v))).run := by
        apply none_not_mem_support_simulateQ_queryFiberPoints
          (γ_repetitions := γ_repetitions) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝔽q := 𝔽q) (β := β)
          (so := so) (k := k) (v := v)
      -- The guard and pure computation
      intro fiber_vec_opt h_fiber_vec_opt_mem_support
      have h_fiber_vec_eq_some :=
        exists_eq_some_of_mem_support_of_none_not_mem.{0, 0} (x := fiber_vec_opt)
          (hx := h_fiber_vec_opt_mem_support)
          (hnone := h_fiber_safe)
      rcases h_fiber_vec_eq_some with ⟨fiber_vec, rfl⟩
      simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast,
        gt_iff_lt, CanonicallyOrderedAdd.mul_pos, Message, guard_eq, Fin.val_last, bind_pure_comp,
        dite_eq_ite]
      have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
      simp only [h_ϑ_pos, and_true]
      by_cases h_i_pos : k.val > 0
      · -- Case k > 0: guard (c_k = f_i_val)
        let k_idx : Fin (ℓ / ϑ) := ⟨k.val, by
          have h := k.isLt
          simp only [List.length_finRange] at h
          exact h⟩
        have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k_idx)
        have h_k_idx_eq : k_idx = (List.finRange (ℓ / ϑ)).get k := by
          simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta]
          apply Fin.eq_of_val_eq
          simp only [Fin.val_cast]; rfl
        -- 1. Simplify failure probability to just the guard condition
        simp only [h_i_pos, ↓reduceIte, OptionT.simulateQ_map]
        have h_guard_pass :
            c_k = fiber_vec.get
              (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (v := v) (i := ⟨k.val * ϑ, by omega⟩) (steps := ϑ)) := by
          -- ⊢ c_k = f_i_on_fiber.get (extractMiddleFinMask ...)
          -- 1. Construct the correct index type for the lemma
          -- 3. Unfold Rel to get the equality
          unfold Rel checkSingleRepetition_foldRel at h_rel_k_c
          have h_k_castSucc_ne_0 : ¬(k.castSucc.val = 0) := by
            simp only [Fin.val_castSucc]; omega
          rw [dite_eq_right h_k_castSucc_ne_0] at h_rel_k_c
          simp only [Fin.val_castSucc] at h_rel_k_c
          -- simp only [Fin.isValue, List.get_eq_getElem, List.getElem_finRange, Fin.eta,
          --   Fin.val_cast]
          have h_mul_gt_0 : k.val * ϑ > 0 := by
            simp only [gt_iff_lt, CanonicallyOrderedAdd.mul_pos]
            omega
          -- 4. Apply the lemma
          have res := query_phase_consistency_guard_safe 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k_idx) (v := v) (c_k := c_k)
            (f_i_on_fiber := fiber_vec) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
            (witIn := witIn) (h_relIn := h_relIn) (h_c_k_correct := h_rel_k_c)
            (h_k_pos := h_mul_gt_0) (γ_repetitions := γ_repetitions)
            (challenges := challenges) (h_fiber_mem := by
            rw [h_k_idx_eq]
            exact h_fiber_vec_opt_mem_support
          )
          exact res
        simp only [h_guard_pass, ↓reduceIte, OptionT.run_pure, simulateQ_pure]
        exact OptionT.none_not_mem_support_pure _
      · -- Case k = 0: no guard
        simp only [h_i_pos, ↓reduceIte]
        erw [simulateQ_pure]
        exact OptionT.none_not_mem_support_pure _
    · -- Part 2: Results in support satisfy the next relation
      intro s' h_s'_support
      simp only [checkSingleRepetition_foldRel, dite_eq_ite, Fin.val_succ, Rel]
      simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, support_map,
        Set.mem_image, OptionT.mem_support_iff, toPFunctor_emptySpec, OptionT.run,
        f] at h_s'_support
      -- Extract the actual value from ForInStep.yield
      rcases h_s'_support with ⟨x, h_x_support, h_s'_eq⟩
      rw [←h_s'_eq]
      dsimp only [ForInStep.state]
      -- Handle the index casting issue
      let k_idx : Fin (ℓ / ϑ) := ⟨k.val, by
        have h := k.isLt
        simp only [List.length_finRange] at h
        exact h
      ⟩
      -- Apply the preservation lemma
      let res := query_phase_step_preserves_fold 𝔽q β (γ_repetitions := γ_repetitions)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k_idx) (v := v) (c_k := c_k)
        (s' := x) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (h_relIn := h_relIn)
        (challenges := challenges) (h_s'_mem := by
        dsimp only [so] at h_x_support
        dsimp only [pSpecQuery]
        exact h_x_support
      ) (h_c_k_correct_of_k_pos := by
        dsimp only [k_idx]
        dsimp only [Rel, checkSingleRepetition_foldRel] at h_rel_k_c
        simp only [Fin.val_castSucc, dite_eq_ite] at h_rel_k_c
        by_cases hk : k.val > 0
        · simp only [gt_iff_lt, hk, ↓reduceDIte]
          have h_ne_k_pos : ¬ (k.val = 0) := by omega
          simp only [h_ne_k_pos, ↓reduceIte] at h_rel_k_c
          exact h_rel_k_c
        · simp only [gt_iff_lt, hk, ↓reduceDIte]
      )
      exact res
  )

omit [CharP L 2] [SampleableType L] in
/--
Safety and Correctness of `checkSingleRepetition` under Honest Simulation.

This lemma proves that for any repetition `rep`, the check:
1. Never fails (safety).
2. Only returns if the accumulated value equals `final_constant`.
-/
lemma checkSingleRepetition_none_not_mem_support
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    (rep : Fin γ_repetitions)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges) :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      let v := (FullTranscript.mk1 (challenges ⟨0, by rfl⟩)).challenges ⟨0, by rfl⟩ rep
      none ∉ support (OptionT.mk.{0, 0} (simulateQ.{0, 0, 0} so
        (checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v stmtIn stmtIn.final_constant).run)).run := by
  intro step transcript so v
  let f₀ := getFirstOracle 𝔽q β oStmtIn
  let Rel : Fin ((List.finRange (ℓ / ϑ)).length + 1) → L → Prop :=
    checkSingleRepetition_foldRel 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)
  -- 1. Expand definition to expose the `forIn` and `guard`
  dsimp only [checkSingleRepetition]
  -- 2. Distribute simulateQ and liftM over the Bind (>>=)
  --    This splits `simulateQ (Loop >>= Guard)` into `simulateQ Loop >>= simulateQ Guard`
  simp only [bind_pure_comp]
  simp only [Fin.eta]
  -- erw [liftComp_bind]
  erw [simulateQ_bind]
  dsimp only [Function.comp_def]
  -- dsimp only [liftComp]
  simp only [OptionT.simulateQ_forIn.{0}] -- **universe 0 is important** here
  dsimp only [OptionT.mk]
  erw [none_not_mem_support_mk_bind_iff.{0, 0}]
  intro c h_c_support_inner_loop
  -- **if the inner for loop is passed, then the guard must be passed (given relIn)**
  simp only [MessageIdx, Message,
    OptionT.simulateQ_map] at h_c_support_inner_loop
  set f : Fin (ℓ / ϑ) → L → OracleComp []ₒ (Option (ForInStep L)) :=
    fun (a :  Fin (ℓ / ϑ)) (b : L) ↦
    ((ForInStep.yield <$>
      (simulateQ.{0, 0, 0} so
        (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) a b v stmtIn
        ).run
      )) : OptionT (OracleComp []ₒ) (ForInStep L)) with h_f_def
  set inner_forIn_block := ((forIn (List.finRange (ℓ / ϑ)) (0 : L) f) :
    OptionT (OracleComp []ₒ) L) with h_inner_forIn_block
  have h_loop_safe : none ∉ support inner_forIn_block.run := by
    exact checkSingleRepetition_inner_forIn_none_not_mem_support 𝔽q β
      (γ_repetitions := γ_repetitions) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (rep := rep) (challenges := challenges)
  have h_c_eq_some := exists_eq_some_of_mem_support_of_none_not_mem.{0, 0} (x := c)
      (hx := h_c_support_inner_loop) (hnone := h_loop_safe)
  rcases h_c_eq_some with ⟨c_val, rfl⟩
  -- h_c_support_inner_loop : c ∈ forIn (List.finRange (ℓ / ϑ)) 0 f .support
  -- ⊢ x = stmtIn.final_constant
  -- We reuse the SAME relation `Rel` and the SAME logic we used for safety!
  have h_c_eq_final_constant : c_val = stmtIn.final_constant := by
    apply query_phase_final_fold_eq_constant 𝔽q β (v := v) (c := c_val)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (witIn := witIn)
      (h_relIn := h_relIn) (h_c_correct := by
        -- 1. Apply the helper lemma to transport the invariant to the end
      -- h_x_support : x ∈
      --   (forIn (List.finRange (ℓ / ϑ)) 0 fun a b ↦
      --       simulateQ (QueryImpl.lift so) (checkSingleFoldingStep 𝔽q β a b v stmtIn)
        -- >>= pure ∘ ForInStep.yield).support
      have h_rel_final : Rel ⟨ℓ/ϑ, by simp only [List.length_finRange,
        lt_add_iff_pos_right, zero_lt_one]⟩ c_val := by
        -- unfold OptionT at h_c_support_inner_loop
        -- Apply the yield-only helper
        let relation_correct_of_mem_support := support_forIn_subset_rel_yield_only.{0}
          (m := OptionT (OracleComp []ₒ)) (l := List.finRange (ℓ/ϑ)) (rel := Rel) (f := f)
          (init := 0) (h_start := by rfl) (h_step := by
          -- simp only [←simulateQ_liftComp]
          intro (k : Fin (List.finRange (ℓ / ϑ)).length) (c_k : L) h_rel_k_c iteration_output
            h_iteration_output_iteration
          -- 1. Unpack support (extract c_next)
          -- 1. Distribute simulateQ over >>= and pure
          --    This transforms: simulateQ (action >>= pure) -> (simulateQ action) >>= pure
          simp only [MessageIdx,  List.get_eq_getElem, List.getElem_finRange,
            Fin.eta, support_map, Set.mem_image, OptionT.mem_support_iff, toPFunctor_emptySpec,
            OptionT.run, f] at h_iteration_output_iteration
          -- 2. Now the hypothesis is exactly: ∃ c_next, c_next ∈ support ∧ output = yield c_next
          --    Extract it just like before!
          rcases h_iteration_output_iteration with ⟨c_next, h_c_next_mem, h_iteration_output_eq⟩
          rw [←h_iteration_output_eq]
          -- simp only [h_iteration_output_eq]
          constructor
          · rfl
          · -- Construct index (Same logic as Part 2)
            let k_idx : Fin (ℓ / ϑ) :=
              ⟨k.val, by
                have h_k_lt := k.isLt
                simp only [List.length_finRange] at h_k_lt
                exact h_k_lt⟩
            -- Apply preservation lemma (Exact same syntax as Part 2)
            let res := query_phase_step_preserves_fold 𝔽q β (γ_repetitions := γ_repetitions)
              (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k_idx) (v := v) (c_k := c_k)
              (s' := c_next) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (h_relIn := h_relIn)
              (challenges := challenges) (h_s'_mem := h_c_next_mem)
              (h_c_k_correct_of_k_pos := by
                dsimp only [k_idx]
                dsimp only [Rel, checkSingleRepetition_foldRel] at h_rel_k_c
                simp only [Fin.val_castSucc, dite_eq_ite] at h_rel_k_c
                by_cases hk : k.val > 0
                · simp only [gt_iff_lt, hk, ↓reduceDIte]
                  have h_ne_k_pos : ¬ (k.val = 0) := by omega
                  simp only [h_ne_k_pos, ↓reduceIte] at h_rel_k_c
                  exact h_rel_k_c
                · simp only [gt_iff_lt, hk, ↓reduceDIte]
              )
            exact res
        )
        let res := relation_correct_of_mem_support c_val h_c_support_inner_loop
        simp only [List.length_finRange] at res
        exact res
      -- 2. Unpack the relation at the final index (ℓ/ϑ)
      unfold Rel at h_rel_final
      -- Prove that the final index is not 0
      have h_nonzero : (⟨ℓ/ϑ, by simp only [List.length_finRange,
        lt_add_iff_pos_right, zero_lt_one]⟩ :
          Fin (List.length (List.finRange (ℓ / ϑ)) + 1)) ≠ 0 := by
        simp only [ne_eq, Fin.mk_eq_zero, Nat.div_eq_zero_iff, not_or, not_lt]
        constructor
        · have h := Nat.pos_of_neZero (ϑ); omega
        · exact Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
      -- Resolve the "if" statement to the "else" branch
      -- unfold Rel at h_rel_final
      dsimp only [checkSingleRepetition_foldRel] at h_rel_final
      simp only [ne_eq, Fin.mk_eq_zero] at h_nonzero
      rw [dite_eq_right h_nonzero] at h_rel_final
      -- Matches the goal exactly
      exact h_rel_final
    )
  rw [h_c_eq_final_constant]
  simp only [MessageIdx, guard_eq, ↓reduceIte]
  erw [simulateQ_pure.{0, 0, 0}]
  exact OptionT.none_not_mem_support_pure _

omit [CharP L 2] [SampleableType L] in
/-- Strong completeness for the query phase logic step.

This proves that for any valid input satisfying `strictFinalSumcheckRelOut`,
the verifier check succeeds with probability 1, and the output satisfies
`acceptRejectOracleRel` (i.e., the statement is `true`). -/
theorem queryPhaseLogicStep_isStronglyComplete :
    (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).IsStronglyCompleteUnderSimulation := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  -- 1. Generate the Honest Transcript (Deterministic given challenges)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  -- 2. Define the honest oracle simulator
  -- simOracle2 oSpec t₁ t₂ : SimOracle.Stateless (oSpec + ([T₁]ₒ + [T₂]ₒ)) oSpec
  -- This answers queries to OracleIn using oStmtIn and queries to Messages using transcript
  let so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages
  -- Every repetition is safe; the pure output then satisfies the relation and agreement clauses.
  have h_guards_pass : none ∉ support
      (simulateQ so (step.verifierCheck stmtIn transcript)) := by
    dsimp only [step, queryPhaseLogicStep]
    erw [OptionT.simulateQ_bind, OptionT.none_not_mem_support_bind_iff]
    constructor
    · erw [OptionT.simulateQ_forIn]
      apply none_not_mem_support_forIn_of_body_safe
      intro rep _ s_rep
      erw [OptionT.simulateQ_bind, OptionT.none_not_mem_support_bind_iff]
      constructor
      · exact checkSingleRepetition_none_not_mem_support 𝔽q β
          (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          stmtIn oStmtIn witIn h_relIn rep challenges
      · intro result _
        erw [simulateQ_pure]
        exact OptionT.none_not_mem_support_pure _
    · intro result _
      erw [simulateQ_pure]
      exact OptionT.none_not_mem_support_pure _
  exact ⟨h_guards_pass, rfl, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
omit [CharP L 2] [SampleableType L] in
/-- Perfect completeness for the final query round (using the oracle queryProof). -/
theorem queryOracleProof_perfectCompleteness {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relation := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleProof := queryOracleProof 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (init := init)
    (impl := impl) := by
  unfold OracleProof.perfectCompleteness
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_V_to_P
    (Oₛₒ := fun i : Empty => nomatch i)
    (reduction := queryOracleProof 𝔽q β (ϑ := ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (hDir0 := rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  apply OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support
  intro output h_output
  dsimp only [queryOracleProof, queryOracleReduction, queryOracleProver, queryOracleVerifier,
    OracleProofVerifier.ofVerify, OracleVerifier.toVerifier] at h_output
  obtain ⟨chal, _, h_output⟩ := OptionT.mem_support_run_lift_bind _ _ h_output
  obtain ⟨receive, h_receive, h_output⟩ := OptionT.mem_support_run_lift_bind _ _ h_output
  simp only [liftComp_eq_liftM] at h_receive
  subst receive
  obtain ⟨proverOutput, h_proverOutput, h_output⟩ :=
    OptionT.mem_support_run_lift_bind _ _ h_output
  simp only [liftComp_pure] at h_proverOutput
  subst proverOutput
  let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  have h_safe := (queryPhaseLogicStep_isStronglyComplete (L := L)
    𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    stmtIn witIn oStmtIn (fun ⟨j, hj⟩ => by
      match j with
      | 0 => exact chal) h_relIn).1
  rcases OptionT.mem_support_run_bind _ _ h_output with
    ⟨h_verifier, _⟩ | ⟨verifierResult, h_verifier, h_output⟩
  · change none ∈ MonadAttach.support (liftComp _ _) at h_verifier
    rw [support_liftComp] at h_verifier
    change none ∈ MonadAttach.support (Option.map _ <$> _) at h_verifier
    simp only [support_map, Set.mem_image] at h_verifier
    rcases h_verifier with ⟨result, h_result, h_none⟩
    erw [simulateQ_bind] at h_result
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_result
    obtain ⟨checkResult, h_check, h_result⟩ := h_result
    cases checkResult with
    | none => exact False.elim (h_safe h_check)
    | some value =>
      subst result
      simp at h_none
  · change some verifierResult ∈ MonadAttach.support (liftComp _ _) at h_verifier
    rw [support_liftComp] at h_verifier
    change some verifierResult ∈ MonadAttach.support (Option.map _ <$> _) at h_verifier
    simp only [support_map, Set.mem_image] at h_verifier
    rcases h_verifier with ⟨result, h_result, h_some⟩
    erw [simulateQ_bind] at h_result
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_result
    obtain ⟨checkResult, h_check, h_result⟩ := h_result
    cases checkResult with
    | none => exact False.elim (h_safe h_check)
    | some value =>
      subst result
      simp only [Option.map_some, Option.some.injEq] at h_some
      subst verifierResult
      have h_output_eq := OracleComp.eq_of_mem_support_pure _ h_output
      refine ⟨_, h_output_eq, ?_⟩
      exact ⟨by simp [queryPhaseLogicStep, acceptRejectOracleRel], rfl,
        Subsingleton.elim _ _⟩


end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase
