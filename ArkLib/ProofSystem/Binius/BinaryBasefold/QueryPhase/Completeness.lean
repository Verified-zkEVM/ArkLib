/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Folding
-- These probability proofs use the protocol module's private probability helpers.
import all ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Protocol

/-!
# Binary Basefold query-phase completeness
-/

@[expose] public section

open OracleSpec
attribute [local instance] queryEmptySpecInhabited
noncomputable local instance completenessEmptyUniformSpec : IsUniformSpec []ₒ :=
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
`checkSingleRepetition_probFailure_eq_zero`. -/
lemma checkSingleRepetition_inner_forIn_probFailure_eq_zero
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
      Pr[⊥ | inner_forIn_block] = 0 := by
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
  apply probFailure_forIn_of_relations_simplified (rel := Rel) (h_start := by rfl) (h_step := by
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
      erw [probFailure_map] -- Pr[⊥ | f <$> mx] = Pr[⊥ | mx] **IMPORTANT**
      -- ⊢ Pr[⊥ | simulateQ so (checkSingleFoldingStep 𝔽q β γ_repetitions
      --   ((List.finRange (ℓ / ϑ)).get k) c_k v stmtIn).run] = 0
      dsimp only [checkSingleFoldingStep]
      erw [simulateQ_bind]
      erw [probFailure_mk_bind_eq_zero_iff.{0, 0}]
      have h_probFailure_queryFiberPoints_eq_zero : Pr[⊥ |
        OptionT.mk
          (simulateQ so
            (queryFiberPoints 𝔽q β γ_repetitions ((List.finRange (ℓ / ϑ)).get k) v))] = 0 := by
        apply probFailure_simulateQ_queryFiberPoints_eq_zero
          (γ_repetitions := γ_repetitions) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝔽q := 𝔽q) (β := β)
          (so := so) (k := k) (v := v)
      have h_probOutput_none_queryFiberPoints_eq_zero :=
        (add_eq_zero.mp ((OptionT.probFailure_eq _).symm.trans
          h_probFailure_queryFiberPoints_eq_zero)).2
      constructor
      · -- queryFiberPoints never fails (oracle queries)
        simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta,
          probFailure_eq_zero]
      · -- The guard and pure computation
        intro fiber_vec_opt h_fiber_vec_opt_mem_support
        have h_fiber_vec_eq_some :=
          exists_eq_some_of_mem_support_of_probOutput_none_eq_zero.{0, 0} (x := fiber_vec_opt)
            (hx := h_fiber_vec_opt_mem_support)
            (hnone := h_probOutput_none_queryFiberPoints_eq_zero)
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
            rw [dif_neg h_k_castSucc_ne_0] at h_rel_k_c
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
          erw [probFailure_pure]
        · -- Case k = 0: no guard
          simp only [h_i_pos, ↓reduceIte]
          erw [simulateQ_pure, probFailure_pure]
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
lemma checkSingleRepetition_probFailure_eq_zero
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
      Pr[⊥ | OptionT.mk.{0, 0} (simulateQ.{0, 0, 0} so
        (checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v stmtIn stmtIn.final_constant).run)] = 0 := by
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
  erw [probFailure_mk_bind_eq_zero_iff.{0, 0}]
  dsimp only [OptionT.mk]
  -- rw [OptionT.liftComp_forIn]
  conv =>
    enter [1];
    simp only [MessageIdx, List.forIn_yield_eq_foldlM, id_map', List.foldlM_range, bind_pure_comp,
      probFailure_eq_zero, zero_add, probOutput_eq_zero_iff', finSupport_map,
      Finset.mem_image, reduceCtorEq, and_false, exists_const, not_false_eq_true]
  rw [true_and]
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
  have h_probFailure_loop_eq_zero : Pr[⊥ | inner_forIn_block] = 0 := by
    exact checkSingleRepetition_inner_forIn_probFailure_eq_zero 𝔽q β
      (γ_repetitions := γ_repetitions) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (rep := rep) (challenges := challenges)
  have h_probOutput_inner_forIn_block_eq_none :=
    (add_eq_zero.mp ((OptionT.probFailure_eq _).symm.trans
      h_probFailure_loop_eq_zero)).2
  have h_c_eq_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero.{0, 0} (x := c)
      (hx := h_c_support_inner_loop) (hnone := h_probOutput_inner_forIn_block_eq_none)
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
      rw [dif_neg h_nonzero] at h_rel_final
      -- Matches the goal exactly
      exact h_rel_final
    )
  rw [h_c_eq_final_constant]
  simp only [MessageIdx, guard_eq, ↓reduceIte]
  erw [simulateQ_pure.{0, 0, 0}]
  erw [probFailure_pure.{0, 0}]

omit [CharP L 2] [SampleableType L] in
/-- Strong completeness for the query phase logic step.

This proves that for any valid input satisfying `strictFinalSumcheckRelOut`,
the verifier check succeeds with probability 1, and the output satisfies
`acceptRejectOracleRel` (i.e., the statement is `true`). -/
theorem queryPhaseLogicStep_isStronglyComplete :
    (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).IsStronglyCompleteUnderSimulation := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let f₀ := getFirstOracle 𝔽q β oStmtIn
  have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
  let step := queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  -- 1. Generate the Honest Transcript (Deterministic given challenges)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  -- 2. Define the honest oracle simulator
  -- simOracle2 oSpec t₁ t₂ : SimOracle.Stateless (oSpec + ([T₁]ₒ + [T₂]ₒ)) oSpec
  -- This answers queries to OracleIn using oStmtIn and queries to Messages using transcript
  let so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages
  -- We need to prove:
  -- 1. [⊥ | verifierCheck ...] = 0  (never fails)
  -- 2. [fun b => b = true | verifierCheck ...] = 1  (always returns true)
  -- 3. completeness_relOut holds
  -- 4-5. Prover and verifier agree
  -- Prove safety: verifier check never fails
  have h_guards_pass : Pr[⊥ | OptionT.mk
    (simulateQ so (step.verifierCheck stmtIn transcript))] = 0 := by
    -- Unfold the definitions
    dsimp only [step, queryPhaseLogicStep]
    rw [OptionT.probFailure_eq]
    conv_lhs => -- first summand is 0
      enter [1]; simp only [MessageIdx, Message, Fin.isValue, liftM_OptionT_eq, bind_pure_comp,
        map_pure, id_map', List.foldlM_range, OptionT.simulateQ_map,
        probFailure_eq_zero]
    rw [zero_add]
    -- 2. Push simulation inside the 'bind' structure
    -- simulateQ (do a <- x; b) = do a <- simulateQ x; simulateQ b
    erw [simulateQ_bind]
    -- simp only [Function.comp_apply, probOutput_eq_zero_iff]
    -- rw [OptionT.support_run_eq]
    -- simp only [←probOutput_eq_zero_iff]
    -- erw [probOutput_none_OptionT_pure_eq_zero]
    apply probOutput_none_eq_zero_of_probFailure_eq_zero
    -- rw [probFailure_bind_eq_zero_iff]
    erw [probFailure_mk_bind_eq_zero_iff]
    -- [⊥|simulateQ so (forIn ...)] = 0 ∧ (∀ x ∈ (simulateQ so (forIn ...)).support, ...))
    -- conv => -- Simp away the second term (which is simulateQ of pure)
      -- enter [2]
      -- simp only [liftM_OptionT_eq, bind_pure_comp]
    set simulateQ_forIn_block :  OracleComp []ₒ (Option PUnit.{1}) :=
      simulateQ so _ with h_simulateQ_forIn_block
    have h_probFailure_simulateQ_forIn_eq_0 : Pr[⊥ | OptionT.mk simulateQ_forIn_block] = 0 := by
      dsimp only [simulateQ_forIn_block]
      rw [OptionT.simulateQ_forIn]
      dsimp only [OptionT.mk]
      -- rw [OptionT.probFailure_mk]
      -- conv_lhs =>
      --   enter [1]; simp only [MessageIdx, Message, Fin.isValue, liftM_OptionT_eq, bind_pure_comp,
      --     map_pure, List.forIn_yield_eq_foldlM, id_map', List.foldlM_range,
      --     probFailure_eq_zero]
      -- rw [zero_add]
      -- -- ⊢ Pr[=none | simulateQ_forIn_block] = 0
      -- change (Pr[=none | simulateQ_forIn_block] = 0)
      -- 3. Now we are at the outer loop (forIn γ_repetitions).
      -- Push simulateQ inside the loop using the lemma that `simulateQ distributes over the loop`
      -- NOW apply the safety lemma
      -- The goal is: [⊥ | forIn ... (fun ... ↦ simulateQ so ...)] = 0
      apply _root_.probFailure_forIn_eq_zero_of_body_safe
      intro rep h_rep_mem s_rep
      -- 4. Push simulation inside the inner logic
      erw [simulateQ_bind]
      -- rw [probFailure_bind_eq_zero_iff]
      conv =>
        enter [2]
      erw [OptionT.probFailure_eq]
      conv_lhs =>
        enter [1];
        simp only [MessageIdx, Message, Fin.isValue, liftM_OptionT_eq, bind_pure_comp, map_pure,
          probFailure_eq_zero]
      rw [zero_add]
      apply probOutput_none_eq_zero_of_probFailure_eq_zero
      erw [probFailure_mk_bind_eq_zero_iff]
      set simulateQ_singleRepetition_block :  OracleComp []ₒ (Option PUnit.{1}) :=
      simulateQ so _ with h_simulateQ_singleRepetition_block
      have h_probFailure_simulateQ_singleRepetition_eq_0 :
        Pr[⊥ | OptionT.mk simulateQ_singleRepetition_block] = 0 := by
        apply checkSingleRepetition_probFailure_eq_zero (h_relIn := h_relIn)
      have h_probOutput_simulateQ_singleRepetition_eq_none :=
        probOutput_none_eq_zero_of_probFailure_eq_zero
          (hfail := h_probFailure_simulateQ_singleRepetition_eq_0)
      constructor
      · simp only [probFailure_eq_zero]
      · intro x hx -- output from the single repetition
        have h_x_eq : ∃ val, x = some (val) := by
          have h_exists_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero (x := x)
            (hx := hx) (hnone := h_probOutput_simulateQ_singleRepetition_eq_none)
          exact h_exists_some
        rcases h_x_eq with ⟨val, h_x_eq⟩
        rw [h_x_eq]
        rw [OptionT.probFailure_eq]
        simp only [MessageIdx, Message, probFailure_eq_zero, zero_add]
        erw [simulateQ_pure]
        simp only [OptionT.run_mk, probOutput_eq_zero_iff, support_pure,
          Set.mem_singleton_iff, reduceCtorEq,
          not_false_eq_true]
    have h_probOutput_simulateQ_forIn_eq_none :=
      probOutput_none_eq_zero_of_probFailure_eq_zero
        (hfail := h_probFailure_simulateQ_forIn_eq_0)
    constructor
    · simp only [probFailure_eq_zero]
    · intro x hx -- output from the forIn loop
      have h_x_eq : ∃ val, x = some (val) := by
        have h_exists_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero (x := x)
          (hx := hx) (hnone := h_probOutput_simulateQ_forIn_eq_none)
        exact h_exists_some
      rcases h_x_eq with ⟨val, h_x_eq⟩
      rw [h_x_eq]
      rw [OptionT.probFailure_eq]
      simp only [OptionT.run_mk, probFailure_eq_zero, zero_add]
      erw [simulateQ_pure]
      simp only [probOutput_pure, reduceCtorEq, ↓reduceIte]
  exact ⟨h_guards_pass, rfl, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
omit [CharP L 2] [SampleableType L] in
/-- Perfect completeness for the final query round (using the oracle queryProof). -/
theorem queryOracleProof_perfectCompleteness {σ : Type}
    (init : ProbComp σ) (hInit : NeverFail init)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relation := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleProof := queryOracleProof 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (init := init)
    (impl := impl) := by
  unfold OracleProof.perfectCompleteness
  let p := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let : OracleSpec.Fintype [p.Challenge]ₒ :=
    { fintypeB := fun j => inferInstanceAs (Fintype (p.Challenge j.1)) }
  let : OracleSpec.Inhabited [p.Challenge]ₒ :=
    { inhabitedB := fun j => inferInstanceAs (Inhabited (p.Challenge j.1)) }
  let : IsUniformSpec ([]ₒ + [p.Challenge]ₒ) := IsUniformSpec.ofFintypeInhabited _
  -- Supply the empty output interface explicitly when unrolling the sole verifier challenge.
  rw [@OracleReduction.unroll_1_message_reduction_perfectCompleteness_V_to_P
    _ _ []ₒ _ _ _ _ _ Empty _ (fun _ : Empty => Unit) _ (fun i => nomatch i) p _ _
    (queryOracleProof 𝔽q β (ϑ := ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) _ _ init impl hInit rfl
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  -- dsimp only [queryOracleProof, queryOracleProver, queryOracleVerifier,
  dsimp only [queryOracleProof, queryOracleReduction, queryOracleProver, queryOracleVerifier,
    OracleProofVerifier.ofVerify, OracleVerifier.toVerifier, FullTranscript.mk1]
  let step := (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  let strongly_complete : step.IsStronglyCompleteUnderSimulation :=
    queryPhaseLogicStep_isStronglyComplete (L := L)
      𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  constructor
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    -- ⊢ [⊥| do
    --   let challenge ← getChallenge          -- (A) V samples v ← B_{ℓ+R}
    --   let receiveChallengeFn ← pure (...)               -- (B) P receives challenge
      -- (pure, never fails)
    --   let __discr ← proverOut ...           -- (C) P computes output (pure, never fails)
    --   let verifierStmtOut ← simulateQ ...   -- (D) V runs verifierCheck ← THIS IS THE KEY
    --       do
    --         let _ ← liftM verifierCheck     -- The guards live here!
    --         pure verifierOut
    --   pure (...)
    -- ] = 0
    -- Step 1: Peel off the safe layers
    -- For each layer:
    --   A: neverFails_getChallenge or neverFails_query
    --   B: neverFails_pure
    --   C: neverFails_pure (after liftComp)
    rw [probFailure_mk_bind_eq_zero_iff]
    refine ⟨(neverFail_iff init).mp hInit, ?_⟩
    intro initialState h_initialState
    apply probFailure_simulateQ_run'_eq_zero
    dsimp only [OptionT.run, OptionT.mk]
    simp only [probFailure_bind_eq_zero_iff]
    conv_lhs =>
      simp only [liftComp_eq_liftM, liftM_pure, probFailure_eq_zero]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [OptionT.probFailure_lift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_zero, liftComp_eq_liftM,
        probFailure_eq_zero]
    rw [true_and]
    intro chal h_chal_support
    -- 1.B Handle the `let receiveChallengeFn ← pure (...)`
    conv =>
      enter [1]; simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one, liftComp_eq_liftM]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [OptionT.probFailure_lift]
      simp only [Fin.isValue, liftComp_eq_liftM, probFailure_eq_zero]
    rw [true_and]
    intro h_receiveChallengeFn h_receiveChallengeFn_support
    simp only [liftComp_pure, liftM_pure, support_pure, Set.mem_singleton_iff]
      at h_receiveChallengeFn_support
    subst h_receiveChallengeFn
    -- 1.B Handle the `(queryOracleReduction 𝔽q β γ_repetitions).prover.output
      -- (h_receiveChallengeFn chal)) ...`
    conv =>
      enter [1];
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one, liftComp_eq_liftM]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [OptionT.probFailure_lift]
      simp only [Fin.isValue, liftComp_eq_liftM, probFailure_eq_zero]
    rw [true_and]
    intro prover_final_output h_prover_final_output_support
    simp only [liftComp_pure, liftM_pure, support_pure, Set.mem_singleton_iff]
      at h_prover_final_output_support
    -- 1.C Handle the `let __discr ← proverOut ...`
    -- Note: Use simp instead of rw to avoid typeclass diamond issues with Fintype instances
    -- split;
    simp only [ChallengeIdx, Challenge, MessageIdx, bind_pure_comp, liftComp_eq_liftM,
      OptionT.mem_support_iff, toPFunctor_add, toPFunctor_emptySpec, OptionT.run,
      Prod.mk.eta, probFailure_eq_zero, implies_true, and_true]
    -- erw [OptionT.probFailure_mk]
    rw [OptionT.probFailure_eq]
    conv_lhs =>
      enter [1]
      simp only [MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        id_eq, bind_pure_comp, OptionT.run_map, probFailure_eq_zero]
    rw [zero_add]
    simp only [probOutput_eq_zero_iff]
    rw [OptionT.support_run_eq]
    simp only [←probOutput_eq_zero_iff]
    rw [← liftComp_eq_liftM, probOutput_liftComp, probOutput_eq_zero_iff]
    simp only [support_map, Set.mem_image]
    rintro ⟨vStmtOut, h_vStmtOut_mem_support, h_output_none⟩
    -- Apply the simulateQ safety lemma
    -- Can't apply probFailure_simulateQ_simOracle2_eq_zero here
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete
      (stmtIn := stmtIn) (witIn := witIn) (h_relIn := h_relIn)
      (challenges := fun ⟨j, hj⟩ => by
        match j with
        | 0 => exact chal
      )
    have h_transcript_eq : FullTranscript.mk1 ((FullTranscript.mk1 chal).challenges ⟨0, by rfl⟩) =
      FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions) chal := by
      rfl
    rw [h_transcript_eq] at h_vStmtOut_mem_support
    have h_probOutput_none_V_check_eq_0 :=
      probOutput_none_eq_zero_of_probFailure_eq_zero (hfail := h_V_check)
    have h_vStmtOut_eq : ∃ val, vStmtOut = some (val) := by
      have h_exists_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero (x := vStmtOut)
        (hx := h_vStmtOut_mem_support) (hnone := by
          dsimp only [step] at h_probOutput_none_V_check_eq_0
          dsimp only [queryOracleProof, queryOracleReduction, queryPhaseLogicStep,
            queryOracleVerifier, OracleVerifier.toVerifier] at h_probOutput_none_V_check_eq_0 ⊢
          rw [h_transcript_eq] at h_probOutput_none_V_check_eq_0 ⊢
          simp only [MessageIdx, Message, Fin.isValue, bind_pure_comp, Functor.map_map,
            OptionT.simulateQ_map]
          simp only [MessageIdx, Message, Fin.isValue, bind_pure_comp,
            OptionT.simulateQ_map] at h_probOutput_none_V_check_eq_0
          exact h_probOutput_none_V_check_eq_0
        )
      exact h_exists_some
    rcases h_vStmtOut_eq with ⟨val, h_vStmtOut_eq⟩
    simp only [h_vStmtOut_eq, Option.map_some, reduceCtorEq] at h_output_none
  · -- GOAL 2: CORRECTNESS - Prove all outputs in support satisfy the relation
    intro x hx_mem_support
    rw [OptionT.mem_support_iff] at hx_mem_support
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion, exists_prop]
      at hx_mem_support
    rcases hx_mem_support with ⟨initialState, h_initialState, h_simulated⟩
    have hx_mem_support :=
      OracleComp.support_simulateQ_run'_subset _ _ initialState h_simulated
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only
    -- Step 2a: Simplify the support membership to extract the challenge
    simp only [OptionT.run_bind, OptionT.run_pure,
      liftComp_pure, liftM_pure, Option.elimM, pure_bind,
      support_bind,
      Set.mem_iUnion, exists_prop
    ] at hx_mem_support
    conv at hx_mem_support =>
      simp only [OptionT.run, support_pure]
      simp only [
        Set.mem_singleton_iff, Option.some.injEq, Set.ofPred_eq_eq_singleton, Prod.mk.injEq,
        OptionT.mem_support_iff,
        OptionT.run_monadLift, support_map, Set.mem_image, exists_eq_right, Fin.succ_one_eq_two,
        id_eq, guard_eq, bind_pure_comp,
        toPFunctor_add, toPFunctor_emptySpec, OptionT.run, ↓existsAndEq, and_true, true_and,
        exists_eq_right_right', liftM_pure, support_pure, exists_eq_left]
    simp only [Fin.isValue, Challenge, ChallengeIdx,
      liftComp_eq_liftM, MessageIdx] at hx_mem_support
    dsimp only [liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk]
      at hx_mem_support
    simp only [support_liftComp, support_map, Set.mem_image, existsAndEq,
      support_pure, Set.mem_singleton_iff,
      Option.elim_some, support_bind, Set.mem_iUnion, exists_prop,
      ] at hx_mem_support
    -- Step 2b: Extract the challenge r1 and the trace equations
    obtain ⟨r1, ⟨_h_r1_mem_challenge_support, h_trace_support⟩⟩ := hx_mem_support
    rcases h_trace_support with ⟨prvWitOut, h_prvOut_mem_support, h_verOut_mem_support⟩
    -- Successful query verification returns true; failure has no successful output.
    erw [simulateQ_bind] at h_prvOut_mem_support
    simp only [support_bind, Set.mem_iUnion, exists_prop, and_true] at h_prvOut_mem_support
    obtain ⟨checkResult, _, h_result⟩ := h_prvOut_mem_support
    cases checkResult with
    | none =>
      simp only [Option.elim_none, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at h_result
      subst prvWitOut
      simp only [Option.map_none, Option.elim_none, support_pure,
        Set.mem_singleton_iff, reduceCtorEq] at h_verOut_mem_support
    | some checkResult =>
      simp only [Option.elim_some, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at h_result
      subst prvWitOut
      dsimp only [queryPhaseLogicStep] at h_verOut_mem_support
      simp only [Option.map_some, Option.elim_some, support_pure,
        Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at h_verOut_mem_support
      obtain ⟨⟨h_prover, _⟩, ⟨h_verifier, _⟩, _⟩ := h_verOut_mem_support
      subst prvStmtOut
      subst verStmtOut
      exact ⟨by simp [acceptRejectOracleRel], rfl, Subsingleton.elim _ _⟩


end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase
