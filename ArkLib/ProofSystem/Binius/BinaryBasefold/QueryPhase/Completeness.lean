/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Execution

/-!
# Binary Basefold query-phase completeness

Honest query simulation is proved equal to a pure accepted value. The invariant tracks
exact iterated folds through the fiber-query loop, including every rejection guard.
-/

@[expose] public section

variable {ι : Type} {oSpec : OracleSpec ι}

open OracleSpec OracleComp ProtocolSpec AdditiveNTT

namespace Binius.BinaryBasefold.QueryPhase
noncomputable section
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q]
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Fintype 𝔽q] [DecidableEq 𝔽q]
  [Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [Fact (LinearIndependent 𝔽q β)] [Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [hdiv : Fact (ϑ ∣ ℓ)]

/-- Relation used in the forIn loop of `checkSingleRepetition`: at index 0 the folded value is 0
  at index `oraclePositionIdx > 0` it equals `iteratedFold` up to that position with challenges
    from `stmtIn` and suffix from `v`. -/
@[reducible]
def CheckSingleRepetitionFoldRel
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
      val_folded_point = iteratedFold
        (i := 0) (steps := oraclePositionIdx * ϑ) (destIdx := destIdx) (h_destIdx := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
        (h_destIdx_le := by
          rw [←h_mul]
          dsimp only [destIdx]
          apply Nat.mul_le_mul_right; exact h_le
        ) (f := f₀)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega)) (y := suffix_point_from_v)

private theorem honest_step_pure (γ : ℕ)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (chals : (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    (hstrict : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmt, oStmt), ()))
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (cur : L)
    (hcur : CheckSingleRepetitionFoldRel 𝔽q β (stmtIn := stmt) (oStmtIn := oStmt) (v := v)
      ⟨k.val, by simp only [List.length_finRange]; omega⟩ cur) :
    let tr := (queryPhaseLogicStep (oSpec := oSpec) 𝔽q β
      (ϑ := ϑ) γ).honestProverTranscript stmt () oStmt chals
    let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} oSpec oStmt tr.messages
    ∃ next : L,
      simulateQ so (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k cur v stmt).run = pure (some next) ∧
      CheckSingleRepetitionFoldRel 𝔽q β (stmtIn := stmt) (oStmtIn := oStmt) (v := v)
        ⟨k.val + 1, by simp only [List.length_finRange]; omega⟩ next := by
  intro tr so
  obtain ⟨t, hfold, _⟩ := hstrict
  have hguard (hk : k.val * ϑ > 0) :
      cur = logicalQueryFiberPoints 𝔽q β oStmt k v
        (extractMiddleFinMask 𝔽q β v ⟨k.val * ϑ, by
          have := k_mul_ϑ_lt_ℓ (k := k); omega⟩ ϑ) := by
    have hk0 : 0 < k.val := by nlinarith
    have hcur' := hcur
    simp only [CheckSingleRepetitionFoldRel, Fin.val_mk, hk0.ne', ↓reduceDIte] at hcur'
    exact hcur'.trans (iteratedFold_eq_queryFiberPoint_of_strictConsistency 𝔽q β v stmt oStmt t
      hfold)
  let next := logicalComputeFoldedValue 𝔽q β k v stmt
    (logicalQueryFiberPoints 𝔽q β oStmt k v)
  have hrun : simulateQ so
      (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k cur v stmt).run = pure (some next) := by
    rw [checkSingleFoldingStep_simulate]
    by_cases hk : k.val * ϑ > 0
    · simp only [hk, ↓reduceIte, hguard hk, guard_eq, ↓reduceIte, pure_bind]
      rfl
    · simp only [hk, ↓reduceIte]
      rfl
  refine ⟨next, hrun, ?_⟩
  simpa only [CheckSingleRepetitionFoldRel, Fin.val_mk, ne_eq,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte,
    Nat.add_one_sub_one, next] using
      logicalComputeFoldedValue_eq_totalFold_of_strictConsistency 𝔽q β v stmt oStmt t hfold

private theorem honest_loop_pure (γ : ℕ)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (chals : (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    (hstrict : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmt, oStmt), ()))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    let tr := (queryPhaseLogicStep (oSpec := oSpec) 𝔽q β
      (ϑ := ϑ) γ).honestProverTranscript stmt () oStmt chals
    let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} oSpec oStmt tr.messages
    let body := fun k cur => do
      let next ← (OptionT.mk (simulateQ so (checkSingleFoldingStep 𝔽q β
        (γ_repetitions := γ) (ϑ := ϑ) k cur v stmt).run) : OptionT (OracleComp oSpec) L)
      pure (ForInStep.yield next)
    ∃ final : L,
      (forIn (List.finRange (ℓ / ϑ)) (0 : L) body : OptionT (OracleComp oSpec) L) = pure final ∧
      CheckSingleRepetitionFoldRel 𝔽q β stmt oStmt v (Fin.last _) final := by
  intro tr so body
  let blocks := List.finRange (ℓ / ϑ)
  let Rel := CheckSingleRepetitionFoldRel 𝔽q β stmt oStmt v
  have loop : ∀ (pref xs : List (Fin (ℓ / ϑ))) (h : blocks = pref ++ xs)
      (cur : L), Rel ⟨pref.length, by
        have hh := congrArg List.length h
        dsimp only [blocks] at hh
        simp only [List.length_append, List.length_finRange] at hh ⊢
        omega⟩ cur →
      ∃ final, (forIn xs cur body : OptionT (OracleComp oSpec) L) = pure final ∧
        Rel (Fin.last _) final := by
    intro pref xs
    induction xs generalizing pref with
    | nil =>
      intro h cur hcur
      refine ⟨cur, by simp, ?_⟩
      have hp : pref.length = blocks.length := by simpa using congrArg List.length h.symm
      simpa only [hp, blocks, Fin.last] using hcur
    | cons k xs ih =>
      intro h cur hcur
      have hlen : pref.length < ℓ / ϑ := by
        have hh := congrArg List.length h
        simp only [blocks, List.length_finRange, List.length_append, List.length_cons] at hh
        omega
      have hk : k.val = pref.length := by
        have he : blocks[pref.length]'(by
            simpa only [blocks, List.length_finRange] using hlen) = k := by
          simp [h]
        simpa only [blocks, List.getElem_finRange, Fin.val_cast, Fin.val_mk] using
          (congrArg Fin.val he).symm
      obtain ⟨next, hnext, hrel⟩ := honest_step_pure 𝔽q β γ stmt oStmt chals hstrict k v cur
        (by simpa only [← hk] using hcur)
      have hb : body k cur = (pure (ForInStep.yield next) : OptionT (OracleComp oSpec) _) := by
        dsimp only [body]
        have ht : (OptionT.mk (simulateQ so (checkSingleFoldingStep 𝔽q β
            (γ_repetitions := γ) (ϑ := ϑ) k cur v stmt).run) : OptionT (OracleComp oSpec) L) =
            pure next := hnext
        rw [ht, pure_bind]
      rw [List.forIn_cons, hb, pure_bind]
      exact ih (pref ++ [k])
        (by simpa only [List.append_assoc, List.singleton_append] using h) next
        (by simpa only [List.length_append, List.length_singleton, hk] using hrel)
  exact loop [] blocks (by simp) 0 rfl

private theorem honest_repetition_pure (γ : ℕ)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (chals : (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    (hstrict : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmt, oStmt), ()))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    let tr := (queryPhaseLogicStep (oSpec := oSpec) 𝔽q β
      (ϑ := ϑ) γ).honestProverTranscript stmt () oStmt chals
    let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} oSpec oStmt tr.messages
    simulateQ so (checkSingleRepetition (oSpec := oSpec) 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
      v stmt stmt.finalConstant).run = pure (some ()) := by
  intro tr so
  obtain ⟨final, hloop, hrel⟩ := honest_loop_pure 𝔽q β γ stmt oStmt chals hstrict v
  have hpos : 0 < ℓ / ϑ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out)
    (Nat.pos_of_neZero ϑ)
  have hcorrect : final = stmt.finalConstant := by
    apply iteratedFold_eq_finalConstant_of_strictFinalSumcheckRelOut 𝔽q β v final stmt oStmt ()
      hstrict
    have hidx : Fin.last (List.finRange (ℓ / ϑ)).length =
        (⟨ℓ / ϑ, by simp⟩ : Fin ((List.finRange (ℓ / ϑ)).length + 1)) := by
      apply Fin.ext
      simp
    rw [hidx] at hrel
    dsimp only [CheckSingleRepetitionFoldRel, Fin.val_mk] at hrel
    simpa only [Nat.ne_of_gt hpos, ↓reduceDIte] using hrel
  change (simulateQ so (checkSingleRepetition (oSpec := oSpec) 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
    v stmt stmt.finalConstant) : OptionT (OracleComp oSpec) Unit) = pure ()
  dsimp only [checkSingleRepetition]
  rw [simulateQ_optionT_bind, simulateQ_optionT_list_forIn]
  simp only [simulateQ_optionT_bind, simulateQ_optionT_pure]
  have hloop' : (forIn (List.finRange (ℓ / ϑ)) (0 : L) (fun k cur => do
      let next ← (simulateQ so (checkSingleFoldingStep 𝔽q β
        (γ_repetitions := γ) (ϑ := ϑ) k cur v stmt) : OptionT (OracleComp oSpec) L)
      pure (ForInStep.yield next)) : OptionT (OracleComp oSpec) L) = pure final := by
    simpa only [Fin.eta, OptionT.mk, OptionT.run, so, tr] using hloop
  simp only [Fin.eta]
  rw [hloop', pure_bind]
  simp only [guard_eq, hcorrect, ↓reduceIte]
  rfl

/-- Honest simulation of the query-phase check is exactly pure acceptance.
The identity proves total execution as well as absence of rejection. -/
theorem queryPhaseLogicStep_simulate_honest (γ : ℕ)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (chals : (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    (hstrict : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmt, oStmt), ())) :
    let step := queryPhaseLogicStep (oSpec := oSpec) 𝔽q β (ϑ := ϑ) γ
    let tr := step.honestProverTranscript stmt () oStmt chals
    let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} oSpec oStmt tr.messages
    simulateQ so (step.verifierCheck stmt tr).run = pure (some true) := by
  intro step tr so
  change (simulateQ so (step.verifierCheck stmt tr) : OptionT (OracleComp oSpec) Bool) = pure true
  dsimp only [step, queryPhaseLogicStep]
  rw [simulateQ_optionT_bind]
  let body := fun (rep : Fin γ) (_ : PUnit) => do
    let _ ← checkSingleRepetition (oSpec := oSpec) 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
      (tr.challenges ⟨0, by rfl⟩ rep) stmt stmt.finalConstant
    pure (ForInStep.yield PUnit.unit)
  have hloopsim : simulateQ so
      (forIn (List.finRange γ) PUnit.unit body : OptionT (OracleComp _) PUnit).run =
      pure (some PUnit.unit) := by
    apply simulateQ_optionT_forIn_yield_pure_some
    intro rep
    change (simulateQ so (body rep PUnit.unit) : OptionT (OracleComp oSpec) _) =
      pure (ForInStep.yield PUnit.unit)
    dsimp only [body]
    rw [simulateQ_optionT_bind]
    have hr : (simulateQ so (checkSingleRepetition (oSpec := oSpec) 𝔽q β
      (γ_repetitions := γ) (ϑ := ϑ)
        (tr.challenges ⟨0, by rfl⟩ rep) stmt stmt.finalConstant) :
        OptionT (OracleComp oSpec) Unit) = pure () := by
      simpa only [so, tr, step, OptionT.run, pure_bind] using
        honest_repetition_pure 𝔽q β γ stmt oStmt chals hstrict (tr.challenges ⟨0, by rfl⟩ rep)
    rw [hr, pure_bind]
    rfl
  have ht : (OptionT.mk (simulateQ so
      (forIn (List.finRange γ) PUnit.unit body : OptionT (OracleComp _) PUnit).run) :
      OptionT (OracleComp oSpec) PUnit) = pure PUnit.unit := by
    exact hloopsim
  change Bind.bind (m := OptionT (OracleComp oSpec))
    (OptionT.mk (simulateQ so
      (forIn (List.finRange γ) PUnit.unit body : OptionT (OracleComp _) PUnit).run))
    (fun (_ : PUnit) => OptionT.mk (simulateQ so (pure true : OptionT (OracleComp _) Bool).run)) =
      (pure true : OptionT (OracleComp oSpec) Bool)
  rw [ht, pure_bind]
  rfl

/-- The oracle proof verifier accepts every strict honest input with total mass. -/
theorem queryOracleVerifier_simulate_honest (γ : ℕ)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (chals : (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    (hstrict : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmt, oStmt), ())) :
    let tr := FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (chals ⟨0, by rfl⟩)
    simulateQ (OracleInterface.simOracle2.{0, 0, 0, 0, 0} oSpec oStmt tr.messages)
      ((queryOracleVerifier (oSpec := oSpec) 𝔽q β (ϑ := ϑ) γ).verify
        (Oₛₒ := fun i : Empty => nomatch i) stmt chals).run = pure (some true) := by
  intro tr
  let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} oSpec oStmt tr.messages
  have hpure : (OptionT.mk (simulateQ so
      ((queryPhaseLogicStep (oSpec := oSpec) 𝔽q β (ϑ := ϑ) γ).verifierCheck stmt tr).run) :
      OptionT (OracleComp oSpec) Bool) = pure true :=
    queryPhaseLogicStep_simulate_honest 𝔽q β γ stmt oStmt chals hstrict
  change (simulateQ so ((queryOracleVerifier (oSpec := oSpec) 𝔽q β (ϑ := ϑ) γ).verify
    (Oₛₒ := fun i : Empty => nomatch i) stmt chals) : OptionT (OracleComp oSpec) Bool) = pure true
  dsimp only [queryOracleVerifier, OracleProofVerifier.ofVerify]
  rw [simulateQ_optionT_bind]
  change Bind.bind (m := OptionT (OracleComp oSpec))
    (OptionT.mk (simulateQ so
      ((queryPhaseLogicStep (oSpec := oSpec) 𝔽q β (ϑ := ϑ) γ).verifierCheck stmt tr).run))
    (fun (_ : Bool) => OptionT.mk (simulateQ so (pure true : OptionT (OracleComp _) Bool).run)) =
      (pure true : OptionT (OracleComp oSpec) Bool)
  rw [hpure, pure_bind]
  rfl

-- The final verifier run unfolds dependent oracle-interface fields.
set_option backward.isDefEq.respectTransparency false in
/-- Perfect completeness of the final query reduction on strictly consistent inputs. -/
theorem queryOracleReduction_perfectCompleteness (γ_repetitions : ℕ) {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relation := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleProof := queryOracleReduction (oSpec := oSpec) 𝔽q β (ϑ:=ϑ) γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (init := init)
    (impl := impl) := by
  unfold OracleProof.perfectCompleteness OracleReduction.perfectCompleteness
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro ⟨stmtIn, oStmtIn⟩ witIn h_relIn
  let _ : VerifierFirst (pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := ⟨rfl⟩
  let _ : VerifierOnly (pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := {}
  simp only [OracleReduction.toReduction, Reduction.run, queryOracleReduction, Prover.run]
  have hRun := Prover.runToRound_one_of_verifier_first (stmtIn, oStmtIn) witIn
    (queryOracleProver (oSpec := oSpec) 𝔽q β γ_repetitions (ϑ := ϑ))
  change Prover.runToRound (Fin.last 1) (stmtIn, oStmtIn) witIn
    (queryOracleProver (oSpec := oSpec) 𝔽q β γ_repetitions (ϑ := ϑ)) = _ at hRun
  rw [hRun]
  simp only [queryOracleProver, Verifier.run, bind_pure_comp, liftComp_pure,
    map_pure, monadLift_bind, bind_assoc]
  apply OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support
  intro output h_output
  obtain ⟨x, hx, h_output⟩ := OptionT.mem_support_run_lift_bind _ _ h_output
  simp only [monadLift_self] at hx
  rw [support_map] at hx
  obtain ⟨chal, _, rfl⟩ := hx
  simp only [queryPhaseLogicStep, map_pure, monadLift_pure,
    pure_bind] at h_output
  let tr := FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) chal
  have hstrict : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      ((stmtIn, oStmtIn), ()) := by cases witIn; exact h_relIn
  have hv : (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
      (queryOracleVerifier (oSpec := oSpec) 𝔽q β
        (ϑ := ϑ) γ_repetitions)).verify (stmtIn, oStmtIn) tr =
      (pure (true, fun i : Empty => nomatch i) : OptionT (OracleComp oSpec) _) := by
    have hr := queryOracleVerifier_simulate_honest (oSpec := oSpec) 𝔽q β γ_repetitions
      stmtIn oStmtIn tr.challenges hstrict
    dsimp only [OracleVerifier.toVerifier]
    erw [hr]
    simp only [map_pure, Option.map_some]
    congr 1
  dsimp only [tr, FullTranscript.mk1] at hv
  erw [hv] at h_output
  simp only [OptionT.run_pure, monadLift_pure, pure_bind, Option.getM, map_pure,
    support_pure, Set.mem_singleton_iff] at h_output
  refine ⟨_, h_output, ?_⟩
  constructor
  · rfl
  · congr 1

end
end Binius.BinaryBasefold.QueryPhase
