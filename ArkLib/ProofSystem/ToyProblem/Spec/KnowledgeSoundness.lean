/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.Spec.SimplifiedIOR

/-!
# Exact-extractor knowledge soundness for the toy protocol

This module assembles the three-round knowledge-soundness game while retaining
the identity of a supplied executable transition extractor.  The coding-theory
argument for the combination round is a premise; the spot-check tail and all
protocol/game plumbing are proved here once, independently of a concrete code.

`oracleVerifier_knowledgeSoundnessWith_of_transition_failure_prob_le` concludes the public
`knowledgeSoundnessWith` predicate, so the extractor remains visible in the
theorem type.  Concrete implementations may derive the older existential
`knowledgeSoundness` contract only as a corollary.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26], Section 6.
-/

namespace ToyProblem.Spec

open OracleSpec OracleComp ProtocolSpec
open Probability
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {ι F A : Type} [Fintype ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]
variable [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A]

/-- Turn a deterministic transition algorithm reading `(statement, γ, g)` into
the straightline extractor shape used by ArkLib's game. -/
def transitionStraightlineExtractor {k t : ℕ}
    (transition :
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) →
        F → (Fin k → F) → Witness (F := F) k) :
    Extractor.Straightline []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i))
      (Witness (F := F) k) OutputWitness
      (pSpec (ι := ι) (F := F) k t) :=
  fun stmtIn _ tr _ _ ↦ pure <|
    transition stmtIn
      (tr ⟨0, Nat.zero_lt_succ _⟩)
      (tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)

/-- A predicate false at every point has probability zero. -/
private theorem Pr_eq_zero_of_forall_not {α : Type} (D : PMF α) (P : α → Prop)
    (h : ∀ x, ¬ P x) : Pr_{let x ← D}[P x] = 0 := by
  classical
  rw [prob_tsum_form_singleton]
  simp [h]

omit [Fintype ι] [DecidableEq ι] [Fintype F] [Fintype A] in
private theorem verifier_run_loggingOracle_eq
    {k t : ℕ} (encode : (Fin k → F) → (ι → A))
    (stmt : Statement (F := F) k) (oStmt : ∀ i, OracleStatement ι A i)
    (tr : (pSpec (ι := ι) (F := F) k t).FullTranscript) :
    (simulateQ loggingOracle
        ((oracleVerifier (k := k) (t := t) encode).toVerifier.run
          (stmt, oStmt) tr)).run =
      pure ((if Accepts (k := k) (t := t) encode stmt oStmt
            (tr.challenges ⟨0, rfl⟩) (tr.messages ⟨1, rfl⟩)
            (tr.challenges ⟨2, rfl⟩)
          then some (((), nofun) :
            OutputStatement × ∀ i, OutputOracleStatement i) else none), ∅) := by
  classical
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [oracleVerifier_simulateQ_eq_pure_ite (k := k) (t := t)
    encode stmt oStmt tr.challenges tr.messages]
  have hmap : ∀ (fn : Unit → OutputStatement × ∀ i, OutputOracleStatement i)
      (o : Option Unit),
      (simulateQ loggingOracle
        (OptionT.mk (Option.map fn <$> (pure o : OracleComp []ₒ (Option Unit))))).run =
        pure (o.map fn, ∅) := by
    intro fn o
    cases o with
    | none => simp only [map_pure, Option.map_none]; rfl
    | some u => simp only [map_pure, Option.map_some]; rfl
  rw [hmap]
  split
  · simp only [Option.map_some]
    refine congrArg pure (congrArg (·, ∅)
      (congrArg some (congrArg (Prod.mk ()) ?_)))
    funext i
    exact i.elim0
  · simp only [Option.map_none]

omit [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A] in
private theorem prover_run_map_eq {k t : ℕ} {β : Type}
    (prover : Prover []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i))
      (Witness (F := F) k)
      (OutputStatement × ∀ i, OutputOracleStatement i) OutputWitness
      (pSpec (ι := ι) (F := F) k t))
    (stmt : Statement (F := F) k × (∀ i, OracleStatement ι A i))
    (witIn : Witness (F := F) k)
    (post : F → (Fin k → F) → (Fin t → ι) →
      ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness) → β) :
    (fun r ↦ post (r.1.challenges ⟨0, rfl⟩)
      (r.1.messages ⟨1, rfl⟩) (r.1.challenges ⟨2, rfl⟩) r.2) <$>
        Prover.run stmt witIn prover =
      (do
      let c ← liftComp ((pSpec (ι := ι) (F := F) k t).getChallenge ⟨0, rfl⟩)
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let f0 ← liftComp
        (prover.receiveChallenge ⟨0, rfl⟩ (prover.input (stmt, witIn)))
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let pre ← liftComp (prover.sendMessage ⟨1, rfl⟩ (f0 c))
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let xs ← liftComp
        ((pSpec (ι := ι) (F := F) k t).getChallenge ⟨2, rfl⟩)
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let f2 ← liftComp (prover.receiveChallenge ⟨2, rfl⟩ pre.2)
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let out ← liftComp (prover.output (f2 xs))
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      pure (post c pre.1 xs out)) := by
  have h0 : (pSpec (ι := ι) (F := F) k t).dir 0 = .V_to_P := rfl
  have h1 : (pSpec (ι := ι) (F := F) k t).dir 1 = .P_to_V := rfl
  have h2 : (pSpec (ι := ι) (F := F) k t).dir 2 = .V_to_P := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_three,
    Prover.processRound_of_dir_eq_V_to_P 0 h0,
    Prover.processRound_of_dir_eq_P_to_V 1 h1,
    Prover.processRound_of_dir_eq_V_to_P 2 h2,
    map_eq_bind_pure_comp, bind_assoc, liftComp_eq_liftM, pure_bind,
    Function.comp, Fin.castSucc_zero', Fin.isValue]
  dsimp only [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.castLT, Fin.last]
  simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift,
    pure_bind, bind_assoc, FullTranscript.challenges, FullTranscript.messages,
    Transcript.concat, Fin.snoc, Fin.val_zero, Fin.val_one, Fin.val_two,
    lt_self_iff_false, Fin.val_castLT, Fin.castSucc_castLT,
    show (0 : ℕ) < 2 from by norm_num, show (0 : ℕ) < 1 from by norm_num,
    show (1 : ℕ) < 2 from by norm_num, show ¬ ((2 : ℕ) < 0) from by norm_num,
    dif_pos, cast_eq, dite_false]
  rfl

omit [DecidableEq ι] [Fintype F] [Fintype A] in
/-- Full fixed-radius knowledge soundness for one exact transition-based
straightline extractor.  The combination-round premise is composed with the
spot-check tail by the sharp convex/union expression. -/
theorem oracleVerifier_knowledgeSoundnessWith_of_transition_failure_prob_le
    {k t : ℕ} [SampleableType F] [SampleableType ι] [Nonempty ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (δ gammaError : ℝ≥0) (encode : (Fin k → F) →ₗ[F] (ι → A))
    (transition :
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) →
        F → (Fin k → F) → Witness (F := F) k)
    (extractor : Extractor.Straightline []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i))
      (Witness (F := F) k) OutputWitness
      (pSpec (ι := ι) (F := F) k t))
    (hextractor : extractor = transitionStraightlineExtractor transition)
    (hgamma : ∀ stmtIn,
      Pr[ fun γ : F ↦ ∃ g : Fin k → F,
          (stmtIn, transition stmtIn γ g) ∉
              outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ ∧
            GammaState k (encode : (Fin k → F) → (ι → A)) δ
              stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
              (stmtIn.2 0) (stmtIn.2 1) γ g
        | $ᵗ F] ≤ (gammaError : ENNReal)) :
    (oracleVerifier (k := k) (t := t)
      (encode : (Fin k → F) → (ι → A))).knowledgeSoundnessWith
      (WitOut := OutputWitness) init impl
      (outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) ×
        OutputWitness)) extractor
      ((1 - δ) ^ t + gammaError * (1 - (1 - δ) ^ t)) := by
  subst extractor
  classical
  unfold OracleVerifier.knowledgeSoundnessWith Verifier.knowledgeSoundnessWith
  rintro ⟨stmt, oStmt⟩ witIn prover
  rw [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_sub, ENNReal.coe_one]
  refine ProtocolSpec.probEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_convex
    (ε₂ := (((1 - δ) ^ t : ℝ≥0) : ENNReal))
    init impl _ ⟨0, rfl⟩
    (fun γ ↦ do
      let pre ← (liftComp (prover.receiveChallenge ⟨0, rfl⟩
            (prover.input ((stmt, oStmt), witIn)))
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)) >>= fun fc ↦
          liftComp (prover.sendMessage ⟨1, rfl⟩ (fc γ))
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let xs ← liftComp ((pSpec (ι := ι) (F := F) k t).getChallenge ⟨2, rfl⟩)
          ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      (fun out : (OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness ↦
        if Accepts (k := k) (t := t)
            ((encode : (Fin k → F) → (ι → A))) stmt oStmt γ pre.1 xs
        then some ((stmt, oStmt), some (transition (stmt, oStmt) γ pre.1),
          (((), nofun) : OutputStatement × ∀ i, OutputOracleStatement i), out.2)
        else none) <$>
        ((liftComp (prover.receiveChallenge
            (⟨2, by rfl⟩ : (pSpec (ι := ι) (F := F) k t).ChallengeIdx) pre.2)
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)) >>= fun fc2 ↦
          liftComp (prover.output (fc2 xs))
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)))
    _
    (fun γ ↦ ∃ g : Fin k → F,
      ((stmt, oStmt), transition (stmt, oStmt) γ g) ∉
          outputRelationFor k ((encode : (Fin k → F) → (ι → A))) δ ∧
        GammaState k ((encode : (Fin k → F) → (ι → A))) δ
          stmt.1 stmt.2.1 stmt.2.2 (oStmt 0) (oStmt 1) γ g)
    ?hε₂ ?hoa ?h₁ ?h₂
  case hε₂ =>
    exact ENNReal.coe_le_one_iff.mpr (pow_le_one' tsub_le_self t)
  case h₁ =>
    exact hgamma (stmt, oStmt)
  case h₂ =>
    intro γ hγ s0
    refine ProtocolSpec.probEvent_optionT_simulateQ_addLift_prefix_getChallenge_bind_le
      s0 impl _ ⟨2, rfl⟩ _ _ _ _ rfl (fun pre ↦ ?_)
    refine le_trans (probEvent_mono ?_) (spotcheck_round_game_bound k t
      ((encode : (Fin k → F) → (ι → A))) δ (stmt, oStmt) γ pre.1)
    rintro xs - ⟨out, b, hfb, hE⟩
    by_cases hacc : Accepts (k := k) (t := t)
        ((encode : (Fin k → F) → (ι → A))) stmt oStmt γ pre.1 xs
    · rw [if_pos hacc, Option.some_inj] at hfb
      subst hfb
      refine ⟨PUnit.unit.{1}, fun hgs ↦ hγ ⟨pre.1, hE.1 _ rfl, hgs⟩, hacc⟩
    · rw [if_neg hacc] at hfb
      exact absurd hfb (by simp)
  case hoa =>
    let post : ((pSpec (ι := ι) (F := F) k t).FullTranscript ×
        (OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness) →
      Option ((Statement (F := F) k × (∀ i, OracleStatement ι A i)) ×
        Option (Witness (F := F) k) ×
        (OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness) :=
      fun r ↦
        if Accepts (k := k) (t := t)
              (encode : (Fin k → F) → (ι → A))
              stmt oStmt (r.1.challenges ⟨0, rfl⟩)
              (r.1.messages ⟨1, rfl⟩) (r.1.challenges ⟨2, rfl⟩)
        then some ((stmt, oStmt),
          some (transition (stmt, oStmt)
            (r.1.challenges ⟨0, rfl⟩) (r.1.messages ⟨1, rfl⟩)),
          (((), nofun) : OutputStatement × ∀ i, OutputOracleStatement i), r.2.2)
        else none
    refine Eq.trans ?hA (Eq.trans (loggingOracle.map_fst_run_simulateQ
      (Prover.run (stmt, oStmt) witIn prover) post) ?hC)
    case hA =>
      simp only [Reduction.runWithLog, Prover.runWithLog, pure_bind, bind_assoc]
      simp_rw [verifier_run_loggingOracle_eq
        (encode := (encode : (Fin k → F) → (ι → A)))]
      simp only [liftM_pure, pure_bind]
      simp only [transitionStraightlineExtractor, OptionT.liftM_def, bind_pure_comp]
      simp only [OptionT.run_bind, OptionT.run_lift, OptionT.run_map,
        OptionT.run_pure, bind_pure_comp]
      simp only [Option.getM, Option.elimM]
      simp only [bind_map_left, Option.elim_some]
      rw [map_eq_bind_pure_comp]
      apply bind_congr
      intro x
      simp only [Function.comp]
      split_ifs with h
      · change (pure (some ((stmt, oStmt),
            some (transition (stmt, oStmt)
              (x.1.1.challenges ⟨0, rfl⟩) (x.1.1.messages ⟨1, rfl⟩)),
            (((), nofun) : OutputStatement × ∀ i, OutputOracleStatement i),
            x.1.2.2)) : OracleComp
              ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ) _) =
            pure (post x.1)
        simp only [post, h, if_true]
      · simp only [Option.elim_none, OptionT.run_failure, pure_bind]
        change (pure none : OracleComp
          ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ) _) =
            pure (post x.1)
        simp only [post, h, if_false]
    case hC =>
      refine (prover_run_map_eq prover (stmt, oStmt) witIn
        (fun c m xs out ↦
          if Accepts (k := k) (t := t)
            ((encode : (Fin k → F) → (ι → A))) stmt oStmt c m xs
          then some ((stmt, oStmt), some (transition (stmt, oStmt) c m),
            (((), nofun) : OutputStatement × ∀ i, OutputOracleStatement i), out.2)
          else none)).trans ?_
      simp only [bind_assoc, map_eq_bind_pure_comp, Function.comp_def]

/-! ## Direct bridge for the Definition 6.11 winning-set quantity

This bridge intentionally uses the generic classical selector `chooseRelaxedWitness`.
The executable IRS theorem is separate and uses the distinct
`certifiedExtractorError` interface. -/

omit [DecidableEq ι] in
/-- Proof-side transition which ignores the transcript and chooses a relaxed
input witness when one exists.  This is noncomputable and is not an executable
extractor claim. -/
noncomputable def choiceTransition {k : ℕ}
    (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0) :
    (Statement (F := F) k × (∀ i, OracleStatement ι A i)) →
      F → (Fin k → F) → Witness (F := F) k :=
  fun stmtIn _ _ ↦ chooseRelaxedWitness k encode δ stmtIn

omit [DecidableEq ι] in
/-- Straightline wrapper around `choiceTransition`.  Its name and docstring
make the proof-side classical choice explicit. -/
noncomputable def choiceStraightlineExtractor {k t : ℕ}
    (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0) :
    Extractor.Straightline []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i))
      (Witness (F := F) k) OutputWitness
      (pSpec (ι := ι) (F := F) k t) :=
  transitionStraightlineExtractor (choiceTransition encode δ)

omit [DecidableEq ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- The choice transition's bad combination-round event is bounded by the
actual Definition-6.11 winning-set soundness. -/
theorem choiceTransition_failure_sample_le {k : ℕ}
    [SampleableType F]
    (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)) :
    Pr[fun γ : F ↦ ∃ g : Fin k → F,
        (stmtIn, choiceTransition
          (encode : (Fin k → F) → (ι → A)) δ stmtIn γ g) ∉
            outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ ∧
          GammaState k (encode : (Fin k → F) → (ι → A)) δ
            stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
            (stmtIn.2 0) (stmtIn.2 1) γ g
      | $ᵗ F] ≤ (winningSetDensity encode δ : ENNReal) := by
  classical
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  by_cases hw : ∃ M,
      (stmtIn, M) ∈ outputRelationFor k
        (encode : (Fin k → F) → (ι → A)) δ
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le
    intro γ hbad
    obtain ⟨g, hnot, _⟩ := hbad
    exact hnot (chooseRelaxedWitness_mem k hw)
  · have hviol : ¬ RelaxedRelationFor (ℓ := 2) encode δ
        stmtIn.1.1 ![stmtIn.1.2.1, stmtIn.1.2.2]
        ![stmtIn.2 0, stmtIn.2 1] := by
      rintro ⟨Wstar, ⟨M, hWeq, hlin⟩, S, hScard, hagree⟩
      apply hw
      refine ⟨M, hlin, S, hScard, fun i j hj ↦ ?_⟩
      fin_cases i
      · simpa [hWeq 0] using hagree 0 j hj
      · simpa [hWeq 1] using hagree 1 j hj
    let x : ViolatingInstance encode δ :=
      ⟨stmtIn.1.1, stmtIn.1.2.1, stmtIn.1.2.2,
        stmtIn.2 0, stmtIn.2 1, hviol⟩
    have hbad : (fun γ : F ↦ ∃ g : Fin k → F,
        (stmtIn, choiceTransition
          (encode : (Fin k → F) → (ι → A)) δ stmtIn γ g) ∉
            outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ ∧
          GammaState k (encode : (Fin k → F) → (ι → A)) δ
            stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
            (stmtIn.2 0) (stmtIn.2 1) γ g) =
        GammaEvent encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
          (stmtIn.2 0) (stmtIn.2 1) := by
      funext γ
      apply propext
      constructor
      · rintro ⟨g, _, hstate⟩
        exact ⟨g, hstate⟩
      · rintro ⟨g, hstate⟩
        exact ⟨g, fun hmem ↦ hw ⟨_, hmem⟩, hstate⟩
    have hWin : winningSetFor encode δ stmtIn.1.1
        stmtIn.1.2.1 stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) =
        {γ : F | GammaEvent encode δ stmtIn.1.1
          stmtIn.1.2.1 stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) γ} := by
      ext γ
      constructor
      · rintro ⟨Wstar, ⟨M, hWeq, hlin⟩, S, hScard, hagree⟩
        refine ⟨M 0, by simpa using hlin 0, S, hScard, fun j hj ↦ ?_⟩
        have h := hagree 0 j hj
        rw [hWeq 0] at h
        simpa using h
      · rintro ⟨m, hlin, S, hScard, hagree⟩
        exact ⟨fun _ ↦ encode m,
          ⟨fun _ ↦ m, fun _ ↦ rfl, fun _ ↦ by simpa using hlin⟩,
          S, hScard, fun i j hj ↦ by simpa using hagree j hj⟩
    refine le_trans (Pr_le_Pr_of_implies ($ᵖ F) _
      (GammaEvent encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1))
      (fun γ h ↦ Eq.mp (congrFun hbad γ) h)) ?_
    calc
      Pr_{let γ ← $ᵖ F}[GammaEvent encode δ stmtIn.1.1
          stmtIn.1.2.1 stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) γ] =
          (winningSetRatio x : ENNReal) := by
        rw [prob_uniform_eq_card_filter_div_card, winningSetRatio, hWin,
          Set.ncard_eq_toFinset_card',
        Set.toFinset_setOf,
        ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
        ENNReal.coe_natCast, ENNReal.coe_natCast]
      _ ≤ (winningSetDensity encode δ : ENNReal) := by
        exact_mod_cast winningSetRatio_le_winningSetDensity x

/-- Direct simplified-IOR game theorem at the worst-case winning-set density.

This is the protocol-level upper coupling missing from the bare combinatorial
definition: the classical proof-side transition extractor fails with
probability at most `winningSetDensity encode δ`.  It does not assert the
separate optimal-adversary/lower-coupling result that would identify this
quantity as the minimal achievable game error. -/
theorem simplifiedOracleVerifier_knowledgeSoundnessWith_choiceTransition
    {k : ℕ} [SampleableType F]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) :
    (SimplifiedIOR.oracleVerifier (ι := ι) (F := F) (A := A)
      (k := k)).knowledgeSoundnessWith
      (WitOut := SimplifiedIOR.OutputWitness (F := F) k)
      init impl
      (outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
      (SimplifiedIOR.outputRelationFor k
        (encode : (Fin k → F) → (ι → A)) δ)
      (SimplifiedIOR.transitionStraightlineExtractor k
        (choiceTransition (encode : (Fin k → F) → (ι → A)) δ))
      (winningSetDensity encode δ) := by
  apply SimplifiedIOR.knowledgeSoundnessWith_of_transition_failure_prob_le
  exact choiceTransition_failure_sample_le encode δ

omit [DecidableEq ι] [Fintype A] in
/-- Direct fixed-radius game theorem for the winning-set/spot-check upper bound. The theorem
type names the classical `choiceStraightlineExtractor`; executable IRS clients
should use the certified theorem in `Impl.IRS` instead. -/
theorem oracleVerifier_knowledgeSoundnessWith_choiceStraightlineExtractor
    {k t : ℕ} [SampleableType F] [SampleableType ι] [Nonempty ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) :
    (oracleVerifier (k := k) (t := t)
      (encode : (Fin k → F) → (ι → A))).knowledgeSoundnessWith
      (WitOut := OutputWitness) init impl
      (outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) ×
        OutputWitness))
      (choiceStraightlineExtractor
        (t := t) (encode : (Fin k → F) → (ι → A)) δ)
      (winningSetUpperBound encode δ t) := by
  apply oracleVerifier_knowledgeSoundnessWith_of_transition_failure_prob_le
    init impl δ (winningSetDensity encode δ) encode
      (choiceTransition (encode : (Fin k → F) → (ι → A)) δ)
      (choiceStraightlineExtractor
        (t := t) (encode : (Fin k → F) → (ι → A)) δ) rfl
  exact choiceTransition_failure_sample_le encode δ

omit [DecidableEq ι] [Fintype A] in
/-- Existential knowledge soundness for the winning-set/spot-check upper bound, retained as
a corollary of the theorem naming the classical extractor.

**Consumer note on `δ`.**  No hypothesis constrains `δ` here, and that is sound: the error
`winningSetUpperBound encode δ t` is the winning-set/spot-check expression at
whatever `δ` is supplied, so the statement is true at every radius.  It is only *meaningful*
for `δ ∈ (0, d_min(C))`; outside that band the relaxed output relation degenerates and the
bound, while true, certifies nothing useful.  The step that does need the band is the bridge
to the certified error, `winningSetDensity_le_certifiedGammaError`, whose `hδ` hypothesis is
exactly `δ ∈ Set.Ioo 0 (minRelHammingDistCode …)`; the executable IRS contracts in
`Impl/IRS.lean`
carry it as an explicit argument. -/
theorem oracleVerifier_knowledgeSoundness_winningSetUpperBound {k t : ℕ}
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) :
    (oracleVerifier (k := k) (t := t)
      (encode : (Fin k → F) → (ι → A))).knowledgeSoundness
      (WitOut := OutputWitness) init impl
      (outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) ×
        OutputWitness))
      (winningSetUpperBound encode δ t) :=
  OracleVerifier.knowledgeSoundness_of_with init impl
    (oracleVerifier_knowledgeSoundnessWith_choiceStraightlineExtractor
      init impl encode δ)

end ToyProblem.Spec
