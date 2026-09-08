/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Logup.Security.Soundness.Lemmas

/-!
# LogUp Soundness

Soundness target for the LogUp lookup argument (Cryptology ePrint Archive, Paper 2022/1530,
<https://eprint.iacr.org/2022/1530>).

The protocol verifier is the sequential composition of three phases (outer LogUp, embedded
sumcheck, final point check), so its soundness error decomposes as a sum of one error per phase.
We bound each phase separately and combine them with `OracleVerifier.append_soundness`, which
turns the soundness of a composed verifier into the sum of the parts' errors.

The paper's Theorem 4 presents the bound as `ε₁ + ε₂ + ε₃ + εsumcheck`, grouped by the
mathematical bad events.  The formal proof below instead groups errors by the verifier phase that
samples each challenge.  The random Lagrange-kernel point is sampled in the outer phase, so the
error for hiding a nonzero domain identity is charged to the outer phase here.  Following
Remark 3, this verifier also samples the outer challenge `x` from all of `F`, so the outer bound
separately pays for the chance that `x` hits a denominator pole.
-/

open scoped NNReal BigOperators

namespace Logup

section Soundness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-! ## Outer Phase Soundness

The outer phase samples the `x`, `z`, and batching challenges and turns a false lookup statement
into a nonzero outer sumcheck claim except with the error budget `logupOuterSoundnessError`. -/

section

omit [DecidableEq F]
/-- Soundness of the outer LogUp phase, with the conservative error `logupOuterSoundnessError`.

The hypothesis `hcard : |H| < |F|` is retained from the paper-shaped statement; the current formal
bound itself is an unconditional union bound over occurrence poles, cleared-identity roots, bad
`z`, and bad batching scalars. -/
theorem logup_outer_soundness
    (hcard : Fintype.card (Fin n → Fin 2) < Fintype.card F) :
    (outerVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language (logupMidRelation F n M params).language
      (logupOuterSoundnessError F n M params) := by
  classical
  letI : DecidableEq F := Classical.decEq F
  exact logup_outer_soundness_from_local_algebra
    (oSpec := oSpec) (F := F) (n := n) (M := M) (params := params)
    (init := init) (impl := impl) hcard
    (fun stmt oStmt multiplicity hnot =>
      clearedLookupIdentity_ne_zero_of_not_input (F := F) (n := n) (M := M)
        stmt oStmt multiplicity hnot)
    (fun table columns multiplicity =>
      clearedLookupIdentity_natDegree_le (F := F) (n := n) (M := M)
        table columns multiplicity)
    (fun table columns multiplicity hpoly =>
      clearedLookupIdentity_bad_x_card_le (F := F) (n := n) (M := M)
        table columns multiplicity hpoly)
    (fun K c₀ c hNonzero => random_linear_batch_zero_prob_le (F := F) K c₀ c hNonzero)

end

/-! ## Sumcheck Phase Soundness

The embedded sumcheck phase is ArkLib's generic sumcheck verifier lifted through the LogUp context
lens.  The helper lemmas in this section preserve the oracle statement through that lift and allow
the generic sumcheck soundness bound to be widened to the requested error. -/

section

omit [Fintype F]
private theorem sumcheckVerifier_compat_oracleStmt
    {outerStmt : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)}
    {innerStmtOut : Sumcheck.Spec.StatementRound F n (Fin.last n) ×
      (∀ i, Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params) i)}
    (hCompat :
      Verifier.compatStatement (logupSumcheckContextLens F n M params).stmt
        (logupConcreteSumcheckOracleReduction oSpec F n M params).verifier.toVerifier
        outerStmt innerStmtOut) :
    innerStmtOut.2 = logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2 := by
  rcases hCompat with ⟨tr, htr⟩
  have hrun : innerStmtOut ∈ support
      ((Sumcheck.Spec.verifier F (logupSumcheckDegree M params) (booleanDomain F) n oSpec).run
        (logupInitialSumcheckStatement F n,
          logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2) tr) := by
    rw [logupConcreteSumcheckOracleReduction,
      Sumcheck.Spec.oracleReduction_toReduction_verifier_eq_verifier] at htr
    change innerStmtOut ∈ support
      ((Sumcheck.Spec.verifier F (logupSumcheckDegree M params) (booleanDomain F) n oSpec).run
        (logupInitialSumcheckStatement F n,
          logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2) tr) at htr
    exact htr
  exact Sumcheck.Spec.verifier_preserves_oracleStmt F (logupSumcheckDegree M params)
    (booleanDomain F) n oSpec hrun

end

private instance logupSumcheckLensSound :
    (logupSumcheckContextLens F n M params).stmt.IsSound
      (logupMidRelation F n M params).language
      (logupAfterSumcheckRelation F n M params).language
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F) 0).language
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
        (Fin.last n)).language
      (Verifier.compatStatement (logupSumcheckContextLens F n M params).stmt
        (logupConcreteSumcheckOracleReduction oSpec F n M params).verifier.toVerifier) where
  proj_sound := by
    rintro ⟨stmt, oStmt⟩ hOuter hInner
    simp only [Set.mem_language_iff] at hInner
    rcases hInner with ⟨w, hInner⟩
    cases w
    apply hOuter
    simp only [Set.mem_language_iff]
    refine ⟨(), ?_⟩
    unfold logupMidRelation
    simp only [Set.mem_setOf_eq]
    exact (logupSumcheckRelationInput_iff (F := F) (n := n) (M := M)
      (params := params)).mp hInner
  lift_sound := by
    intro outerStmt innerStmtOut hCompat hInner hOuter
    simp only [Set.mem_language_iff] at hInner hOuter
    rcases hOuter with ⟨w, hOuter⟩
    cases w
    have hOStmt :
        innerStmtOut.2 = logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2 := by
      exact sumcheckVerifier_compat_oracleStmt (oSpec := oSpec) (F := F) (n := n) (M := M)
        (params := params) hCompat
    apply hInner
    refine ⟨(), ?_⟩
    have hPair :
        (innerStmtOut.1, logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2) =
          innerStmtOut := by
      cases innerStmtOut
      simpa using hOStmt.symm
    simpa [hPair, logupSumcheckContextLens, logupAfterSumcheckRelation] using hOuter

section

omit [Fintype F] [DecidableEq F]
private theorem OracleVerifier.soundness_mono
    {V : OracleVerifier oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params)
      (StmtAfterSumcheck F n M params) (OStmtAfterOuter F n M params)
      (Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n)}
    {langIn : Set (StmtAfterOuter F n M params × ∀ i, OStmtAfterOuter F n M params i)}
    {langOut : Set (StmtAfterSumcheck F n M params × ∀ i, OStmtAfterOuter F n M params i)}
    {e₁ e₂ : ℝ≥0}
    (h : V.soundness init impl langIn langOut e₁) (hle : e₁ ≤ e₂) :
    V.soundness init impl langIn langOut e₂ := by
  unfold OracleVerifier.soundness Verifier.soundness at h ⊢
  intro WitIn WitOut witIn prover stmtIn hstmt
  exact le_trans (h WitIn WitOut witIn prover stmtIn hstmt) (by exact_mod_cast hle)

end

/-- Soundness of the embedded sumcheck phase, with error `sumcheckSoundnessError`.

This is the soundness of ArkLib's generic sumcheck reduction lifted through the LogUp context lens;
the bound `sumcheckSoundnessError` is supplied by the generic sumcheck soundness result. -/
theorem logup_sumcheck_soundness (sumcheckSoundnessError : ℝ≥0)
    (hSumcheckSoundness :
      logupSumcheckSoundnessError F n M params ≤ sumcheckSoundnessError) :
    (sumcheckVerifier oSpec F n M params).soundness init impl
      (logupMidRelation F n M params).language
      (logupAfterSumcheckRelation F n M params).language
      sumcheckSoundnessError := by
  classical
  letI : Inhabited F := ⟨0⟩
  letI : Inhabited (Sumcheck.Spec.StatementRound F n (Fin.last n)) :=
    ⟨{ target := 0, challenges := fun _ => 0 }⟩
  let rbrErr :
      (Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n).ChallengeIdx → ℝ≥0 :=
    fun _ => ((logupSumcheckDegree M params : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)
  have hKS :
      (logupConcreteSumcheckOracleReduction oSpec F n M params).verifier.rbrKnowledgeSoundness
        init impl
        (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F) 0)
        (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
          (Fin.last n))
        rbrErr := by
    simpa [logupConcreteSumcheckOracleReduction, rbrErr] using
      (Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness
        (R := F) (deg := logupSumcheckDegree M params) (D := booleanDomain F)
        (n := n) (oSpec := oSpec) (init := init) (impl := impl))
  have hRbrInner :
      (logupConcreteSumcheckOracleReduction oSpec F n M params).verifier.rbrSoundness
        init impl
        (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
          0).language
        (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
          (Fin.last n)).language
        rbrErr := by
    unfold OracleVerifier.rbrKnowledgeSoundness at hKS
    unfold OracleVerifier.rbrSoundness
    exact Verifier.rbrKnowledgeSoundness_implies_rbrSoundness
      (init := init) (impl := impl) (h := hKS)
  have hRbrLift :
      (sumcheckVerifier oSpec F n M params).rbrSoundness init impl
        (logupMidRelation F n M params).language
        (logupAfterSumcheckRelation F n M params).language
        rbrErr := by
    simpa [sumcheckVerifier] using
      (OracleVerifier.liftContext_rbr_soundness
        (init := init) (impl := impl)
        (V := (logupConcreteSumcheckOracleReduction oSpec F n M params).verifier)
        (lens := (logupSumcheckContextLens F n M params).stmt)
        hRbrInner)
  have hSoundConcrete :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (logupMidRelation F n M params).language
        (logupAfterSumcheckRelation F n M params).language
        (logupSumcheckSoundnessError F n M params) := by
    unfold OracleVerifier.rbrSoundness at hRbrLift
    unfold OracleVerifier.soundness
    have hSound :=
      Verifier.rbrSoundness_implies_soundness
        (init := init) (impl := impl)
        ((logupMidRelation F n M params).language)
        ((logupAfterSumcheckRelation F n M params).language)
        ((sumcheckVerifier oSpec F n M params).toVerifier)
        rbrErr hRbrLift
    convert hSound using 1
    simp [logupSumcheckSoundnessError, rbrErr]
  exact OracleVerifier.soundness_mono (oSpec := oSpec) (F := F) (n := n) (M := M)
    (params := params) (init := init) (impl := impl) hSoundConcrete hSumcheckSoundness

/-! ## Final-Check Phase Soundness

The final check is deterministic: if the retained sumcheck final claim is not in the post-sumcheck
language, the reconstructed value `qAtPoint` disagrees with the claimed target and the verifier
rejects. -/

omit [SampleableType F] [Fintype F] in
/-- Soundness of the deterministic final LogUp point check with zero phase error. -/
theorem logup_finalCheck_soundness :
    (finalCheckVerifier oSpec F n M params).soundness init impl
      (logupAfterSumcheckRelation F n M params).language
      outputRelation.language
      (logupFinalCheckSoundnessError) := by
  classical
  unfold OracleVerifier.soundness Verifier.soundness
  intro WitIn WitOut witIn prover stmtPair hstmt
  obtain ⟨stmt, oStmt⟩ := stmtPair
  -- The final point check is deterministic (`finalCheckPSpec = ProtocolSpec 0`): the verifier just
  -- queries the retained oracles at `r` and runs one guard. For inputs outside the language that
  -- guard fails, so the verifier rejects and the soundness probability is `0`.
  -- Step 1: the guard `qAtPoint(…) = target` fails on `(stmt, oStmt) ∉ language`.
  have hNe : MvPolynomial.eval stmt.finalClaim.challenges
        (logupQPolynomial (params.group) (oStmt (.input .table)).1
          (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
          (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
          stmt.outer.batchingScalars) ≠ stmt.finalClaim.target := by
    rw [Set.mem_language_iff, not_exists] at hstmt
    intro he
    refine hstmt () ?_
    show ((stmt, oStmt), ()) ∈ logupAfterSumcheckRelation F n M params
    change ((stmt.finalClaim, logupSumcheckOracleStmt F n M params stmt.outer oStmt), ()) ∈
      Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
        (Fin.last n)
    refine (Sumcheck.Spec.relationRound_last_iff
      (R := F) (n := n) (deg := logupSumcheckDegree M params) (D := booleanDomain F)
      (stmt := stmt.finalClaim)
      (polyOracle := logupSumcheckOracleStmt F n M params stmt.outer oStmt)).2 ?_
    change MvPolynomial.eval stmt.finalClaim.challenges
        (logupQPolynomial (params.group) (oStmt (.input .table)).1
          (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
          (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
          stmt.outer.batchingScalars) =
      stmt.finalClaim.target
    exact he
  -- Step 2: rephrase the guard failure in terms of the oracle answers the verifier reads.
  have hGuardFail : qAtPoint (params.group) stmt.outer.xChallenge stmt.outer.zChallenge
        stmt.finalClaim.challenges stmt.outer.batchingScalars
        (MvPolynomial.eval stmt.finalClaim.challenges (oStmt .multiplicity).1)
        (MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input .table)).1)
        (fun i => MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input (.column i))).1)
        (fun k => MvPolynomial.eval stmt.finalClaim.challenges (oStmt .helpers k).1) ≠
      stmt.finalClaim.target := by
    intro hEq
    exact hNe ((logupQPolynomial_eval_point (params.group) (oStmt (.input .table)).1
      (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
      (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
      stmt.finalClaim.challenges stmt.outer.batchingScalars).trans hEq)
  -- Step 3: the verifier rejects (`finalCheckPSpec` has no messages, and `verify` ignores its
  -- empty challenges), so `simulateQ` of the verification computation is `pure none`.
  let qImpl :
      QueryImpl
        (oSpec + ([OStmtAfterOuter F n M params]ₒ + [finalCheckPSpec.Message]ₒ))
        (OracleComp oSpec) :=
    OracleInterface.simOracle2.{0, 0, 0} (T₁ := OStmtAfterOuter F n M params)
      (T₂ := finalCheckPSpec.Message) oSpec oStmt
      (fun i : finalCheckPSpec.MessageIdx => Fin.elim0 i)
  have hquery :
      ∀ (i : OuterOracleIdx M)
        (q : (instOStmtAfterOuterOracleInterface (F := F) (n := n) (params := params) i).Query),
        simulateQ qImpl ((finalCheckQuery oSpec F n M params i q).run) =
          (pure (some ((instOStmtAfterOuterOracleInterface
            (F := F) (n := n) (params := params) i).answer (oStmt i) q)) :
            OracleComp oSpec _) := by
    intro i q
    simp only [finalCheckQuery, OptionT.run_mk, simulateQ_map, qImpl,
      OracleInterface.simOracle2, QueryImpl.addLift_def, simulateQ_query,
      QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply, QueryImpl.add,
      OracleInterface.simOracle0, OracleInterface.answer, OracleQuery.cont_query,
      OracleQuery.input_query]
    change some <$> id <$>
        (pure (ReaderT.run (OracleInterface.toOC.impl q) (oStmt i)) :
          OracleComp oSpec _) =
      (pure (some (ReaderT.run (OracleInterface.toOC.impl q) (oStmt i))) :
        OracleComp oSpec _)
    simp
  let colValue := fun i : Fin M =>
    MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input (.column i))).1
  let helperValue := fun k : Fin params.numGroups =>
    MvPolynomial.eval stmt.finalClaim.challenges (oStmt .helpers k).1
  have hcolAnswer : ∀ i : Fin M,
      ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
          (oStmt (.input (.column i))) =
        colValue i := fun _ => rfl
  have hhelperAnswer : ∀ k : Fin params.numGroups,
      ReaderT.run (OracleInterface.toOC.impl
          (show OracleInterface.Query (OStmtAfterOuter F n M params .helpers) from
            ⟨k, stmt.finalClaim.challenges⟩))
          (oStmt .helpers) =
        helperValue k := fun _ => rfl
  have hmultAnswer :
      ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
          (oStmt .multiplicity) =
        MvPolynomial.eval stmt.finalClaim.challenges (oStmt .multiplicity).1 := rfl
  have htableAnswer :
      ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
          (oStmt (.input .table)) =
        MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input .table)).1 := rfl
  have hGuardFail' :
      qAtPoint (params.group) stmt.outer.xChallenge stmt.outer.zChallenge
          stmt.finalClaim.challenges stmt.outer.batchingScalars
          (ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
            (oStmt .multiplicity))
          (ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
            (oStmt (.input .table)))
          colValue helperValue ≠
        stmt.finalClaim.target := by
    simpa [hmultAnswer, htableAnswer, colValue, helperValue] using hGuardFail
  have hGuardFailAnswer :
      qAtPoint (params.group) stmt.outer.xChallenge stmt.outer.zChallenge
          stmt.finalClaim.challenges stmt.outer.batchingScalars
          (OracleInterface.answer (oStmt .multiplicity) stmt.finalClaim.challenges)
          (OracleInterface.answer (oStmt (.input .table)) stmt.finalClaim.challenges)
          colValue helperValue ≠
        stmt.finalClaim.target := by
    simpa [OracleInterface.answer] using hGuardFail'
  have hVerifyNone :
      simulateQ qImpl
          ((finalCheckVerifier oSpec F n M params).verify stmt (fun i => Fin.elim0 i)).run =
        (pure none : OracleComp oSpec (Option StmtOut)) := by
    simp only [finalCheckVerifier, OptionT.run_bind, OptionT.run_pure]
    erw [simulateQ_bind]
    rw [hquery .multiplicity stmt.finalClaim.challenges]
    simp only [pure_bind, Option.elim_some]
    erw [simulateQ_bind]
    rw [hquery (.input .table) stmt.finalClaim.challenges]
    simp only [pure_bind, Option.elim_some]
    have hcols := simulateQ_optionT_vector_mapM_pure qImpl
      (fun i : Fin M =>
        finalCheckQuery oSpec F n M params (.input (.column i)) stmt.finalClaim.challenges)
      colValue (Vector.finRange M) (by
        intro i
        change simulateQ qImpl
            ((finalCheckQuery oSpec F n M params (.input (.column i))
              stmt.finalClaim.challenges).run) =
          (pure (some (colValue i)) : OracleComp oSpec (Option F))
        rw [hquery (.input (.column i)) stmt.finalClaim.challenges]
        change (pure (some
          (ReaderT.run (OracleInterface.toOC.impl stmt.finalClaim.challenges)
            (oStmt (.input (.column i)))))) =
          (pure (some (colValue i)) : OracleComp oSpec (Option F))
        rw [hcolAnswer]
        rfl)
    erw [simulateQ_option_elimM]
    erw [hcols]
    simp only [pure_bind, Option.elimM, Option.elim_some]
    have hhelpers := simulateQ_optionT_vector_mapM_pure qImpl
      (fun k : Fin params.numGroups =>
        finalCheckQuery oSpec F n M params .helpers ⟨k, stmt.finalClaim.challenges⟩)
      helperValue (Vector.finRange params.numGroups) (by
        intro k
        change simulateQ qImpl
            ((finalCheckQuery oSpec F n M params .helpers
              ⟨k, stmt.finalClaim.challenges⟩).run) =
          (pure (some (helperValue k)) : OracleComp oSpec (Option F))
        rw [hquery .helpers ⟨k, stmt.finalClaim.challenges⟩]
        change (pure (some
          (ReaderT.run (OracleInterface.toOC.impl
            (show OracleInterface.Query (OStmtAfterOuter F n M params .helpers) from
              ⟨k, stmt.finalClaim.challenges⟩))
            (oStmt .helpers)))) =
          (pure (some (helperValue k)) : OracleComp oSpec (Option F))
        rw [hhelperAnswer]
        rfl)
    erw [simulateQ_option_elimM]
    erw [hhelpers]
    simp only [pure_bind, Option.elimM, Option.elim_some]
    erw [simulateQ_option_elimM]
    simp [guard, hGuardFailAnswer, Option.elimM]
  -- Step 4: the verifier rejects for every transcript (the empty one), so the `toVerifier`
  -- verification computation is `pure none`.
  have hRejectRun :
      ∀ t : finalCheckPSpec.FullTranscript,
        OptionT.run
            ((finalCheckVerifier oSpec F n M params).toVerifier.verify ⟨stmt, oStmt⟩ t) =
          (pure none : OracleComp oSpec (Option (StmtOut × (∀ i, OStmtOut i)))) := by
    intro t
    obtain rfl : t = default := Unique.eq_default t
    simp only [OracleVerifier.toVerifier, OptionT.run_bind]
    have hInner :
        simulateQ
            (OracleInterface.simOracle2 oSpec oStmt
              (ProtocolSpec.FullTranscript.messages
                (default : finalCheckPSpec.FullTranscript)))
            (((finalCheckVerifier oSpec F n M params).verify stmt
              (ProtocolSpec.FullTranscript.challenges
                (default : finalCheckPSpec.FullTranscript))).run) =
          (pure none : OracleComp oSpec (Option StmtOut)) := by
      change simulateQ qImpl
          (((finalCheckVerifier oSpec F n M params).verify stmt (fun i => Fin.elim0 i)).run) =
        (pure none : OracleComp oSpec (Option StmtOut))
      exact hVerifyNone
    have hInnerT :
        OptionT.run
          (simulateQ
            (OracleInterface.simOracle2 oSpec oStmt
              (ProtocolSpec.FullTranscript.messages default))
            ((finalCheckVerifier oSpec F n M params).verify stmt
              (ProtocolSpec.FullTranscript.challenges default))) =
          (pure none : OracleComp oSpec (Option StmtOut)) := by
      change simulateQ
          (OracleInterface.simOracle2 oSpec oStmt
            (ProtocolSpec.FullTranscript.messages (default : finalCheckPSpec.FullTranscript)))
          (((finalCheckVerifier oSpec F n M params).verify stmt
            (ProtocolSpec.FullTranscript.challenges
              (default : finalCheckPSpec.FullTranscript))).run) =
        (pure none : OracleComp oSpec (Option StmtOut))
      exact hInner
    erw [hInnerT]
    simp
  -- Step 5: with the verifier rejecting, the whole reduction never produces output, so its run
  -- is always `none` and the soundness event has probability `0 ≤ bound`.
  refine le_trans (le_of_eq ?_) (zero_le)
  refine probEvent_eq_zero (fun x hx => ?_)
  exfalso
  rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
  simp only [support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, -, hx⟩ := hx
  have hrunNone :
      OptionT.run
          ((Reduction.mk prover (finalCheckVerifier oSpec F n M params).toVerifier).run
            ⟨stmt, oStmt⟩ witIn) =
        ((fun _ => none) <$> prover.run ⟨stmt, oStmt⟩ witIn) := by
    simp only [Reduction.run, Verifier.run, map_eq_bind_pure_comp, OptionT.run_bind,
      OptionT.run_monadLift, monadLift_self, Option.getM, Option.elimM, bind_assoc]
    refine bind_congr fun pr => ?_
    simp only [Function.comp_apply, pure_bind, Option.elim_some]
    rw [hRejectRun pr.1]
    simp
  rw [hrunNone, simulateQ_map] at hx
  simp only [StateT.run'_map', support_map, Set.mem_image] at hx
  obtain ⟨_, _, hx⟩ := hx
  cases hx

/-! ## Composed LogUp Soundness

The full verifier is the sequential composition of the outer phase, the embedded sumcheck phase,
and the final check.  The composed soundness error is the sum of the per-phase errors. -/

/-- Main ArkLib soundness theorem for the LogUp protocol.

Obtained by composing the three per-phase soundness lemmas with `OracleVerifier.append_soundness`,
following the protocol's `outer ++ sumcheck ++ finalCheck` structure: the total error is the sum
of the three per-phase errors. -/
theorem logup_soundness (sumcheckSoundnessError : ℝ≥0)
    (hSumcheckSoundness :
      logupSumcheckSoundnessError F n M params ≤ sumcheckSoundnessError)
    (hcard : Fintype.card (Fin n → Fin 2) < Fintype.card F) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) := by
  unfold logupVerifier logupSoundnessError
  refine OracleVerifier.append_soundness.{0, 0, 0, 0}
    (lang₂ := (logupAfterSumcheckRelation F n M params).language) _ _
    (OracleVerifier.append_soundness
      (lang₂ := (logupMidRelation F n M params).language) _ _ ?_ ?_) ?_
  · exact logup_outer_soundness oSpec F n M params init impl hcard
  · exact logup_sumcheck_soundness oSpec F n M params init impl sumcheckSoundnessError
      hSumcheckSoundness
  · exact logup_finalCheck_soundness oSpec F n M params init impl

end Soundness

end Logup
