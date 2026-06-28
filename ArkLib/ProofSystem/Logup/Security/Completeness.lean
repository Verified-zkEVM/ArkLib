import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.ProofSystem.Logup.Protocol
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec

/-!
# LogUp Completeness

Completeness statements for Protocol 2 of Haböck's LogUp lookup argument (Cryptology ePrint
Archive, Paper 2022/1530, <https://eprint.iacr.org/2022/1530>).
-/

open scoped NNReal

namespace Logup

section ProtocolAlgebra

variable {F : Type} [Field F] {M : ℕ}

/-- The protocol's concrete partial-sum groups partition the term indices `{0, …, M}`. -/
theorem sum_protocolGroups (params : ProtocolParams M) (g : TermIdx M → F) :
    (∑ k : Fin params.numGroups, ∑ i ∈ params.group k, g i) = ∑ i : TermIdx M, g i := by
  classical
  have hℓ := params.sumSize_pos
  have hidx : ∀ i : TermIdx M, i.val / params.sumSize < params.numGroups := by
    intro i
    have hiM : i.val ≤ M := Nat.lt_succ_iff.mp i.isLt
    have hle : i.val / params.sumSize ≤ M / params.sumSize := Nat.div_le_div_right hiM
    rw [ProtocolParams.numGroups, Nat.add_div_right _ hℓ]
    omega
  rw [← Finset.sum_fiberwise Finset.univ
      (fun i : TermIdx M => (⟨i.val / params.sumSize, hidx i⟩ : Fin params.numGroups)) g]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  ext i
  simp only [ProtocolParams.group, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have ha : k.val ≤ i.val / params.sumSize := (Nat.le_div_iff_mul_le hℓ).mpr h1
    have hb : i.val / params.sumSize < k.val + 1 := (Nat.div_lt_iff_lt_mul hℓ).mpr h2
    omega
  · intro h
    exact ⟨(Nat.le_div_iff_mul_le hℓ).mp (by omega), (Nat.div_lt_iff_lt_mul hℓ).mp (by omega)⟩

end ProtocolAlgebra

section Completeness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instOracleCompLawfulMonad' {τ : Type} (spec : OracleSpec τ) :
    LawfulMonad (OracleComp spec) :=
  OracleComp.instLawfulMonad spec

local instance instOuterChallengeOracleInterface' :
    (i : (outerPSpec F n params).ChallengeIdx) →
      OracleInterface ((outerPSpec F n params).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

omit [Fintype F] [DecidableEq F] [SampleableType F] in
private theorem sum_piFinset_map_univ_eq_sum_hypercube
    (D : Fin 2 ↪ F) (f : (Fin n → F) → F) :
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map D, f x) =
      ∑ u : (Fin n → Fin 2), f (fun j => D (u j)) := by
  let e : (Fin n → Fin 2) ↪ (Fin n → F) := Function.Embedding.arrowCongrRight D
  change (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map D, f x) =
    ∑ u : (Fin n → Fin 2), f (e u)
  rw [← Finset.sum_map]
  congr 1
  ext x
  constructor
  · intro hx
    rw [Fintype.mem_piFinset] at hx
    have hx_coord : ∀ j : Fin n, ∃ b : Fin 2, D b = x j := by
      intro j
      rcases Finset.mem_map.mp (hx j) with ⟨b, _, hb⟩
      exact ⟨b, hb⟩
    let u : (Fin n → Fin 2) := fun j => Classical.choose (hx_coord j)
    exact Finset.mem_map.mpr ⟨u, Finset.mem_univ _, by
      funext j
      exact Classical.choose_spec (hx_coord j)⟩
  · intro hx
    rw [Fintype.mem_piFinset]
    intro j
    rcases Finset.mem_map.mp hx with ⟨u, _, rfl⟩
    exact Finset.mem_map.mpr ⟨u j, Finset.mem_univ _, rfl⟩

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- If LogUp's outer algebra proves a zero sum, then the generic Sumcheck input relation is exactly
the claim sent to Sumcheck. -/
theorem logupSumcheckRelationInput_of_zero
    {stmt : StmtAfterOuter F n M params}
    {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    (hZero : logupOuterSumcheckClaim F n M params stmt oStmt = 0) :
    logupSumcheckRelationInput F n M params stmt oStmt := by
  unfold logupSumcheckRelationInput Sumcheck.Spec.relationRound
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero, logupInitialSumcheckStatement,
    Set.mem_setOf_eq, Fin.elim0_append, logupSumcheckOracleStmt]
  change
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map (booleanDomain F),
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val) = 0
  rw [sum_piFinset_map_univ_eq_sum_hypercube
    (F := F) (n := n) (D := booleanDomain F)
    (f := fun x =>
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val)]
  calc
    (∑ u : (Fin n → Fin 2),
        MvPolynomial.eval
          ((((fun j => (booleanDomain F) (u j)) ∘ Fin.cast (by omega)) ∘
              Fin.cast (by omega)))
          (logupSumcheckPolynomial F n M params stmt oStmt).val)
        =
      logupOuterSumcheckClaim F n M params stmt oStmt := by
        rw [logupOuterSumcheckClaim]
        apply Finset.sum_congr rfl
        intro u _
        simp only [booleanDomain, logupSumcheckPolynomial]
        congr 1
    _ = 0 := hZero

/-- Completeness error from the current `x`-sampling model: the verifier samples `x` from all of
`F`. Following Remark 3 of the LogUp paper, table-pole challenges are treated as bad inputs for
the honest handoff rather than rejected by an exponential verifier scan. -/
noncomputable def logupCompletenessError (F : Type) [Fintype F] (n : ℕ) : ℝ≥0 :=
  (Fintype.card (Fin n → Fin 2) : ℝ≥0) / (Fintype.card F)

omit [DecidableEq F] in
private theorem uniform_avoids_table_poles_prob [Inhabited F]
    (oStmt : ∀ i, OStmtIn F n M i) :
    (1 : ENNReal) - (logupCompletenessError F n : ENNReal) ≤
      Pr[fun x : F => ∀ u : (Fin n → Fin 2),
        x + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0 | $ᵗ F] := by
  classical
  letI : DecidableEq F := Classical.decEq F
  let bad : F → Prop :=
    fun x => ∃ u : (Fin n → Fin 2), x + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u = 0
  have hbad :
      Pr[bad | $ᵗ F] ≤ (logupCompletenessError F n : ENNReal) := by
    rw [probEvent_uniformSample]
    unfold logupCompletenessError
    have hcard :
        ((Finset.univ.filter bad).card : ENNReal) ≤
          (Fintype.card (Fin n → Fin 2) : ENNReal) := by
      exact_mod_cast (by
        simpa [bad] using
          pole_card_le (F := F) (n := n) (table := MvPolynomial.toEvalsZeroOne (oStmt .table).1))
    convert ENNReal.div_le_div_right hcard (Fintype.card F : ENNReal) using 1; norm_num
  have hcompl :
      Pr[fun x : F => ¬ bad x | $ᵗ F] + Pr[bad | $ᵗ F] = (1 : ENNReal) := by
    have h := probEvent_compl ($ᵗ F) (fun x : F => ¬ bad x)
    simpa [bad, probFailure_uniformSample, not_not] using h
  rw [tsub_le_iff_right]
  calc
    (1 : ENNReal) = Pr[fun x : F => ¬ bad x | $ᵗ F] + Pr[bad | $ᵗ F] := hcompl.symm
    _ ≤ Pr[fun x : F => ¬ bad x | $ᵗ F] + (logupCompletenessError F n : ENNReal) :=
        add_le_add le_rfl hbad
  · apply le_of_eq
    congr
    funext x
    simp [bad]

private theorem le_probEvent_bind_of_forall_le {m : Type → Type*} [Monad m] [LawfulMonad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    {α β : Type} {mx : m α} {my : α → m β} {q : β → Prop} {r : ENNReal}
    (hfail : Pr[⊥ | mx] = 0) (h : ∀ x ∈ support mx, r ≤ Pr[ q | my x]) :
    r ≤ Pr[ q | mx >>= my] := by
  have htrue : Pr[fun _ : α => True | mx] = (1 : ENNReal) := by
    exact probEvent_eq_one (mx := mx) (p := fun _ : α => True) ⟨hfail, by simp⟩
  have hmul := mul_le_probEvent_bind (mx := mx) (my := my)
    (p := fun _ : α => True) (q := q) (r := 1) (r' := r)
    (by simp [htrue]) (fun x hx _ => h x hx)
  simpa using hmul

private theorem support_pure_eq {m : Type → Type*} [Monad m] [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {α : Type} {x y : α} (h : y ∈ support (pure x : m α)) : y = x := by
  simpa [mem_support_pure_iff] using h

private theorem support_simulateQ_run_fst_subset {ι : Type} {spec : OracleSpec ι}
    {m : Type → Type*} [Monad m] [LawfulMonad m] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM] {σ α : Type}
    (impl : QueryImpl spec (StateT σ m)) {oa : OracleComp spec α} {s s' : σ} {y : α}
    (h : (y, s') ∈ support ((simulateQ impl oa).run s)) :
    y ∈ support oa :=
  OracleComp.support_simulateQ_run'_subset impl oa s (by
    rw [StateT.run'_eq, support_map, Set.mem_image]
    exact ⟨(y, s'), h, rfl⟩)

private theorem mem_support_liftM_oracleComp {ι τ : Type} {spec : OracleSpec ι}
    {superSpec : OracleSpec τ} {α : Type}
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    {oa : OracleComp spec α} {x : α}
    (h : x ∈ support (liftM oa : OracleComp superSpec α)) : x ∈ support oa := by
  rw [← OracleComp.liftComp_eq_liftM (superSpec := superSpec) oa] at h
  exact OracleComp.mem_support_of_mem_support_liftComp oa x h


private theorem reduction_run_prover_mem {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (tr : pSpec.FullTranscript) (out : StmtOut) (witOut : WitOut) (verOut : StmtOut)
    (h : some ((tr, out, witOut), verOut) ∈ support (R.run stmt wit).run) :
    (tr, out, witOut) ∈ support (Prover.run stmt wit R.prover) := by
  simp only [ProtocolSpec.ChallengeIdx, ProtocolSpec.Challenge, Reduction.run, bind_pure_comp,
    OptionT.run_bind, OptionT.run_monadLift, monadLift_self,
    OracleSpec.ProgrammingPolicy.empty_apply, OptionT.run_map, Option.elimM_map, Option.elim_some,
    support_bind, Set.mem_iUnion, exists_prop, Prod.exists] at h
  rcases h with ⟨a, a_1, b, hp, hv⟩
  suffices hEq : (a, a_1, b) = (tr, out, witOut) by
    simpa [hEq] using hp
  simp only [Option.elimM, support_bind, Set.mem_iUnion, exists_prop] at hv
  rcases hv with ⟨i, _hi, hv⟩
  cases i with
  | none => simp at hv
  | some verCandidate =>
      simp only [Option.elim_some, support_map, Set.mem_image, Option.map_eq_some_iff,
        Prod.mk.injEq, exists_eq_right_right, ↓existsAndEq, true_and] at hv
      rcases hv with ⟨_, rfl, rfl, rfl⟩
      rfl

private theorem seqCompose_prover_preserves {ι : Type} {oSpec : OracleSpec ι} (m : ℕ) :
    ∀ {Stmt : Fin (m + 1) → Type} {O : Type}
      {rounds : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (rounds i)}
      (P : (i : Fin m) → Prover oSpec (Stmt i.castSucc) Unit (Stmt i.succ) Unit (pSpec i))
      (proj : (i : Fin (m + 1)) → Stmt i → O),
      (∀ (i : Fin m) (stmt : Stmt i.castSucc) (out : Stmt i.succ)
          (tr : (pSpec i).FullTranscript),
        (tr, out, ()) ∈ support (Prover.run stmt () (P i)) →
          proj i.succ out = proj i.castSucc stmt) →
      ∀ (stmt : Stmt 0) (out : Stmt (Fin.last m))
        (tr : (ProtocolSpec.seqCompose pSpec).FullTranscript),
        (tr, out, ()) ∈ support (Prover.run stmt () (Prover.seqCompose Stmt (fun _ => Unit) P)) →
        proj (Fin.last m) out = proj 0 stmt := by
  induction m with
  | zero =>
      intro Stmt O rounds pSpec P proj hP stmt out tr h
      rw [Prover.seqCompose_zero] at h
      simp only [Fin.vsum_zero, Fin.reduceLast, Nat.reduceAdd, ProtocolSpec.ChallengeIdx,
        ProtocolSpec.Challenge, Prover.run, Fin.isValue, Prover.id, ProtocolSpec.MessageIdx,
        ProtocolSpec.Message, Prover.runToRound, id_eq, Fin.induction_zero] at h
      cases h
      rfl
  | succ m ih =>
      intro Stmt O rounds pSpec P proj hP stmt out tr h
      let tailSpec : ProtocolSpec (Fin.vsum fun i : Fin m => rounds (Fin.succ i)) :=
        ProtocolSpec.seqCompose (fun i : Fin m => pSpec (Fin.succ i))
      let tail : Prover oSpec (Stmt (Fin.succ 0)) Unit (Stmt (Fin.last (m + 1))) Unit
          tailSpec :=
        Prover.seqCompose (fun i => Stmt i.succ) (fun _ => Unit)
          (fun i => P (Fin.succ i))
      let trApp : ((pSpec 0) ++ₚ tailSpec).FullTranscript := tr
      have h' : (trApp, out, ()) ∈ support (((do
          let ⟨tr₁, stmt₂, wit₂⟩ ← liftM (Prover.run stmt () (P 0))
          let ⟨tr₂, stmt₃, wit₃⟩ ← liftM (Prover.run stmt₂ wit₂ tail)
          pure (tr₁ ++ₜ tr₂, stmt₃, wit₃)) :
            OracleComp (oSpec + [((pSpec 0) ++ₚ tailSpec).Challenge]ₒ)
              (((pSpec 0) ++ₚ tailSpec).FullTranscript × Stmt (Fin.last (m + 1)) × Unit))) := by
        rw [← @Prover.append_run ι oSpec (Stmt 0) Unit (Stmt (Fin.succ 0)) Unit
          (Stmt (Fin.last (m + 1))) Unit (rounds 0)
          (Fin.vsum fun i : Fin m => rounds (Fin.succ i))
          (pSpec 0) tailSpec (P 0) tail stmt ()]
        simpa [trApp, tail, tailSpec, Prover.seqCompose_succ] using h
      rw [mem_support_bind_iff] at h'
      rcases h' with ⟨⟨tr₁, stmt₂, wit₂⟩, h₁, hrest⟩
      cases wit₂
      rw [mem_support_bind_iff] at hrest
      rcases hrest with ⟨⟨tr₂, stmt₃, wit₃⟩, h₂, hpure⟩
      cases wit₃
      rw [support_pure, Set.mem_singleton_iff] at hpure
      injection hpure with htr hout
      have h₁' : (tr₁, stmt₂, ()) ∈ support (Prover.run stmt () (P 0)) :=
        mem_support_liftM_oracleComp
          (superSpec := oSpec + [((pSpec 0) ++ₚ tailSpec).Challenge]ₒ) h₁
      have h₂' : (tr₂, out, ()) ∈ support
          (Prover.run stmt₂ ()
            (Prover.seqCompose (fun i => Stmt i.succ) (fun _ => Unit)
              (fun i => P (Fin.succ i)))) := by
        cases hout
        exact mem_support_liftM_oracleComp
          (superSpec := oSpec + [((pSpec 0) ++ₚ tailSpec).Challenge]ₒ) h₂
      calc
        proj (Fin.last (m + 1)) out = proj (Fin.succ (Fin.last m)) out := rfl
        _ = proj (Fin.succ (0 : Fin (m + 1))) stmt₂ := by
          exact ih
            (P := fun i => P (Fin.succ i))
            (proj := fun i => proj (Fin.succ i))
            (fun i stmt out tr h => hP (Fin.succ i) stmt out tr h)
            stmt₂ out tr₂ h₂'
        _ = proj 0 stmt := hP 0 stmt stmt₂ tr₁ h₁'

private theorem sumcheckSingleRound_prover_preserves_oracleStmt
    {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
    {n deg : ℕ} {m : ℕ} (D : Fin m ↪ R) {ι : Type} (oSpec : OracleSpec ι) (i : Fin n)
    (stmt : Sumcheck.Spec.StatementRound R n i.castSucc ×
      (∀ j, Sumcheck.Spec.OracleStatement R n deg j))
    (out : Sumcheck.Spec.StatementRound R n i.succ ×
      (∀ j, Sumcheck.Spec.OracleStatement R n deg j))
    (tr : (Sumcheck.Spec.SingleRound.pSpec R deg).FullTranscript)
    (h : (tr, out, ()) ∈ support
      (Prover.run stmt ()
        ((Sumcheck.Spec.SingleRound.oracleReduction R n deg D oSpec i).toReduction.prover))) :
    out.2 = stmt.2 := by
  rw [Sumcheck.Spec.SingleRound.oracleReduction, OracleReduction.toReduction,
    OracleReduction.liftContext, OracleProver.liftContext, Prover.liftContext_run] at h
  rw [mem_support_bind_iff] at h
  rcases h with ⟨⟨trInner, innerOut, innerWit⟩, _, hout⟩
  rw [support_pure, Set.mem_singleton_iff] at hout
  cases hout
  rcases stmt with ⟨⟨oldTarget, challenges⟩, oStmt⟩
  rcases innerOut with ⟨⟨newTarget, chal⟩, oStmt'⟩
  rfl

private theorem sumcheckProver_preserves_oracleStmt
    {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
    {deg : ℕ} {m : ℕ} (D : Fin m ↪ R) {ι : Type} (oSpec : OracleSpec ι) (n : ℕ)
    (stmt : Sumcheck.Spec.StatementRound R n 0 ×
      (∀ j, Sumcheck.Spec.OracleStatement R n deg j))
    (out : Sumcheck.Spec.StatementRound R n (Fin.last n) ×
      (∀ j, Sumcheck.Spec.OracleStatement R n deg j))
    (tr : (Sumcheck.Spec.pSpec R deg n).FullTranscript)
    (h : (tr, out, ()) ∈ support
      (Prover.run stmt () ((Sumcheck.Spec.oracleReduction R deg D n oSpec).toReduction.prover))) :
    out.2 = stmt.2 := by
  refine @seqCompose_prover_preserves ι oSpec n
    (Stmt := fun i => Sumcheck.Spec.StatementRound R n i ×
      (∀ j, Sumcheck.Spec.OracleStatement R n deg j))
    (O := ∀ j, Sumcheck.Spec.OracleStatement R n deg j)
    (rounds := fun _ => 2)
    (pSpec := fun _ => Sumcheck.Spec.SingleRound.pSpec R deg)
    (P := fun i => (Sumcheck.Spec.SingleRound.oracleReduction R n deg D oSpec i).toReduction.prover)
    (proj := fun _ stmt => stmt.2) ?_ stmt out tr ?_
  · intro i stmt out tr h
    exact sumcheckSingleRound_prover_preserves_oracleStmt D oSpec i stmt out tr h
  · simpa [Sumcheck.Spec.oracleReduction, OracleReduction.seqCompose, OracleProver.seqCompose,
      OracleReduction.toReduction] using h

local macro "peel_sim_map " h:ident " with " pat:rcasesPat : tactic =>
  `(tactic|
    (erw [simulateQ_map, StateT.run_map] at $h:ident
     rw [support_map, Set.mem_image] at $h:ident
     obtain $pat := $h))

local macro "peel_sim_bind " h:ident " with " pat:rcasesPat : tactic =>
  `(tactic|
    (erw [simulateQ_bind, StateT.run_bind] at $h:ident
     rw [mem_support_bind_iff] at $h:ident
     obtain $pat := $h))

open OracleComp OracleSpec in
omit σ init impl [DecidableEq F] [SampleableType F] in
/-- Simulating the scan-free outer verifier against the honest oracles leaves only the public
challenge data packaged as the outer statement. -/
theorem outerVerify_simulateQ_eq (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (messages : ∀ i, (outerPSpec F n params).Message i)
    (challenges : ∀ i, (outerPSpec F n params).Challenge i) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        ((outerVerifier oSpec F n M params).verify stmt challenges)
      = (do
          let x : F := challenges (outerChallengeXIdx F n M params)
          let batch : BatchingChallenge F n params.numGroups :=
            challenges (outerChallengeBatchIdx F n M params)
          pure { xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 }
        : OptionT (OracleComp oSpec) (StmtAfterOuter F n M params)) := by
  simp [outerVerifier, outerChallengeXIdx, outerChallengeBatchIdx]
  rfl

/-- Four-round unfolding of `Fin.induction` (the analog of `Fin.induction_two`), for the outer
LogUp prover's `runToRound`. -/
private theorem Fin.induction_four {motive : Fin 5 → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin 4, motive i.castSucc → motive i.succ} :
    Fin.induction (motive := motive) zero succ (Fin.last 4)
      = succ 3 (succ 2 (succ 1 (succ 0 zero))) := rfl

set_option maxHeartbeats 1000000 in
-- The proof peels the whole four-round outer transcript and reconstructs the handoff relation;
-- the generated support terms are large even though the reasoning is deterministic.

/-- Completeness of the outer LogUp phase: the honest outer prover reaches the zero-sum handoff
relation, except with the pole-sampling error. -/
theorem logup_outer_completeness [Inhabited F] :
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (logupMidRelation F n M params) (logupCompletenessError F n) := by
  unfold OracleReduction.completeness Reduction.completeness
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hIn
  simp only [outerOracleReduction, OracleReduction.toReduction, Reduction.run, Prover.run,
    Verifier.run, Prover.runToRound, outerProver, Fin.induction_four,
    Prover.processRound, outerPSpec]
  repeat' split <;> rename_i hd <;> first | exact absurd hd (by decide) | skip
  simp only [ProtocolSpec.getChallenge, liftM, monadLift, MonadLift.monadLift,
    MonadLiftT.monadLift, OracleComp.liftComp_pure, bind_pure_comp, map_pure,
    QueryImpl.addLift_def]
  refine ge_trans (probEvent_mono
    (p := fun out => ∀ u : (Fin n → Fin 2),
      out.2.1.xChallenge + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0)
    ?goodOutputs) ?goodProb
  · -- every output with a non-pole outer challenge satisfies the success predicate
    intro out hout hGood
    rw [OptionT.mem_support_iff] at hout
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
    obtain ⟨s, -, hout⟩ := hout
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hout
    obtain ⟨⟨_, s'⟩, hout, rfl⟩ := hout
    peel_sim_bind hout with ⟨⟨pres, s2⟩, hpres, hver⟩
    simp only [OptionT.lift, OptionT.mk] at hpres
    peel_sim_map hpres with ⟨⟨pval, sp⟩, hpval, hpeq⟩
    peel_sim_map hpval with ⟨⟨a, sa⟩, ha, hpval_eq⟩
    peel_sim_bind ha with ⟨⟨b, sb⟩, hb, ha3⟩
    peel_sim_map ha3 with ⟨⟨zlam, szlam⟩, hzlam, ha3eq⟩
    -- round 1: peel `hb` to reach the `x` challenge query
    peel_sim_map hb with ⟨⟨c, sc⟩, hc, hbeq⟩
    peel_sim_bind hc with ⟨⟨d, sd⟩, hd, hc2⟩
    peel_sim_map hc2 with ⟨⟨xval, sx⟩, hx, hc2eq⟩
    -- round 0 is deterministic (a pure `honestMultiplicity` send)
    peel_sim_map hd with ⟨⟨e, se⟩, he, hdeq⟩
    erw [simulateQ_pure, StateT.run_pure] at he
    rw [support_pure, Set.mem_singleton_iff] at he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    -- substitute the prover-side equation chain to make `pval`/`pres` concrete
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hdeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc2eq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha3eq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpval_eq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpeq
    change F at xval
    change BatchingChallenge F n params.numGroups at zlam
    -- peel the verifier (match on `some pval` resolves; then its bind)
    simp only at hver
    erw [simulateQ_bind, StateT.run_bind] at hver
    rw [mem_support_bind_iff] at hver
    obtain ⟨⟨vstmt, sv⟩, hverify, hvout⟩ := hver
    -- The scan-free verifier packages the sampled challenges; the non-pole assumption comes from
    -- the good-challenge event above.
    simp only [OracleVerifier.toVerifier] at hverify
    rw [outerVerify_simulateQ_eq] at hverify
    -- The verifier accepted: `vstmt = some _` (the `none` branch of `hvout` yields `none ≠ some`).
    rcases vstmt with _ | vAccepted
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hvout
      simp at hvout
    · rcases vAccepted with _ | vAccepted
      · simp only [OStmtAfterOuter, OStmtIn, MultiplicityMessage, HelperMessages,
          Nat.reduceAdd, Fin.vcons_fin_zero, BatchingChallenge] at hvout
        have hvoutBase := support_simulateQ_run_fst_subset
          (impl + QueryImpl.liftTarget (StateT σ ProbComp)
            (ProtocolSpec.challengeQueryImpl (pSpec := outerPSpec F n params))) hvout
        letI :
            (i : (outerPSpec F n params).ChallengeIdx) →
              OracleInterface ((outerPSpec F n params).Challenge i) :=
          ProtocolSpec.challengeOracleInterface
        letI : LawfulMonad (OracleComp (oSpec + [(outerPSpec F n params).Challenge]ₒ)) :=
          OracleComp.instLawfulMonad _
        change some out ∈ support
          ((_ <$>
            (failure :
              OptionT (OracleComp (oSpec + [(outerPSpec F n params).Challenge]ₒ)) _)).run)
          at hvoutBase
        rw [OptionT.run_map, OptionT.run_failure] at hvoutBase
        rw [support_map, support_pure, Set.mem_image] at hvoutBase
        obtain ⟨a, ha, hmap⟩ := hvoutBase
        rw [Set.mem_singleton_iff] at ha
        subst a
        simp at hmap
      · -- The honest output: `out` pairs the prover view with the verifier's accepted statement.
        rw [show (some (some vAccepted), sv).1 = some (some vAccepted) by rfl] at hvout
        simp only [Option.getM_some, map_pure] at hvout
        obtain ⟨rfl, rfl⟩ := hvout
        simp only [OStmtAfterOuter, OStmtIn, MultiplicityMessage, HelperMessages] at hverify
        have hverifyBase := support_simulateQ_run_fst_subset
          (impl + QueryImpl.liftTarget (StateT σ ProbComp)
            (ProtocolSpec.challengeQueryImpl (pSpec := outerPSpec F n params))) hverify
        letI :
            (i : (outerPSpec F n params).ChallengeIdx) →
              OracleInterface ((outerPSpec F n params).Challenge i) :=
          ProtocolSpec.challengeOracleInterface
        letI : LawfulMonad (OracleComp (oSpec + [(outerPSpec F n params).Challenge]ₒ)) :=
          OracleComp.instLawfulMonad _
        have hverifyEq := support_pure_eq
          (m := OracleComp (oSpec + [(outerPSpec F n params).Challenge]ₒ)) hverifyBase
        simp only [Option.some.injEq] at hverifyEq
        subst vAccepted
        have hNoTablePoles :
            ∀ u : (Fin n → Fin 2),
              xval + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0 := by
          intro u
          simpa [outerVerifier, outerChallengeXIdx, outerChallengeBatchIdx,
            ProtocolSpec.FullTranscript.challenges, ProtocolSpec.Transcript.concat, Fin.snoc]
            using hGood u
        have hcols : ∀ j : Fin M, ∀ u : (Fin n → Fin 2), ∃ v : (Fin n → Fin 2),
            MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1 u =
              MvPolynomial.toEvalsZeroOne (oStmt .table).1 v := by
          simpa [inputRelation] using hIn
        have hchar : ∀ a : F,
            lookupMultiplicityCount
                (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1) a ≠ 0 →
              (tableMultiplicityCount (MvPolynomial.toEvalsZeroOne (oStmt .table).1) a : F) ≠ 0 :=
          fun _ hlookup =>
            tableMultiplicityCount_cast_ne_zero_of_lookupMultiplicityCount_ne_zero
              stmt.charLarge (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
              (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1) hcols hlookup
        have hpoles : ∀ (i : TermIdx M) (u : (Fin n → Fin 2)),
            termPhi (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
              (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1) xval i u ≠ 0 :=
          termPhi_ne_zero_of_table_poles (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
            (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1) xval hcols
            hNoTablePoles
        let stmtAfter : StmtAfterOuter F n M params :=
          { xChallenge := xval, zChallenge := zlam.1, batchingScalars := zlam.2 }
        let oStmtAfter : ∀ i, OStmtAfterOuter F n M params i :=
          fun
            | .input i => oStmt i
            | .multiplicity => honestMultiplicity oStmt
            | .helpers => honestHelpers params oStmt xval
        have hMultiplicity :
            MvPolynomial.toEvalsZeroOne (honestMultiplicity oStmt).1 =
              normalizedMultiplicityValue (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
                (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1) := by
          change (MvPolynomial.MLEEquiv (R := F) (σ := Fin n)) (honestMultiplicity oStmt) = _
          simp [honestMultiplicity]
        have hHelpers :
            (fun k => MvPolynomial.toEvalsZeroOne (honestHelpers params oStmt xval k).1) =
              fun k u =>
                helperValue params.group (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
                  (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1)
                  (normalizedMultiplicityValue (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
                    (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1))
                  xval k u := by
          funext k
          change (MvPolynomial.MLEEquiv (R := F) (σ := Fin n))
              (honestHelpers params oStmt xval k) = _
          simp [honestHelpers, hMultiplicity]
        have hmid : ((stmtAfter, oStmtAfter), ()) ∈ logupMidRelation F n M params := by
          unfold logupMidRelation logupOuterSumcheckClaim
          rw [← logupOuterClaim_zero
            (groups := params.group) (hgroups := sum_protocolGroups (F := F) params)
            (table := MvPolynomial.toEvalsZeroOne (oStmt .table).1)
            (columns := fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1)
            (xChallenge := xval) (zChallenge := zlam.1) (batchingScalars := zlam.2)
            hchar hpoles]
          apply Finset.sum_congr rfl
          intro u _
          rw [logupQPolynomial_eval_hypercube]
          simp [stmtAfter, oStmtAfter, hMultiplicity, hHelpers]
        simp? [outerVerifier, outerChallengeXIdx, outerChallengeBatchIdx,
          ProtocolSpec.FullTranscript.challenges, ProtocolSpec.FullTranscript.messages,
          ProtocolSpec.Transcript.concat, Fin.snoc]
        constructor
        · convert hmid using 2
          apply Prod.ext
          · rfl
          · funext i
            cases i <;> simp [oStmtAfter, outerMultiplicityMessageIdx,
              outerHelpersMessageIdx]
        · funext i
          cases i <;> simp [outerMultiplicityMessageIdx,
            outerHelpersMessageIdx]
  · -- pole-probability bound `Pr[x avoids all table poles] ≥ 1 - |H|/|F|`
    refine le_trans (uniform_avoids_table_poles_prob (F := F) (n := n) (M := M) oStmt) ?_
    rw [OptionT.mk_bind]
    apply le_probEvent_bind_of_forall_le
    · simp
    · intro s hs
      clear hs
      simp only [OptionT.run_mk, OptionT.run_bind, OptionT.run_lift, Option.elimM,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, bind_pure_comp, simulateQ_bind,
        StateT.run'_eq, StateT.run_bind, Function.comp_apply]
      erw [simulateQ_bind]
      erw [simulateQ_bind]
      erw [simulateQ_bind]
      erw [simulateQ_bind]
      erw [simulateQ_pure]
      simp only [pure_bind]
      erw [simulateQ_pure]
      simp only [pure_bind]
      erw [simulateQ_bind]
      rw [QueryImpl.simulateQ_add_liftComp_right, simulateQ_liftTarget]
      erw [simulateQ_query]
      simp only [OracleSpec.query_def, OracleQuery.input_apply, ProtocolSpec.challengeQueryImpl,
        OracleQuery.cont_apply, outerPSpec]
      simp
      · simpa [probEvent_uniformSample] using
          (mul_le_probEvent_bind
            (mx := (liftM ($ᵗ F : ProbComp F) : OptionT ProbComp F))
            (p := fun x : F => ∀ u : (Fin n → Fin 2),
              x + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0)
            (r := Pr[fun x : F => ∀ u : (Fin n → Fin 2),
              x + MvPolynomial.toEvalsZeroOne (oStmt .table).1 u ≠ 0 | $ᵗ F])
            (r' := 1) (by simp) (by
              intro x hx hGood
              erw [simulateQ_pure]
              simp only [StateT.run_pure, liftM_pure, pure_bind]
              erw [simulateQ_pure]
              simp only [StateT.run_pure, liftM_pure, pure_bind]
              rw [one_le_probEvent_iff, probEvent_eq_one_iff]
              constructor
              · rw [probFailure_bind_eq_zero_iff]
                constructor
                · simp [OptionT.probFailure_liftM]
                · intro batchState hbatch
                  rw [probFailure_bind_eq_zero_iff]
                  constructor
                  · simp [OptionT.probFailure_liftM]
                  · intro verifiedState hverified
                    have hSome : ∃ accepted, verifiedState.1 = some accepted := by
                      cases hfirst : verifiedState.1 with
                      | none =>
                          exfalso
                          have hv := hverified
                          rw [OptionT.support_liftM] at hv
                          simp only [OracleVerifier.toVerifier] at hv
                          erw [outerVerify_simulateQ_eq] at hv
                          erw [simulateQ_bind, StateT.run_bind] at hv
                          rw [mem_support_bind_iff] at hv
                          obtain ⟨⟨ver, sver⟩, hverPure, hverRest⟩ := hv
                          erw [simulateQ_pure, StateT.run_pure] at hverPure
                          rw [support_pure, Set.mem_singleton_iff] at hverPure
                          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hverPure
                          erw [simulateQ_pure, StateT.run_pure] at hverRest
                          rw [support_pure, Set.mem_singleton_iff] at hverRest
                          cases hverRest
                          simp at hfirst
                      | some accepted =>
                          exact ⟨accepted, rfl⟩
                    rcases hSome with ⟨accepted, haccepted⟩
                    rw [OptionT.probFailure_eq, OptionT.run_mk, haccepted]
                    simp
              · intro out hout
                rw [mem_support_bind_iff] at hout
                obtain ⟨batchState, hbatch, hout⟩ := hout
                rw [OptionT.support_liftM] at hbatch
                erw [simulateQ_bind, StateT.run_bind] at hbatch
                rw [mem_support_bind_iff] at hbatch
                obtain ⟨⟨batch, sbatch⟩, hbatchSample, hbatchPure⟩ := hbatch
                erw [simulateQ_pure, StateT.run_pure] at hbatchPure
                rw [support_pure, Set.mem_singleton_iff] at hbatchPure
                subst batchState
                rw [mem_support_bind_iff] at hout
                obtain ⟨verifiedState, hverified, hout⟩ := hout
                rw [OptionT.mem_support_iff] at hout
                simp only [OptionT.run_mk, support_pure, Set.mem_singleton_iff] at hout
                have hverified' := hverified
                rw [OptionT.support_liftM] at hverified'
                simp only [OracleVerifier.toVerifier] at hverified'
                erw [outerVerify_simulateQ_eq] at hverified'
                simp [outerChallengeXIdx, outerChallengeBatchIdx,
                  ProtocolSpec.FullTranscript.challenges, ProtocolSpec.Transcript.concat,
                  Fin.snoc] at hverified'
                erw [simulateQ_bind, StateT.run_bind] at hverified'
                rw [mem_support_bind_iff] at hverified'
                obtain ⟨⟨verOpt, sver⟩, hverOpt, hverified''⟩ := hverified'
                erw [simulateQ_pure, StateT.run_pure] at hverOpt
                rw [support_pure, Set.mem_singleton_iff] at hverOpt
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hverOpt
                erw [simulateQ_pure, StateT.run_pure] at hverified''
                rw [support_pure, Set.mem_singleton_iff] at hverified''
                subst verifiedState
                cases hout
                exact hGood))

/-- Lens-completeness for the LogUp→Sumcheck lens: `proj` builds the zero-sum instance, and `lift`
retains the outer LogUp data together with sumcheck's final valid point claim. -/
instance logupSumcheckLensComplete :
    (logupSumcheckContextLens F n M params).toContext.IsComplete
      (logupMidRelation F n M params)
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F) 0)
      (logupAfterSumcheckRelation F n M params)
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
        (Fin.last n))
      ((logupConcreteSumcheckOracleReduction oSpec F n M params).toReduction.compatContext
        (logupSumcheckContextLens F n M params).toContext) where
  proj_complete := by
    rintro ⟨stmt, oStmt⟩ ⟨⟩ h
    exact logupSumcheckRelationInput_of_zero F n M params h
  lift_complete := by
    intro outerStmt outerWit innerStmtOut innerWitOut hCompat _ hRelOut
    have hOStmt :
        innerStmtOut.2 = logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2 := by
      simp only [Reduction.compatContext, Function.comp_apply, ProtocolSpec.ChallengeIdx,
        ProtocolSpec.Challenge, OStmtAfterOuter, OStmtIn, MultiplicityMessage, HelperMessages,
        Set.mem_image, OptionT.mem_support_iff, Prod.exists, exists_and_right,
        exists_eq_right] at hCompat
      rcases hCompat with ⟨td, vOut, verOStmt, hRun⟩
      have hProver := reduction_run_prover_mem
        ((logupConcreteSumcheckOracleReduction oSpec F n M params).toReduction)
        ((logupSumcheckContextLens F n M params).toContext.proj (outerStmt, outerWit)).1
        ((logupSumcheckContextLens F n M params).toContext.proj (outerStmt, outerWit)).2
        td innerStmtOut innerWitOut (vOut, verOStmt) hRun
      have hPres := sumcheckProver_preserves_oracleStmt (booleanDomain F) oSpec n
        ((logupSumcheckContextLens F n M params).toContext.proj (outerStmt, outerWit)).1
        innerStmtOut td hProver
      simpa [logupSumcheckContextLens] using hPres
    cases innerWitOut
    have hPair :
        (innerStmtOut.1, logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2) =
          innerStmtOut := by
      cases innerStmtOut
      simpa using hOStmt.symm
    simpa [logupSumcheckContextLens, logupAfterSumcheckRelation, hPair] using hRelOut

omit [Fintype F] in
/-- Completeness of the embedded sumcheck phase: it carries `logupMidRelation` to the retained
final sumcheck claim with no extra error, by reusing the generic sumcheck's perfect completeness
through the LogUp-to-Sumcheck context lens. -/
theorem logupSumcheckPhaseCompleteness :
    (sumcheckOracleReduction oSpec F n M params).completeness init impl
      (logupMidRelation F n M params) (logupAfterSumcheckRelation F n M params) 0 :=
  OracleReduction.liftContext_perfectCompleteness
    (lens := logupSumcheckContextLens F n M params)
    (lensComplete := logupSumcheckLensComplete oSpec F n M params)
    (Sumcheck.Spec.oracleReduction_perfectCompleteness
      F (logupSumcheckDegree M params) (booleanDomain F) n oSpec)


omit [Fintype F] [SampleableType F] in
/-- Completeness of the final LogUp point check: once sumcheck's final claim is valid for the
retained LogUp polynomial, the verifier's oracle queries reconstruct the same value. -/
theorem finalCheckCompleteness :
    (finalCheckOracleReduction oSpec F n M params).completeness init impl
      (logupAfterSumcheckRelation F n M params) outputRelation 0 := by
  unfold OracleReduction.completeness Reduction.completeness
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hRel
  have hExpected :
      MvPolynomial.eval stmt.finalClaim.challenges
          (logupQPolynomial (params.group) (oStmt (.input .table)).1
            (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
            (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
            stmt.outer.batchingScalars) =
        stmt.finalClaim.target := by
    unfold logupAfterSumcheckRelation Sumcheck.Spec.relationRound at hRel
    simp only [Set.mem_setOf_eq, logupSumcheckOracleStmt, logupSumcheckPolynomial] at hRel
    have tailSize_zero : n - (Fin.last n : Fin (n + 1)) = 0 := by simp
    let tail0 : Fin (n - (Fin.last n : Fin (n + 1))) → F :=
      fun i => Fin.elim0 (Fin.cast (by simp) i)
    have hfinalPoint :
        Fin.append stmt.finalClaim.challenges tail0 ∘
            Fin.cast (Sumcheck.Spec.relationRound._proof_1 n (Fin.last n)) =
          stmt.finalClaim.challenges := by
      funext i
      change Fin.append stmt.finalClaim.challenges tail0
          (Fin.cast (Sumcheck.Spec.relationRound._proof_1 n (Fin.last n)) i) =
        stmt.finalClaim.challenges i
      rw [Fin.append_right_nil stmt.finalClaim.challenges tail0 tailSize_zero]
      congr 1
    have hsum :
        (∑ x ∈ Fintype.piFinset fun _ : Fin (n - (Fin.last n : Fin (n + 1))) =>
            Finset.univ.map (booleanDomain F),
          MvPolynomial.eval
            (Fin.append stmt.finalClaim.challenges x ∘
              Fin.cast (Sumcheck.Spec.relationRound._proof_1 n (Fin.last n)))
            (logupQPolynomial (params.group) (oStmt (.input .table)).1
              (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
              (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
              stmt.outer.batchingScalars)) =
          MvPolynomial.eval stmt.finalClaim.challenges
            (logupQPolynomial (params.group) (oStmt (.input .table)).1
              (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
              (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
              stmt.outer.batchingScalars) := by
      rw [Finset.sum_eq_single tail0]
      · rw [hfinalPoint]
        rfl
      · intro b _ hb
        exact False.elim (hb (funext fun i => Fin.elim0 (Fin.cast (by simp) i)))
      · intro hnot
        exact False.elim (hnot (by
          rw [Fintype.mem_piFinset]
          intro i
          exact Fin.elim0 (Fin.cast tailSize_zero i)))
    exact hsum ▸ hRel
  have hGuard :
      qAtPoint (params.group) stmt.outer.xChallenge stmt.outer.zChallenge
          stmt.finalClaim.challenges stmt.outer.batchingScalars
          (MvPolynomial.eval stmt.finalClaim.challenges (oStmt .multiplicity).1)
          (MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input .table)).1)
          (fun i => MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input (.column i))).1)
          (fun k => MvPolynomial.eval stmt.finalClaim.challenges (oStmt .helpers k).1) =
        stmt.finalClaim.target := by
    rw [← hExpected]
    exact (logupQPolynomial_eval_point (params.group) (oStmt (.input .table)).1
      (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
      (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
      stmt.finalClaim.challenges stmt.outer.batchingScalars).symm
  let qImpl :
      QueryImpl
        (oSpec + ([OStmtAfterOuter F n M params]ₒ + [finalCheckPSpec.Message]ₒ))
        (OracleComp oSpec) :=
    OracleInterface.simOracle2 (T₁ := OStmtAfterOuter F n M params)
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
  have hVerify :
      simulateQ qImpl
          ((finalCheckVerifier oSpec F n M params).verify stmt (fun i => Fin.elim0 i)).run =
        (pure (some ()) : OracleComp oSpec (Option StmtOut)) := by
    simp only [finalCheckVerifier, OptionT.run_bind, OptionT.run_pure]
    erw [simulateQ_bind]
    rw [hquery .multiplicity stmt.finalClaim.challenges]
    simp only [pure_bind, Option.elim_some]
    erw [simulateQ_bind]
    rw [hquery (.input .table) stmt.finalClaim.challenges]
    simp only [pure_bind, Option.elim_some]
    let colValue := fun i : Fin M =>
      MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input (.column i))).1
    have hcols := simulateQ_optionT_mapM_pure qImpl
      (fun i : Fin M =>
        finalCheckQuery oSpec F n M params (.input (.column i)) stmt.finalClaim.challenges)
      colValue (Vector.finRange M) (by
        intro i
        simpa [colValue, OracleInterface.answer] using
          hquery (.input (.column i)) stmt.finalClaim.challenges)
    erw [simulateQ_option_elimM]
    erw [hcols]
    simp only [pure_bind, Option.elimM, Option.elim_some]
    let helperValue := fun k : Fin params.numGroups =>
      MvPolynomial.eval stmt.finalClaim.challenges (oStmt .helpers k).1
    have hhelpers := simulateQ_optionT_mapM_pure qImpl
      (fun k : Fin params.numGroups =>
        finalCheckQuery oSpec F n M params .helpers ⟨k, stmt.finalClaim.challenges⟩)
      helperValue (Vector.finRange params.numGroups) (by
        intro k
        simpa [helperValue, OracleInterface.answer] using
          hquery .helpers ⟨k, stmt.finalClaim.challenges⟩)
    erw [simulateQ_option_elimM]
    erw [hhelpers]
    simp only [pure_bind, Option.elimM, Option.elim_some]
    have hGuard' :
        qAtPoint (params.group) stmt.outer.xChallenge stmt.outer.zChallenge
            stmt.finalClaim.challenges stmt.outer.batchingScalars
            (OracleInterface.answer (oStmt .multiplicity) stmt.finalClaim.challenges)
            (OracleInterface.answer (oStmt (.input .table)) stmt.finalClaim.challenges)
            colValue
            helperValue =
          stmt.finalClaim.target := by
      simpa [OracleInterface.answer, colValue, helperValue] using hGuard
    erw [simulateQ_option_elimM]
    simp [guard, hGuard', OptionT.run_pure, Option.elimM]
  have hVerifyDefault :
      simulateQ
          (OracleInterface.simOracle2 oSpec oStmt
            (ProtocolSpec.FullTranscript.messages (default : finalCheckPSpec.FullTranscript)))
          (((finalCheckVerifier oSpec F n M params).verify stmt
            (ProtocolSpec.FullTranscript.challenges
              (default : finalCheckPSpec.FullTranscript))).run) =
        (pure (some ()) : OracleComp oSpec (Option StmtOut)) := by
    simpa [qImpl, finalCheckPSpec] using hVerify
  have hVerifyDefaultT :
      OptionT.run
        (simulateQ
          (OracleInterface.simOracle2 oSpec oStmt
            (ProtocolSpec.FullTranscript.messages (default : finalCheckPSpec.FullTranscript)))
          ((finalCheckVerifier oSpec F n M params).verify stmt
            (ProtocolSpec.FullTranscript.challenges
              (default : finalCheckPSpec.FullTranscript)))) =
        (pure (some ()) : OracleComp oSpec (Option StmtOut)) := by
    simpa [OptionT.run] using hVerifyDefault
  have hVerifyDefaultT' :
      OptionT.run
        (simulateQ
          (OracleInterface.simOracle2 oSpec oStmt
            (ProtocolSpec.FullTranscript.messages default))
          ((finalCheckVerifier oSpec F n M params).verify stmt
            (ProtocolSpec.FullTranscript.challenges default))) =
        (pure (some ()) : OracleComp oSpec (Option StmtOut)) := by
    simpa [finalCheckPSpec] using hVerifyDefaultT
  have hrun :
      (finalCheckOracleReduction oSpec F n M params).toReduction.run (stmt, oStmt) () =
        (pure ((default, ((), fun i => Fin.elim0 i), ()), ((), fun i => Fin.elim0 i)) :
          OptionT (OracleComp _) _) := by
    simp [finalCheckOracleReduction, OracleReduction.toReduction, Reduction.run,
      finalCheckProver, Prover.run, Verifier.run, Prover.runToRound,
      finalCheckPSpec, OracleVerifier.toVerifier]
    erw [hVerifyDefaultT']
    simp
    congr
    funext i
    exact Fin.elim0 i
  simp only [ENNReal.coe_zero, tsub_zero]
  rw [hrun]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    change none ∈ _root_.support
      (StateT.run' (simulateQ _
        (pure (some
          ((default, ((), fun i => Fin.elim0 i), ()), ((), fun i => Fin.elim0 i))) :
            OracleComp _ _)) s) at hmem
    rw [simulateQ_pure] at hmem
    change none ∈ _root_.support
      (Prod.fst <$> (pure (some
        ((default, ((), fun i => Fin.elim0 i), ()), ((), fun i => Fin.elim0 i))) :
          StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro out hout
    rw [OptionT.mem_support_iff] at hout
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
    obtain ⟨s, -, hout⟩ := hout
    change some out ∈ _root_.support
      (StateT.run' (simulateQ _
        (pure (some
          ((default, ((), fun i => Fin.elim0 i), ()), ((), fun i => Fin.elim0 i))) :
            OracleComp _ _)) s) at hout
    rw [simulateQ_pure] at hout
    change some out ∈ _root_.support
      (Prod.fst <$> (pure (some
        ((default, ((), fun i => Fin.elim0 i), ()), ((), fun i => Fin.elim0 i))) :
          StateT σ ProbComp _).run s) at hout
    rw [StateT.run_pure] at hout
    simp [map_pure, support_pure] at hout
    cases hout
    exact ⟨Set.mem_univ _, rfl⟩

/-- Main ArkLib completeness theorem for LogUp Protocol 2. -/
theorem logup_completeness :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) := by
  letI : Inhabited F := ⟨0⟩
  have hOuterSumcheck := OracleReduction.append_completeness.{0, 0, 0, 0}
    (outerOracleReduction oSpec F n M params)
    (sumcheckOracleReduction oSpec F n M params)
    (logup_outer_completeness oSpec F n M params init impl)
    (logupSumcheckPhaseCompleteness oSpec F n M params init impl)
  have hFull := OracleReduction.append_completeness.{0, 0, 0, 0}
    ((outerOracleReduction oSpec F n M params).append
      (sumcheckOracleReduction oSpec F n M params))
    (finalCheckOracleReduction oSpec F n M params)
    hOuterSumcheck
    (finalCheckCompleteness oSpec F n M params init impl)
  simpa only [add_zero] using hFull

end Completeness

end Logup
