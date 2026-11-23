/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Executable
public import ArkLib.ProofSystem.Binius.FRIBinius.RingSwitch
public import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.General

/-!
# Perfect completeness of executable FRI-Binius

The prefix prover works with Boolean evaluation tables. The input and intermediate relations
interpret each table as its multilinear extension. Supported honest runs satisfy the same
batching, sumcheck, and opening relations as the polynomial prover.
-/

@[expose] public section

namespace Binius.FRIBinius.Executable

open OracleComp OracleSpec ProtocolSpec Probability
open Module RingSwitching RingSwitching.Packing Sumcheck.Structured
open CoordinateWise.ScalarRound

private theorem perfectCompleteness_of_accepted_support
    {StmtIn StmtOut WitIn WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ j, SampleableType (pSpec.Challenge j)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    (reduction : Reduction []ₒ StmtIn WitIn StmtOut WitOut pSpec) (fallback : StmtIn → StmtOut)
    (hHonest : ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn →
      ∀ run ∈ support (reduction.prover.run stmtIn witIn),
        let (transcript, stmtOut, witOut) := run
        reduction.verifier.verify stmtIn transcript = pure stmtOut ∧ (stmtOut, witOut) ∈ relOut) :
    reduction.perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_guarded_prover_support
    (R := reduction) (G := Verifier.GuardedForm.ofEmpty reduction.verifier fallback)
  intro stmtIn witIn hInput ⟨transcript, stmtOut, witOut⟩ hRun
  obtain ⟨hAccept, hOutput⟩ := hHonest stmtIn witIn hInput (transcript, stmtOut, witOut) hRun
  dsimp only [Verifier.GuardedForm.ofEmpty]
  rw [hAccept]
  exact ⟨rfl, hOutput, rfl⟩

section Head

open TensorPrefix.Computable

variable {K L : Type} [Field K] [DecidableEq K] [Field L] [DecidableEq L]
  [Algebra K L] [SampleableType L] {κ ℓ m : ℕ}
  (P : RingSwitchingProfile K L κ) (h : ℓ = m + κ) (a : AbstractOStmtIn L m)

private theorem headReduction_perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (headReduction (TensorPrefix.commitment a).OStmt P.basis
      (fun x u => P.basis.repr x u) h).perfectCompleteness init impl
      (tableWitnessRelation (TensorPrefix.relIn P h a))
      (tableWitnessRelation (TensorPrefix.headRelOut P h a)) := by
  let fallback :=
    fun (input : ((Fin ℓ → L) × L) × (∀ j, (TensorPrefix.commitment a).OStmt j)) =>
      let ((query, _), oracles) := input
      (headNext (m := m) P.basis (fun x u => P.basis.repr x u)
        query (fun _ => 0) (fun _ => 0), oracles)
  apply perfectCompleteness_of_accepted_support (fallback := fallback)
  intro ⟨stmtIn, oracles⟩ sourceTable hInput run hRun
  change run ∈ support
    ((headProver (TensorPrefix.commitment a).OStmt P.basis
      (fun x u => P.basis.repr x u) h).run (stmtIn, oracles) sourceTable) at hRun
  rw [headProver_run] at hRun
  obtain ⟨challenge, _, hRun⟩ := (mem_support_bind_iff _ _ _).mp hRun
  have hRunEq := OracleComp.eq_of_mem_support_pure _ hRun
  subst run
  change ((stmtIn, oracles), tableWitnessEquiv sourceTable) ∈ TensorPrefix.relIn P h a at hInput
  rw [tableWitnessEquiv_apply_eq] at hInput
  obtain ⟨hAccept, hOutput⟩ :=
    head_preservesRelation P h a stmtIn oracles sourceTable challenge hInput
  refine ⟨?_, ?_⟩
  · change (headVerifier (TensorPrefix.commitment a).OStmt P.basis
      (fun x u => P.basis.repr x u) h).toVerifier.verify (stmtIn, oracles)
        (FullTranscript.mk2 (honestMessage h stmtIn.1 sourceTable) challenge) = _
    rw [headVerifier_verify, hAccept]
  · change ((_, oracles), tableWitnessEquiv (pack P.basis h sourceTable)) ∈
      TensorPrefix.headRelOut P h a
    rw [tableWitnessEquiv_apply_eq]
    exact hOutput

end Head

section ProductSumcheck

open RingSwitching.Packing.ProductSumcheck ProductSumcheck.Computable MvPolynomial

section Runs

variable {C Context ι : Type} [CommRing C] {m : ℕ} (OStmt : ι → Type)

private theorem roundProver_run [BEq C] [LawfulBEq C] (i : Fin m)
    (multiplierTable : Context → (Fin m → Fin 2) → C)
    (stmtIn : ProductSumcheck.Statement Context C i.castSucc)
    (oracles : ∀ j, OStmt j) (packedTable : (Fin m → Fin 2) → C) :
    (roundProver OStmt i multiplierTable).run (stmtIn, oracles) packedTable = (do
      let challenge ← liftComp ((roundPSpec C).getChallenge ⟨1, rfl⟩)
        ([]ₒ + [(roundPSpec C).Challenge]ₒ'challengeOracleInterface)
      let message := roundMessage i (multiplierTable stmtIn.ctx) packedTable stmtIn.challenges
      pure (FullTranscript.mk2 message challenge, (roundNext i stmtIn message challenge, oracles),
        packedTable)) := by
  rw [roundProver, scalarRoundOracleProver_run]

private theorem terminalProver_run
    (stmtIn : ProductSumcheck.Statement Context C (Fin.last m))
    (oracles : ∀ j, OStmt j) (packedTable : (Fin m → Fin 2) → C) :
    (terminalProver OStmt).run (stmtIn, oracles) packedTable =
      pure (Terminal.transcript (terminalMessage packedTable stmtIn),
        (Terminal.nextStatement stmtIn (terminalMessage packedTable stmtIn), oracles),
        packedTable) :=
  messageRoundOracleProver_run (oSpec := []ₒ)
    (prepare := fun (input : (ProductSumcheck.Statement Context C (Fin.last m) × (∀ j, OStmt j)) ×
        ((Fin m → Fin 2) → C)) =>
      let ((stmt, _), table) := input
      let value := terminalMessage table stmt
      (value, (input, value)))
    (finish := fun (((stmt, oracles), table), value) =>
      ((Terminal.nextStatement stmt value, oracles), table))
    stmtIn oracles packedTable

end Runs

variable {C Context : Type} [Field C] [DecidableEq C] [SampleableType C] {m : ℕ}
  (multiplier : Multiplier Context C m) (pc : PackedCommitment C m)
  {σ : Type}

omit [SampleableType C] in
private theorem table_aeval (p : (Fin m → Fin 2) → C) (b : Fin m → Fin 2) :
    p b = aeval (b : Fin m → C) (tableWitnessEquiv p).val := by
  rw [tableWitnessEquiv_apply, aeval_eq_eval]
  exact (eval_multilinearOfTable p b).symm

private theorem roundReduction_perfectCompleteness
    (multiplierTable : Context → (Fin m → Fin 2) → C)
    (hMultiplierTable : ∀ ctx b, multiplierTable ctx b = (multiplier ctx).val.eval (b : Fin m → C))
    (i : Fin m) (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (roundReduction pc.OStmt i multiplierTable).perfectCompleteness init impl
      (tableWitnessRelation (rel multiplier pc i.castSucc))
      (tableWitnessRelation (rel multiplier pc i.succ)) := by
  let fallback :=
    fun (input : ProductSumcheck.Statement Context C i.castSucc × (∀ j, pc.OStmt j)) =>
      let (stmt, oracles) := input
      ((⟨stmt.ctx, Fin.snoc stmt.challenges 0, 0⟩ : ProductSumcheck.Statement Context C i.succ),
        oracles)
  apply perfectCompleteness_of_accepted_support (fallback := fallback)
  intro ⟨stmtIn, oracles⟩ packedTable hInput run hRun
  change run ∈ support
    ((roundProver pc.OStmt i multiplierTable).run (stmtIn, oracles) packedTable) at hRun
  rw [roundProver_run] at hRun
  obtain ⟨challenge, _, hRun⟩ := (mem_support_bind_iff _ _ _).mp hRun
  have hRunEq := OracleComp.eq_of_mem_support_pure _ hRun
  subst run
  let packedPoly := tableWitnessEquiv packedTable
  let message := roundMessage i (multiplierTable stmtIn.ctx) packedTable stmtIn.challenges
  obtain ⟨hAccept, hOutput⟩ :=
    verifyRound_honest multiplier pc i stmtIn oracles packedPoly challenge
      (a := multiplierTable stmtIn.ctx) (p := packedTable)
      (ha := hMultiplierTable stmtIn.ctx) (hp := table_aeval packedTable) hInput
  have hNext : roundNext i stmtIn message challenge =
      Round.nextStatement i stmtIn (Round.honestMessage multiplier i stmtIn packedPoly)
        challenge := by
    unfold verifyRound at hAccept
    split at hAccept
    · exact Option.some.inj hAccept
    · cases hAccept
  refine ⟨?_, ?_⟩
  · change (roundVerifier pc.OStmt i).toVerifier.verify (stmtIn, oracles)
      (FullTranscript.mk2 message challenge) = pure (roundNext i stmtIn message challenge, oracles)
    rw [roundVerifier_verify, hAccept, hNext]
  · change ((roundNext i stmtIn message challenge, oracles), packedPoly) ∈
      rel multiplier pc i.succ
    rw [hNext]
    exact hOutput

omit [SampleableType C] in
private theorem terminalReduction_perfectCompleteness
    (evaluateMultiplier : Context → (Fin m → C) → C)
    (hEvaluate : ∀ ctx r, evaluateMultiplier ctx r = multiplier.evaluate ctx r)
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (terminalReduction pc.OStmt evaluateMultiplier).perfectCompleteness init impl
      (tableWitnessRelation (rel multiplier pc (Fin.last m)))
      (tableWitnessRelation (pc.evalRelWithContext Context)) := by
  let fallback :=
    fun (input : ProductSumcheck.Statement Context C (Fin.last m) × (∀ j, pc.OStmt j)) =>
      let (stmt, oracles) := input
      (Terminal.nextStatement stmt 0, oracles)
  apply perfectCompleteness_of_accepted_support (fallback := fallback)
  intro ⟨stmtIn, oracles⟩ packedTable hInput run hRun
  change run ∈ support ((terminalProver pc.OStmt).run (stmtIn, oracles) packedTable) at hRun
  rw [terminalProver_run] at hRun
  have hRunEq := OracleComp.eq_of_mem_support_pure _ hRun
  subst run
  let packedPoly := tableWitnessEquiv packedTable
  let value := terminalMessage packedTable stmtIn
  obtain ⟨hAccept, hOutput⟩ := verifyTerminal_honest multiplier pc
    (evaluateMultiplier := evaluateMultiplier) (hEvaluate := hEvaluate)
    stmtIn oracles packedPoly packedTable (hp := table_aeval packedTable) hInput
  have hValue : value = aeval stmtIn.challenges packedPoly.val :=
    terminalMessage_eq packedTable packedPoly (table_aeval packedTable) stmtIn
  refine ⟨?_, ?_⟩
  · change (terminalVerifier pc.OStmt evaluateMultiplier).toVerifier.verify (stmtIn, oracles)
      (Terminal.transcript value) = pure (Terminal.nextStatement stmtIn value, oracles)
    rw [terminalVerifier_verify, hAccept, hValue]
  · change ((Terminal.nextStatement stmtIn value, oracles), packedPoly) ∈
      pc.evalRelWithContext Context
    rw [hValue]
    exact hOutput

private theorem tailReduction_perfectCompleteness
    (multiplierTable : Context → (Fin m → Fin 2) → C)
    (hMultiplierTable : ∀ ctx b, multiplierTable ctx b = (multiplier ctx).val.eval (b : Fin m → C))
    (evaluateMultiplier : Context → (Fin m → C) → C)
    (hEvaluate : ∀ ctx r, evaluateMultiplier ctx r = multiplier.evaluate ctx r)
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (tailReduction pc.OStmt multiplierTable evaluateMultiplier).perfectCompleteness init impl
      (tableWitnessRelation (rel multiplier pc 0))
      (tableWitnessRelation (pc.evalRelWithContext Context)) := by
  have hLoopComplete : (tailLoopReduction pc.OStmt multiplierTable).perfectCompleteness init impl
      (tableWitnessRelation (rel multiplier pc 0))
      (tableWitnessRelation (rel multiplier pc (Fin.last m))) :=
    OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
      (ProductSumcheck.Statement Context C) (fun _ => pc.OStmt) (fun _ => (Fin m → Fin 2) → C)
      init impl (rel := fun i => tableWitnessRelation (rel multiplier pc i))
      (R := fun i => roundReduction pc.OStmt i multiplierTable)
      (hP := fun _ => inferInstance)
      (hV := fun _ => Verifier.GuardedForm.ofEmpty _
        (fun ⟨stmt, oracles⟩ => (⟨stmt.ctx, fun _ => 0, 0⟩, oracles)))
      (h := fun i state =>
        roundReduction_perfectCompleteness multiplier pc multiplierTable hMultiplierTable i
          (pure state) impl)
  unfold tailReduction
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers _ _
    (V₁ := Verifier.GuardedForm.ofEmpty _
      (fun ⟨stmt, oracles⟩ => (⟨stmt.ctx, fun _ => 0, 0⟩, oracles)))
    (V₂ := Verifier.GuardedForm.ofEmpty _
      (fun ⟨stmt, oracles⟩ => (Terminal.nextStatement stmt 0, oracles)))
    (hSeam := fun _ => Or.inl inferInstance) (h₁ := hLoopComplete)
    (h₂ := fun state =>
      terminalReduction_perfectCompleteness multiplier pc evaluateMultiplier hEvaluate
        (pure state) impl)

end ProductSumcheck

section Prefix

open TensorPrefix.Computable

variable {K L : Type} [Field K] [DecidableEq K] [Field L] [DecidableEq L]
  [Algebra K L] [SampleableType L] {κ ℓ m : ℕ}
  (P : RingSwitchingProfile K L κ) (h : ℓ = m + κ) (a : AbstractOStmtIn L m)

private theorem ringSwitchReduction_perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (ringSwitchReduction (TensorPrefix.commitment a).OStmt P.basis
      (fun x u => P.basis.repr x u) h).perfectCompleteness init impl
      (tableWitnessRelation (TensorPrefix.relIn P h a))
      (tableWitnessRelation ((TensorPrefix.commitment a).evalRelWithContext (Context L ℓ κ))) := by
  unfold ringSwitchReduction
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers _ _
    (V₁ := Verifier.GuardedForm.ofEmpty _
      (fun ⟨⟨query, _⟩, oracles⟩ => (⟨(query, fun _ => 0), Fin.elim0, 0⟩, oracles)))
    (V₂ := Verifier.GuardedForm.ofEmpty _
      (fun ⟨stmt, oracles⟩ => ((stmt.ctx, fun _ => 0, 0), oracles)))
    (hSeam := fun _ => Or.inl inferInstance)
    (h₁ := headReduction_perfectCompleteness P h a init impl)
    (h₂ := fun state => tailReduction_perfectCompleteness
      (TensorPrefix.multiplier P h) (TensorPrefix.commitment a)
      (multiplierTable := prefixMultiplierTable (fun x u => P.basis.repr x u) h)
      (hMultiplierTable := prefixMultiplierTable_eq P h)
      (evaluateMultiplier := prefixEvaluateMultiplier P.basis (fun x u => P.basis.repr x u) h)
      (hEvaluate := fun ctx r => congrFun (prefixEvaluateMultiplier_eq P h ctx) r)
      (pure state) impl)

end Prefix

section Openings

open BinaryBasefold
open TensorPrefix.Computable

variable {κ ℓ ℓ' R ϑ : ℕ}
variable {K L : Type} [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Field L] [Fintype L] [DecidableEq L] [SampleableType L] [Algebra K L]
variable [NeZero ℓ'] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
variable (b : Basis (Fin (2 ^ κ)) K L) [Fact (b 0 = 1)]
variable (hRate : ℓ' + R < 2 ^ κ) (h : ℓ = ℓ' + κ) (γ : ℕ)
variable (coordinates : L → (Fin κ → Fin 2) → K)
variable (hc : coordinates = fun x u => b.repr x (finFunctionFinEquiv u))

local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩

/-- An exact packed encoding and a valid evaluation claim make the executable unrolled
opening accept with probability one. -/
theorem unrolledReduction_perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness (init := init) (impl := impl)
      (oracleProof := unrolledReduction (ϑ := ϑ) (⇑b) coordinates h hRate γ ⟨b, rfl, hc⟩)
      (relation := strictInputRelation (ϑ := ϑ) b hRate h) := by
  let profile := biniusProfile κ L K b
  let inputOracle := binaryBasefoldInput κ L K b ℓ' R ϑ hRate
  let runtimeMultiplier := multiplier (⇑b) coordinates h ⟨b, rfl, hc⟩
  have hBasis : (⇑b ∘ finFunctionFinEquiv) = ⇑profile.basis :=
    (biniusProfile_basis_eq κ L K b).symm
  have hCoordinates : coordinates = fun x u => profile.basis.repr x u := by
    simpa only [profile, biniusProfile_basis_repr_eq] using hc
  have hHeadComplete :
      (headReduction (TensorPrefix.commitment inputOracle).OStmt
        (⇑b ∘ finFunctionFinEquiv) coordinates h).perfectCompleteness init impl
        (strictInputRelation (ϑ := ϑ) b hRate h)
        (tableWitnessRelation (TensorPrefix.headRelOut profile h inputOracle.strictView)) := by
    rw [hBasis, hCoordinates]
    exact headReduction_perfectCompleteness profile h inputOracle.strictView init impl
  have hHeadOut_eq_openingIn :
      tableWitnessRelation (TensorPrefix.headRelOut profile h inputOracle.strictView) =
        ProductClaim.strictInputRelation K (⇑b) runtimeMultiplier
          (ProductSumcheck.Statement.claim (m := ℓ')) tableWitnessEquiv
          (ϑ := ϑ) (h_rate := hRate) := by
    dsimp only [profile, inputOracle, runtimeMultiplier]
    rw [multiplier_eq (⇑b) coordinates h ⟨b, rfl, hc⟩ b rfl hc,
      Unrolled.headRelOut_strictView_eq]
    rfl
  let fallback :=
    fun (input : ((Fin ℓ → L) × L) × (∀ j, (TensorPrefix.commitment inputOracle).OStmt j)) =>
      let ((query, _), oracles) := input
      (headNext (m := ℓ') profile.basis (fun x u => profile.basis.repr x u) query
        (fun _ => 0) (fun _ => 0), oracles)
  unfold OracleProof.perfectCompleteness unrolledReduction
  refine OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (V₁ := Verifier.GuardedForm.ofEmpty _ fallback)
    (V₂ := Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
    (hSeam := fun _ => Or.inl inferInstance) (h₁ := hHeadComplete) (h₂ := ?_)
  intro state
  exact ProductClaim.openingReduction_perfectCompleteness K (⇑b) runtimeMultiplier
    (ProductSumcheck.Statement.claim (m := ℓ')) tableWitnessEquiv _ γ
    (ϑ := ϑ) (h_rate := hRate) (pure state) impl hHeadOut_eq_openingIn.le

/-- An exact packed encoding and a valid evaluation claim make the executable modular opening
accept with probability one. -/
theorem modularReduction_perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness (init := init) (impl := impl)
      (oracleProof := modularReduction (ϑ := ϑ) (⇑b) coordinates h hRate γ ⟨b, rfl, hc⟩)
      (relation := strictInputRelation (ϑ := ϑ) b hRate h) := by
  let profile := biniusProfile κ L K b
  let inputOracle := RingSwitch.inputInterface κ K b (ϑ := ϑ) hRate
  let openingQuery := Opening.contextualQuery (L := L) (ℓ := ℓ') (Context L ℓ κ)
  have hBasis : (⇑b ∘ finFunctionFinEquiv) = ⇑profile.basis :=
    (biniusProfile_basis_eq κ L K b).symm
  have hCoordinates : coordinates = fun x u => profile.basis.repr x u := by
    simpa only [profile, biniusProfile_basis_repr_eq] using hc
  have hPrefixComplete :
      (ringSwitchReduction (TensorPrefix.commitment inputOracle).OStmt
        (⇑b ∘ finFunctionFinEquiv) coordinates h).perfectCompleteness init impl
        (strictInputRelation (ϑ := ϑ) b hRate h)
        (tableWitnessRelation ((TensorPrefix.commitment inputOracle.strictView).evalRelWithContext
          (Context L ℓ κ))) := by
    rw [hBasis, hCoordinates]
    exact ringSwitchReduction_perfectCompleteness profile h inputOracle.strictView init impl
  have hPrefixOut_eq_openingIn :
      tableWitnessRelation ((TensorPrefix.commitment inputOracle.strictView).evalRelWithContext
          (Context L ℓ κ)) =
        Opening.strictInputRelation K (⇑b) openingQuery tableWitnessEquiv
          (ϑ := ϑ) (h_rate := hRate) := by
    rw [RingSwitch.opening_strict_input_eq]
    rfl
  let fallback :=
    fun (input : ((Fin ℓ → L) × L) × (∀ j, (TensorPrefix.commitment inputOracle).OStmt j)) =>
      let ((query, _), oracles) := input
      (((query, fun _ : Fin κ => (0 : L)), (fun _ : Fin ℓ' => (0 : L)), (0 : L)), oracles)
  unfold OracleProof.perfectCompleteness modularReduction
  refine OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (V₁ := Verifier.GuardedForm.ofEmpty _ fallback)
    (V₂ := Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
    (hSeam := fun _ => Or.inl inferInstance) (h₁ := hPrefixComplete) (h₂ := ?_)
  intro state
  rw [hPrefixOut_eq_openingIn]
  exact Opening.openingReduction_perfectCompleteness K (⇑b) openingQuery tableWitnessEquiv
    γ (ϑ := ϑ) (h_rate := hRate) (pure state) impl

end Openings

end Binius.FRIBinius.Executable
