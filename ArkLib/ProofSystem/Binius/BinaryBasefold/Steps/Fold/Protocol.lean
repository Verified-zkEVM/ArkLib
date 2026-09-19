/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
public import ArkLib.ToVCVio.Simulation
public import ArkLib.OracleReduction.Completeness
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness

/-!
# Binary Basefold Fold Step
-/

@[expose] public section


namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
open scoped NNReal ProbabilityTheory

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
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section SingleIteratedSteps
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context

section FoldStep

/-! The prover for the `i`-th round of Binary Foldfold. -/
noncomputable def foldOracleProver (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    -- current round
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.castSucc)
    -- Both stmt and wit advances, but oStmt only advances at the commitment rounds only
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecFold (L := L)) where
  PrvState := foldPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage -- There are either 2 or 3 messages in the pSpec depending on commitment rounds
  | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => do
    -- USE THE SHARED KERNEL (Guarantees match with foldStepLogic)
    let h_i := foldProverComputeMsg (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i wit
    -- Return message and update state
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))
  -- | ⟨2, h⟩ => nomatch h -- no challenge after third message
  -- output : PrvState → StmtOut × (∀i, OracleStatement i) × WitOut
  output := fun finalPrvState =>
    let (stmt, oStmt, wit, h_i, r_i') := finalPrvState
    let t := FullTranscript.mk2 (pSpec := pSpecFold (L := L)) h_i r_i'
    -- 2. Delegate to Logic Instance
    pure ((foldStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i).proverOut stmt wit oStmt t)

/-! The oracle verifier for the `i`-th round of Binary Foldfold. -/
open Classical in
def foldOracleVerifier (i : Fin ℓ) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (Oₘ := fun i => by infer_instance)
    -- next round
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (pSpec := pSpecFold (L := L)) where
  -- The core verification logic. Takes the input statement `stmtIn` and the transcript, and
  -- performs an oracle computation that outputs a new statement
  verify := fun stmtIn pSpecChallenges => do
    let h_i ← query (spec := [(pSpecFold (L := L)).Message]ₒ) ⟨⟨0, by rfl⟩, (by exact ())⟩
    let r_i' := pSpecChallenges ⟨1, rfl⟩
    let t := FullTranscript.mk2 h_i r_i'
    let logic := (foldStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  outputOracle := .inl {
    embed := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := mp) i).embed
    hEq := by
      intro oracleIdx
      simp only [foldStepLogic, Fin.is_lt, ↓reduceDIte, Fin.eta,
        Function.Embedding.coeFn_mk]
    outputInterface_heq := by
      intro oracleIdx
      simp only [foldStepLogic, Fin.is_lt, ↓reduceDIte, Fin.eta,
        Function.Embedding.coeFn_mk]
      rfl }

/-! The oracle reduction that is the `i`-th round of Binary Foldfold. -/
noncomputable def foldOracleReduction (i : Fin ℓ) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L)) where
  prover := foldOracleProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i
  verifier := foldOracleVerifier 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-! Simplifies membership in a conditional singleton set.
  `x ∈ (if c then {a} else {b})` is equivalent to `x = (if c then a else b)`.
-/
lemma mem_ite_singleton {α : Type*} {c : Prop} [Decidable c] {a b x : α} :
    (x ∈ (if c then {a} else {b} : Set α)) ↔ (x = if c then a else b) := by
  split_ifs with h
  · simp only [Set.mem_singleton_iff] -- Case c is True: x ∈ {a} ↔ x = a
  · simp only [Set.mem_singleton_iff] -- Case c is False: x ∈ {b} ↔ x = b

/-!
Perfect completeness for the binary folding oracle reduction.

This theorem proves that the honest prover-verifier interaction for one round of binary folding
always succeeds (with probability 1) and produces valid outputs.

**Proof Strategy:**
1. Unroll the 2-message reduction to convert probabilistic statement to logical statement
2. Split into safety (no failures) and correctness (valid outputs)
3. For safety: prove the verifier never crashes on honest prover messages
4. For correctness: extract the challenge from the support and apply the logic completeness lemma

**Key Technique:**
- Use `foldStep_is_logic_complete` to get the pure logic properties
- Convert the challenge function by proving the only valid challenge index is 1
- Rewrite all intermediate variables to their concrete values
- Apply the logic properties to complete the proof
-/
open Classical in
omit [DecidableEq 𝔽q] in
set_option backward.isDefEq.respectTransparency false in
theorem foldOracleReduction_perfectCompleteness (hInit : NeverFail init) (i : Fin ℓ) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFold (L := L))
      (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc (mp := mp))
      (relOut := strictFoldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i (mp := mp))
      (oracleReduction := foldOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
      (init := init)
      (impl := impl) := by
  classical
  -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  let : OracleSpec.Inhabited []ₒ := { inhabitedB := fun i => PEmpty.elim i }
  let : OracleSpec.Fintype [(pSpecFold (L := L)).Challenge]ₒ :=
    { fintypeB := fun j => by
        change Fintype ((pSpecFold (L := L)).Challenge j.1)
        exact Fintype.ofFinite _ }
  let : OracleSpec.Inhabited [(pSpecFold (L := L)).Challenge]ₒ :=
    { inhabitedB := fun j => by
        change Inhabited ((pSpecFold (L := L)).Challenge j.1)
        exact Classical.inhabited_of_nonempty inferInstance }
  -- **NOTE**: this requires `ProtocolSpec.challengeOracleInterface` to avoid conflict
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecFold (L := L)) (init := init) (impl := impl)
    (hInit := hInit) (hDir0 := by rfl) (hDir1 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image,
      IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- The support argument is uniform in the initial simulation state.
  apply OptionT.probEvent_eq_one_of_simulateQ_support_bind
  intro output h_output
  dsimp only [foldOracleReduction, foldOracleProver, foldOracleVerifier,
    OracleVerifier.toVerifier] at h_output
  simp only [liftComp_pure, liftM_pure, pure_bind, OptionT.run_bind,
    OptionT.run_pure] at h_output
  simp only [liftComp_eq_liftM, OptionT.run_monadLift, Option.elimM,
    bind_map_left, support_bind, Set.mem_iUnion,
    exists_prop] at h_output
  obtain ⟨r1, _, h_output⟩ := h_output
  dsimp only [liftM, monadLift, MonadLift.monadLift] at h_output
  simp only [Option.elim] at h_output
  let step := foldStepLogic 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i
  have h_complete := foldStep_is_logic_complete 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i
      stmtIn witIn oStmtIn
      (fun ⟨j, hj⟩ => by
        match j with
        | 0 => nomatch hj
        | 1 => exact r1) h_relIn
  let tr : (pSpecFold (L := L)).FullTranscript :=
    FullTranscript.mk2 (foldProverComputeMsg 𝔽q β (𝓑 := 𝓑) i witIn) r1
  obtain ⟨h_check, h_rel, h_stmt, h_oracles⟩ := h_complete
  change step.verifierCheck stmtIn tr at h_check
  simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output
  simp only [OptionT.run, OptionT.mk, support_liftComp, support_map,
    Set.mem_image] at h_output
  erw [simulateQ_bind, OptionT.simulateQ_simOracle2_liftM_query_T2, pure_bind] at h_output
  dsimp only [step, tr] at h_check
  have h_answer : @OracleInterface.answer _
      (instOracleInterfaceMessagePSpecFold (L := L) ⟨0, rfl⟩)
      (foldProverComputeMsg 𝔽q β (𝓑 := 𝓑) i witIn :
        (pSpecFold (L := L)).Message ⟨0, rfl⟩) () =
      foldProverComputeMsg 𝔽q β (𝓑 := 𝓑) i witIn := rfl
  dsimp only [OracleInterface.answer, FullTranscript.mk2, FullTranscript.messages,
    FullTranscript.challenges] at h_output
  simp only [guard_eq, Prod.mk.eta, ↓existsAndEq, and_true] at h_output
  dsimp only [OracleInterface.answer] at h_answer
  simp only [h_answer, h_check, if_pos] at h_output
  erw [OptionT.simulateQ_pure] at h_output
  simp only [OptionT.pure, OptionT.mk,
    support_pure, Set.mem_singleton_iff, exists_eq_left, Option.map_some] at h_output
  refine ⟨_, h_output, ?_⟩
  have h_mat : (foldOracleVerifier 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑) (mp := mp) i).materializeOutput
      tr.challenges oStmtIn tr.messages = oStmtIn := by
    funext j
    simp [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
      foldOracleVerifier, foldStepLogic]
  change oStmtIn = materializeOutputByEmbedding step.embed step.hEq oStmtIn tr at h_oracles
  change step.completeness_relOut ((step.verifierOut stmtIn tr,
    materializeOutputByEmbedding step.embed step.hEq oStmtIn tr),
    (step.proverOut stmtIn witIn oStmtIn tr).2) at h_rel
  rw [← h_oracles] at h_rel
  change step.completeness_relOut ((step.verifierOut stmtIn tr,
      (foldOracleVerifier 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑) (mp := mp) i).materializeOutput
        tr.challenges oStmtIn tr.messages), (step.proverOut stmtIn witIn oStmtIn tr).2) ∧ _
  rw [h_mat]
  exact ⟨h_rel, h_stmt, h_mat.symm⟩

end FoldStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
