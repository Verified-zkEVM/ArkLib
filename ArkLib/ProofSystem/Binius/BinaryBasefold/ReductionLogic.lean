/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
public import ArkLib.ProofSystem.Sumcheck.Structured.RoundLemmas
public import ArkLib.OracleReduction.Security.Guarded

/-!
# Binary Basefold: the logic of a single step

A `ReductionLogicStep` is the deterministic content of one interactive reduction step: the
verifier's check and output statement on a full transcript, the selection of its output oracles,
the honest prover's transcript as a function of the challenges and its output, and the relations
under which the step is complete. Its strong completeness (`ReductionLogicStep.IsStronglyComplete`)
is the per-challenge statement that the honest transcript passes the check and lands in the output
relation. An oracle verifier that queries one prover message and runs a step's check and output
on the transcript rebuilt from the answer has the guarded form
`ReductionLogicStep.queryGuardedForm`, through `Verifier.GuardedForm.ofQueryGuard`.

## Main definitions and statements

* `foldStepLogic`, `foldStepLogic_isStronglyComplete`: the fold step. The prover sends the
  univariate round polynomial `hᵢ`; the verifier checks `hᵢ(𝓑 0) + hᵢ(𝓑 1) = sᵢ` and sets
  `sᵢ₊₁ := hᵢ(r'ᵢ)`.
* `commitStepLogic`, `commitStepLogic_isStronglyComplete`: the commit step at a commitment round.
  The prover sends its folded word `f⁽ⁱ⁺¹⁾` as a new oracle.
* `finalSumcheckStepLogic`, `finalSumcheckStepLogic_isStronglyComplete`: the final sum-check
  step. The prover sends the constant `c` of `f⁽ˡ⁾`; the verifier checks `s_ℓ = eq̃(r, r') · c`.

The oracle reductions built from these steps are in `Steps/`.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  The fold step is lines 1–4 of the loop of the evaluation IOP of Construction 4.12, the commit
  step line 6, and the final sum-check step line 5 with step 3. Their completeness is part of
  Theorem 4.13, with the fold of the prover's word as in Lemma 4.14.
-/

@[expose] public section

namespace Binius.BinaryBasefold

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section GenericLogic

/-- Every output oracle type is the type of the source it is selected from by `embed`: an input
oracle (`Sum.inl`) or a prover message (`Sum.inr`). -/
def EmbeddingTypeEq {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type}
    {OracleOut : ιₒₒ → Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx) :=
  ∀ i, OracleOut i =
    match embed i with
    | Sum.inl j => OracleIn j
    | Sum.inr j => pSpec.Message j

/-- The output oracles selected by an embedding, as values: each output oracle is the input oracle
or prover message it is selected from, cast along `EmbeddingTypeEq`. -/
def materializeOutputByEmbedding
    {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type} {OracleOut : ιₒₒ → Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx)
    (hTypeEq : EmbeddingTypeEq (OracleIn := OracleIn) (OracleOut := OracleOut) (pSpec := pSpec)
      embed)
    (oStmt : ∀ i, OracleIn i) (transcript : FullTranscript pSpec) : ∀ i, OracleOut i :=
  fun i => match h : embed i with
    | Sum.inl j => by
      have hType : OracleOut i = OracleIn j := by simpa only [h] using hTypeEq i
      exact cast hType.symm (oStmt j)
    | Sum.inr j => by
      have hType : OracleOut i = pSpec.Message j := by simpa only [h] using hTypeEq i
      exact cast hType.symm (transcript.messages j)

/-- An output oracle selected from an input oracle is that input oracle, cast along the type
equation. -/
@[simp]
theorem materializeOutputByEmbedding_inl
    {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type} {OracleOut : ιₒₒ → Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx)
    (hTypeEq : EmbeddingTypeEq (OracleIn := OracleIn) (OracleOut := OracleOut) (pSpec := pSpec)
      embed)
    (oStmt : ∀ i, OracleIn i) (transcript : FullTranscript pSpec)
    (i : ιₒₒ) (j : ιₒᵢ) (h : embed i = Sum.inl j) :
    materializeOutputByEmbedding embed hTypeEq oStmt transcript i =
      cast (by simpa only [h] using (hTypeEq i).symm) (oStmt j) := by
  unfold materializeOutputByEmbedding
  split
  · rename_i h'
    rw [h] at h'
    simp only [Sum.inl.injEq] at h'
    subst h'
    rfl
  · rename_i h'
    rw [h] at h'
    cases h'

/-- An output oracle selected from a prover message is that message, cast along the type
equation. -/
@[simp]
theorem materializeOutputByEmbedding_inr
    {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type} {OracleOut : ιₒₒ → Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx)
    (hTypeEq : EmbeddingTypeEq (OracleIn := OracleIn) (OracleOut := OracleOut) (pSpec := pSpec)
      embed)
    (oStmt : ∀ i, OracleIn i) (transcript : FullTranscript pSpec)
    (i : ιₒₒ) (j : pSpec.MessageIdx) (h : embed i = Sum.inr j) :
    materializeOutputByEmbedding embed hTypeEq oStmt transcript i =
      cast (by simpa only [h] using (hTypeEq i).symm) (transcript.messages j) := by
  unfold materializeOutputByEmbedding
  split
  · rename_i h'
    rw [h] at h'
    cases h'
  · rename_i h'
    rw [h] at h'
    simp only [Sum.inr.injEq] at h'
    subst h'
    rfl

/-- The deterministic logic of one interactive reduction step: the completeness relations, the
verifier's check and output statement, the selection of the output oracles, the honest prover's
transcript as a function of the challenges, and the honest prover's output. The oracle verifier
and prover of the step are built from it, and its strong completeness (`IsStronglyComplete`) is
what their perfect completeness reduces to. -/
structure ReductionLogicStep
    (StmtIn WitIn : Type)
    {ιₒᵢ ιₒₒ : Type}
    (OracleIn : ιₒᵢ → Type) (OracleOut : ιₒₒ → Type)
    (StmtOut WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The input relation under which the step is complete. -/
  completeness_relIn : (StmtIn × (∀ i, OracleIn i)) × WitIn → Prop
  /-- The output relation the honest execution lands in. -/
  completeness_relOut : (StmtOut × (∀ i, OracleOut i)) × WitOut → Prop
  /-- The verifier's check on the full transcript. -/
  verifierCheck : StmtIn → FullTranscript pSpec → Prop
  /-- The verifier's output statement on the full transcript. -/
  verifierOut : StmtIn → FullTranscript pSpec → StmtOut
  /-- Which input oracle or prover message each output oracle is. -/
  embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx
  /-- The output oracle types agree with their sources. -/
  hEq : EmbeddingTypeEq (OracleIn := OracleIn) (OracleOut := OracleOut) (ιₒᵢ := ιₒᵢ)
    (ιₒₒ := ιₒₒ) (pSpec := pSpec) (embed := embed)
  /-- The honest prover's transcript, given all the challenges. -/
  honestProverTranscript : StmtIn → WitIn → (∀ i, OracleIn i) → pSpec.Challenges →
    FullTranscript pSpec
  /-- The honest prover's output statement, output oracles and output witness. -/
  proverOut : StmtIn → WitIn → (∀ i, OracleIn i) → FullTranscript pSpec →
    ((StmtOut × (∀ i, OracleOut i)) × WitOut)

/-- The output oracles of a logic step as values, selected by its embedding. -/
abbrev ReductionLogicStep.materializeOutput
    {StmtIn WitIn : Type}
    {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type} {OracleOut : ιₒₒ → Type}
    {StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (step : ReductionLogicStep StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec)
    (oStmtIn : ∀ i, OracleIn i) (transcript : FullTranscript pSpec) : ∀ i, OracleOut i :=
  materializeOutputByEmbedding step.embed step.hEq oStmtIn transcript

/-- **Strong completeness** of a logic step: for every input in the input relation and every
choice of challenges, the honest transcript passes the verifier's check, the verifier's output with
the prover's output witness lies in the output relation, and the prover and the verifier agree on
the output statement and output oracles. -/
@[reducible]
def ReductionLogicStep.IsStronglyComplete
    {StmtIn WitIn : Type}
    {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type} {OracleOut : ιₒₒ → Type}
    {StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (step : ReductionLogicStep StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec) : Prop :=
  ∀ (stmtIn : StmtIn) (witIn : WitIn) (oStmtIn : ∀ i, OracleIn i) (challenges : pSpec.Challenges),
    (h_relIn : step.completeness_relIn ((stmtIn, oStmtIn), witIn)) →
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript ∧
    let verifierStmtOut := step.verifierOut stmtIn transcript
    let verifierOStmtOut := materializeOutputByEmbedding step.embed step.hEq oStmtIn transcript
    let ((proverStmtOut, proverOStmtOut), proverWitOut) :=
      step.proverOut stmtIn witIn oStmtIn transcript
    step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) ∧
    proverStmtOut = verifierStmtOut ∧
    proverOStmtOut = verifierOStmtOut

section QueryGuardedForm

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)] [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
  [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  (step : ReductionLogicStep StmtIn WitIn OStmtIn OStmtOut StmtOut WitOut pSpec)
  [∀ s t, Decidable (step.verifierCheck s t)]
  (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
  (q : [pSpec.Message]ₒ.Domain)
  (transcriptOf : [pSpec.Message]ₒ.Range q → pSpec.Challenges → FullTranscript pSpec)

/-- The guarded form of an oracle verifier built from a logic step: it queries one prover message,
rebuilds the transcript from the answer and the challenges (`transcriptOf`), and runs the step's
check and output statement on it. The guard is the step's check on the rebuilt transcript, and the
verdict is the step's output statement there, with the materialized output oracles. -/
def ReductionLogicStep.queryGuardedForm
    (hV : ∀ stmt chals, verifier.verify stmt chals = do
      let a ← query (spec := [pSpec.Message]ₒ) q
      guard (step.verifierCheck stmt (transcriptOf a chals))
      return step.verifierOut stmt (transcriptOf a chals)) :
    verifier.toVerifier.GuardedForm :=
  Verifier.GuardedForm.ofQueryGuard verifier q
    (fun s a c => step.verifierCheck s (transcriptOf a c))
    (fun s a c => step.verifierOut s (transcriptOf a c)) hV

end QueryGuardedForm

end GenericLogic

section SingleIteratedSteps
variable {Context : Type} {multpoly : Context → MultilinearPoly L ℓ}
section FoldStep

/-- The logic of the `i`-th fold step. The prover sends the univariate round polynomial of its
current round polynomial; the verifier checks that its values at the two points of `𝓑` sum to the
sum-check target, and outputs the statement with target the round polynomial at the challenge and
the challenge appended. The oracle statements pass through. Completeness is stated for the strict
relations. -/
def foldStepLogic (i : Fin ℓ) :
    ReductionLogicStep
      -- In/Out Types
      (Statement (L := L) Context i.castSucc)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      -- Protocol Spec
      (pSpecFold (L := L))
      where
  -- 1. Relations (using strict relations for completeness)
  completeness_relIn := fun ((s, o), w) =>
    ((s, o), w) ∈ strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i.castSucc (multpoly := multpoly)
  completeness_relOut := fun ((s, o), w) =>
    ((s, o), w) ∈ strictFoldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i (multpoly := multpoly)
  -- 2. Verifier Logic (Using extracted kernels)
  verifierCheck := fun s t =>
    foldVerifierCheck i s (𝓑 := 𝓑) (t.messages ⟨0, rfl⟩)
  verifierOut := fun s t =>
    foldVerifierStmtOut i s (t.messages ⟨0, rfl⟩) (t.challenges ⟨1, rfl⟩)
  embed := ⟨fun j => by
    if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
      exact Sum.inl ⟨j.val, by omega⟩
    else omega
  , by
    intro a b h_ab_eq
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Sum.inl.injEq] at h_ab_eq
    exact h_ab_eq
  ⟩
  hEq := fun oracleIdx => by
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Function.Embedding.coeFn_mk]
  -- 3. Honest Prover Logic (Constructing the transcript)
  --    "Given input and the future challenge, what would the transcript look like?"
  honestProverTranscript := fun _stmtIn witIn _oStmtIn chal =>
    let msg : ↥L⦃≤ 2⦄[X] := foldProverComputeMsg (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i witIn
    FullTranscript.mk2 msg (chal ⟨1, rfl⟩)
  -- 4. Prover Output (State Update)
  proverOut := fun s w o t =>
    let h_i : (pSpecFold (L := L)).«Type» 0 := t ⟨0, by omega⟩
    let r_i' : (pSpecFold (L := L)).«Type» 1 := t ⟨1, by omega⟩
    getFoldProverFinalOutput 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
      (s, o, w, h_i, r_i')

omit [SampleableType L] [DecidableEq 𝔽q] [CharP L 2] h_β₀_eq_1 in
/-- The fold step is strongly complete: from the strict round relation at `i`, the honest round
polynomial passes the check, and the honest output lies in the strict fold-step output relation,
for every challenge. -/
lemma foldStepLogic_isStronglyComplete (i : Fin ℓ) :
    (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i).IsStronglyComplete := by
  classical
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := step.materializeOutput oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  -- Extract properties from h_relIn (strictRoundRelation)
  simp only [foldStepLogic, strictRoundRelation, strictRoundRelationProp,
    Set.mem_ofPred_eq] at h_relIn
  -- We'll need sumcheck consistency for Fact 1, so extract it from either branch
  have h_sumcheck_cons : sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _)
      stmtIn.sumcheck_target witIn.H :=
    h_relIn.1
  let h_VCheck_passed : step.verifierCheck stmtIn transcript := by
    -- Fact 1: Verifier check passes (sumcheck condition)
    simp only [step, foldStepLogic, foldVerifierCheck, foldProverComputeMsg]
    rw [h_sumcheck_cons]
    exact Sumcheck.Structured.eval_add_eval_getSumcheckRoundPoly ℓ 𝓑 i witIn.H
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    -- Fact 3: Prover and verifier statements agree
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, foldStepLogic]
    simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Fin.val_succ]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.2
      = step.materializeOutput oStmtIn transcript
    simp only [step, foldStepLogic]
    -- Fact 4: Prover and verifier oracle statements agree
    funext j
    have hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc := j.isLt
    simp only [ReductionLogicStep.materializeOutput, materializeOutputByEmbedding,
      Function.Embedding.coeFn_mk, Fin.eta]
    split
    · rename_i j' heq
      -- heq : (if hj : ↑j < ... then Sum.inl j else ...) = Sum.inl j'
      -- Since hj holds, we have Sum.inl j = Sum.inl j', so j = j'
      simp only [hj, ↓reduceDIte] at heq
      cases heq
      simp
    · rename_i heq
      -- This case is impossible: the if-then-else evaluates to Sum.inl j when hj holds
      -- So we have Sum.inl j = Sum.inr j✝, which is a contradiction
      simp only [hj, ↓reduceDIte] at heq
      -- heq : Sum.inl j = Sum.inr j✝ is a contradiction
      cases heq
  -- Key fact: Oracle statements are unchanged in the fold step
  -- (all oracle indices map via Sum.inl in the embedding)
  have h_verifierOStmtOut_eq : verifierOStmtOut = oStmtIn := by
    rw [← hOStmtOut_eq]
    simp only [proverOStmtOut, proverOutput, step, foldStepLogic]
  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- Fact 2: Output relation holds (strictFoldStepRelOut)
    simp only [step, foldStepLogic, strictFoldStepRelOut, strictFoldStepRelOutProp,
      Set.mem_ofPred_eq]
    simp only [Fin.val_succ]
    constructor
    · -- Part 2.1: sumcheck consistency
      unfold sumcheckConsistencyProp
      dsimp only [verifierStmtOut, proverWitOut, proverOutput]
      simp only [step, foldStepLogic, foldVerifierStmtOut, getFoldProverFinalOutput, transcript]
      exact (Sumcheck.Structured.sum_projectToNextSumcheckPoly_uniform ℓ 𝓑 i _ _).symm
    · -- Part 2.2: strictOracleWitnessConsistency
      simp only [Fin.val_castSucc] at h_relIn
      have h_oracleWitConsistency_In := h_relIn.2
      rw [h_verifierOStmtOut_eq];
      dsimp only [strictOracleWitnessConsistency] at h_oracleWitConsistency_In ⊢
      -- Extract the three components from the input
      obtain ⟨h_wit_struct_In, h_oracle_folding_In⟩ :=
        h_oracleWitConsistency_In
      -- Now prove each component for the output
      refine ⟨?_, ?_⟩
      · -- Component 1: witnessStructuralInvariant
        unfold witnessStructuralInvariant
        obtain ⟨h_H_In, h_f_In⟩ := h_wit_struct_In
        dsimp only [Fin.val_succ, proverWitOut, proverOutput, step,
          foldStepLogic, verifierStmtOut]
        constructor
        · rw [h_H_In]
          exact (Sumcheck.Structured.projectToMidSumcheckPoly_succ ℓ witIn.t _ i _ _).symm
        · rw [h_f_In]
          exact (getMidCodewords_succ 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn.t i stmtIn.challenges
            (transcript.challenges ⟨1, by rfl⟩)).symm
      · -- Component 2: strictOracleFoldingConsistencyProp
        have h_oracleIdx_eq : (OracleFrontierIndex.mkFromStmtIdx i.castSucc).val
          = (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i).val := by rfl
        have h_challenges_eq : Fin.init verifierStmtOut.challenges = stmtIn.challenges :=
          Fin.init_snoc (α := fun _ => L) _ _
        rw! (castMode := .all) [h_oracleIdx_eq] at h_oracle_folding_In
        simp only [Fin.val_succ, OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc,
          Fin.val_castSucc, Fin.take_eq_self, Fin.take_eq_init] at h_oracle_folding_In ⊢
        rw [h_challenges_eq]
        exact h_oracle_folding_In
  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

end FoldStep

section CommitStep

/-- The output oracles of a commit step: the old oracles, then the sent oracle as the last one. -/
def commitStepLogic_embedFn (i : Fin ℓ) :
    (Fin (toOutCodewordsCount ℓ ϑ i.succ)) →
      Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕
        (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).MessageIdx :=
  fun j => by
  if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
    exact Sum.inl ⟨j.val, hj⟩
  else
    exact Sum.inr ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- At a commitment round, `commitStepLogic_embedFn` is injective. -/
theorem commitStepLogic_embedFn_injective (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    Function.Injective
      (commitStepLogic_embedFn 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i) := by
  intro a b h_ab_eq
  simp only [MessageIdx, commitStepLogic_embedFn] at h_ab_eq
  split_ifs at h_ab_eq with h_ab_eq_l h_ab_eq_r
  · simp only [Sum.inl.injEq, Fin.mk.injEq] at h_ab_eq; apply Fin.eq_of_val_eq; exact h_ab_eq
  · have ha_lt : a < toOutCodewordsCount ℓ ϑ i.succ := by omega
    have hb_lt : b < toOutCodewordsCount ℓ ϑ i.succ := by omega
    conv_rhs at ha_lt => rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    conv_rhs at hb_lt => rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    simp only [hCR, ↓reduceIte] at ha_lt hb_lt
    omega

/-- The output-oracle embedding of a commit step at a commitment round. -/
def commitStepLogic_embed (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    Fin (toOutCodewordsCount ℓ ϑ i.succ) ↪
      Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕
        (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).MessageIdx := ⟨
  commitStepLogic_embedFn 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i,
  commitStepLogic_embedFn_injective 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i hCR
  ⟩

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- At a commitment round, the output oracle types of a commit step agree with their sources: the
sent oracle is the oracle statement at the next oracle position. -/
theorem commitStepLogic_embeddingTypeEq (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    EmbeddingTypeEq
    (OracleIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (OracleOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (ιₒᵢ := Fin (toOutCodewordsCount ℓ ϑ i.castSucc))
    (ιₒₒ := Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (pSpec := pSpecCommit 𝔽q β i)
    (embed := commitStepLogic_embed 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i hCR) :=
  fun oracleIdx => by
    unfold OracleStatement pSpecCommit commitStepLogic_embed commitStepLogic_embedFn
    simp only [MessageIdx, Function.Embedding.coeFn_mk, Message,
      Matrix.cons_val_fin_one]
    by_cases hlt : oracleIdx.val < toOutCodewordsCount ℓ ϑ i.castSucc
    · simp only [hlt, ↓reduceDIte]
    · simp only [hlt, ↓reduceDIte]
      have hOracleIdx_lt : oracleIdx.val < toOutCodewordsCount ℓ ϑ i.succ := by omega
      simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hCR, ↓reduceIte] at hOracleIdx_lt
      have hOracleIdx : oracleIdx = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
      simp_rw [hOracleIdx]
      have h := toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ (i := i) (hCR := hCR)
      unfold OracleFunction
      congr 1; congr 1
      funext x
      congr 1; congr 1
      simp only [Fin.mk.injEq]; rw [h]

/-- The logic of the commit step at a commitment round `i`. The prover sends its folded word as an
oracle; the verifier accepts and keeps the statement, and the sent oracle becomes the last oracle
statement. -/
def commitStepLogic (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    ReductionLogicStep
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictFoldStepRelOut (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i
  completeness_relOut := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictRoundRelation (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ
  -- No verification needed - just accept
  verifierCheck := fun _ _ => True
  -- Statement doesn't change
  verifierOut := fun stmt _ => stmt
  embed := commitStepLogic_embed 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR
  hEq := commitStepLogic_embeddingTypeEq 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR
  -- No challenges in 1-message protocol, so transcript is just the message
  honestProverTranscript := fun _stmt wit _oStmt _challenges =>
    fun ⟨0, _⟩ => wit.f
  -- Prover output: statement unchanged, oracle extended with new function
  proverOut := fun stmt wit oStmtIn transcript =>
    let oStmtOut :=
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn (newOracleFn := wit.f)
    ((stmt, oStmtOut), wit)

omit [Field L] [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L] in
private theorem cast_apply_eq_apply_cast {A B : Type} (h : A = B) (f : A → L) (x : B) :
    cast (congrArg (· → L) h) f x = f (cast h.symm x) := by
  subst h
  rfl

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- Appending the sent oracle with `snoc_oracle` is the commit step's output-oracle selection. -/
lemma snoc_oracle_eq_commitStepLogic_materializeOutput
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩))
    (transcript : FullTranscript (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (h_transcript_eq : transcript.messages ⟨0, rfl⟩ = newOracle) :
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn newOracle =
    (commitStepLogic (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).materializeOutput
        oStmtIn transcript := by
  change _ = materializeOutputByEmbedding
    (commitStepLogic (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed
    (commitStepLogic (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).hEq oStmtIn transcript
  funext j
  dsimp only [snoc_oracle]
  simp only [hCR, ↓reduceDIte]
  have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
  by_cases hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
  · -- Old oracle case: embed j = Sum.inl
    have h_embed : (commitStepLogic (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed j =
        Sum.inl ⟨j.val, hj⟩ := by
      simp only [commitStepLogic, commitStepLogic_embed, Function.Embedding.coeFn_mk,
        commitStepLogic_embedFn, hj, dite_eq_left]
    rw [materializeOutputByEmbedding_inl
      (embed := (commitStepLogic (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed)
      (hTypeEq := (commitStepLogic (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).hEq)
      (oStmt := oStmtIn) (transcript := transcript) (i := j)
      (j := ⟨j.val, hj⟩) (h := h_embed)]
    simp only [hj, dite_eq_left]
    rfl
  · -- New oracle case: embed j = Sum.inr 0
    have h_embed : (commitStepLogic (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed j =
        Sum.inr ⟨0, rfl⟩ := by
      simp only [commitStepLogic, commitStepLogic_embed, Function.Embedding.coeFn_mk,
        commitStepLogic_embedFn, hj, dite_eq_right, not_false_eq_true]
      rfl
    rw [materializeOutputByEmbedding_inr
      (embed := (commitStepLogic (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed)
      (hTypeEq := (commitStepLogic (multpoly := multpoly) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).hEq)
      (oStmt := oStmtIn) (transcript := transcript) (i := j)
      (j := ⟨0, rfl⟩) (h := h_embed)]
    simp only [hj, dite_eq_right, not_false_eq_true]
    rw [← h_transcript_eq]
    funext x
    have h_msg0: transcript.messages ⟨0, rfl⟩ = transcript 0 := by rfl
    rw [h_msg0]
    -- ⊢ transcript 0 (cast ⋯ x) = cast ⋯ (transcript 0) x
    symm
    apply cast_apply_eq_apply_cast
    have h_j_eq : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by
      have h_lt := j.isLt
      conv_rhs at h_lt => rw [h_count_succ]
      omega
    -- Show: oraclePositionToDomainIndex j = j.val * ϑ
    have h_idx_eq : (⟨i.val + 1, by omega⟩ : Fin r)
      = (⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩) := by
      apply Fin.eq_of_val_eq
      simp only [h_j_eq]
      rw [toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ i hCR]
    rw [h_idx_eq]

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- Appending an oracle does not change the first oracle. -/
lemma getFirstOracle_snoc_oracle
    (i : Fin ℓ) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := destIdx)) :
    getFirstOracle 𝔽q β
    (snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_destIdx oStmtIn newOracleFn) =
    getFirstOracle 𝔽q β oStmtIn := by
  unfold getFirstOracle snoc_oracle
  have h_lt : 0 < toOutCodewordsCount ℓ ϑ i.castSucc := by
    have h := (instNeZeroNatToOutCodewordsCount ℓ ϑ i.castSucc).out
    omega
  simp only [Fin.mk_zero', h_lt, ↓reduceDIte]
  rfl

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- At a commitment round, if the witness is structured and the oracle statements are the honest
folds of the witness's codeword, then so are the commit step's output oracles at the next oracle
frontier. -/
lemma strictOracleFoldingConsistencyProp_commitStepLogic
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (stmtIn : Statement (L := L) Context i.succ)
    (witIn : Witness 𝔽q β i.succ)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ i.castSucc j)
    (challenges : (pSpecCommit 𝔽q β i).Challenges)
    (h_wit_struct_In : witnessStructuralInvariant 𝔽q β (multpoly := multpoly) stmtIn witIn)
    (h_oracle_folding_In : strictOracleFoldingConsistencyProp 𝔽q β (t := witIn.t) (i := i.castSucc)
      (challenges := Fin.take (m := i)
        (v := stmtIn.challenges) (h := by
          simp only [Fin.val_succ, le_add_iff_nonneg_right, zero_le]))
      (oStmt := oStmtIn)) :
    let step := (commitStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) i (hCR := hCR))
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    let verifierStmtOut := step.verifierOut stmtIn transcript
    let verifierOStmtOut := step.materializeOutput oStmtIn transcript
    strictOracleFoldingConsistencyProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i.succ)
      (challenges := Fin.take (m := i.val + 1)
        (v := verifierStmtOut.challenges) (h := by simp only [Fin.val_succ, le_refl]))
      (oStmt := verifierOStmtOut) (t := witIn.t) := by
  -- Key observations:
  -- 1. (mkFromStmtIdxCastSuccOfSucc i).val = i.castSucc.val = i.val
  -- 2. (mkFromStmtIdx i.succ).val = i.succ.val = i.val + 1
  -- 3. toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1
  --    (when isCommitmentRound)
  -- 4. verifierStmtOut = stmtIn (commit step doesn't change statement)
  -- 5. verifierOStmtOut extends oStmtIn with the new oracle witIn.f
  -- Simplify the step definitions
  intro step transcript verifierStmtOut verifierOStmtOut
  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => witIn.t.val.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  have h_wit_f_eq : witIn.f = getMidCodewords 𝔽q β witIn.t stmtIn.challenges :=
    h_wit_struct_In.2
  -- Oracle extension: verifierOStmtOut = snoc_oracle oStmtIn witIn.f
  have h_OStmtOut_eq : verifierOStmtOut = snoc_oracle 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl)
      oStmtIn (newOracleFn := witIn.f) := by
    rw [snoc_oracle_eq_commitStepLogic_materializeOutput 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR oStmtIn witIn.f transcript]
    · rfl
  have h_challenges_eq : stmtIn.challenges = verifierStmtOut.challenges := by rfl
  -- Expand strictOracleFoldingConsistencyProp - goal is ∀ j, verifierOStmtOut j = iterated_fold ...
  simp only [strictOracleFoldingConsistencyProp]
  intro j
  -- The output oracle count is one more than input
  have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
  -- Case analysis: old oracle vs new oracle
  have h_j_bound : j.val < toOutCodewordsCount ℓ ϑ i.succ := j.isLt
  by_cases hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
  · -- Case A: Old oracle (j < old count)
    -- verifierOStmtOut j = oStmtIn j (from snoc_oracle)
    have h_verifier_eq_old : verifierOStmtOut j = oStmtIn ⟨j.val, hj⟩ := by
      rw [h_OStmtOut_eq]
      dsimp only [snoc_oracle]
      simp only [hj, ↓reduceDIte]
    rw [h_verifier_eq_old]
    -- Use input hypothesis: oStmtIn j = iterated_fold ... (with challenges from i.castSucc)
    have h_old_eq := h_oracle_folding_In ⟨j.val, hj⟩
    rw [h_old_eq]
    -- Show that iterated_fold with challenges from i.castSucc equals iterated_fold with
    -- challenges from i.succ when j * ϑ < i.val (holds since j < toOutCodewordsCount i.castSucc)
    rfl
  · -- Case B: New oracle (j = toOutCodewordsCount i.castSucc)
    rw [h_OStmtOut_eq]
    dsimp only [snoc_oracle]
    simp only [hj, ↓reduceDIte, hCR]
    have h_j_eq : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
    -- verifierOStmtOut j is the cast version of witIn.f (from snoc_oracle)
    -- The domain indices match: oraclePositionToDomainIndex j = i.val + 1 when j is the new oracle
    have h_domain_idx_eq : (oraclePositionToDomainIndex (positionIdx := j)).val = i.val + 1 :=
      by simp only [h_j_eq]; exact toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ i hCR
    -- Use witness structural invariant: witIn.f = getMidCodewords witIn.t stmtIn.challenges
    have h_steps_eq : (toOutCodewordsCount ℓ ϑ i.castSucc) * ϑ = i.val + 1 := by
      exact toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ i hCR
    funext x
    dsimp only [Fin.val_last, getMidCodewords] at h_wit_f_eq
    rw [h_wit_f_eq]
    simp only
    have h_cast_elim := iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := i.succ)
      (destIdx := ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩)
      (destIdx' := ⟨i.succ, by simp only [Fin.val_succ]; omega⟩)
      (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ, zero_add]
        exact h_domain_idx_eq)
      (h_destIdx_le := by simp only [oracle_index_le_ℓ])
      (h_destIdx_eq_destIdx' := by simp only [Fin.val_succ, Fin.mk.injEq]; exact h_domain_idx_eq)
      (f := f₀) (r_challenges := stmtIn.challenges)
    dsimp only [f₀, P₀] at h_cast_elim
    unfold polyToOracleFunc at h_cast_elim
    rw [← h_cast_elim]
    unfold getFoldingChallenges
    rw [←h_challenges_eq]
    unfold polyToOracleFunc
    have h_cast_elim2 := iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := i.succ) (steps' := j.val * ϑ)
      (destIdx := ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩)
      (h_steps_eq_steps' := by exact h_domain_idx_eq.symm)
      (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ, zero_add]
        exact h_domain_idx_eq)
      (h_destIdx_le := by simp only [oracle_index_le_ℓ])
      (f := f₀) (r_challenges := stmtIn.challenges)
    dsimp only [f₀, P₀] at h_cast_elim2
    unfold polyToOracleFunc at h_cast_elim2
    rw [h_cast_elim2]
    dsimp only [Fin.val_succ, Fin.take_apply, Fin.castLE_refl]
    congr 1
    dsimp only [oraclePositionToDomainIndex] at h_domain_idx_eq
    have h_challenges_eq_take : (fun cIdx : Fin (j.val * ϑ) => stmtIn.challenges ⟨cIdx.val, by
      simp only [Fin.val_succ]; rw [h_domain_idx_eq.symm]; exact cIdx.isLt⟩) =
      (fun cIdx : Fin (j.val * ϑ) => stmtIn.challenges ⟨0 + cIdx.val, by
        simp only [zero_add, Fin.val_succ]; rw [h_domain_idx_eq.symm]; exact cIdx.isLt⟩) := by
      funext cId
      simp only [Fin.val_succ, zero_add]
    exact h_challenges_eq_take

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- The commit step is strongly complete: from the strict fold-step output relation, the honest
output lies in the strict round relation at `i + 1`. -/
lemma commitStepLogic_isStronglyComplete (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitStepLogic (multpoly := multpoly) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i (hCR := hCR)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (commitStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (multpoly := multpoly) i (hCR := hCR))
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := step.materializeOutput oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  -- Extract properties from h_relIn (strictFoldStepRelOut)
  dsimp only [commitStepLogic, strictFoldStepRelOut, strictFoldStepRelOutProp,
    strictRoundRelation, strictRoundRelationProp, Set.mem_ofPred_eq] at h_relIn
  dsimp only [strictFoldStepRelOutProp, strictRoundRelationProp, Fin.val_succ] at h_relIn
  -- We'll need sumcheck consistency for Fact 1, so extract it from either branch
  have h_sumcheck_cons : sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _)
      stmtIn.sumcheck_target witIn.H :=
    h_relIn.1
  let h_VCheck_passed : step.verifierCheck stmtIn transcript := by
    dsimp only [commitStepLogic, Prod.mk.eta, step]
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    dsimp only [step, commitStepLogic]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.2
      = step.materializeOutput oStmtIn transcript
    conv_lhs => dsimp only [step, commitStepLogic]
    dsimp only [transcript, step]
    rw [snoc_oracle_eq_commitStepLogic_materializeOutput 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)];
        rfl
  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- Fact 2: Output relation holds (strictRoundRelation)
    dsimp only [step, commitStepLogic, strictRoundRelation, strictRoundRelationProp,
      Set.mem_ofPred_eq]
    simp only [Fin.val_succ]
    constructor
    · -- Part 2.1: sumcheck consistency
      exact h_sumcheck_cons
    · -- Part 2.2: strictOracleWitnessConsistency
      have h_strictOracleWitConsistency_In := h_relIn.2
      dsimp only [strictOracleWitnessConsistency] at h_strictOracleWitConsistency_In ⊢
      -- Extract the two components from the input
      obtain ⟨h_wit_struct_In, h_strict_oracle_folding_In⟩ := h_strictOracleWitConsistency_In
      -- Now prove each component for the output
      refine ⟨?_, ?_⟩
      · -- Component 1: witnessStructuralInvariant
        exact h_wit_struct_In
      · -- Component 2: strictOracleFoldingConsistencyProp
        exact strictOracleFoldingConsistencyProp_commitStepLogic 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (witIn := witIn)
          (stmtIn := stmtIn) (hCR := hCR) (h_wit_struct_In := h_wit_struct_In)
          (h_oracle_folding_In := h_strict_oracle_folding_In) (challenges := challenges)
  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

end CommitStep

section FinalSumcheckStep

/-- The logic of the final sum-check step. The prover sends the constant `c` of its fully folded
word; the verifier checks the closing sum-check equation `s_ℓ = eq̃(r, r') · c` and outputs the
statement extended by `c`. The oracle statements pass through. -/
def finalSumcheckStepLogic :
    ReductionLogicStep
      -- In/Out Types
      (Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
      (Unit)
      -- Protocol Spec
      (pSpecFinalSumcheckStep (L := L))
      where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictRoundRelation 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := BBF_multiplier)
      (Fin.last ℓ)
  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    -- For strict relations, we need t from the input witness
    -- In completeness proofs, extracted from h_relIn via strictOracleWitnessConsistency
    ((stmtOut, oStmtOut), witOut) ∈ strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifierCheck := fun stmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    let eq_tilde_eval := eqTilde (r := stmtIn.ctx.t_eval_point) (r' := stmtIn.challenges)
    stmtIn.sumcheck_target = eq_tilde_eval * c
  verifierOut := fun stmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }
  honestProverTranscript := fun _stmtIn witIn _oStmtIn _chal =>
    -- The honest prover sends c = f^(ℓ)(0, ..., 0)
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩
    FullTranscript.mk1 c
  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }
    ((stmtOut, oStmtIn), ())
  embed := ⟨fun j => by
    have h_lt : j.val < toOutCodewordsCount ℓ ϑ (Fin.last ℓ) := j.isLt
    exact Sum.inl ⟨j.val, by omega⟩
  , by
    intro a b h_ab_eq
    simp only [MessageIdx, Fin.eta, Sum.inl.injEq] at h_ab_eq
    exact h_ab_eq
  ⟩
  hEq := fun oracleIdx => by simp only [Function.Embedding.coeFn_mk, Fin.eta]

omit [SampleableType L] [CharP L 2] [DecidableEq 𝔽q] in
/-- Under the strict oracle-witness consistency at round `ℓ`, folding the last oracle over the last
block of challenges gives the constant function at the honest final constant. -/
lemma iterated_fold_lastOracle_eq_finalConstant
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_strictOracleWitConsistency_In : strictOracleWitnessConsistency 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := SumcheckBaseContext L ℓ)
      (multpoly := BBF_multiplier) (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (stmt := stmtIn) (wit := witIn) (oStmt := oStmtIn)) :
    let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    let verifierStmtOut := step.verifierOut stmtIn transcript
    let verifierOStmtOut := step.materializeOutput oStmtIn transcript
    let lastDomainIdx := getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)
    let k := lastDomainIdx.val
    have h_k: k = ℓ - ϑ := by
      dsimp only [k, lastDomainIdx]
      rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    let curDomainIdx : Fin r := ⟨k, by
      rw [h_k]
      omega
    ⟩
    have h_destIdx_eq: curDomainIdx.val = lastDomainIdx.val := rfl
    let f_k : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) curDomainIdx :=
      getLastOracle (h_destIdx := h_destIdx_eq) (oracleFrontierIdx := Fin.last ℓ)
        𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := verifierOStmtOut)
    let finalChallenges : Fin ϑ → L := fun cId => verifierStmtOut.challenges ⟨k + cId, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
      have h_cId : cId.val < ϑ := cId.isLt
      have h_last : (Fin.last ℓ).val = ℓ := rfl
      omega
    ⟩
    let destDomainIdx : Fin r := ⟨k + ϑ, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
      omega
    ⟩
    let folded := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curDomainIdx) (steps := ϑ) (destIdx := destDomainIdx) (h_destIdx := by rfl)
      (h_destIdx_le := by
        dsimp only [destDomainIdx, k, lastDomainIdx];
        rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
          Nat.div_mul_cancel (hdiv.out)]
        rw [Nat.sub_add_cancel (by exact Nat.le_of_dvd (h:=by
          exact Nat.pos_of_neZero ℓ) (hdiv.out))]
      ) (f := f_k)
      (r_challenges := finalChallenges)
    ∀ y, folded y = transcript.messages ⟨0, rfl⟩ := by
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  intro step transcript verifierStmtOut verifierOStmtOut lastDomainIdx k h_k curDomainIdx
    h_destIdx_eq f_k finalChallenges destDomainIdx folded
  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => witIn.t.val.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  -- From strictOracleWitnessConsistency, we can construct strictfinalSumcheckStepFoldingStateProp
  -- which contains strictFinalConstantConsistency, giving us the desired equality
  -- Extract components from h_strictOracleWitConsistency_In
  have h_wit_struct := h_strictOracleWitConsistency_In.1
  have h_strict_oracle_folding := h_strictOracleWitConsistency_In.2
  dsimp only [Fin.val_last, OracleFrontierIndex.val_mkFromStmtIdx,
    strictOracleFoldingConsistencyProp] at h_strict_oracle_folding
  -- Construct the input for strictfinalSumcheckStepFoldingStateProp
  let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
    ctx := stmtIn.ctx,
    sumcheck_target := stmtIn.sumcheck_target,
    challenges := stmtIn.challenges,
    final_constant := transcript.messages ⟨0, rfl⟩
  }
  let c : L := transcript.messages ⟨0, rfl⟩
  have h_VOStmtOut_eq : verifierOStmtOut = oStmtIn := by rfl
  have h_challenges_eq : stmtIn.challenges = verifierStmtOut.challenges := by rfl
  have h_eq : folded = fun x => stmtOut.final_constant := by
    change folded = fun x => c
    dsimp only [folded, f_k]
    -- f_last is the iterated_fold of f₀ yielded from P₀
    have h_f_last_consistency := h_strict_oracle_folding
      (j := (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)))
    rw [h_VOStmtOut_eq]
    dsimp only [c, transcript, step, finalSumcheckStepLogic]
    dsimp only [FullTranscript.mk1, FullTranscript.messages]
    simp only [Fin.val_last]
    have h_wit_f_eq : witIn.f = getMidCodewords 𝔽q β witIn.t stmtIn.challenges := h_wit_struct.2
    dsimp only [Fin.val_last, getMidCodewords] at h_wit_f_eq
    conv_rhs => rw [h_wit_f_eq]; simp only
    have h_curDomainIdx_eq : curDomainIdx = ⟨ℓ - ϑ, by omega⟩ := by
      dsimp [curDomainIdx, k, lastDomainIdx]
      simp only [Fin.mk.injEq]
      rw [getLastOraclePositionIndex_last, Nat.sub_mul,
        Nat.div_mul_cancel (hdiv.out)]; simp only [one_mul]
    let res := iterated_fold_congr_source_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curDomainIdx) (i' := ⟨ℓ - ϑ, by omega⟩) (h := h_curDomainIdx_eq) (steps := ϑ)
      (destIdx := destDomainIdx)
      (h_destIdx := by rfl) (h_destIdx' := by simp only [destDomainIdx, h_k])
      (h_destIdx_le := by
        dsimp only [destDomainIdx]; rw [h_k];
        rw [Nat.sub_add_cancel (by exact Nat.le_of_dvd (h:=by
          exact Nat.pos_of_neZero ℓ) (hdiv.out))]
      ) (f := (getLastOracle 𝔽q β h_destIdx_eq oStmtIn)) (r_challenges := finalChallenges)
    rw [res]
    dsimp only [getLastOracle, finalChallenges, verifierStmtOut, step, finalSumcheckStepLogic]
    rw [h_f_last_consistency]
    simp only [Fin.take_eq_self]
    -- Extract the inner iterated_fold function
    let k_pos_idx := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    let k_steps := k_pos_idx.val * ϑ
    have h_k_steps_eq : k_steps = k := by
      dsimp only [k_steps, k_pos_idx, k, lastDomainIdx]
    -- The inner iterated_fold is already a function from domain k to L
    -- We can remove the cast wrapper since the domains match
    have h_cast_elim := iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := k_steps) (destIdx := curDomainIdx) (destIdx' := ⟨k_steps, by omega⟩)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by
        dsimp only [curDomainIdx]; simp only [h_k, tsub_le_iff_right, le_add_iff_nonneg_right,
          zero_le]; )
      (h_destIdx_eq_destIdx' := by rfl)
      (f := f₀)
      (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
        (by simp only [zero_add, Fin.val_last]; omega))
    have h_cast_elim2 := iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0)
      (steps := k_steps)
      (destIdx := ⟨ℓ - ϑ, by omega⟩)
      (destIdx' := curDomainIdx)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by
        dsimp only [curDomainIdx]; simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le])
      (h_destIdx_eq_destIdx' := by dsimp only [curDomainIdx]; simp only [Fin.mk.injEq]; omega)
      (f := f₀)
      (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
        (by simp only [zero_add, Fin.val_last]; omega))
    dsimp only [k_steps, k_pos_idx, f₀, P₀] at h_cast_elim
    dsimp only [k_steps, k_pos_idx, f₀, P₀] at h_cast_elim2
    conv_lhs =>
      simp only [←h_cast_elim]
      simp only [←h_cast_elim2]
    have h_transitivity := iterated_fold_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (midIdx := ⟨ℓ - ϑ, by omega⟩) (destIdx := destDomainIdx)
      (steps₁ := k_steps) (steps₂ := ϑ)
      (h_midIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, h_k_steps_eq, h_k, zero_add])
      (h_destIdx := by
        dsimp only [destDomainIdx, k_steps, k_pos_idx];
        rw [h_k]; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff]
        rw [getLastOraclePositionIndex_last]; simp only
        rw [Nat.sub_mul]; rw [Nat.div_mul_cancel (hdiv.out)]; simp only [one_mul]
      )
      (h_destIdx_le := by
        dsimp only [destDomainIdx]
        rw [h_k]
        rw [Nat.sub_add_cancel (by exact Nat.le_of_dvd (Nat.pos_of_neZero ℓ) (hdiv.out))])
      (f := f₀)
      (r_challenges₁ := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
        (by simp only [zero_add, Fin.val_last]; omega))
      (r_challenges₂ := finalChallenges)
    have h_finalChallenges_eq : finalChallenges = fun cId : Fin ϑ =>
      stmtIn.challenges ⟨k + cId.val, by
        rw [h_k]
        have h_cId : cId.val < ϑ := cId.isLt
        have h_last : (Fin.last ℓ).val = ℓ := rfl
        omega
      ⟩ := by rfl
    rw [h_finalChallenges_eq] at h_transitivity
    rw [h_transitivity]
    have h_steps_eq : k_steps + ϑ = ℓ := by
      dsimp only [k_steps, k_pos_idx, h_k_steps_eq, h_k]
      rw [getLastOraclePositionIndex_last];
      simp only [Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)];
      rw [Nat.sub_add_cancel (by exact Nat.le_of_dvd (h:=by exact Nat.pos_of_neZero ℓ) (hdiv.out))]
    -- Show that the concatenated challenges equal stmtIn.challenges
    have h_concat_challenges_eq : Fin.append
        (getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := k_steps) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega))
        finalChallenges = fun (cIdx : Fin (k_steps + ϑ)) =>
          stmtIn.challenges ⟨cIdx, by simp only [Fin.val_last]; omega⟩ := by
      funext cId
      dsimp only [getFoldingChallenges, finalChallenges]
      by_cases h : cId.val < k_steps
      · -- Case 1: cId < k_steps, so it's from the first part
        simp only [Fin.val_last]
        dsimp only [Fin.append, Fin.addCases]
        simp only [h, ↓reduceDIte, getFoldingChallenges, Fin.val_last, Fin.val_castLT, zero_add]
      · -- Case 2: cId >= k_steps, so it's from the second part
        simp only [Fin.val_last]
        dsimp only [Fin.append, Fin.addCases]
        simp only [h, ↓reduceDIte, Fin.val_subNat, Fin.val_cast, eq_rec_constant]
        congr 1
        simp only [Fin.val_last, Fin.mk.injEq]
        rw [add_comm]; rw [←h_k_steps_eq]; omega
    dsimp only [finalChallenges] at h_concat_challenges_eq
    rw [h_challenges_eq.symm] at h_concat_challenges_eq
    simp only [h_concat_challenges_eq]
    funext y
    have h_cast_elim3 := iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := k_steps + ϑ)
      (destIdx := destDomainIdx)
      (destIdx' := ⟨Fin.last ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
      (h_destIdx_le := by dsimp only [destDomainIdx]; omega)
      (h_destIdx_eq_destIdx' := by
        dsimp only [destDomainIdx]; simp only [Fin.val_last, Fin.mk.injEq]; omega)
      (f := f₀)
      (r_challenges := fun (cIdx : Fin (k_steps + ϑ)) =>
        stmtIn.challenges ⟨cIdx, by simp only [Fin.val_last]; omega⟩)
    rw [h_cast_elim3]
    have h_cast_elim4 := iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := ℓ) (steps' := k_steps + ϑ)
      (destIdx := ⟨Fin.last ℓ, by omega⟩)
      (h_steps_eq_steps' := by simp only [h_steps_eq])
      (h_destIdx := by
        dsimp only [destDomainIdx]; simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          zero_add])
      (h_destIdx_le := by simp only [Fin.val_last, le_refl])
      (f := f₀) (r_challenges := stmtIn.challenges)
    rw [← h_cast_elim4]
    set f_ℓ := iterated_fold 𝔽q β 0 ℓ (destIdx := ⟨Fin.last ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
      (h_destIdx_le := by simp only [Fin.val_last, le_refl]) (f := f₀)
      (r_challenges := stmtIn.challenges)
    have h_eval_eq : ∀ x, f_ℓ x = f_ℓ ⟨0, by simp only [zero_mem]⟩ := by
      intro x
      apply iterated_fold_to_level_ℓ_is_constant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (t := witIn.t) (destIdx := ⟨Fin.last ℓ, by omega⟩)
        (h_destIdx := by simp only [Fin.val_last]) (challenges := stmtIn.challenges)
        (x := x) (y := 0)
    rw [h_eval_eq]; rfl
  rw [h_eq]
  intro y
  rfl

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] in
/-- Under sum-check consistency and the strict oracle-witness consistency at round `ℓ`, the honest
final constant passes the closing sum-check equation. -/
lemma finalSumcheckStepLogic_verifierCheck_honest
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtIn.sumcheck_target
        witIn.H)
    (h_strictOracleWitConsistency_In : strictOracleWitnessConsistency 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := SumcheckBaseContext L ℓ)
      (multpoly := BBF_multiplier) (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)) (stmt := stmtIn)
      (wit := witIn) (oStmt := oStmtIn)) :
    let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  classical
  let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  -- Simplify the verifier check to the equality we need to prove
  change (finalSumcheckStepLogic 𝔽q β).verifierCheck stmtIn transcript
  simp only [finalSumcheckStepLogic]
  dsimp only [sumcheckConsistencyProp] at h_sumcheck_cons
  -- Simplify the sum to a single evaluation since 𝓑^ᶠ(0) = {∅}
  rw [Finset.sum_eq_single (a := fun _ => 0) (h₀ := fun b _ hb_ne => by
    have : b = fun x ↦ 0 := by
      funext i;
      rw [Fin.val_last] at i
      simp only [tsub_self] at i; exact i.elim0
    contradiction
    ) (h₁ := fun h_not_mem => by
      exfalso; apply h_not_mem
      simp only [SumcheckDomain.mem_cube]; intro x
      rw [Fin.val_last] at x
      simp only [tsub_self] at x; exact x.elim0
    )] at h_sumcheck_cons
  have h_wit_structural_invariant := h_strictOracleWitConsistency_In.1
  have h_f_eq_getMidCodewords_t : witIn.f = getMidCodewords 𝔽q β witIn.t stmtIn.challenges :=
    h_wit_structural_invariant.2
  have h_witIn_f_0_eq_c : witIn.f ⟨0, by simp only [zero_mem]⟩ = transcript.messages ⟨0, rfl⟩ := by
    rfl
  let h_c_eq : (transcript.messages ⟨0, rfl⟩) = witIn.t.val.eval stmtIn.challenges := by
    change witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges
    dsimp only [getMidCodewords, Fin.coe_ofNat_eq_mod] at h_f_eq_getMidCodewords_t
    rw [congr_fun h_f_eq_getMidCodewords_t ⟨0, by simp only [zero_mem]⟩]
    let h_eval := iterated_fold_to_level_ℓ_eval 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t := witIn.t) (destIdx := ⟨Fin.last ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.val_last]) (challenges := stmtIn.challenges)
    exact congr_fun (h := h_eval) ⟨0, by simp only [Fin.val_last, zero_mem]⟩
  -- Apply `eval_projectToMidSumcheckPoly_last` to connect H.eval with eqTilde * f(0)
  have h_H_eval_at_zero_eq_mul : witIn.H.val.eval (fun _ => (0 : L)) =
      eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges *
      (witIn.f ⟨0, by simp only [zero_mem]⟩) := by
    rw [h_wit_structural_invariant.1]
    rw [Sumcheck.Structured.eval_projectToMidSumcheckPoly_last]
    -- ↑witIn.t = witIn.f ⟨0, ⋯⟩
    rw [h_witIn_f_0_eq_c, h_c_eq]; rfl
  -- Combine to finish the proof
  change stmtIn.sumcheck_target = eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges *
    witIn.f ⟨0, by simp only [Fin.val_last, zero_mem]⟩
  rw [←h_H_eval_at_zero_eq_mul]
  exact h_sumcheck_cons

omit [DecidableEq 𝔽q] [CharP L 2] [SampleableType L] in
/-- The final sum-check step is strongly complete: from the strict round relation at `ℓ`, the
honest constant passes the check and the output lies in the strict final sum-check output
relation. -/
lemma finalSumcheckStepLogic_isStronglyComplete :
    (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑))
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := step.materializeOutput oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  -- Extract properties from h_relIn BEFORE any simp changes its structure
  simp only [finalSumcheckStepLogic, strictRoundRelation, strictRoundRelationProp,
    Set.mem_ofPred_eq] at h_relIn
  obtain ⟨h_sumcheck_cons, h_strictOracleWitConsistency_In⟩ := h_relIn
  -- The multilinear polynomial of the witness
  let t := witIn.t
  let h_VCheck_passed := finalSumcheckStepLogic_verifierCheck_honest 𝔽q β (𝓑 := 𝓑) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
    (oStmtIn := oStmtIn) (challenges := challenges)
    (h_sumcheck_cons := h_sumcheck_cons)
    (h_strictOracleWitConsistency_In := by exact h_strictOracleWitConsistency_In)
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, finalSumcheckStepLogic]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by rfl -- not new oracles added
  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- Fact 2: Output relation holds (foldStepRelOut)
    simp only [finalSumcheckStepLogic, strictRoundRelation, strictRoundRelationProp, Fin.val_last,
      Prod.mk.eta, Set.mem_ofPred_eq, strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
      strictfinalSumcheckStepFoldingStateProp, exists_and_right, Subtype.exists,
        Fin.isValue, MessageIdx, Fin.eta, step]
    dsimp only [strictOracleWitnessConsistency, Fin.val_last, OracleFrontierIndex.mkFromStmtIdx,
      strictOracleFoldingConsistencyProp, Fin.eta, ↓dreduceIte,
    Bool.false_eq_true] at h_strictOracleWitConsistency_In ⊢
    -- Extract the three components from the input
    let ⟨_, h_oracle_folding_In⟩ := h_strictOracleWitConsistency_In
    -- Now prove each component for the output
    refine ⟨?_, ?_⟩
    · -- Component 1: oracleFoldingConsistencyProp
      use t
      simp only [SetLike.coe_mem, exists_const]
      exact h_oracle_folding_In
    · -- Component 2: finalOracleFoldingConsistency
      funext y
      classical
      let res := iterated_fold_lastOracle_eq_finalConstant 𝔽q β (𝓑 := 𝓑) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
        (oStmtIn := oStmtIn) (challenges := challenges)
        (h_strictOracleWitConsistency_In := h_strictOracleWitConsistency_In)
      rw [res]
      rfl
  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold
