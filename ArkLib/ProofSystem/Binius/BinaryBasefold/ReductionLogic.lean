/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.Simulation
import ArkLib.OracleReduction.Completeness
import ArkLib.Data.Misc.Basic

set_option maxHeartbeats 400000  -- Increase if needed
set_option profiler true
-- set_option profiler.threshold 50  -- Show anything taking over 10ms
namespace Binius.BinaryBasefold
/-!
## Binary Basefold single steps
- **Fold step** :
  P sends V the polynomial `h_i(X) := Σ_{w ∈ B_{ℓ-i-1}} h(r'_0, ..., r'_{i-1}, X, w_0, ...
  w_{ℓ-i-2})`.
  V requires `s_i ?= h_i(0) + h_i(1)`. V samples `r'_i ← L`, sets `s_{i+1} := h_i(r'_i)`,
  and sends P `r'_i`.
- **Relay step** : transform relOut of fold step in case of non-commitment round to match
  roundRelation
- **Commit step** :
    P defines `f^(i+1): S^(i+1) → L` as the function `fold(f^(i), r'_i)` of Definition 4.6.
    if `i+1 < ℓ` and `ϑ | i+1` then
    P submits (submit, ℓ+R-i-1, f^(i+1)) to the oracle `F_Vec^L`
- **Final sum-check step** :
  - P sends V the final constant `c := f^(ℓ)(0, ..., 0)`
  - V verifies : `s_ℓ = eqTilde(r, r') * c`
  => `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})`
-/
section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
open scoped NNReal

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

section GenericLogic

def hEq {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type}
  {OracleOut : ιₒₒ → Type} {n : ℕ} {pSpec : ProtocolSpec n}
  (embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx) :=
  ∀ i, OracleOut i =
    match embed i with
    | Sum.inl j => OracleIn j
    | Sum.inr j => pSpec.Message j

/-- **RBR Extraction Failure Event**: Generic predicate for round-by-round knowledge soundness.

This captures when the RBR extractor fails to produce a valid witness at round `i.1.castSucc`,
but a valid witness exists at round `i.1.succ`. This is the fundamental "bad event" that must
be bounded in all RBR knowledge soundness proofs.

**Usage:** Instantiate with protocol-specific `kSF`, `extractor`, and transcript to get the -/
@[reducible]
def rbrExtractionFailureEvent {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} {WitMid : Fin (n + 1) → Type}
  (kSF : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop)
  (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
  (i : pSpec.ChallengeIdx) (stmtIn : StmtIn)
  (transcript : Transcript i.1.castSucc pSpec) (challenge : pSpec.Challenge i) : Prop :=
  ∃ witMid : WitMid i.1.succ,
    ¬ kSF i.1.castSucc stmtIn transcript
      (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
    kSF i.1.succ stmtIn (transcript.concat challenge) witMid

/-- The Pure Logic of an interactive reduction step.
Parametrized by a 'Challenges' type that aggregates all verifier randomness. -/
structure ReductionLogicStep
    (StmtIn WitIn : Type)
    {ιₒᵢ ιₒₒ : Type}
    (OracleIn : ιₒᵢ → Type) (OracleOut : ιₒₒ → Type)
    (StmtOut WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) where
  -- 1. The Specification (Relations) - now with indexed oracles
  completeness_relIn : (StmtIn × (∀ i, OracleIn i)) × WitIn → Prop
  completeness_relOut : (StmtOut × (∀ i, OracleOut i)) × WitOut → Prop
  -- 2. The Verifier (Pure Logic)
  verifierCheck : StmtIn → FullTranscript pSpec → Prop
  verifierOut   : StmtIn → FullTranscript pSpec → StmtOut
  -- 2b. Oracle Embedding (like OracleVerifier)
  embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx
  hEq : hEq (OracleIn := OracleIn) (OracleOut := OracleOut) (ιₒᵢ := ιₒᵢ) (ιₒₒ := ιₒₒ)
    (pSpec := pSpec) (embed := embed)
  -- 3. The Honest Prover (Pure Logic)
  honestProverTranscript : StmtIn → WitIn → (∀ i, OracleIn i) → pSpec.Challenges →
    FullTranscript pSpec
  -- 4. The Prover's Output State
  proverOut : StmtIn → WitIn → (∀ i, OracleIn i) → FullTranscript pSpec →
    ((StmtOut × (∀ i, OracleOut i)) × WitOut)

/-- Strong Completeness:
  "For ANY set of challenges, the honest transcript passes the check
   and leads to a valid next state." -/
@[reducible]
def ReductionLogicStep.IsStronglyComplete
    {StmtIn WitIn : Type}
    {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type} {OracleOut : ιₒₒ → Type}
    {StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (step : ReductionLogicStep StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec) : Prop :=
  ∀ (stmtIn : StmtIn) (witIn : WitIn) (oStmtIn : ∀ i, OracleIn i) (challenges : pSpec.Challenges),
    -- Assumption: The input relation holds (valid start state)
    (h_relIn : step.completeness_relIn ((stmtIn, oStmtIn), witIn)) →
    -- 1. Generate the Honest Transcript (Deterministic given challenges)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    -- 2. The Verifier MUST accept this transcript
    step.verifierCheck stmtIn transcript ∧
    -- 3. The output MUST be valid and consistent
    let verifierStmtOut := step.verifierOut stmtIn transcript
    -- Compute verifier oracle output via embedding (like OracleVerifier.toVerifier)
    let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
      oStmtIn transcript
    let ((proverStmtOut, proverOStmtOut), proverWitOut) :=
      step.proverOut stmtIn witIn oStmtIn transcript
    -- Conclusion A: The Prover's output satisfies the next relation (Soundness/Completeness)
    step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) ∧
    -- Conclusion B: The Prover and Verifier agree on the next statement
    proverStmtOut = verifierStmtOut ∧
    -- Conclusion C: The Prover and Verifier agree on the oracle statements
    proverOStmtOut = verifierOStmtOut

/-- Oracle-aware reduction logic step for protocols where the verifier queries oracles
during verification (e.g., QueryPhase in Binary Basefold).

Unlike `ReductionLogicStep` where `verifierCheck` is a pure `Prop`, here it returns
`OracleComp (oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)) StmtOut` to support oracle
queries during verification. This matches the signature of `OracleVerifier.verify`.

All other components (embed, hEq, relations, proverOut, verifierOut) remain pure,
giving definitional equality when accessed via dot notation. -/
structure OracleAwareReductionLogicStep
    {ι : Type} (oSpec : OracleSpec ι)
    (StmtIn WitIn : Type)
    {ιₒᵢ ιₒₒ : Type}
    (OracleIn : ιₒᵢ → Type) (OracleOut : ιₒₒ → Type)
    (StmtOut WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [Oₛᵢ : ∀ i, OracleInterface (OracleIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)] where
  -- 1. The Specification (wRelations) - same as ReductionLogicStep
  completeness_relIn : (StmtIn × (∀ i, OracleIn i)) × WitIn → Prop
  completeness_relOut : (StmtOut × (∀ i, OracleOut i)) × WitOut → Prop
  -- 2. The Verifier (Oracle-Aware)
  -- Key difference: verifierCheck is monadic, can query oracles
  -- Uses the extended spec: oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)
  -- Same signature as OracleVerifier.verify (including OptionT for guard/failure)
  verifierCheck : StmtIn → FullTranscript pSpec →
    OptionT (OracleComp (oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ))) StmtOut
  -- Output computation remains pure/deterministic
  verifierOut   : StmtIn → FullTranscript pSpec → StmtOut
  -- 2b. Oracle Embedding (same as ReductionLogicStep)
  embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx
  hEq : hEq (OracleIn := OracleIn) (OracleOut := OracleOut) (ιₒᵢ := ιₒᵢ) (ιₒₒ := ιₒₒ)
    (pSpec := pSpec) (embed := embed)
  -- 3. The Honest Prover (Pure Logic) - same as ReductionLogicStep
  honestProverTranscript : StmtIn → WitIn → (∀ i, OracleIn i)
    → pSpec.Challenges → FullTranscript pSpec
  -- 4. The Prover's Output State - same as ReductionLogicStep
  proverOut : StmtIn → WitIn → (∀ i, OracleIn i) → FullTranscript pSpec →
    ((StmtOut × (∀ i, OracleOut i)) × WitOut)

/-- Strong Completeness Under Simulation for Oracle-Aware Reduction Logic:
  \"For ANY set of challenges, when the verifier check is run under honest oracle simulation,
   it succeeds with probability 1, and the output satisfies the relation.\"
  This is the appropriate notion of completeness for verifiers that query oracles during
  verification (e.g., the query phase in Binary Basefold). Unlike `IsStronglyComplete`,
  which checks the raw `OracleComp`, this checks the simulated execution where oracle
  queries are answered by the honest oracle statements.
  The key difference: In raw execution, oracle queries return arbitrary values, so guards
  checking oracle responses will fail. Under simulation with `simOracle2`, queries are
  answered by `oStmtIn`, making the guards pass.
  **Type Constraint**: The step's `querySpec` must be `oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)`
  for the simulation to type-check. This is the natural structure where:
  - `oSpec` is the shared/base oracle (e.g., random oracle, hash function)
  - `[OracleIn]ₒ` are the oracle statements the verifier can query
  - `[pSpec.Message]ₒ` are the prover messages the verifier can query -/
@[reducible]
def OracleAwareReductionLogicStep.IsStronglyCompleteUnderSimulation
    {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {StmtIn WitIn : Type}
    {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type} {OracleOut : ιₒₒ → Type}
    {StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₛᵢ : ∀ i, OracleInterface (OracleIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    -- The step uses oSpec as its base oracle; internally it accesses
    --   oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)
    (step : OracleAwareReductionLogicStep oSpec
      StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec) : Prop :=
  ∀ (stmtIn : StmtIn) (witIn : WitIn) (oStmtIn : ∀ i, OracleIn i) (challenges : pSpec.Challenges),
    -- Assumption: The input relation holds (valid start state)
    (h_relIn : step.completeness_relIn ((stmtIn, oStmtIn), witIn)) →
    -- 1. Generate the Honest Transcript (Deterministic given challenges)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    -- 2. Define the honest oracle simulator
    -- simOracle2 oSpec t₁ t₂ : SimOracle.Stateless (oSpec + ([T₁]ₒ + [T₂]ₒ)) oSpec
    -- This answers queries to OracleIn using oStmtIn and queries to Messages using transcript
    let so := OracleInterface.simOracle2 oSpec oStmtIn transcript.messages
    -- 3. The Verifier check under simulation MUST succeed with probability 1
    Pr[⊥ | OptionT.mk (simulateQ so (step.verifierCheck stmtIn transcript))] = 0 ∧
    -- 4. The output MUST be valid and consistent
    let verifierStmtOut := step.verifierOut stmtIn transcript
    -- Compute verifier oracle output via embedding (like OracleVerifier.toVerifier)
    let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
      oStmtIn transcript
    let ((proverStmtOut, proverOStmtOut), proverWitOut) :=
      step.proverOut stmtIn witIn oStmtIn transcript
    -- Conclusion A: The Prover's output satisfies the next relation
    step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) ∧
    -- Conclusion B: The Prover and Verifier agree on the next statement
    proverStmtOut = verifierStmtOut ∧
    -- Conclusion C: The Prover and Verifier agree on the oracle statements
    proverOStmtOut = verifierOStmtOut

end GenericLogic

section SingleIteratedSteps
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context
section FoldStep

/-- The Logic Instance for the i-th round of Binary Folding.
**Computability note:** the prover-side fields are routed through the explicit fold kernels.
The structure is now computable again; proof obligations are still deferred where needed. -/
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
      (𝓑 := 𝓑) i.castSucc (mp := mp)
  completeness_relOut := fun ((s, o), w) =>
    ((s, o), w) ∈ strictFoldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i (mp := mp)
  -- 2. Verifier Logic (Using extracted kernels)
  verifierCheck := fun s t =>
    foldVerifierCheck i s (𝓑 := 𝓑) (t.messages ⟨0, rfl⟩)
  verifierOut := fun s t =>
    foldVerifierStmtOut i s (t.messages ⟨0, rfl⟩) (t.challenges ⟨1, rfl⟩)
  -- 2b. Oracle Embedding (must match foldOracleVerifier)
  embed := ⟨fun j => by
    if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
      exact Sum.inl ⟨j.val, by omega⟩
    else omega -- never happens
  , by
    intro a b h_ab_eq
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Sum.inl.injEq] at h_ab_eq
    exact h_ab_eq
  ⟩
  hEq := fun oracleIdx => by
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Function.Embedding.coeFn_mk]
  -- 3. Honest Prover Logic
  honestProverTranscript := fun s w oStmt chal =>
    FullTranscript.mk2
      (foldProverComputeMsg (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i w)
      (chal ⟨1, rfl⟩)
  -- 4. Prover Output
  proverOut := by
    intro _ _ _ _
    sorry

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-! The Main Lemma: Binary Folding satisfies Strong Completeness.

This proves that for any valid input satisfying `roundRelation`, the honest prover-verifier
interaction correctly computes the sumcheck polynomial and updates the witness through folding.

**Proof Structure:**
- Verifier check: Uses `projectToNextSumcheckPoly_sum_eq`.
- Output relation: Uses `badEventExistsProp_succ_preserved` for bad events, and preservation lemmas
  (e.g., `witnessStructuralInvariant_succ_preserved`) otherwise.
- Agreement: Prover and verifier agree on output statements and oracles. -/
omit [SampleableType L] in
lemma foldStep_is_logic_complete (i : Fin ℓ) :
    (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := mp) i).IsStronglyComplete := by
  sorry

end FoldStep

section CommitStep

def commitStepLogic_embedFn (i : Fin ℓ) :
  (Fin (toOutCodewordsCount ℓ ϑ i.succ)) →
    Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕
      (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).MessageIdx :=
  fun j => by
  if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
    exact Sum.inl ⟨j.val, hj⟩
  else
    exact Sum.inr ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩

def commitStepLogic_embed_inj (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
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
    have h_a : a = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
    have h_b : b = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
    omega

/- the CommitStep is a 1-message oracle reduction to place the conditional oracle message -/
def commitStepLogic_embed (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  Fin (toOutCodewordsCount ℓ ϑ i.succ) ↪
    Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕
      (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).MessageIdx := ⟨
  commitStepLogic_embedFn 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i,
  commitStepLogic_embed_inj 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i hCR
  ⟩

def commitStepHEq (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  hEq (OracleIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (OracleOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (ιₒᵢ := Fin (toOutCodewordsCount ℓ ϑ i.castSucc))
    (ιₒₒ := Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (pSpec := pSpecCommit 𝔽q β i)
    (embed := commitStepLogic_embed 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i hCR) :=
  by
    intro oracleIdx
    sorry

/-- The Logic Instance for the commit step.
This is a trivial 1-message protocol where the prover just sends an oracle and the verifier
accepts it.
**Computability note:** The `honestProverTranscript` and `proverOut` fields are sorry'd so that
the structure is computable. The actual prover logic is in
`commitStepLogic_honestProverTranscript` / `commitStepLogic_proverOut`. -/
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
    ((stmt, oStmt), wit) ∈ strictFoldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i
  completeness_relOut := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i.succ
  -- No verification needed - just accept
  verifierCheck := fun _ _ => True
  -- Statement doesn't change
  verifierOut := fun stmt _ => stmt
  -- Oracle embedding: new oracle index maps to the message
  embed := commitStepLogic_embed 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR
  hEq := (commitStepHEq 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)
  -- Prover fields sorry'd for computability (actual logic uses snoc_oracle)
  honestProverTranscript := sorry
  proverOut := sorry

/-- Actual (noncomputable) honest prover transcript for the commit step. -/
noncomputable def commitStepLogic_honestProverTranscript (i : Fin ℓ) :
    Statement (L := L) Context i.succ →
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ →
    (∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j) →
    (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenges →
    FullTranscript (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  by
    sorry

/-- Actual (noncomputable) prover output for the commit step. -/
noncomputable def commitStepLogic_proverOut (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    Statement (L := L) Context i.succ →
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ →
    (∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j) →
    FullTranscript (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) →
    ((Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :=
  by
  intro stmt wit oStmtIn _transcript
  let newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩) := fun x => wit.f x
  let oStmtOut :=
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn newOracleFn
  exact ((stmt, oStmtOut), wit)

@[simp] lemma commitStepLogic_honestProverTranscript_eq (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      i hCR).honestProverTranscript =
    commitStepLogic_honestProverTranscript 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
  sorry

@[simp] lemma commitStepLogic_proverOut_eq (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      i hCR).proverOut =
    commitStepLogic_proverOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR := by
  sorry

/-! Helper lemma: snoc_oracle matches mkVerifierOStmtOut for commit steps.

This proves that when we add a new oracle via `snoc_oracle`, the result matches what the verifier
computes using `OracleVerifier.mkVerifierOStmtOut` with the commit step's embedding.

The key insight:
- For indices `j < toOutCodewordsCount ℓ ϑ i.castSucc`: embed maps to `Sum.inl j` (old oracle)
- For index `j = toOutCodewordsCount ℓ ϑ i.castSucc`: embed maps to `Sum.inr 0` (new oracle from
  message)
-/
lemma snoc_oracle_eq_mkVerifierOStmtOut_commitStep
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩))
    (transcript : FullTranscript (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (h_transcript_eq : transcript.messages ⟨0, rfl⟩ = newOracle)
    :
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn newOracle =
    OracleVerifier.mkVerifierOStmtOut (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed
      (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i hCR).hEq oStmtIn transcript := by
  sorry

/-- The first oracle is preserved when snocing a new oracle.

Since `getFirstOracle` extracts index 0, and `snoc_oracle` at index 0 always falls into
the "old oracle" branch (0 < toOutCodewordsCount), the first oracle is unchanged.
-/
lemma getFirstOracle_snoc_oracle
    (i : Fin ℓ) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := destIdx)) :
    getFirstOracle 𝔽q β
    (snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_destIdx oStmtIn newOracleFn) =
    getFirstOracle 𝔽q β oStmtIn := by
  sorry

/-- Oracle folding consistency is preserved when adding a new oracle in a commit step.

This lemma shows that if `oStmtIn` satisfies `oracleFoldingConsistencyProp` at round `i.castSucc`,
then `oStmtOut` (constructed via `mkVerifierOStmtOut` with commit step's embed/hEq) satisfies it at
`i.succ`.

**Key insight**: In a commit step:
- The oracle frontier index values are equal:
  `(mkFromStmtIdxCastSuccOfSucc i).val = (mkFromStmtIdx i.succ).val`
- The challenges don't change (commit step has no verifier challenges)
- Therefore oracle folding consistency trivially carries over
-/
-- Arithmetic bound lemmas
lemma commitStep_j_bound (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i.succ) :
    j.val < toOutCodewordsCount ℓ ϑ i.castSucc :=
  by
  have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
  conv_rhs at hj => rw [h_count_succ]
  omega

lemma commitStep_j_is_last (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i.succ)
    (hj_next : ¬ j.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc) :
    j.val + 1 = toOutCodewordsCount ℓ ϑ i.castSucc := by
  have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
  conv_rhs at hj => rw [h_count_succ]
  omega

lemma strictOracleFoldingConsistency_commitStep
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (stmtIn : Statement (L := L) Context i.succ)
    (witIn : Witness 𝔽q β i.succ)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ i.castSucc j)
    (challenges : (pSpecCommit 𝔽q β i).Challenges)
    (h_wit_struct_In : witnessStructuralInvariant 𝔽q β (mp := mp) stmtIn witIn)
    (h_oracle_folding_In : strictOracleFoldingConsistencyProp 𝔽q β (t := witIn.t) (i := i.castSucc)
      (challenges := Fin.take (m := i)
        (v := stmtIn.challenges) (h := by
          simp only [Fin.val_succ, le_add_iff_nonneg_right, zero_le]))
      (oStmt := oStmtIn)) :
    let step := (commitStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i (hCR := hCR))
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    let verifierStmtOut := step.verifierOut stmtIn transcript
    let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
      oStmtIn transcript
    strictOracleFoldingConsistencyProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i.succ)
      (challenges := Fin.take (m := i.val + 1)
        (v := verifierStmtOut.challenges) (h := by simp only [Fin.val_succ, le_refl]))
      (oStmt := verifierOStmtOut) (t := witIn.t)
    := by
  sorry

/-! Commit step logic is strongly complete.
The key insight is that the commit step just extends the oracle without changing the statement,
and the verifier always accepts (no verification check). -/
lemma commitStep_is_logic_complete (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i (hCR := hCR)).IsStronglyComplete := by
  sorry

end CommitStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step

This section implements the final sumcheck step that sends the constant `c := f^(ℓ)(0, ..., 0)`
from the prover to the verifier. This step completes the sumcheck verification by ensuring
the final constant is consistent with the folding chain.

The step consists of :
- P → V : constant `c := f^(ℓ)(0, ..., 0)`
- V verifies : `s_ℓ = eqTilde(r, r') * c`
=> `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})` and `f^(ℓ)(0, ..., 0)`

**Key Mathematical Insight** : At round ℓ, we have :
- `P^(ℓ)(X) = Σ_{w ∈ B_0} H_ℓ(w) · X_w^(ℓ)(X) = H_ℓ(0) · X_0^(ℓ)(X) = H_ℓ(0)`
- Since `H_ℓ(X)` is constant (zero-variate): `H_ℓ(X) = t(r'_0, ..., r'_{ℓ-1})`
- Therefore : `P^(ℓ)(X) = t(r'_0, ..., r'_{ℓ-1})` (constant polynomial)
- And `s_ℓ = ∑_{w ∈ B_0} t(r'_0, ..., r'_{ℓ-1}) = t(r'_0, ..., r'_{ℓ-1})`
-/

/-- The Logic Instance for the final sumcheck step.
This is a 1-message protocol where the prover sends the final constant c. -/
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
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := BBF_SumcheckMultiplierParam)
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
  hEq := fun oracleIdx => by simp only [Fin.eta]

/-! **Strict version**: When folding the last oracle to level `ℓ` (final sumcheck),
the iterated fold of the last oracle equals the constant function.

This is the strict version that uses exact equality instead of UDR codewords.
It is used in the final sumcheck step to show that the folding chain correctly
terminates at the constant function. -/
lemma iterated_fold_to_const_strict
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_strictOracleWitConsistency_In : strictOracleWitnessConsistency 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := SumcheckBaseContext L ℓ)
      (mp := BBF_SumcheckMultiplierParam) (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (stmt := stmtIn) (wit := witIn) (oStmt := oStmtIn)) :
    let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    let verifierStmtOut := step.verifierOut stmtIn transcript
    let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq oStmtIn transcript
    let lastDomainIdx := getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)
    -- have h_eq := getLastOracleDomainIndex_last (ℓ := ℓ) (ϑ := ϑ)
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
  sorry

/-! The verifier check passes in the final sumcheck step.
**Proof structure:**
1. From `sumcheckConsistencyProp`:
   - `stmtIn.sumcheck_target = ∑ x ∈ 𝓑^ᶠ(0), witIn.H.val.eval x`
   - Since `𝓑^ᶠ(0) = {∅}`, this simplifies to `witIn.H.val.eval (fun _ => 0)`

2. From `witnessStructuralInvariant`:
   - `witIn.H = projectToMidSumcheckPoly ...`
   - Using `projectToMidSumcheckPoly_at_last`:
   - `witIn.H.val.eval (fun _ => 0) = eqTilde(...) * witIn.f ⟨0, ...⟩`
3. Combining these gives the verifier check equation. -/
lemma finalSumcheckStep_verifierCheck_passed
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H)
    (h_strictOracleWitConsistency_In : strictOracleWitnessConsistency 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := SumcheckBaseContext L ℓ)
      (mp := BBF_SumcheckMultiplierParam) (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)) (stmt := stmtIn)
    (wit := witIn) (oStmt := oStmtIn)) :
    let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  sorry

/-! Final sumcheck step logic is strongly complete.
**Key Proof Obligations:**
1. **Verifier Check**: Show that `stmtIn.sumcheck_target = eq_tilde_eval * c` where
   `c = wit.f ⟨0, ...⟩`
   - This should follow from `h_relIn` (roundRelation) which includes `oracleWitnessConsistency`
   - The `oracleWitnessConsistency` includes:
     * `witnessStructuralInvariant`: `wit.H = projectToMidSumcheckPoly ...` and
       `wit.f = getMidCodewords ...`
     * `sumcheckConsistencyProp`: `stmt.sumcheck_target = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ℓ),
       wit.H.val.eval x`. For `i = Fin.last ℓ`, we have `ℓ - ℓ = 0`, so this is a sum over 0 vars
   - Need to connect these properties to show the verifier check passes

2. **Relation Out**: Show that the output satisfies `finalSumcheckRelOut`
   - This involves showing `finalSumcheckStepFoldingStateProp` holds for the output
-/
lemma finalSumcheckStep_is_logic_complete :
    (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).IsStronglyComplete := by
  sorry

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold
