/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims
public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.OracleReduction.Basic
public import ArkLib.OracleReduction.LogicStep
public import ArkLib.Data.Misc.Basic

/-!
# Binary Basefold query-phase protocol

Oracle-aware logic, prover, verifier, and reduction bundles for the final query round.
Folding, completeness, and soundness proofs live in the corresponding sibling modules;
the `QueryPhase` umbrella re-exports their public API.
-/

@[expose] public section

open OracleSpec

namespace Binius.BinaryBasefold.QueryPhase

/-!
## Query Phase (Final Query Round)
The final verification phase (proximity testing) as an oracle reduction.
(Note that here `B_k` means the boolean hypercube of dimension `k`)

- `V` executes the following querying procedure:
  for `γ` repetitions do
    `V` samples a challenge `v ← B_{ℓ+R}` randomly and sends it to P.
    for `i in {0, ϑ, ..., ℓ-ϑ}` (i.e., taking `ϑ`-sized steps) do
      for each `u` in `B_v`, => gather data for `c_{i+ϑ}`
        `V` sends (query, [f^(i)], (u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})) to the oracle.
      if `i > 0` then `V` requires `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})`.
      `V` defines `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`.
    `V` requires `c_ℓ ?= c`.
-/
noncomputable section
open OracleSpec OracleComp
open AdditiveNTT Polynomial MvPolynomial ProtocolSpec
open Probability

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]

variable (𝔽q : Type) [Field 𝔽q]
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section FinalQueryRoundIOR

/-!
### Oracle-Aware Reduction Logic for Query Phase

The query phase uses `OracleReduction.OracleAwareLogicStep` because its verifier check involves
oracle queries (querying committed codewords at fiber points).
-/

/-- The oracle-aware reduction logic step for the query phase.

This encapsulates the pure logic of the query phase:
- `verifierCheck`: Runs oracle checks at the fiber evaluations
- `verifierOut`: Returns `true` after the checks pass
- `honestProverTranscript`: The honest transcript just receives the challenges
- `proverOut`: The honest prover always outputs `(true, ())` -/
noncomputable def queryPhaseLogicStep :
    OracleReduction.OracleAwareLogicStep
      -- oSpec is the base/shared oracle (empty for query phase - no random oracles)
      -- The structure internally uses oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)
      (oSpec := []ₒ)
      (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
      (WitIn := Unit)
      (OracleIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleOut := fun _ : Empty => Unit)
      (StmtOut := Bool)
      (WitOut := Unit)
      (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  -- Relations
  completeness_relIn := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  completeness_relOut := acceptRejectOracleRel
  -- Verifier (Oracle-Aware): verifierCheck queries oracles and returns StmtOut
  -- Iterates through all γ_repetitions and checks each one
  verifierCheck := fun stmtIn transcript => do
    let challenges := transcript.challenges
    let fold_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0 :=
      challenges ⟨0, by rfl⟩
    for rep in (List.finRange γ_repetitions) do
      let v := fold_challenges rep
      let _ ← checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        v stmtIn stmtIn.finalConstant
    return true  -- StmtOut = Bool for QueryPhase
  -- Pure output computation (deterministic)
  verifierOut := fun _stmtIn _transcript => true
  outputInterfaces := fun i => nomatch i
  outputOracle := .inl (OracleOutputEmbedding.mk (Oₛₒ := fun i : Empty => nomatch i)
    ⟨Empty.elim, fun a _ => Empty.elim a⟩ (fun i => Empty.elim i) (fun i => Empty.elim i))
  -- Honest prover transcript: just receives the challenges
  honestProverTranscript := fun stmtIn _witIn _oStmtIn challenges =>
    FullTranscript.mk1 (challenges ⟨0, by rfl⟩)
  -- Prover output: always outputs (true, ())
  proverOut := fun _stmtIn _witIn _oStmtIn _transcript =>
    ((true, fun i => Empty.elim i), ())

/-- Before the query challenge the prover retains the input; afterwards it also retains the
sampled query points. -/
def QueryPhaseProverState : Fin (1 + 1) → Type := fun
  | 0 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit
  | 1 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit ×
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge ⟨0, by rfl⟩

/-- The oracle prover for the final query phase.

Uses components from `queryPhaseLogicStep` for consistency with the logic specification. -/
noncomputable def queryOracleProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  -- Prover state: tracks (stmtIn, oStmtIn, witIn) and optionally the challenges
  PrvState := QueryPhaseProverState 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  input := fun ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ => (stmtIn, oStmtIn, witIn)
  sendMessage
  | ⟨0, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩  => do
    -- V sends all γ challenges v₁, ..., v_γ
    pure (fun challenges => (stmtIn, oStmtIn, witIn, challenges))
  output := fun ⟨stmtIn, oStmtIn, witIn, challenges⟩ => do
    -- Build the transcript using the logic step's honestProverTranscript
    let transcript := FullTranscript.mk1 (pSpec :=
      pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (challenges)
    -- Delegate to proverOut from the logic step
    pure (OracleReduction.LogicStep.proverOut
      (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) stmtIn witIn oStmtIn transcript)

/-- The oracle verifier for the final query phase.

Uses components from `queryPhaseLogicStep` for consistency with the logic specification:
- `verifierCheck`: monadic check via `verifyQueryPhase`
- `verifierOut`: pure output computation
- The output has no oracles; `OracleProofVerifier.ofVerify` supplies that interface. -/
noncomputable def queryOracleVerifier :
  OracleProofVerifier
    (oSpec := []ₒ)
    (Statement := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStatement := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleProofVerifier.ofVerify fun stmtIn challenges => do
    let transcript := FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (challenges ⟨0, by rfl⟩)
    let logic := queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    let _ ← (logic.verifierCheck stmtIn transcript)
    pure (logic.verifierOut stmtIn transcript)

/-- The oracle reduction for the final query phase. -/
noncomputable def queryOracleReduction :
  OracleReduction
    (Oₛₒ := fun i : Empty => nomatch i)
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.mk (Oₛₒ := fun i : Empty => nomatch i)
    (queryOracleProver 𝔽q β (ϑ := ϑ) γ_repetitions)
    (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions)

end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase
