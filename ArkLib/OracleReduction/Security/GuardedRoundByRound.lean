/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Alexander Hicks
-/
module

public import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Guarded verifiers in round-by-round arguments

A guarded verifier either returns a deterministic verdict or aborts. This file collects the
facts a round-by-round proof needs about such a verifier.

* `Verifier.guard_and_of_prEvent_pos`: a positive-probability output event of a guarded
  verifier forces its guard to pass and the event to hold at its verdict. This discharges the
  terminal obligation `KnowledgeStateFunction.toFun_full`.
* `Verifier.rbrKnowledgeSoundnessWorstCaseWith_of_two_message`: for a prover-message,
  verifier-challenge protocol, worst-case round-by-round knowledge soundness
  (`Verifier.rbrKnowledgeSoundnessWorstCaseWith`) follows from a bound on the extraction-failure
  event `rbrExtractionFailureEvent` for every input statement and every length-one transcript
  prefix, that is, every prover message. The averaged notion follows through
  `Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness`.

The run equation that puts a query-guard-return oracle verifier in guarded form is
`OracleVerifier.toVerifier_verify_of_query_guard`.
-/

@[expose] public section

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal ProbabilityTheory

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

namespace Verifier

/-- A positive-probability output event of a guarded verifier forces the guard to pass and the
event to hold at the verdict: a failed guard aborts, and an aborted run outputs nothing. -/
theorem guard_and_of_prEvent_pos {n : ℕ} {pSpec : ProtocolSpec n}
    {V : Verifier oSpec StmtIn StmtOut pSpec} {stmt : StmtIn} {tr : FullTranscript pSpec}
    {check : Prop} [Decidable check] {out : StmtOut}
    (hV : V.verify stmt tr = if check then pure out else failure) {p : StmtOut → Prop}
    (h : Pr{let s ← OptionT.mk do
      (simulateQ impl (V.run stmt tr)).run' (← init)}[p s] > 0) :
    check ∧ p out := by
  have hrun : (V.run stmt tr : OracleComp oSpec (Option StmtOut)) =
      if check then pure (some out) else pure none := by
    simp only [Verifier.run, hV]
    split <;> rfl
  rw [gt_iff_lt, OptionT.prEvent_mk_pos_iff] at h
  obtain ⟨x, hx, hp⟩ := h
  rw [hrun] at hx
  by_cases hc : check
  · simp only [hc, ite_true, simulateQ_pure, support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨s, -, hs⟩ := hx
    have hxo : x = out := by
      simpa [StateT.run'_eq, StateT.run_pure] using hs
    exact ⟨hc, hxo ▸ hp⟩
  · simp only [hc, ite_false, simulateQ_pure, support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨s, -, hs⟩ := hx
    simp [StateT.run'_eq] at hs

/-- **Worst-case round-by-round knowledge soundness of a message-then-challenge round.** For a
protocol in which the prover sends one message and the verifier then sends one challenge, a bound
on the extraction-failure event at the challenge, for every input statement and every prover
message, is worst-case round-by-round knowledge soundness at that error, with the given
extractor and knowledge-state function. -/
theorem rbrKnowledgeSoundnessWorstCaseWith_of_two_message {pSpec : ProtocolSpec 2}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (hDir0 : pSpec.dir 0 = .P_to_V) (hDir1 : pSpec.dir 1 = .V_to_P)
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0} {WitMid : Fin 3 → Type}
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : V.KnowledgeStateFunction init impl relIn relOut extractor)
    (hbound : ∀ (stmtIn : StmtIn)
      (transcript : Transcript (⟨1, hDir1⟩ : pSpec.ChallengeIdx).1.castSucc pSpec),
      Pr{let c ← $ᵗ (pSpec.Challenge ⟨1, hDir1⟩)}[rbrExtractionFailureEvent kSF.toFun
        extractor ⟨1, hDir1⟩ stmtIn transcript c] ≤ rbrKnowledgeError ⟨1, hDir1⟩) :
    V.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut WitMid extractor kSF
      rbrKnowledgeError := by
  intro stmtIn i transcript
  obtain ⟨j, hj⟩ := i
  fin_cases j
  · exact absurd (hDir0.symm.trans hj) (by decide)
  · exact hbound stmtIn transcript

end Verifier
