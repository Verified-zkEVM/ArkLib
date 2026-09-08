/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Phase
import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness

/-!
# Execution, completeness and knowledge of the scalar head

The head has no random challenge. A successful related output deterministically reads back a
source witness using the proved layout inverse. Its zero-error knowledge theorem has an explicit
extractor and knowledge state; this does not assert that the unchecked partial family is correct.
Perfect completeness quantifies over every initial oracle-state distribution.
-/

noncomputable section

namespace RingSwitching.Packing.ScalarHead

open OracleSpec OracleComp ProtocolSpec MvPolynomial ProbabilityTheory
open scoped NNReal

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  (layout : ClaimLayout data m) (pc : PackedCommitment data.P m)

/-- The sole-message transcript, with no challenge coordinates. -/
def transcript (α : data.ιP → data.E) : FullTranscript (pSpec data) :=
  fun | ⟨0, _⟩ => α

/-- The honest prover returns the partial-evaluation family and preserves the commitment oracle. -/
theorem prover_run (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j) (p : layout.Source) :
    (prover data m layout pc).run (stmt, ost) p =
      pure (transcript data (partials data m layout stmt.1 (layout.components p)),
        (nextStatement data m layout stmt (partials data m layout stmt.1 (layout.components p)),
          ost), layout.components p) := by
  have h0 : (pSpec data).dir 0 = .P_to_V := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_one,
    Prover.processRound_of_dir_eq_P_to_V 0 h0]
  simp only [prover, pure_bind, liftM_pure]
  congr 1
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · rfl

open scoped Classical in
/-- Full production execution returns no output when the scalar reconstruction fails. -/
theorem reduction_run (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j) (p : layout.Source) :
    ((reduction data m layout pc).toReduction.run (stmt, ost) p).run =
      pure (if check data m layout stmt (partials data m layout stmt.1 (layout.components p)) then
        some ((transcript data (partials data m layout stmt.1 (layout.components p)),
          (nextStatement data m layout stmt (partials data m layout stmt.1 (layout.components p)),
            ost), layout.components p),
          (nextStatement data m layout stmt (partials data m layout stmt.1 (layout.components p)),
            ost)) else none) := by
  rw [Reduction.run_eq_of_guarded_verifier _ (guardedForm data m layout pc)]
  change ((prover data m layout pc).run (stmt, ost) p >>= _) = _
  rw [prover_run, pure_bind]
  by_cases hc : check data m layout stmt (partials data m layout stmt.1 (layout.components p)) <;>
    simp [guardedForm, transcript, FullTranscript.messages, hc]

/-- Perfect completeness holds at every oracle state, with no distribution restriction. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction data m layout pc).perfectCompleteness init impl
      (relIn data m layout pc) (relOut data m pc) := by
  classical
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt p hIn x hx
  rw [reduction_run, if_pos (honest_check data m layout pc hIn)] at hx
  have hx := OracleComp.eq_of_mem_support_pure _ hx
  subst x
  exact ⟨_, rfl, honest_relOut data m layout pc hIn, rfl⟩

/-- A positive-probability related output determines the scalar check and family output. -/
theorem positive_output {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j) (tr : FullTranscript (pSpec data))
    (ps : data.ιP → B⦃≤ 1⦄[X Fin m])
    (h : Pr[ fun out => (out, ps) ∈ relOut data m pc |
      OptionT.mk do (simulateQ impl
        ((verifier data m layout pc).toVerifier.run (stmt, ost) tr)).run' (← init)] > 0) :
    check data m layout stmt (tr.messages ⟨0, rfl⟩) ∧
      ((nextStatement data m layout stmt (tr.messages ⟨0, rfl⟩), ost), ps) ∈
        relOut data m pc := by
  classical
  rw [gt_iff_lt, probEvent_pos_iff] at h
  obtain ⟨out, hout, hrel⟩ := h
  rw [OptionT.mem_support_iff] at hout
  simp only [Verifier.run, verifier_verify] at hout
  by_cases hc : check data m layout stmt (tr.messages ⟨0, rfl⟩)
  · rw [if_pos hc] at hout
    change some out ∈ support (init >>= fun _ => pure (some
      (nextStatement data m layout stmt (tr.messages ⟨0, rfl⟩), ost))) at hout
    simp only [support_bind_const, support_pure, Set.mem_ofPred_eq] at hout
    obtain rfl := Option.some.inj hout.1
    exact ⟨hc, hrel⟩
  · rw [if_neg hc] at hout
    change some out ∈ support (init >>= fun _ => pure none) at hout
    simp at hout

/-- A source witness before the message and its component family afterwards. -/
def WitMid : Fin 2 → Type
  | ⟨0, _⟩ => layout.Source
  | ⟨1, _⟩ => data.ιP → B⦃≤ 1⦄[X Fin m]

/-- Reassemble the original source witness at the sole prover-message step. -/
def extractor :
    Extractor.RoundByRound []ₒ (StmtIn := Input data m layout × (∀ j, pc.OStmt j))
      (WitIn := layout.Source) (WitOut := data.ιP → B⦃≤ 1⦄[X Fin m])
      (pSpec := pSpec data) (WitMid := WitMid data m layout) where
  eqIn := rfl
  extractMid
    | ⟨0, _⟩ => fun _ _ ps => layout.components.symm ps
  extractOut _ _ ps := ps

/-- The post-message state retains both the scalar check and the full-family relation. -/
def knowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier data m layout pc).KnowledgeStateFunction init impl
      (relIn data m layout pc) (relOut data m pc) (extractor data m layout pc) where
  toFun
    | ⟨0, _⟩ => fun stmt _ p => (stmt, p) ∈ relIn data m layout pc
    | ⟨1, _⟩ => fun stmt tr ps => check data m layout stmt.1 (tr 0) ∧
      ((nextStatement data m layout stmt.1 (tr 0), stmt.2), ps) ∈ relOut data m pc
  toFun_empty _ _ := Iff.rfl
  toFun_next
    | ⟨0, _⟩ => fun _ stmt _tr α ps h => readback data m layout pc stmt.1 stmt.2 α ps h.1 h.2
  toFun_full stmt tr ps h := positive_output data m layout pc init impl stmt.1 stmt.2 tr ps h

/-- Exact zero-error worst-case knowledge: there are no challenge positions in this head. -/
theorem rbrKnowledgeSoundnessWorstCaseWith {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn data m layout pc) (relOut data m pc) (verifier data m layout pc).toVerifier
      (WitMid data m layout) (extractor data m layout pc)
      (knowledgeStateFunction data m layout pc init impl) (fun _ => 0) := by
  intro stmt i tr
  rcases i with ⟨⟨i, hi⟩, hdir⟩
  have : i = 0 := by omega
  subst i
  contradiction

/-- The zero-error extractor and knowledge state satisfy the prover-averaged contract. -/
theorem rbrKnowledgeSoundnessWith {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (relIn data m layout pc) (relOut data m pc) (verifier data m layout pc).toVerifier
      (WitMid data m layout) (extractor data m layout pc)
      (knowledgeStateFunction data m layout pc init impl) (fun _ => 0) :=
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith init impl
    (rbrKnowledgeSoundnessWorstCaseWith data m layout pc init impl)

/-- The library's existential averaged knowledge contract for the zero-error scalar head. -/
theorem rbrKnowledgeSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier data m layout pc).rbrKnowledgeSoundness init impl
      (relIn data m layout pc) (relOut data m pc) (fun _ => 0) :=
  ⟨WitMid data m layout, extractor data m layout pc,
    knowledgeStateFunction data m layout pc init impl,
    rbrKnowledgeSoundnessWith data m layout pc init impl⟩

end RingSwitching.Packing.ScalarHead

end
