/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.GuardedKnowledge
public import ArkLib.OracleReduction.Composition.Sequential.GuardedNary
public import ArkLib.OracleReduction.Security.ActualExtraction

/-!
# Stateful implementations of guarded knowledge-sound protocols

An implementation may query, mutate shared state, and reject nondeterministically.
Its accepting outputs must refine a guarded reference verifier at actual shared states.
This is an execution condition; component knowledge bounds are proved for the references.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {V U : Verifier oSpec StmtIn StmtOut pSpec}

/-- Every accepting execution agrees with the reference check and output. There is no
restriction on the final oracle state or on the probability of rejection. -/
def GuardedForm.AcceptingRefinement (G : U.GuardedForm)
    (V : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  ∀ stmt tr s out,
    some out ∈ support ((simulateQ impl (V.run stmt tr).run).run' s) →
      G.check stmt tr = true ∧ out = G.out stmt tr

/-- Reference knowledge predicates and extraction are unchanged by accepting refinement. -/
def KnowledgeStateFunction.of_acceptingRefinement
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}
    (G : U.GuardedForm) (K : U.KnowledgeStateFunction init impl relIn relOut E)
    (h : G.AcceptingRefinement impl V) :
    V.KnowledgeStateFunction init impl relIn relOut E where
  toFun := K.toFun
  toFun_empty := K.toFun_empty
  toFun_next := K.toFun_next
  toFun_full := by
    intro stmt tr wit hpos
    rw [gt_iff_lt, OptionT.prEvent_mk_pos_iff] at hpos
    obtain ⟨out, hout, hrel⟩ := hpos
    simp only [mem_support_bind_iff] at hout
    obtain ⟨s, _, hs⟩ := hout
    obtain ⟨hc, rfl⟩ := h stmt tr s out hs
    exact G.knowledgeState_of_related_output init impl K stmt tr wit hc hrel

/-- The transported terminal certificate holds at every actual state, not just fresh init. -/
theorem KnowledgeStateFunction.of_acceptingRefinement_terminal
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}
    (G : U.GuardedForm) (K : U.KnowledgeStateFunction init impl relIn relOut E)
    (h : G.AcceptingRefinement impl V) :
    (K.of_acceptingRefinement init impl G h).TerminalFromEveryState init impl := by
  intro stmt tr wit s out hout hrel
  obtain ⟨hc, rfl⟩ := h stmt tr s out hout
  exact G.knowledgeState_of_related_output init impl K stmt tr wit hc hrel

/-- Accepting refinement preserves fixed-prefix knowledge errors without resetting state. -/
theorem rbrKnowledgeSoundness_of_acceptingRefinement
    [∀ j, SampleableType (pSpec.Challenge j)]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    (G : U.GuardedForm) (h : G.AcceptingRefinement impl V)
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (hU : U.rbrKnowledgeSoundness init impl relIn relOut ε) :
    V.rbrKnowledgeSoundness init impl relIn relOut ε := by
  obtain ⟨W, E, K, hK⟩ := hU
  exact ⟨W, E, K.of_acceptingRefinement init impl G h, hK⟩

/-- Stateful accepting refinements have plain knowledge soundness with the sum of reference
round errors. Terminal knowledge is checked at the actual verifier-start state. -/
theorem knowledgeSoundness_of_acceptingRefinement
    [∀ j, SampleableType (pSpec.Challenge j)]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    (G : U.GuardedForm) (h : G.AcceptingRefinement impl V)
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (hU : U.rbrKnowledgeSoundness init impl relIn relOut ε) :
    V.knowledgeSoundness init impl relIn relOut (∑ i, ε i) := by
  obtain ⟨W, E, K, hK⟩ := hU
  apply (knowledgeSoundness_iff_exists_with init impl relIn relOut V _).mpr
  refine ⟨E.toStraightline, ?_⟩
  apply rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_terminal
    init impl (K.of_acceptingRefinement init impl G h)
    (K.of_acceptingRefinement_terminal init impl G h) ε
  apply rbrKnowledgeSoundnessWith_implies_rbrKnowledgeSoundnessAveragedWith init impl
  exact hK

section Append

variable {Stmt₁ Stmt₂ Stmt₃ : Type} {m k : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec k}
  {V₁ U₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
  {V₂ U₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}

/-- Accepting refinement composes through the actual intermediate shared state. -/
theorem GuardedForm.AcceptingRefinement.append
    (G₁ : U₁.GuardedForm) (G₂ : U₂.GuardedForm)
    (h₁ : G₁.AcceptingRefinement impl V₁) (h₂ : G₂.AcceptingRefinement impl V₂) :
    (G₁.append G₂).AcceptingRefinement impl (V₁.append V₂) := by
  intro stmt tr s out hout
  have hex : ∃ sOut, (some out, sOut) ∈ support
      ((simulateQ impl ((V₁.append V₂).run stmt tr).run).run s) := by
    simpa [StateT.run'_eq] using hout
  obtain ⟨sOut, hsOut⟩ := hex
  obtain ⟨mid, sMid, hm, ho⟩ :=
    (append_accepting_support_iff impl stmt tr s sOut out).mp hsOut
  have hm' : some mid ∈ support ((simulateQ impl (V₁.run stmt tr.fst).run).run' s) := by
    simpa [StateT.run'_eq] using (show ∃ t,
      (some mid, t) ∈ support ((simulateQ impl (V₁.run stmt tr.fst).run).run s) from
        ⟨sMid, hm⟩)
  have ho' : some out ∈ support ((simulateQ impl (V₂.run mid tr.snd).run).run' sMid) := by
    simpa [StateT.run'_eq] using (show ∃ t,
      (some out, t) ∈ support ((simulateQ impl (V₂.run mid tr.snd).run).run sMid) from
        ⟨sOut, ho⟩)
  obtain ⟨hc₁, rfl⟩ := h₁ stmt tr.fst s mid hm'
  obtain ⟨hc₂, heq⟩ := h₂ (G₁.out stmt tr.fst) tr.snd sMid out ho'
  exact ⟨by simp [GuardedForm.append, hc₁, hc₂], heq⟩

/-- Stateful implementations of guarded references compose with the references' original
per-round errors. Neither actual verifier is required to preserve shared state. -/
theorem append_rbrKnowledgeSoundness_of_acceptingRefinement
    {Wit₁ Wit₂ Wit₃ : Type}
    [∀ j, SampleableType (pSpec₁.Challenge j)]
    [∀ j, SampleableType (pSpec₂.Challenge j)]
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)}
    (G₁ : U₁.GuardedForm) (G₂ : U₂.GuardedForm)
    (h₁ : G₁.AcceptingRefinement impl V₁) (h₂ : G₂.AcceptingRefinement impl V₂)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hs₁ : U₁.rbrKnowledgeSoundness init impl rel₁ rel₂ ε₁)
    (hs₂ : U₂.rbrKnowledgeSoundness init impl rel₂ rel₃ ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  exact rbrKnowledgeSoundness_of_acceptingRefinement init impl (G₁.append G₂)
    (h₁.append impl G₁ G₂ h₂)
    (append_rbrKnowledgeSoundness_of_guarded_first init impl G₁ hs₁ hs₂)

end Append

/-- Accepting refinement composes over a finite sequence using actual intermediate states. -/
theorem GuardedForm.AcceptingRefinement.seqCompose
    {m : ℕ} (Stmt : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (U V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (U i).GuardedForm)
    (h : ∀ i, (G i).AcceptingRefinement impl (V i)) :
    (GuardedForm.seqCompose Stmt U G).AcceptingRefinement impl
      (Verifier.seqCompose Stmt V) := by
  induction m with
  | zero =>
    intro stmt tr s out hout
    have heq : out = stmt := by
      simpa [Verifier.seqCompose, Verifier.run, Verifier.id, StateT.run'_eq] using hout
    exact ⟨rfl, heq⟩
  | succ m ih =>
    exact (h 0).append impl (G 0)
      (GuardedForm.seqCompose (Stmt ∘ Fin.succ) (fun i => U i.succ) (fun i => G i.succ))
      (ih (Stmt ∘ Fin.succ) (fun i => U i.succ) (fun i => V i.succ)
        (fun i => G i.succ) (fun i => h i.succ))

/-- Stateful refinements preserve each reference component's fixed-prefix error in a sequence.
The refinement condition applies to all states, hence also to the actual reachable states. -/
theorem seqCompose_rbrKnowledgeSoundness_of_acceptingRefinement
    {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set (Stmt i × Wit i))
    (U V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (U i).GuardedForm)
    (h : ∀ i, (G i).AcceptingRefinement impl (V i))
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (hs : ∀ i, (U i).rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (ε i)) :
    (Verifier.seqCompose Stmt V).rbrKnowledgeSoundness init impl
      (rel 0) (rel (Fin.last m))
      (fun i => ε (seqComposeChallengeIdxToSigma i).1 (seqComposeChallengeIdxToSigma i).2) := by
  exact rbrKnowledgeSoundness_of_acceptingRefinement init impl
    (GuardedForm.seqCompose Stmt U G)
    (GuardedForm.AcceptingRefinement.seqCompose impl Stmt U V G h)
    (seqCompose_rbrKnowledgeSoundness_of_guarded init impl Stmt Wit rel U G ε hs)

end Verifier

namespace OracleVerifier

/-- Oracle sequential composition of stateful accepting refinements preserves round errors.
The reference verifiers operate on bundled statements and oracle statements. -/
theorem seqCompose_rbrKnowledgeSoundness_of_acceptingRefinement
    {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {m : ℕ} (Stmt Wit : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : ∀ i, ιₛ i → Type)
    [∀ i j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, OracleInterface ((pSpec i).Message j)]
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : ∀ i, OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (pSpec i))
    (U : ∀ i, Verifier oSpec (Stmt i.castSucc × ∀ j, OStmt i.castSucc j)
      (Stmt i.succ × ∀ j, OStmt i.succ j) (pSpec i))
    (G : ∀ i, (U i).GuardedForm)
    (h : ∀ i, (G i).AcceptingRefinement impl (V i).toVerifier)
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (hs : ∀ i, (U i).rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (ε i)) :
    (OracleVerifier.seqCompose Stmt OStmt V).toVerifier.rbrKnowledgeSoundness
      init impl (rel 0) (rel (Fin.last m))
      (fun i => ε (seqComposeChallengeIdxToSigma i).1 (seqComposeChallengeIdxToSigma i).2) := by
  rw [seqCompose_toVerifier]
  exact Verifier.seqCompose_rbrKnowledgeSoundness_of_acceptingRefinement init impl
    (fun i => Stmt i × ∀ j, OStmt i j) Wit rel U (fun i => (V i).toVerifier) G h ε hs

/-- Plain knowledge soundness for an oracle verifier refining a guarded reference at actual
shared states. No restriction is imposed on the prover's state mutations. -/
theorem knowledgeSoundness_of_acceptingRefinement
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
    {ιIn ιOut : Type} {OStmtIn : ιIn → Type} {OStmtOut : ιOut → Type}
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]
    {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, OracleInterface (pSpec.Message i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec}
    {U : Verifier oSpec (StmtIn × ∀ i, OStmtIn i) (StmtOut × ∀ i, OStmtOut i) pSpec}
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}
    (G : U.GuardedForm) (h : G.AcceptingRefinement impl V.toVerifier)
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (hs : U.rbrKnowledgeSoundness init impl relIn relOut ε) :
    V.knowledgeSoundness init impl relIn relOut (∑ i, ε i) :=
  Verifier.knowledgeSoundness_of_acceptingRefinement init impl G h hs

end OracleVerifier
