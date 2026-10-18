/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
# Terminal knowledge under actual oracle states

Fresh-initialization terminal knowledge alone is insufficient for the plain knowledge game.
Guarded verifiers satisfy the stronger terminal condition from every shared state because
their check and output have no oracle effects.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} {V : Verifier oSpec StmtIn StmtOut pSpec}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A guarded verifier has a related output with positive probability exactly when its
deterministic check passes and its deterministic output is related. -/
theorem GuardedForm.related_output_pos_iff (G : V.GuardedForm)
    (rel : Set (StmtOut × WitOut)) (stmt : StmtIn) (tr : pSpec.FullTranscript) (wit : WitOut) :
    (Pr{let out ← OptionT.mk do
      (simulateQ impl (V.run stmt tr)).run' (← init)}[(out, wit) ∈ rel] > 0) ↔
      G.check stmt tr = true ∧ (G.out stmt tr, wit) ∈ rel := by
  change (Pr{let out ← OptionT.mk do
    (simulateQ impl (V.run stmt tr).run).run' (← init)}[(out, wit) ∈ rel] > 0) ↔ _
  have hrun : (V.run stmt tr).run =
      if G.check stmt tr then pure (some (G.out stmt tr)) else pure none := by
    rw [run, G.verify_eq stmt tr]
    split <;> rfl
  rw [hrun, gt_iff_lt, OptionT.prEvent_mk_pos_iff]
  obtain ⟨s, hs⟩ := OracleComp.support_nonempty init
  by_cases h : G.check stmt tr = true
  · simp [h, StateT.run'_eq, show (support init).Nonempty from ⟨s, hs⟩]
  · simp [h, StateT.run'_eq]

/-- Passing a guarded verifier on a related output justifies the component's final knowledge
state. This fact holds for any initialization distribution and stateful oracle implementation. -/
theorem GuardedForm.knowledgeState_of_related_output
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}
    (G : V.GuardedForm) (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (stmt : StmtIn) (tr : pSpec.FullTranscript) (wit : WitOut)
    (hcheck : G.check stmt tr = true) (hrel : (G.out stmt tr, wit) ∈ relOut) :
    K (.last n) stmt tr (E.extractOut stmt tr wit) :=
  K.toFun_full stmt tr wit ((G.related_output_pos_iff init impl relOut stmt tr wit).mpr
    ⟨hcheck, hrel⟩)

/-- A terminal certificate valid from every actual verifier-start state. It requires knowledge
only for outputs that the given oracle implementation can produce from that state. -/
def KnowledgeStateFunction.TerminalFromEveryState
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}
    (K : V.KnowledgeStateFunction init impl relIn relOut E) : Prop :=
  ∀ stmt tr wit s out,
    some out ∈ support ((simulateQ impl (V.run stmt tr).run).run' s) →
    (out, wit) ∈ relOut → K (.last n) stmt tr (E.extractOut stmt tr wit)

/-- Fresh-initialization terminal knowledge applies at any particular state in the
initialization's support. No purity or state-preservation assumption is needed. -/
theorem KnowledgeStateFunction.terminal_of_mem_init_support
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (stmt : StmtIn) (tr : pSpec.FullTranscript) (wit : WitOut) (s : σ) (out : StmtOut)
    (hs : s ∈ support init)
    (hout : some out ∈ support ((simulateQ impl (V.run stmt tr).run).run' s))
    (hrel : (out, wit) ∈ relOut) :
    K (.last n) stmt tr (E.extractOut stmt tr wit) := by
  apply K.toFun_full stmt tr wit
  rw [gt_iff_lt, OptionT.prEvent_mk_pos_iff]
  refine ⟨out, ?_, hrel⟩
  simp only [mem_support_bind_iff]
  exact ⟨s, hs, hout⟩

/-- Full-support initialization makes the terminal certificate valid at all actual states,
including states modified by a prover. This does not supply composition transition bounds. -/
theorem KnowledgeStateFunction.terminalFromEveryState_of_full_support
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (hinit : ∀ s, s ∈ support init) : K.TerminalFromEveryState init impl := by
  intro stmt tr wit s out hout hrel
  exact K.terminal_of_mem_init_support init impl stmt tr wit s out (hinit s) hout hrel

/-- Guardedness discharges terminal knowledge for every actual shared state,
without resetting it. -/
theorem GuardedForm.terminalFromEveryState
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}
    (G : V.GuardedForm) (K : V.KnowledgeStateFunction init impl relIn relOut E) :
    K.TerminalFromEveryState init impl := by
  intro stmt tr wit s out hs hrel
  have hrun : (V.run stmt tr).run =
      if G.check stmt tr then pure (some (G.out stmt tr)) else pure none := by
    rw [run, G.verify_eq stmt tr]
    split <;> rfl
  rw [hrun] at hs
  by_cases hc : G.check stmt tr = true
  · have heq : out = G.out stmt tr := by simpa [hc, StateT.run'_eq] using hs
    subst out
    exact G.knowledgeState_of_related_output init impl K stmt tr wit hc hrel
  · simp [hc, StateT.run'_eq] at hs

end Verifier
