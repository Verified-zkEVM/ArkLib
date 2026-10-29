/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.Acceptance
public import ArkLib.OracleReduction.Security.GuardedSoundness

/-!
# Guarded bridges from round-by-round knowledge security

The straightline extractor folds the round-by-round extractor backward over the actual
transcript, starting with the actual output witness. A failed fold from a valid guarded
output certifies a bad challenge, whose probability accumulates along the real execution.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {WitMid : Fin (n + 1) → Type}

namespace Extractor.RoundByRound

/-- A pure straightline extractor using the actual output witness and transcript. -/
def foldExtractor (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) :
    Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec :=
  fun stmt w tr _ _ ↦ pure (E.foldPrefix stmt (Fin.last n) tr (E.extractOut stmt tr w))

end Extractor.RoundByRound

namespace Verifier

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {V : Verifier oSpec StmtIn StmtOut pSpec}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}

/-- The extraction failure at a challenge, expressed on its completed prefix. -/
def KnowledgeStateFunction.extractionBadEvent
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (tr : pSpec.Transcript i.1.succ) : Prop :=
  ∃ w, ¬ K i.1.castSucc stmt (Fin.init tr) (E.extractMid i.1 stmt tr w) ∧
    K i.1.succ stmt tr w

/-- In the absence of a bad challenge, a valid intermediate witness folds to a valid input. -/
theorem KnowledgeStateFunction.foldPrefix_mem_of_no_badEvent
    (K : V.KnowledgeStateFunction init impl relIn relOut E) (stmt : StmtIn)
    (m : Fin (n + 1)) (tr : pSpec.Transcript m) (w : WitMid m)
    (hK : K m stmt tr w)
    (hbad : ¬ badEventState ∅ K.extractionBadEvent m stmt tr) :
    (stmt, E.foldPrefix stmt m tr w) ∈ relIn := by
  induction m using Fin.induction with
  | zero =>
    have htr : tr = default := Subsingleton.elim _ _
    simpa only [Extractor.RoundByRound.foldPrefix_zero, htr] using
      K.toFun_empty stmt w (htr ▸ hK)
  | succ j ih =>
    let prev : pSpec.Transcript j.castSucc := Fin.init tr
    let msg : pSpec.«Type» j := tr (Fin.last j.val)
    have htr : prev.concat msg = tr := Fin.snoc_init_self tr
    have hprev : ¬ badEventState ∅ K.extractionBadEvent j.castSucc stmt prev := by
      intro hb
      rcases hb with hf | ⟨i, hi, hb⟩
      · exact hf
      · simp only [Fin.val_castSucc] at hi
        apply hbad
        refine Or.inr ⟨i, by simp only [Fin.val_succ]; omega, ?_⟩
        rw [← htr, Transcript.restrict_concat (show i.1.succ.val ≤ j.val by
          simp only [Fin.val_succ]; omega)]
        exact hb
    have hstep : K j.castSucc stmt prev (E.extractMid j stmt tr w) := by
      cases hd : pSpec.dir j with
      | P_to_V =>
        simpa only [htr] using K.toFun_next j hd stmt prev msg w (htr ▸ hK)
      | V_to_P =>
        by_contra hn
        apply hbad
        exact Or.inr ⟨⟨j, hd⟩, by simp, by
          simpa only [Transcript.restrict_refl] using
            (show K.extractionBadEvent ⟨j, hd⟩ stmt tr from ⟨w, hn, hK⟩)⟩
    exact ih prev (E.extractMid j stmt tr w) hstep hprev

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- Round-by-round knowledge errors sum to ordinary knowledge error for a guarded verifier,
using the pure backward fold of the specified extractor. -/
theorem GuardedForm.knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWith
    (G : V.GuardedForm) (K : V.KnowledgeStateFunction init impl relIn relOut E)
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.rbrKnowledgeSoundnessWith init impl relIn relOut WitMid E K ε) :
    V.knowledgeSoundnessWith init impl relIn relOut E.foldExtractor (∑ i, ε i) := by
  let e := fun stmt w tr ↦ some (E.foldPrefix stmt (Fin.last n) tr (E.extractOut stmt tr w))
  change V.knowledgeSoundnessWith init impl relIn relOut
    (Extractor.Straightline.ofTranscriptAndOutput e) (∑ i, ε i)
  apply G.knowledgeSoundnessWith_of_output_transcript_event init impl relIn relOut e
    (∑ i, ε i) (badEventState ∅ K.extractionBadEvent (Fin.last n))
  · intro stmt tr w hc hr hf
    by_contra hb
    have hk := K.toFun_full stmt tr w (G.prEvent_pos_of_check hc hr)
    exact hf _ rfl (K.foldPrefix_mem_of_no_badEvent stmt (Fin.last n) tr
      (E.extractOut stmt tr w) hk hb)
  · intro Aux stmt aux P os
    rw [ENNReal.ofNNReal_finsetSum]
    apply prob_terminal_event_le_of_badEvents impl ∅ K.extractionBadEvent
      (fun i ↦ (ε i : ℝ≥0∞)) _ P stmt (by simp) aux _ (fun _ hb ↦ hb) os
    intro stmt _ i tr _
    have hinit (c : pSpec.Challenge i) : Fin.init (tr.concat c) = tr := by
      funext j
      exact Fin.snoc_castSucc
        (α := fun k : Fin (i.1.val + 1) ↦ pSpec.«Type» ⟨k.val, by omega⟩) c tr j
    simpa only [KnowledgeStateFunction.extractionBadEvent, hinit] using h stmt i tr

/-- Existential ordinary knowledge soundness from an exact round-by-round certificate. -/
theorem GuardedForm.knowledgeSoundness_of_rbrKnowledgeSoundnessWith
    (G : V.GuardedForm) (K : V.KnowledgeStateFunction init impl relIn relOut E)
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.rbrKnowledgeSoundnessWith init impl relIn relOut WitMid E K ε) :
    V.knowledgeSoundness init impl relIn relOut (∑ i, ε i) :=
  Verifier.knowledgeSoundness_of_with init impl
    (G.knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWith K h)

/-- A guarded verifier's existential round-by-round certificate yields ordinary
knowledge soundness. -/
theorem GuardedForm.knowledgeSoundness_of_rbrKnowledgeSoundness
    (G : V.GuardedForm) {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    V.knowledgeSoundness init impl relIn relOut (∑ i, ε i) := by
  obtain ⟨M, E, K, h⟩ := h
  exact G.knowledgeSoundness_of_rbrKnowledgeSoundnessWith K h

end Verifier

namespace OracleVerifier

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]
  {V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec}
  {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
  {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}
  {E : Extractor.RoundByRound oSpec (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec WitMid}

/-- The named guarded knowledge bridge for an oracle verifier, by materialization. -/
theorem knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWith_of_guarded
    (G : V.toVerifier.GuardedForm)
    (K : V.toVerifier.KnowledgeStateFunction init impl relIn relOut E)
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.toVerifier.rbrKnowledgeSoundnessWith init impl relIn relOut WitMid E K ε) :
    V.knowledgeSoundnessWith init impl relIn relOut E.foldExtractor (∑ i, ε i) :=
  G.knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWith K h

/-- Forget the named fold after applying the guarded oracle knowledge bridge. -/
theorem knowledgeSoundness_of_rbrKnowledgeSoundnessWith_of_guarded
    (G : V.toVerifier.GuardedForm)
    (K : V.toVerifier.KnowledgeStateFunction init impl relIn relOut E)
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.toVerifier.rbrKnowledgeSoundnessWith init impl relIn relOut WitMid E K ε) :
    V.knowledgeSoundness init impl relIn relOut (∑ i, ε i) :=
  G.knowledgeSoundness_of_rbrKnowledgeSoundnessWith K h

/-- Existential round-by-round knowledge security gives ordinary oracle knowledge security. -/
theorem knowledgeSoundness_of_rbrKnowledgeSoundness_of_guarded
    (G : V.toVerifier.GuardedForm) {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.toVerifier.rbrKnowledgeSoundness init impl relIn relOut ε) :
    V.knowledgeSoundness init impl relIn relOut (∑ i, ε i) :=
  G.knowledgeSoundness_of_rbrKnowledgeSoundness h

end OracleVerifier
