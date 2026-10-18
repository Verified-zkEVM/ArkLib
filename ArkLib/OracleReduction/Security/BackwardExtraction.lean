/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Security.RoundByRound
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Backward extraction and bad transitions

The deterministic part of RBR-to-plain knowledge soundness: if terminal knowledge holds but
backward extraction fails, some verifier challenge crossed a bad knowledge transition.
This argument does not reset or inspect the shared oracle state.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} {W : Fin (n + 1) → Type}

namespace Extractor.RoundByRound

/-- Run all intermediate extraction steps backwards from a supplied prefix witness. -/
def extractToInput (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W)
    (stmt : StmtIn) : (r : Fin (n + 1)) → pSpec.Transcript r → W r → WitIn :=
  Fin.induction (fun _ w => cast E.eqIn w)
    (fun j ih tr w => ih (Fin.init tr) (E.extractMid j stmt tr w))

/-- The straightline extractor performs backward extraction and does not query any oracle. -/
def toStraightline (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W) :
    Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec :=
  fun stmt wit tr _ _ => pure (E.extractToInput stmt (.last n) tr (E.extractOut stmt tr wit))

end Extractor.RoundByRound

namespace Verifier.KnowledgeStateFunction

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {V : Verifier oSpec StmtIn StmtOut pSpec}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}

/-- Failed extraction from a knowledgeable prefix entails a bad challenge transition within it.
The witness at that transition is the one obtained by backward extraction, not an honest witness. -/
theorem exists_bad_challenge_of_extract_failure
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (stmt : StmtIn) (r : Fin (n + 1)) (tr : pSpec.Transcript r) (w : W r)
    (hK : K r stmt tr w) (hfail : (stmt, E.extractToInput stmt r tr w) ∉ relIn) :
    ∃ (j : pSpec.ChallengeIdx) (hj : j.1.val < r.val) (v : W j.1.succ),
      let before : pSpec.Transcript j.1.castSucc := fun q =>
        tr ⟨q.val, by have hq : q.val < j.1.val := q.isLt; omega⟩
      let after : pSpec.Transcript j.1.succ := fun q =>
        tr ⟨q.val, by have hq : q.val < j.1.val + 1 := q.isLt; omega⟩
      ¬ K j.1.castSucc stmt before (E.extractMid j.1 stmt after v) ∧
        K j.1.succ stmt after v := by
  induction r using Fin.induction with
  | zero =>
    have htr : tr = default := by funext q; exact Fin.elim0 q
    subst tr
    exact (hfail ((K.toFun_empty stmt w).mpr hK)).elim
  | succ j ih =>
    classical
    by_cases hprev : K j.castSucc stmt (Fin.init tr) (E.extractMid j stmt tr w)
    · have hf : (stmt, E.extractToInput stmt j.castSucc (Fin.init tr)
          (E.extractMid j stmt tr w)) ∉ relIn := hfail
      obtain ⟨i, hi, v, hb⟩ := ih (Fin.init tr) (E.extractMid j stmt tr w) hprev hf
      refine ⟨i, by have h : i.1.val < j.val := hi
                    change i.1.val < j.val + 1; omega, v, ?_⟩
      exact hb
    · have hdir : pSpec.dir j = .V_to_P := by
        cases hd : pSpec.dir j with
        | V_to_P => rfl
        | P_to_V =>
          have hn := K.toFun_next j hd stmt (Fin.init tr) (tr (Fin.last j.val)) w
          simp only [Transcript.concat, Fin.snoc_init_self] at hn
          exact (hprev (hn hK)).elim
      refine ⟨⟨j, hdir⟩, by simp, w, ?_⟩
      exact ⟨hprev, hK⟩

/-- A bad challenge transition, read from a completed transcript. -/
def badChallengeOnTranscript
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (stmt : StmtIn) (tr : pSpec.FullTranscript) (i : pSpec.ChallengeIdx) : Prop :=
  rbrExtractionFailureEvent K E i stmt
    (fun q => tr ⟨q.val, by have hq : q.val < i.1.val := q.isLt; exact lt_trans hq i.1.isLt⟩)
    (tr i.1)

/-- Backward extraction from terminal knowledge fails only on a bad challenge in the transcript. -/
theorem exists_badChallengeOnTranscript_of_extract_failure
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (stmt : StmtIn) (tr : pSpec.FullTranscript) (wit : WitOut)
    (hK : K (.last n) stmt tr (E.extractOut stmt tr wit))
    (hfail : (stmt, E.extractToInput stmt (.last n) tr (E.extractOut stmt tr wit)) ∉ relIn) :
    ∃ i, badChallengeOnTranscript init impl K stmt tr i := by
  obtain ⟨i, hi, w, hbad⟩ := exists_bad_challenge_of_extract_failure
    init impl K stmt (.last n) tr (E.extractOut stmt tr wit) hK hfail
  let before : pSpec.Transcript i.1.castSucc := fun q =>
    tr ⟨q.val, by have hq : q.val < i.1.val := q.isLt; exact lt_trans hq i.1.isLt⟩
  let after : pSpec.Transcript i.1.succ := fun q =>
    tr ⟨q.val, by have hq : q.val < i.1.val + 1 := q.isLt; have := i.1.isLt; omega⟩
  have hext : before.concat (tr i.1) = after := by
    funext q
    apply eq_of_heq
    by_cases hq : q.val < i.1.val
    · exact Transcript.concat_apply_lt before (tr i.1) q.val hq q.isLt
    · have heq : q.val = i.1.val := by have := q.isLt; simp at *; omega
      have hbound : q.val < n := by
        have hq : q.val < i.1.val + 1 := q.isLt
        have := i.1.isLt
        omega
      have hfin : (⟨q.val, hbound⟩ : Fin n) = i.1 := Fin.ext heq
      have hval : HEq (tr i.1) (after q) := by
        change HEq (tr i.1) (tr ⟨q.val, hbound⟩)
        rw [hfin]
      exact (Transcript.concat_apply_last before (tr i.1) q.val heq q.isLt).trans
        hval
  refine ⟨i, w, ?_⟩
  change ¬ K i.1.castSucc stmt before (E.extractMid i.1 stmt (before.concat (tr i.1)) w) ∧
    K i.1.succ stmt (before.concat (tr i.1)) w
  rw [hext]
  exact hbad

/-- The extraction-failure union bound for any distribution of full transcripts and witnesses.
Connecting its round marginals to the actual execution remains a separate obligation. -/
theorem extraction_failure_le_sum_badChallenges
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (stmt : StmtIn) (game : ProbComp (pSpec.FullTranscript × WitOut)) :
    Pr{let x ← game}[
      K (.last n) stmt x.1 (E.extractOut stmt x.1 x.2) ∧
      (stmt, E.extractToInput stmt (.last n) x.1 (E.extractOut stmt x.1 x.2)) ∉ relIn] ≤
      ∑ i : pSpec.ChallengeIdx, Pr{let x ← game}[
        badChallengeOnTranscript init impl K stmt x.1 i] := by
  classical
  calc
    _ ≤ Pr{let x ← game}[∃ i, badChallengeOnTranscript init impl K stmt x.1 i] := by
      apply prEvent_mono
      intro x hx
      exact exists_badChallengeOnTranscript_of_extract_failure init impl K stmt x.1 x.2 hx.1 hx.2
    _ ≤ _ := prEvent_exists_le game (fun i x => badChallengeOnTranscript init impl K stmt x.1 i)

end Verifier.KnowledgeStateFunction
