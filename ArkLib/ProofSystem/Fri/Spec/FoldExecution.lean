/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

module

public import ArkLib.ProofSystem.Fri.Spec.Transcript
public import ArkLib.ProofSystem.Fri.Spec.QueryExecution

/-!
# Execution of the FRI commitment phase

The verifier retains precisely the supplied challenges and committed words. All words in
this module are arbitrary: these execution identities do not assume an honest prover.
-/

@[expose] public section

namespace Fri.Spec

open Domain OracleSpec OracleComp ProtocolSpec Finset

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+)

/-- The accumulated statement at a non-final folding boundary. -/
def foldState (α : Fin k → F) (w : ∀ j, OracleStatement s ω (Fin.last k) j)
    (i : Fin (k + 1)) : Statement F i × (∀ j, OracleStatement s ω i j) :=
  (fun j ↦ α ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.is_le⟩,
    fun j ↦ w ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ i.is_le)⟩)

/-- The challenge and word supplied in a non-final folding round. -/
def foldTranscript (α : Fin k → F) (w : ∀ j, OracleStatement s ω (Fin.last k) j)
    (i : Fin k) : (FoldPhase.pSpec (ω := ω) s i).FullTranscript :=
  !h[α i, w i.succ]

/-- A folding verifier appends exactly its challenge and committed word. -/
theorem foldVerifier_run (α : Fin k → F)
    (w : ∀ j, OracleStatement s ω (Fin.last k) j) (i : Fin k) :
    (FoldPhase.foldVerifier (ω := ω) s i).toVerifier.run
      (foldState s α w i.castSucc) (foldTranscript s α w i) =
        pure (foldState s α w i.succ) := by
  apply OptionT.ext
  change Option.map _ <$> simulateQ _ (pure _) = _
  simp only [simulateQ_pure, map_pure, Option.map_some]
  congr 3
  · funext j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · exact Fin.dconcat_last (motive := fun _ : Fin (i.val + 1) ↦ F) _ _
    · simp only [Fin.vappend, Fin.dappend, Fin.dconcat_castSucc]
      rfl
  · funext j
    apply eq_of_heq
    dsimp only [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
      FoldPhase.foldVerifier, DFunLike.coe]
    split <;> rename_i j' he
    · have hj : j'.val = j.val := by
        split_ifs at he with h
        exact congrArg Fin.val (Sum.inl.inj he).symm
      have hw : HEq (w ⟨j'.val, by
          simp only [Fin.val_last]; have := j'.isLt
          simp only [Fin.val_castSucc] at this; omega⟩) (w ⟨j.val, by
          simp only [Fin.val_last]; have := j.isLt; simp only [Fin.val_succ] at this; omega⟩) :=
        congr_arg_heq w (Fin.ext hj)
      simpa only [eqRec_heq_iff] using hw
    · have hj : j.val = i.val + 1 := by
        split_ifs at he with h
        exact h
      have hj' : j' = ⟨1, by simp⟩ := by
        simpa only [dite_eq_left hj, Sum.inr.injEq] using he.symm
      subst j'
      simp only [eqRec_heq_iff]
      change HEq (w i.succ) (w ⟨j.val, _⟩)
      exact congr_arg_heq w (Fin.ext hj.symm)

/-- The complete sequence of non-final verifiers retains the entire committed history. -/
theorem foldVerifiers_run (α : Fin k → F)
    (w : ∀ j, OracleStatement s ω (Fin.last k) j) :
    (OracleVerifier.seqCompose (Statement F) (OracleStatement s ω)
      (fun i ↦ FoldPhase.foldVerifier (ω := ω) s i)).toVerifier.run
      (foldState s α w 0) (FullTranscript.seqCompose (foldTranscript s α w)) =
        pure (α, w) := by
  rw [OracleVerifier.seqCompose_toVerifier]
  exact Verifier.seqCompose_run_eq_pure _ _ _ (foldState s α w)
    (foldVerifier_run s α w)

/-- Recover the arbitrary committed words from the non-final folding transcript. -/
def foldWords (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (tr : (pSpecFold k (ω := ω) s).FullTranscript) :
    ∀ j, OracleStatement s ω (Fin.last k) j :=
  Fin.cases f (fun i ↦ (FullTranscript.component tr i) 1)

/-- Recover the challenges from the non-final folding transcript. -/
def foldChallenges (tr : (pSpecFold k (ω := ω) s).FullTranscript) : Fin k → F :=
  fun i ↦ (FullTranscript.component tr i) 0

/-- Reading and reassembling the folding transcript recovers the original transcript. -/
theorem foldTranscript_reassemble (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (tr : (pSpecFold k (ω := ω) s).FullTranscript) :
    FullTranscript.seqCompose (foldTranscript s (foldChallenges s tr) (foldWords s f tr)) =
      tr := by
  have hc : foldTranscript s (foldChallenges s tr) (foldWords s f tr) =
      FullTranscript.component tr := by
    funext i j
    fin_cases j <;> rfl
  rw [hc, FullTranscript.seqCompose_component]

/-- Execution of the existing composed non-final verifier on any transcript. -/
theorem foldVerifiers_run_transcript
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (tr : (pSpecFold k (ω := ω) s).FullTranscript) :
    (OracleVerifier.seqCompose (Statement F) (OracleStatement s ω)
      (fun i ↦ FoldPhase.foldVerifier (ω := ω) s i)).toVerifier.run stmt tr =
        pure (foldChallenges s tr, foldWords s (stmt.2 0) tr) := by
  have hs : foldState s (foldChallenges s tr) (foldWords s (stmt.2 0) tr) 0 = stmt := by
    apply Prod.ext
    · funext j
      exact Fin.elim0 j
    · funext j
      fin_cases j
      rfl
  have h := foldVerifiers_run s (foldChallenges s tr) (foldWords s (stmt.2 0) tr)
  rw [hs, foldTranscript_reassemble] at h
  exact h

namespace FinalFoldPhase

/-- Final folding preserves each previously committed word. -/
theorem committedWord_materialize (d : ℕ+)
    (w : ∀ j, OracleStatement s ω (Fin.last k) j)
    (tr : (pSpec F).FullTranscript) (i : Fin (k + 1)) :
    committedWord s ((finalFoldVerifier s d).materializeOutput
      tr.challenges w tr.messages) i = w i := by
  unfold committedWord
  apply eq_of_heq
  refine (cast_heq _ _).trans ?_
  dsimp only [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
    finalFoldVerifier, DFunLike.coe]
  split <;> rename_i j he
  · have hj : j = i := by
      simp only [Fin.val_castSucc, show i.val ≠ k + 1 by omega,
        ↓reduceDIte, Sum.inl.injEq] at he
      exact Fin.ext (congrArg Fin.val he).symm
    subst j
    simp only [eqRec_heq_iff]
    rfl
  · simp only [Fin.val_castSucc, show i.val ≠ k + 1 by omega,
      ↓reduceDIte] at he
    exact (Sum.inl_ne_inr he).elim

/-- The last retained entry is exactly the final polynomial message. -/
theorem finalPolynomial_materialize (d : ℕ+)
    (w : ∀ j, OracleStatement s ω (Fin.last k) j)
    (tr : (pSpec F).FullTranscript) :
    finalPolynomial s ((finalFoldVerifier s d).materializeOutput
      tr.challenges w tr.messages) = tr 1 := by
  unfold finalPolynomial
  apply eq_of_heq
  refine (cast_heq _ _).trans ?_
  dsimp only [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
    finalFoldVerifier, DFunLike.coe]
  split <;> rename_i j he
  · simp only [Fin.val_last, ↓reduceDIte] at he
    exact (Sum.inr_ne_inl he).elim
  · have hj : j = ⟨1, by simp⟩ := by
      simpa only [Fin.val_last, ↓reduceDIte, Sum.inr.injEq] using he.symm
    subst j
    simp only [eqRec_heq_iff]
    rfl

/-- Resolve the final polynomial message using the actual message-oracle interface. -/
theorem simulate_getConst (w : ∀ j, OracleStatement s ω (Fin.last k) j)
    (tr : (pSpec F).FullTranscript) :
    simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) w tr.messages)
      (liftM (getConst F) : OracleComp ((emptySpec.{0, 0}) +
        ([OracleStatement s ω (Fin.last k)]ₒ + [(pSpec F).Message]ₒ)) _) =
      pure (tr 1) := by
  have h := QueryImpl.simulateQ_addLift_add_liftM_right
    (target := OracleComp (emptySpec.{0, 0}))
    (QueryImpl.id (emptySpec.{0, 0}))
    (OracleInterface.simOracle0 (OracleStatement s ω (Fin.last k)) w)
    (OracleInterface.simOracle0 (pSpec F).Message tr.messages) (getConst F)
  exact h.trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The final folding verifier accepts exactly the permitted polynomial degree. -/
theorem toVerifier_run (d : ℕ+) (α : Fin k → F)
    (w : ∀ j, OracleStatement s ω (Fin.last k) j)
    (tr : (pSpec F).FullTranscript) :
    ((finalFoldVerifier s d).toVerifier.run (α, w) tr).run =
      pure (if (tr 1).natDegree < d.val then
        some (Fin.append α (fun _ : Fin 1 ↦ tr 0),
          (finalFoldVerifier s d).materializeOutput tr.challenges w tr.messages)
        else none) := by
  have hlift : (liftM (getConst F) : OptionT (OracleComp ((emptySpec.{0, 0}) +
      ([OracleStatement s ω (Fin.last k)]ₒ + [(pSpec F).Message]ₒ))) _).run =
      some <$> (liftM (getConst F) : OracleComp ((emptySpec.{0, 0}) +
        ([OracleStatement s ω (Fin.last k)]ₒ + [(pSpec F).Message]ₒ)) _) := by
    rfl
  change Option.map _ <$> simulateQ _ ((finalFoldVerifier s d).verify α tr.challenges).run = _
  simp only [finalFoldVerifier, OptionT.run_bind, hlift,
    Option.elimM, simulateQ_bind, simulateQ_map, simulate_getConst, map_pure,
    pure_bind, Option.elim_some]
  split_ifs <;> simp [guard, *]

end FinalFoldPhase

/-- Challenge history after all folding rounds of an arbitrary transcript. -/
def foldPhaseChallenges (tr : (pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F).FullTranscript) :
    FinalStatement F k :=
  Fin.append (foldChallenges s tr.fst) (fun _ ↦ tr.snd 0)

/-- Materialized commitment history after the existing folding verifiers. -/
def foldPhaseHistory (d : ℕ+)
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (tr : (pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F).FullTranscript) :
    ∀ j, FinalOracleStatement s ω j :=
  (FinalFoldPhase.finalFoldVerifier s d).materializeOutput tr.snd.challenges
    (foldWords s (stmt.2 0) tr.fst) tr.snd.messages

/-- The actual composed folding verifier checks the final degree and retains exactly
the transcript-derived histories. -/
theorem reductionFold_run (d : ℕ+)
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (tr : (pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F).FullTranscript) :
    ((reductionFold k s d).verifier.toVerifier.run stmt tr).run =
      pure (if (tr.snd 1).natDegree < d.val then
        some (foldPhaseChallenges s tr, foldPhaseHistory s d stmt tr) else none) := by
  change ((OracleVerifier.append
    (OracleVerifier.seqCompose (Statement F) (OracleStatement s ω)
      (fun i ↦ FoldPhase.foldVerifier s i))
    (FinalFoldPhase.finalFoldVerifier s d)).toVerifier.run stmt tr).run = _
  rw [OracleVerifier.append_toVerifier, Verifier.append_run, foldVerifiers_run_transcript]
  exact FinalFoldPhase.toVerifier_run s d _ _ _

end Fri.Spec
