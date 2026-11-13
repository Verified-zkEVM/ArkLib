/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.Simulation
public import ArkLib.OracleReduction.Security.TranscriptTree.Composition
public import ArkLib.OracleReduction.Security.Accumulation

/-!
# Restrictions of an arbitrary prover at an append boundary

The prefix records its transcript and returns the original private state at the seam. The suffix
uses that state as its auxiliary input and continues the original prover, including its output
computation. Neither restriction assumes that the original prover was constructed with `append`.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open ProtocolSpec.ChallengeTree (leftRound rightRound leftPrefix rightPrefix)

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Restrict an arbitrary composite prover to its first protocol. Its output is a chosen function
of the prefix transcript, paired with the original private state at the seam. -/
def appendPrefix (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (out : pSpec₁.FullTranscript → Stmt₂) :
    Prover oSpec Stmt₁ Wit₁ Stmt₂ (P.PrvState (leftRound (Fin.last m))) pSpec₁ where
  PrvState i := pSpec₁.Transcript i × P.PrvState (leftRound i)
  input sw := (default, P.input sw)
  sendMessage i st := do
    let z ← P.sendMessage (MessageIdx.inl i) st.2
    let msg := cast (append_Type_castAdd i.1) z.1
    return (msg, st.1.concat msg, z.2)
  receiveChallenge i st := do
    let f ← P.receiveChallenge (ChallengeIdx.inl i) st.2
    return fun c => (st.1.concat c, f (cast (challenge_append_inl i).symm c))
  output st := pure (out st.1, st.2)

/-- The prefix's output does not query the shared oracle. -/
instance appendPrefix_outputIsPure
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (out : pSpec₁.FullTranscript → Stmt₂) : (P.appendPrefix out).OutputIsPure :=
  ⟨fun st => (out st.1, st.2), fun _ => rfl⟩

/-- Restrict an arbitrary composite prover to its second protocol, starting from a supplied
private state at the seam. The new input statement is ignored by this adversarial prover. -/
def appendSuffix (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) :
    Prover oSpec Stmt₂ (P.PrvState (leftRound (Fin.last m))) Stmt₃ Wit₃ pSpec₂ where
  PrvState i := P.PrvState (rightRound i)
  input sw := sw.2
  sendMessage i st := do
    let z ← P.sendMessage (MessageIdx.inr i) st
    return (cast (append_Type_natAdd i.1) z.1, z.2)
  receiveChallenge i st := do
    let f ← P.receiveChallenge (ChallengeIdx.inr i) st
    return fun c => f (cast (challenge_append_inr i).symm c)
  output st := P.output st

/-- Read a prefix transcript in the first component's types. -/
def appendPrefixTranscript {i : Fin (m + 1)}
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (leftRound i)) : pSpec₁.Transcript i :=
  fun j => cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    (⟨j.val, by have := j.isLt; have := i.isLt; omega⟩ : Fin m)) (tr j)

@[simp]
theorem appendPrefixTranscript_concat {i : Fin m}
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (leftRound i.castSucc))
    (c : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n i)) :
    appendPrefixTranscript (tr.concat c) =
      (appendPrefixTranscript tr).concat (cast (append_Type_castAdd i) c) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change cast _ ((tr.concat c) (Fin.last (Fin.castAdd n i).val)) = _
    rw [Transcript.concat_last, Transcript.concat_last]
    rfl
  · simp only [appendPrefixTranscript, Transcript.concat_castSucc]
    rfl

private theorem appendPrefix_processRound
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (out : pSpec₁.FullTranscript → Stmt₂) (i : Fin m)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (leftRound i.castSucc))
    (st : P.PrvState (leftRound i.castSucc)) :
    liftAppendLeft pSpec₂ ((P.appendPrefix out).processRound i
      (pure (appendPrefixTranscript tr, appendPrefixTranscript tr, st))) = (do
        let z ← P.processRound (Fin.castAdd n i) (pure (tr, st))
        return (appendPrefixTranscript z.1, appendPrefixTranscript z.1, z.2)) := by
  cases hd : pSpec₁.dir i with
  | P_to_V =>
    have hd' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .P_to_V := by simpa using hd
    rw [processRound_of_dir_eq_P_to_V _ hd, processRound_of_dir_eq_P_to_V _ hd']
    simp only [pure_bind, appendPrefix, liftM_bind, liftM_pure, bind_assoc]
    change (do
      let z ← liftAppendLeft pSpec₂ (liftM (P.sendMessage (MessageIdx.inl ⟨i, hd⟩) st) :
        OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
      pure ((appendPrefixTranscript tr).concat (cast (append_Type_castAdd i) z.1),
        (appendPrefixTranscript tr).concat (cast (append_Type_castAdd i) z.1), z.2)) = _
    rw [liftAppendLeft_liftM]
    simp only [appendPrefixTranscript_concat]
    rfl
  | V_to_P =>
    have hd' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = .V_to_P := by simpa using hd
    rw [processRound_of_dir_eq_V_to_P _ hd, processRound_of_dir_eq_V_to_P _ hd']
    simp only [pure_bind, appendPrefix, liftM_bind, liftM_pure, bind_assoc]
    change (do
      let c ← liftAppendLeft pSpec₂ (liftM (pSpec₁.getChallenge ⟨i, hd⟩) :
        OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
      let f ← liftAppendLeft pSpec₂ (liftM (P.receiveChallenge (ChallengeIdx.inl ⟨i, hd⟩) st) :
        OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
      pure ((appendPrefixTranscript tr).concat c, (appendPrefixTranscript tr).concat c,
        f (cast (challenge_append_inl ⟨i, hd⟩).symm c))) = _
    rw [liftAppendLeft_getChallenge]
    simp only [bind_map_left, liftAppendLeft_liftM,
      cast_cast, cast_eq, appendPrefixTranscript_concat]
    rfl

/-- Running the restricted prefix gives the original execution up to that round, with a second
copy of the transcript in its private state. The challenge inclusion is explicit. -/
theorem appendPrefix_runToRound
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (out : pSpec₁.FullTranscript → Stmt₂) (i : Fin (m + 1)) (stmt : Stmt₁) (wit : Wit₁) :
    liftAppendLeft pSpec₂ ((P.appendPrefix out).runToRound i stmt wit) = (do
      let z ← P.runToRound (leftRound i) stmt wit
      return (appendPrefixTranscript z.1, appendPrefixTranscript z.1, z.2)) := by
  induction i using Fin.induction with
  | zero =>
    change liftAppendLeft pSpec₂ ((P.appendPrefix out).runToRound 0 stmt wit) =
      (do let z ← P.runToRound 0 stmt wit
          pure (appendPrefixTranscript z.1, appendPrefixTranscript z.1, z.2))
    simp only [runToRound_zero_of_prover_first, liftAppendLeft, liftM_pure, pure_bind,
      appendPrefix]
    exact congrArg (fun tr : pSpec₁.Transcript 0 =>
      (pure (tr, tr, P.input (stmt, wit)) : OracleComp _ _)) (Subsingleton.elim _ _)
  | succ i ih =>
    change liftAppendLeft pSpec₂ ((P.appendPrefix out).runToRound i.succ stmt wit) =
      (do let z ← P.runToRound (Fin.castAdd n i).succ stmt wit
          pure (appendPrefixTranscript z.1, appendPrefixTranscript z.1, z.2))
    rw [runToRound_succ, runToRound_succ, Prover.processRound_bind, Prover.processRound_bind]
    simp only [liftAppendLeft, liftM_bind]
    change (do let z ← liftAppendLeft pSpec₂ ((P.appendPrefix out).runToRound i.castSucc stmt wit)
               liftAppendLeft pSpec₂ ((P.appendPrefix out).processRound i (pure z))) = _
    rw [ih]
    simp only [bind_assoc, pure_bind, appendPrefix_processRound]
    rfl

@[simp]
theorem leftPrefix_appendPrefixTranscript {i : Fin (m + 1)}
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (leftRound i)) :
    leftPrefix (appendPrefixTranscript tr) = tr := by
  funext j
  simp only [leftPrefix, appendPrefixTranscript]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

private theorem split_liftRight_ambient {α : Type} (oa : OracleComp oSpec α) :
    liftAppendRight pSpec₁ (liftM oa : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α) =
      (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α) := by
  unfold liftAppendRight
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih => simp [ih]; congr 1

private theorem split_liftRight_challenge (i : pSpec₂.ChallengeIdx) :
    liftAppendRight pSpec₁ (liftM (pSpec₂.getChallenge i) :
      OracleComp (oSpec + [pSpec₂.Challenge]ₒ) (pSpec₂.Challenge i)) =
    cast (challenge_append_inr (pSpec₁ := pSpec₁) i) <$>
      (liftM ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr i)) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := rfl

private theorem appendSuffix_processRound
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (i : Fin n) (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.Transcript i.castSucc)
    (st : P.PrvState (rightRound i.castSucc)) :
    (do let z ← liftAppendRight pSpec₁ ((P.appendSuffix (Stmt₂ := Stmt₂)).processRound i
          (pure (tr₂, st)))
        pure (rightPrefix tr₁ z.1, z.2)) =
      P.processRound (Fin.natAdd m i) (pure (rightPrefix tr₁ tr₂, st)) := by
  cases hd : pSpec₂.dir i with
  | P_to_V =>
    have hd' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .P_to_V := by simpa using hd
    rw [processRound_of_dir_eq_P_to_V _ hd, processRound_of_dir_eq_P_to_V _ hd']
    simp only [pure_bind, appendSuffix, liftM_bind, liftM_pure, bind_assoc]
    change (do
      let z ← liftAppendRight pSpec₁ (liftM (P.sendMessage (MessageIdx.inr ⟨i, hd⟩) st) :
        OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
      pure (rightPrefix tr₁ (tr₂.concat (cast (append_Type_natAdd i) z.1)), z.2)) = _
    rw [split_liftRight_ambient]
    simp only [ChallengeTree.rightPrefix_concat]
    congr 1
    funext z
    congr 2
    congr 1
    exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
  | V_to_P =>
    have hd' : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P := by simpa using hd
    rw [processRound_of_dir_eq_V_to_P _ hd, processRound_of_dir_eq_V_to_P _ hd']
    simp only [pure_bind, appendSuffix, liftM_bind, liftM_pure, bind_assoc]
    dsimp only [ChallengeIdx.inr] at *
    simp only [liftM_bind, liftM_pure, bind_assoc, pure_bind]
    change (do
      let c ← liftAppendRight pSpec₁ (liftM (pSpec₂.getChallenge ⟨i, hd⟩) :
        OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
      let f ← liftAppendRight pSpec₁ (liftM (P.receiveChallenge (ChallengeIdx.inr ⟨i, hd⟩) st) :
        OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
      pure (rightPrefix tr₁ (tr₂.concat c), f (cast (challenge_append_inr ⟨i, hd⟩).symm c))) = _
    rw [split_liftRight_challenge]
    simp only [bind_map_left, split_liftRight_ambient, ChallengeTree.rightPrefix_concat,
      cast_cast, cast_eq]
    rfl

/-- After the seam, the original execution is the prefix execution followed by the suffix
restriction, with the two transcript pieces joined. -/
theorem appendSuffix_runToRound
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (out : pSpec₁.FullTranscript → Stmt₂) (i : Fin (n + 1)) (stmt : Stmt₁) (wit : Wit₁) :
    P.runToRound (rightRound i) stmt wit = (do
      let z ← P.runToRound (leftRound (Fin.last m)) stmt wit
      let z₂ ← liftAppendRight pSpec₁ ((P.appendSuffix (Stmt₂ := Stmt₂)).runToRound i
        (out (appendPrefixTranscript z.1)) z.2)
      pure (rightPrefix (appendPrefixTranscript z.1) z₂.1, z₂.2)) := by
  induction i using Fin.induction with
  | zero =>
    simp only [runToRound_zero_of_prover_first, liftAppendRight, liftM_pure, pure_bind]
    change P.runToRound (leftRound (Fin.last m)) stmt wit = (do
      let z ← P.runToRound (leftRound (Fin.last m)) stmt wit
      pure (rightPrefix (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
        (appendPrefixTranscript z.1) (default : pSpec₂.Transcript 0), z.2))
    have he (z : (pSpec₁ ++ₚ pSpec₂).Transcript (leftRound (Fin.last m)) ×
        P.PrvState (leftRound (Fin.last m))) :
        (rightPrefix (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
          (appendPrefixTranscript z.1) (default : pSpec₂.Transcript 0), z.2) = z := by
      apply Prod.ext
      · exact (ChallengeTree.leftPrefix_last_eq_rightPrefix_default
          (appendPrefixTranscript z.1)).symm.trans (leftPrefix_appendPrefixTranscript z.1)
      · rfl
    exact (bind_pure (P.runToRound (leftRound (Fin.last m)) stmt wit)).symm.trans
      (congrArg (fun f => P.runToRound (leftRound (Fin.last m)) stmt wit >>= f)
        (funext fun z => congrArg pure (he z).symm))
  | succ i ih =>
    change P.runToRound (Fin.natAdd m i).succ stmt wit = _
    rw [runToRound_succ, Prover.processRound_bind]
    change (do let z ← P.runToRound (rightRound i.castSucc) stmt wit
               P.processRound (Fin.natAdd m i) (pure z)) = _
    rw [ih]
    simp only [bind_assoc]
    congr 1
    funext z
    simp only [pure_bind]
    rw [runToRound_succ, Prover.processRound_bind]
    simp only [liftAppendRight, liftM_bind, bind_assoc]
    congr 1
    funext z₂
    exact (appendSuffix_processRound (Stmt₂ := Stmt₂) P i
      (appendPrefixTranscript z.1) z₂.1 z₂.2).symm

/-- An arbitrary prover factors into its restrictions. The prefix output is pure, so no oracle
queries are inserted at the seam. -/
theorem run_appendSplit
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (out : pSpec₁.FullTranscript → Stmt₂) (stmt : Stmt₁) (wit : Wit₁) :
    P.run stmt wit = (do
      let r₁ ← liftAppendLeft pSpec₂ ((P.appendPrefix out).run stmt wit)
      let r₂ ← liftAppendRight pSpec₁ ((P.appendSuffix (Stmt₂ := Stmt₂)).run (out r₁.1) r₁.2.2)
      pure (r₁.1 ++ₜ r₂.1, r₂.2)) := by
  simp only [run, liftAppendLeft, liftAppendRight, liftM_bind, liftM_pure, bind_assoc]
  change (do
    let z ← P.runToRound (rightRound (Fin.last n)) stmt wit
    let r ← liftM (P.output z.2)
    pure (z.1, r)) = (do
    let z ← liftAppendLeft pSpec₂ ((P.appendPrefix out).runToRound (Fin.last m) stmt wit)
    let r ← liftAppendLeft pSpec₂ (liftM ((P.appendPrefix out).output z.2) :
      OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
    let z₂ ← liftAppendRight pSpec₁ ((P.appendSuffix (Stmt₂ := Stmt₂)).runToRound
      (Fin.last n) r.1 r.2)
    let r₂ ← liftAppendRight pSpec₁ (liftM ((P.appendSuffix (Stmt₂ := Stmt₂)).output z₂.2) :
      OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
    pure (z.1 ++ₜ z₂.1, r₂))
  rw [appendPrefix_runToRound, appendSuffix_runToRound P out]
  simp only [bind_assoc, pure_bind, appendPrefix, liftM_pure, liftAppendLeft,
    ChallengeTree.rightPrefix_leaf_eq_append]
  congr 1
  funext z
  change (do
    let z₂ ← liftAppendRight pSpec₁ ((P.appendSuffix (Stmt₂ := Stmt₂)).runToRound
      (Fin.last n) (out (appendPrefixTranscript z.1)) z.2)
    let r ← liftM (P.output z₂.2)
    pure (appendPrefixTranscript z.1 ++ₜ z₂.1, r)) = _
  simp only [appendSuffix, split_liftRight_ambient]
  rfl

/-- State-preserving run decomposition for an arbitrary composite prover. The suffix starts in
exactly the oracle state left by the prefix. -/
theorem simulateQ_run_appendSplit
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (out : pSpec₁.FullTranscript → Stmt₂) (stmt : Stmt₁) (wit : Wit₁) (s : σ) :
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (P.run stmt wit)).run s = (do
        let r₁ ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          ((P.appendPrefix out).run stmt wit)).run s
        let r₂ ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          ((P.appendSuffix (Stmt₂ := Stmt₂)).run (out r₁.1.1) r₁.1.2.2)).run r₁.2
        pure ((r₁.1.1 ++ₜ r₂.1.1, r₂.1.2), r₂.2)) := by
  rw [run_appendSplit P out]
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_liftAppendLeft,
    simulateQ_liftAppendRight, StateT.run_bind, StateT.run_pure]

end Prover
