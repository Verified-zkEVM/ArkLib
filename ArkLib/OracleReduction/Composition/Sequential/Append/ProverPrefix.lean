/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.ProverSuffix

/-! # Restricting an arbitrary composed prover to its first component

The terminal output is supplied separately because the full prover's output belongs to the
last component. It is never evaluated by a prefix challenge game.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type} {m k : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec k}

/-- Restrict a composed prover to its first component, retaining its private state exactly.
The chosen final output does not affect any first-component challenge distribution. -/
def prefixWithOutput
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (finish : P.PrvState ((Fin.last m).castLE (by omega)) → Stmt₂ × Wit₂) :
    Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁ where
  PrvState j := P.PrvState (j.castLE (by omega))
  input := P.input
  sendMessage i st := do
    let (msg, next) ← P.sendMessage (MessageIdx.inl i) st
    return (cast (append_Type_castAdd i.1) msg, next)
  receiveChallenge i st := do
    let next ← P.receiveChallenge (ChallengeIdx.inl i) st
    return fun challenge => next (cast (challenge_append_inl i).symm challenge)
  output st := pure (finish st)

/-- Project a transcript before the boundary to the first protocol's transcript. -/
def prefixTranscript {j : Fin (m + 1)}
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (j.castLE (by omega))) : pSpec₁.Transcript j :=
  fun q => cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    ⟨q.val, by have := q.isLt; have := j.isLt; omega⟩) (tr q)

/-- First-component transcript projection commutes with appending a message. -/
theorem prefixTranscript_concat (j : Fin m)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (j.castAdd k).castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type (j.castAdd k)) :
    prefixTranscript (j := j.succ) (tr.concat msg) =
      (prefixTranscript (j := j.castSucc) tr).concat (cast (append_Type_castAdd j) msg) := by
  funext q
  by_cases hq : q.val < j.val
  · have hl := Transcript.concat_apply_lt tr msg q.val hq q.isLt
    have hr := Transcript.concat_apply_lt (prefixTranscript (j := j.castSucc) tr)
      (cast (append_Type_castAdd j) msg) q.val hq q.isLt
    exact eq_of_heq ((cast_heq _ _).trans
      (hl.trans ((cast_heq _ _).symm.trans hr.symm)))
  · have heq : q = Fin.last j.val := Fin.ext (by
      change q.val = j.val
      have : q.val < j.val + 1 := q.isLt
      omega)
    subst q
    have hl := Transcript.concat_apply_last tr msg j.val rfl
      (by change j.val < j.val + 1; omega)
    have hr := Transcript.concat_apply_last (prefixTranscript (j := j.castSucc) tr)
      (cast (append_Type_castAdd j) msg) j.val rfl (by omega)
    exact eq_of_heq ((cast_heq _ _).trans
      (hl.trans ((cast_heq _ _).symm.trans hr.symm)))

/-- One round of the restricted prover is exactly the corresponding full-protocol round,
after projecting the transcript and injecting first-component challenge queries. -/
theorem prefixWithOutput_processRound
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (finish : P.PrvState ((Fin.last m).castLE (by omega)) → Stmt₂ × Wit₂)
    (j : Fin m)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (j.castAdd k).castSucc)
    (st : P.PrvState (j.castAdd k).castSucc) :
    (fun x => (prefixTranscript (j := j.succ) x.1, x.2)) <$>
      P.processRound (j.castAdd k) (pure (tr, st)) =
      liftAppendLeft pSpec₂ ((P.prefixWithOutput finish).processRound j
        (pure (prefixTranscript (j := j.castSucc) tr, st))) := by
  cases hd : pSpec₁.dir j with
  | V_to_P =>
    have hg : (pSpec₁ ++ₚ pSpec₂).dir (j.castAdd k) = .V_to_P := by
      simpa only [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left] using hd
    rw [processRound_of_dir_eq_V_to_P _ hg, processRound_of_dir_eq_V_to_P _ hd]
    simp only [pure_bind, prefixWithOutput, ChallengeIdx.inl, liftM_bind, liftM_pure,
      liftAppendLeft_liftM, liftAppendLeft_getChallenge, map_bind, map_pure,
      bind_assoc, bind_map_left, prefixTranscript_concat]
    congr 1
    funext challenge
    congr 1
    funext next
    congr 1
    apply Prod.ext
    · rfl
    · apply congrArg next
      exact (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))).symm
  | P_to_V =>
    have hg : (pSpec₁ ++ₚ pSpec₂).dir (j.castAdd k) = .P_to_V := by
      simpa only [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left] using hd
    rw [processRound_of_dir_eq_P_to_V _ hg, processRound_of_dir_eq_P_to_V _ hd]
    simp only [pure_bind, prefixWithOutput, MessageIdx.inl, liftM_bind, liftM_pure,
      liftAppendLeft_liftM, map_bind, map_pure, bind_assoc, prefixTranscript_concat]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the execution to any first-component round preserves its entire prefix
distribution and private state, before choosing an ambient oracle implementation. -/
theorem runToRound_prefixWithOutput
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (finish : P.PrvState ((Fin.last m).castLE (by omega)) → Stmt₂ × Wit₂)
    (stmt : Stmt₁) (wit : Wit₁) (j : Fin (m + 1)) :
    (fun x => (prefixTranscript (j := j) x.1, x.2)) <$>
      P.runToRound (j.castLE (by omega)) stmt wit =
      liftAppendLeft pSpec₂ ((P.prefixWithOutput finish).runToRound j stmt wit) := by
  induction j using Fin.induction with
  | zero =>
    change (fun x => (prefixTranscript (j := 0) x.1, x.2)) <$>
      P.runToRound 0 stmt wit = _
    simp only [runToRound_zero_of_prover_first, prefixWithOutput, map_pure,
      liftAppendLeft, liftM_pure]
    exact congrArg (fun T => pure (T, P.input (stmt, wit))) (Subsingleton.elim _ _)
  | succ j ih =>
    change (fun x => (prefixTranscript (j := j.succ) x.1, x.2)) <$>
      P.runToRound (j.castAdd k).succ stmt wit = _
    rw [runToRound_succ, runToRound_succ]
    conv_lhs => rw [processRound_eq_bind_current]
    conv_rhs => rw [processRound_eq_bind_current]
    simp only [map_bind, liftAppendLeft_bind]
    simp_rw [prefixWithOutput_processRound P finish]
    have h := congrArg (fun oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        (pSpec₁.Transcript j.castSucc × P.PrvState (j.castAdd k).castSucc) =>
      oa >>= fun a => liftAppendLeft pSpec₂
        ((P.prefixWithOutput finish).processRound j (pure a))) ih
    simpa only [bind_map_left, prefixWithOutput, Fin.castLE, Fin.castAdd,
      Fin.castSucc, Fin.succ] using h

variable [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- Simulation of the restricted prover preserves the first-prefix distribution.
This holds for arbitrary lawful target monads, including stateful shared-oracle simulation. -/
theorem simulateQ_runToRound_prefixWithOutput
    {M : Type → Type} [Monad M] [LawfulMonad M]
    [MonadLiftT ProbComp M] [LawfulMonadLiftT ProbComp M]
    (impl : QueryImpl oSpec M)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (finish : P.PrvState ((Fin.last m).castLE (by omega)) → Stmt₂ × Wit₂)
    (stmt : Stmt₁) (wit : Wit₁) (j : Fin (m + 1)) :
    (fun x => (prefixTranscript (j := j) x.1, x.2)) <$>
      simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ M)
        (P.runToRound (j.castLE (by omega)) stmt wit) =
      simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ M)
        ((P.prefixWithOutput finish).runToRound j stmt wit) := by
  rw [← simulateQ_map, runToRound_prefixWithOutput]
  exact simulateQ_liftAppendLeft impl ((P.prefixWithOutput finish).runToRound j stmt wit)

/-- Transport a first-prefix event together with the next fresh challenge. -/
theorem prEvent_runToRound_prefix_challenge
    (impl : QueryImpl oSpec ProbComp)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (finish : P.PrvState ((Fin.last m).castLE (by omega)) → Stmt₂ × Wit₂)
    (stmt : Stmt₁) (wit : Wit₁) (i : pSpec₁.ChallengeIdx)
    (event : pSpec₁.Transcript i.1.castSucc → pSpec₁.Challenge i → Prop) :
    Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
         (P.runToRound (i.1.castAdd k).castSucc stmt wit)
       let c ← $ᵗ (pSpec₁.Challenge i)}[event (prefixTranscript x.1) c] =
    Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
         ((P.prefixWithOutput finish).runToRound i.1.castSucc stmt wit)
       let c ← $ᵗ (pSpec₁.Challenge i)}[event x.1 c] := by
  have h := congrArg (fun draw : ProbComp (pSpec₁.Transcript i.1.castSucc ×
      P.PrvState (i.1.castSucc.castLE (by omega))) =>
      Pr{let x ← draw; let c ← $ᵗ (pSpec₁.Challenge i)}[event x.1 c])
    (simulateQ_runToRound_prefixWithOutput impl P finish stmt wit i.1.castSucc)
  simp only [bind_map_left] at h
  convert h using 1 <;> rfl

end Prover
