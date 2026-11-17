/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Defs
public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Security.Proofs.Execution
public import VCVio.OracleComp.EvalDist.DiscreteTVDistBind
public import VCVio.EvalDist.EvalDistEq

/-!
# Observable execution of the DSFS argument prover for interactive proofs

The comparison interprets ambient queries without shared mutable state and public sponge
queries with a fixed realization. It compares message distributions, not oracle-query traces.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped ProbabilityTheory DuplexSpongeFS

namespace DuplexSpongeFS.ProofExecution

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn U : Type} [SpongeUnit U] [SpongeSize] [Codec pSpec U]

omit [SpongeSize] in
/-- Pointwise equal observed event probabilities remain equal after a common prefix draw. -/
private theorem prEvent_bind_congr_observed {m : Type → Type} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α) {f g : α → m Prop}
    (h : ∀ x, prEvent (f x) = prEvent (g x)) : prEvent (mx >>= f) = prEvent (mx >>= g) := by
  simpa only [prEvent_norm, id_map] using
    prEvent_bind_congr mx f g id id (fun x => by simpa only [id_map] using h x)

/-- Proof-only continuation of the general reduction runner, retaining terminal transitions. -/
def remainingProverMessages (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (i : Fin (n + 1)) : pSpec.MessagesUpTo i → CanonicalDuplexSponge U → P.PrvState i →
      OracleComp (oSpec + duplexSpongeOracle StmtIn U) pSpec.Messages :=
  Fin.reverseInduction
    (last := fun messages _sponge _lastPrvState => pure messages)
    (cast := fun j next messages sponge prvState => do
      let result ← P.referenceRoundDSFS j (pure (messages, sponge, prvState))
      next result.1 result.2.1 result.2.2) i

omit [SpongeSize] in
private theorem prEvent_ignore {α β : Type} (mx : ProbComp α) (my : ProbComp β)
    (event : β → Prop) :
    Pr{let x ← mx >>= fun _ => my}[event x] = Pr{let x ← my}[event x] := by
  let : MeasurableSpace β := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete,
    OracleComp.evalDist_bind_const]

private theorem remainingProverMessages_step (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (j : Fin n) (messages : pSpec.MessagesUpTo j.castSucc)
    (sponge : CanonicalDuplexSponge U) (state : P.PrvState j.castSucc) :
    remainingProverMessages P j.castSucc messages sponge state = (do
      let result ← P.referenceRoundDSFS j (pure (messages, sponge, state))
      remainingProverMessages P j.succ result.1 result.2.1 result.2.2) := by
  simp only [remainingProverMessages, Fin.reverseInduction_castSucc]

/-- Once all prover messages have been sent, interpreting the remaining transitions with a
stateless handler leaves the message distribution unchanged. -/
theorem remainingProverMessages_done (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (a : QueryImpl oSpec ProbComp)
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (i : Fin (n + 1)) (messages : pSpec.MessagesUpTo i)
    (sponge : CanonicalDuplexSponge U) (state : P.PrvState i)
    (h : ∀ k : pSpec.MessageIdx, k.1.val < i.val) (event : pSpec.Messages → Prop) :
    Pr{let x ← (simulateQ (ScheduledExecution.interp a f)
        (remainingProverMessages P i messages sponge state))}[event x] =
    Pr{let x ←
      (pure (MessagesUpTo.completeMessages i messages h) : ProbComp pSpec.Messages)}[event x] := by
  induction i using Fin.reverseInduction generalizing sponge with
  | last => simp only [remainingProverMessages, Fin.reverseInduction_last]
            rfl
  | cast j ih =>
    have hd : pSpec.dir j = .V_to_P := by
      cases he : pSpec.dir j with
      | V_to_P => rfl
      | P_to_V => have := h ⟨j, he⟩; simp at this
    have hnext : ∀ k : pSpec.MessageIdx, k.1.val < j.succ.val := fun k => by
      have := h k
      simp only [Fin.val_castSucc, Fin.val_succ] at *
      omega
    rw [remainingProverMessages_step]
    simp only [Prover.referenceRoundDSFS, pure_bind]
    split
    · rename_i hp
      cases hd.symm.trans hp
    · simp only [simulateQ_bind, ScheduledExecution.interp_forward,
        bind_assoc, pure_bind]
      simp only [prEvent_norm]
      refine (prEvent_bind_congr_observed (m := ProbComp) _
        (g := fun _ => event <$> pure (MessagesUpTo.completeMessages j.castSucc messages h))
        ?_).trans ?_
      · intro receive
        rw [ih _ _ _ hnext, MessagesUpTo.completeMessages_extend j hd messages h hnext]
      · simpa only [prEvent_norm] using
          prEvent_ignore _ (pure (MessagesUpTo.completeMessages j.castSucc messages h)) event

/-- If no remaining verifier message precedes a prover message, the remaining prover messages
do not observe the sponge state. Private prover transitions may still use stateless randomness. -/
theorem remainingProverMessages_sponge_irrel (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (a : QueryImpl oSpec ProbComp)
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (i : Fin (n + 1)) (messages : pSpec.MessagesUpTo i)
    (sponge₁ sponge₂ : CanonicalDuplexSponge U) (state : P.PrvState i)
    (h : ∀ k : Fin n, i.val ≤ k.val → pSpec.dir k = .V_to_P →
      ∀ l : pSpec.MessageIdx, ¬ k < l.1) (event : pSpec.Messages → Prop) :
    Pr{let x ← (simulateQ (ScheduledExecution.interp a f)
        (remainingProverMessages P i messages sponge₁ state))}[event x] =
    Pr{let x ← (simulateQ (ScheduledExecution.interp a f)
        (remainingProverMessages P i messages sponge₂ state))}[event x] := by
  induction i using Fin.reverseInduction generalizing sponge₁ sponge₂ with
  | last => simp only [remainingProverMessages, Fin.reverseInduction_last]
  | cast j ih =>
    have hnext : ∀ k : Fin n, j.succ.val ≤ k.val → pSpec.dir k = .V_to_P →
        ∀ l : pSpec.MessageIdx, ¬ k < l.1 := by
      intro k hk hd
      apply h k (by simp only [Fin.val_succ, Fin.val_castSucc] at *; omega) hd
    cases hd : pSpec.dir j with
    | V_to_P =>
      have hdone : ∀ l : pSpec.MessageIdx, l.1.val < j.castSucc.val := by
        intro l
        have hn := h j (by rfl) hd l
        have hne : j ≠ l.1 := by intro he; have := l.2; rw [← he, hd] at this; cases this
        have hnv : j.val ≠ l.1.val := fun he => hne (Fin.ext he)
        simp only [Fin.lt_def, Fin.val_castSucc] at *
        omega
      rw [remainingProverMessages_done P a f _ _ _ _ hdone,
        remainingProverMessages_done P a f _ _ _ _ hdone]
    | P_to_V =>
      rw [remainingProverMessages_step, remainingProverMessages_step]
      simp only [Prover.referenceRoundDSFS, pure_bind]
      split
      · by_cases ha : HasLaterVerifierMessage pSpec j
        · simp only [ha, ↓reduceIte, simulateQ_bind, ScheduledExecution.interp_forward,
            pure_bind, bind_assoc]
          simp only [prEvent_norm]
          apply prEvent_bind_congr_observed
          intro result
          exact ih _ _ _ _ hnext
        · simp only [ha, ↓reduceIte, simulateQ_bind, pure_bind, bind_assoc]
          simp only [prEvent_norm]
          apply prEvent_bind_congr_observed
          intro result
          exact ih _ _ _ _ hnext
      · rename_i hv
        cases hd.symm.trans hv

private theorem remainingProverMessages_proverMessage
    (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (j : Fin n) (hd : pSpec.dir j = .P_to_V) (messages : pSpec.MessagesUpTo j.castSucc)
    (sponge : CanonicalDuplexSponge U) (state : P.PrvState j.castSucc) :
    remainingProverMessages P j.castSucc messages sponge state = (do
      let (message, nextState) ← P.sendMessage ⟨j, hd⟩ state
      let sponge ← if HasLaterVerifierMessage pSpec j then do
          sponge.absorb ((Codec.instSerializeMessage ⟨j, hd⟩).serialize message).toList
        else pure sponge
      remainingProverMessages P j.succ (messages.concat hd message) sponge nextState) := by
  rw [remainingProverMessages_step]
  simp only [Prover.referenceRoundDSFS, pure_bind]
  split
  · split <;> simp_all only [bind_assoc, pure_bind]
  · rename_i hv
    cases hd.symm.trans hv

private theorem remainingMessages_verifierMessage (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (j : Fin n) (hd : pSpec.dir j = .V_to_P) (messages : pSpec.MessagesUpTo j.castSucc)
    (sponge : CanonicalDuplexSponge U) (state : P.PrvState j.castSucc) :
    remainingProverMessages P j.castSucc messages sponge state = (do
      let receive ← P.receiveChallenge ⟨j, hd⟩ state
      let (verifierMessage, sponge) ← sponge.squeeze (verifierMessageSize ⟨j, hd⟩)
      remainingProverMessages P j.succ (messages.extend hd) sponge
        (receive ((Codec.instDeserializeChallenge ⟨j, hd⟩).deserialize verifierMessage))) := by
  rw [remainingProverMessages_step]
  simp only [Prover.referenceRoundDSFS, pure_bind]
  split
  · rename_i hp
    cases hd.symm.trans hp
  · simp only [bind_assoc, pure_bind]

/-- One optimized step preserves the law of the remaining messages. Omitted absorption
can only affect a sponge state that no subsequent prover message observes. -/
theorem processRound_then_remainingProverMessages (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (a : QueryImpl oSpec ProbComp)
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (j : Fin n) (messages : pSpec.MessagesUpTo j.castSucc)
    (sponge : CanonicalDuplexSponge U) (state : P.PrvState j.castSucc)
    (event : pSpec.Messages → Prop) :
    Pr{let x ← simulateQ (ScheduledExecution.interp a f) (do
        let result ← P.processRoundDSFS j (pure (messages, sponge, state))
        remainingProverMessages P j.succ result.1 result.2.1 result.2.2)}[event x] =
    Pr{let x ← simulateQ (ScheduledExecution.interp a f)
        (remainingProverMessages P j.castSucc messages sponge state)}[event x] := by
  simp only [Prover.processRoundDSFS, pure_bind]
  split
  · rename_i hd
    rw [remainingProverMessages_proverMessage P j hd]
    by_cases ha : needsNARGAbsorption pSpec j
    · have hb : HasLaterVerifierMessage pSpec j := by
        obtain ⟨k, hk, hd, _⟩ := ha
        exact ⟨k, hk, hd⟩
      simp only [ha, hb, ↓reduceIte, bind_assoc, pure_bind]
    · have hnone : ∀ k : Fin n, j.succ.val ≤ k.val → pSpec.dir k = .V_to_P →
          ∀ l : pSpec.MessageIdx, ¬ k < l.1 := by
        intro k hk hd l hl
        apply ha
        exact ⟨k, by simp only [Fin.lt_def, Fin.val_succ] at *; omega, hd, l, hl⟩
      by_cases hb : HasLaterVerifierMessage pSpec j
      · simp only [ha, hb, ↓reduceIte, simulateQ_bind, ScheduledExecution.interp_forward,
          pure_bind, bind_assoc]
        simp only [prEvent_norm]
        apply prEvent_bind_congr_observed
        intro result
        exact remainingProverMessages_sponge_irrel P a f _ _ _ _ _ hnone event
      · simp only [ha, hb, ↓reduceIte, bind_assoc, pure_bind]
  · rename_i hd
    rw [remainingMessages_verifierMessage P j hd]
    simp only [bind_assoc, pure_bind]

/-- Forward induction composes local message-law preservation through the prover prefix. -/
theorem runToRound_then_remainingProverMessages (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (a : QueryImpl oSpec ProbComp)
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (i : Fin (n + 1)) (hi : i ≤ proverMessageEnd pSpec) (sponge : CanonicalDuplexSponge U)
    (initialPrvState : P.PrvState 0) (event : pSpec.Messages → Prop) :
    Pr{let x ← simulateQ (ScheduledExecution.interp a f) (do
        let result ← P.runToRoundDSFS i hi sponge initialPrvState
        remainingProverMessages P i result.1 result.2.1 result.2.2)}[event x] =
    Pr{let x ← simulateQ (ScheduledExecution.interp a f)
        (remainingProverMessages P 0 default sponge initialPrvState)}[event x] := by
  induction i using Fin.induction with
  | zero => simp only [Prover.runToRoundDSFS, Fin.induction_zero, pure_bind]
  | succ j ih =>
    have hprev := (Fin.castSucc_le_succ j).trans hi
    rw [← ih hprev]
    have h := prEvent_bind_congr
      (simulateQ (ScheduledExecution.interp a f)
        (P.runToRoundDSFS j.castSucc hprev sponge initialPrvState))
      (fun result => simulateQ (ScheduledExecution.interp a f) (do
        let next ← P.processRoundDSFS j (pure result)
        remainingProverMessages P j.succ next.1 next.2.1 next.2.2))
      (fun result => simulateQ (ScheduledExecution.interp a f)
        (remainingProverMessages P j.castSucc result.1 result.2.1 result.2.2))
      event event (fun result =>
        processRound_then_remainingProverMessages P a f j result.1 result.2.1 result.2.2 event)
    simpa only [Prover.runToRoundDSFS, Fin.induction_succ,
      Prover.processRoundDSFS, simulateQ_bind, bind_assoc, pure_bind] using h

/-- At the last prover message, the prefix already contains the complete NARG message tuple. -/
theorem runDSFS_eq_remainingProverMessages (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (a : QueryImpl oSpec ProbComp)
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (sponge : CanonicalDuplexSponge U) (initialPrvState : P.PrvState 0)
    (event : pSpec.Messages → Prop) :
    Pr{let x ← simulateQ (ScheduledExecution.interp a f)
        (P.runDSFS sponge initialPrvState)}[event x] =
    Pr{let x ← simulateQ (ScheduledExecution.interp a f)
        (remainingProverMessages P 0 default sponge initialPrvState)}[event x] := by
  unfold Prover.runDSFS
  rw [← runToRound_then_remainingProverMessages P a f (proverMessageEnd pSpec) le_rfl]
  simp only [simulateQ_bind, simulateQ_map, prEvent_norm]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply prEvent_bind_congr_observed
  intro result
  simpa only [prEvent_norm] using
    (remainingProverMessages_done P a f _ _ _ _ (message_lt_proverMessageEnd pSpec) event).symm

/-- Splitting the original runner at any round and then executing its continuation preserves
its complete message tuple. This is a raw computation equality, before oracle interpretation. -/
theorem run_then_remainingProverMessages (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    {δ : ℕ} (salt : Vector U δ) (stmt : StmtIn) (initialPrvState : P.PrvState 0)
    (i : Fin (n + 1)) :
    (do
      let result ← P.referenceRunDSFSSalted salt i stmt initialPrvState
      remainingProverMessages P i result.1 result.2.1 result.2.2) = (do
      let result ← P.referenceRunDSFSSalted salt (Fin.last n) stmt initialPrvState
      pure result.1) := by
  induction i using Fin.reverseInduction with
  | last => simp only [remainingProverMessages, Fin.reverseInduction_last]
  | cast j ih =>
    rw [← ih]
    simp only [Prover.referenceRunDSFSSalted, Fin.induction_succ, remainingProverMessages_step,
      Prover.referenceRoundDSFS, bind_assoc, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- Message probabilities for the actual salted prover agree with the original full runner. -/
theorem proof_prover_messages (P : Prover oSpec StmtIn WitIn Bool Unit pSpec)
    (a : QueryImpl oSpec ProbComp)
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (δ : ℕ) (sampleSalt : OracleComp oSpec (Vector U δ)) (stmt : StmtIn) (wit : WitIn)
    (event : DSFSTypedNARGString (pSpec := pSpec) (U := U) δ → Prop) :
    Pr{let x ← (simulateQ (ScheduledExecution.interp a f) (do
        let result ← (P.duplexSpongeFiatShamir δ sampleSalt).sendMessage ⟨0, rfl⟩
          ((P.duplexSpongeFiatShamir δ sampleSalt).input (stmt, wit))
        pure result.1))}[event x] =
    Pr{let x ← (simulateQ (ScheduledExecution.interp a f) (do
        let salt ← sampleSalt
        let result ← P.referenceRunDSFSSalted salt (Fin.last n) stmt (P.input (stmt, wit))
        pure (salt, result.1)))}[event x] := by
  simp only [Prover.duplexSpongeFiatShamir,
    bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure,
    ScheduledExecution.interp_start]
  simp only [prEvent_norm]
  apply prEvent_bind_congr_observed
  intro salt
  have hr := run_then_remainingProverMessages (U := U) P salt stmt (P.input (stmt, wit)) 0
  have hr' := congrArg (fun program =>
    Pr{let messages ← simulateQ (ScheduledExecution.interp a f) program}[event (salt, messages)]) hr
  simp only [simulateQ_bind, simulateQ_map, prEvent_norm] at hr'
  rw [← hr']
  simp only [Prover.referenceRunDSFSSalted, Fin.induction_zero, bind_assoc, pure_bind,
    simulateQ_bind, simulateQ_pure, ScheduledExecution.interp_start, pure_bind]
  apply prEvent_bind_congr_observed
  intro sponge
  simpa only [simulateQ_bind, simulateQ_pure, prEvent_norm] using
    runDSFS_eq_remainingProverMessages P a f sponge (P.input (stmt, wit))
    (fun messages => event (salt, messages))

end DuplexSpongeFS.ProofExecution
