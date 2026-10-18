/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.Execution
public import ArkLib.OracleReduction.Composition.Sequential.Append.Simulation
public import ArkLib.OracleReduction.Security.ExecutionPrefix

/-! # Continuing an arbitrary prover after a composition boundary

Unlike an appended honest prover, an adversarial prover need not expose two components.
Fixing its state at the boundary nevertheless gives a prover for the suffix protocol.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type} {m k : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec k}

/-- Continue an arbitrary composed-protocol prover from a fixed boundary state.
The suffix input is deliberately ignored: the preceding execution already fixed the state. -/
def suffixFromState
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m)) :
    Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂ where
  PrvState j := P.PrvState (j.natAdd m)
  input _ := state
  sendMessage i st := do
    let (msg, next) ← P.sendMessage (MessageIdx.inr i) st
    return (cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i.1) msg, next)
  receiveChallenge i st := do
    let next ← P.receiveChallenge (ChallengeIdx.inr i) st
    return fun challenge => next (cast (challenge_append_inr i).symm challenge)
  output st := P.output st

/-- Project a transcript past the boundary to a suffix transcript with its exact round index. -/
def suffixTranscript {j : Fin (k + 1)}
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (j.natAdd m)) : pSpec₂.Transcript j :=
  fun q => cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    ⟨q.val, by have := q.isLt; have := j.isLt; omega⟩)
    (tr ⟨m + q.val, by have := q.isLt; change m + q.val < m + j.val; omega⟩)

/-- Appending a suffix message commutes with transcript projection. -/
theorem suffixTranscript_concat (j : Fin k)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (j.natAdd m).castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type (j.natAdd m)) :
    suffixTranscript (j := j.succ) (tr.concat msg) =
      (suffixTranscript (j := j.castSucc) tr).concat (cast (append_Type_natAdd j) msg) := by
  funext q
  by_cases hq : q.val < j.val
  · have hleft := Transcript.concat_apply_lt tr msg (m + q.val)
      (by change m + q.val < m + j.val; omega)
      (by change m + q.val < m + j.val + 1; omega)
    have hright := Transcript.concat_apply_lt (suffixTranscript (j := j.castSucc) tr)
      (cast (append_Type_natAdd j) msg) q.val hq q.isLt
    have hnew : HEq (suffixTranscript (j := j.succ) (tr.concat msg) q)
        ((tr.concat msg) ⟨m + q.val, by change m + q.val < m + j.val + 1; omega⟩) :=
      cast_heq _ _
    have hold : HEq (suffixTranscript (j := j.castSucc) tr ⟨q.val, hq⟩)
        (tr ⟨m + q.val, by change m + q.val < m + j.val; omega⟩) := cast_heq _ _
    exact eq_of_heq (hnew.trans (hleft.trans (hold.symm.trans hright.symm)))
  · have heq : q = Fin.last j.val := Fin.ext (by
      change q.val = j.val
      have : q.val < j.val + 1 := q.isLt
      omega)
    subst q
    have hnew : HEq (suffixTranscript (j := j.succ) (tr.concat msg) (Fin.last j.val))
        ((tr.concat msg) ⟨m + j.val, by change m + j.val < m + j.val + 1; omega⟩) :=
      cast_heq _ _
    have hleft := Transcript.concat_apply_last tr msg (m + j.val)
      (by rfl) (by change m + j.val < m + j.val + 1; omega)
    have hright := Transcript.concat_apply_last (suffixTranscript (j := j.castSucc) tr)
      (cast (append_Type_natAdd j) msg) j.val rfl (by omega)
    exact eq_of_heq (hnew.trans (hleft.trans ((cast_heq _ _).symm.trans hright.symm)))

/-- One suffix round has the same execution as the corresponding global round, after
projecting its transcript and injecting suffix challenge queries into the right component. -/
theorem suffixFromState_processRound
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (initial : P.PrvState ((0 : Fin (k + 1)).natAdd m)) (j : Fin k)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (j.natAdd m).castSucc)
    (st : P.PrvState (j.natAdd m).castSucc) :
    (fun x => (suffixTranscript (j := j.succ) x.1, x.2)) <$>
        P.processRound (j.natAdd m) (pure (tr, st)) =
      liftAppendRight pSpec₁
        ((P.suffixFromState (Stmt₂ := Stmt₂) (Wit₂ := Wit₂) initial).processRound j
          (pure (suffixTranscript (j := j.castSucc) tr, st))) := by
  cases hd : pSpec₂.dir j with
  | V_to_P =>
    have hg : (pSpec₁ ++ₚ pSpec₂).dir (j.natAdd m) = .V_to_P := by
      simpa only [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using hd
    rw [processRound_of_dir_eq_V_to_P _ hg, processRound_of_dir_eq_V_to_P _ hd]
    simp only [pure_bind, suffixFromState, ChallengeIdx.inr, liftM_bind, liftM_pure,
      liftAppendRight_liftM, liftAppendRight_getChallenge, map_bind, map_pure,
      bind_assoc, bind_map_left, suffixTranscript_concat]
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
    have hg : (pSpec₁ ++ₚ pSpec₂).dir (j.natAdd m) = .P_to_V := by
      simpa only [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using hd
    rw [processRound_of_dir_eq_P_to_V _ hg, processRound_of_dir_eq_P_to_V _ hd]
    simp only [pure_bind, suffixFromState, MessageIdx.inr, liftM_bind, liftM_pure,
      liftAppendRight_liftM, map_bind, map_pure, bind_assoc, suffixTranscript_concat]

/-- Execute the suffix rounds while retaining the original full-prefix transcript and state. -/
def runFromBoundary
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m)) (j : Fin (k + 1)) :
    OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (j.natAdd m) × P.PrvState (j.natAdd m)) :=
  Fin.induction (pure (tr, state)) (fun q current => P.processRound (q.natAdd m) current) j

-- Unfold the suffix state family and the appended challenge-interface alias during transport.
set_option backward.isDefEq.respectTransparency false in
/-- Projecting a continuation from the boundary gives precisely the suffix prover's run.
This is an equality of oracle computations, before any probabilistic interpretation. -/
theorem runFromBoundary_suffix
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m))
    (stmt : Stmt₂) (wit : Wit₂) (j : Fin (k + 1)) :
    (fun x => (suffixTranscript (j := j) x.1, x.2)) <$>
        P.runFromBoundary tr state j =
      liftAppendRight pSpec₁ ((P.suffixFromState state).runToRound j stmt wit) := by
  induction j using Fin.induction with
  | zero =>
    simp only [runFromBoundary, Fin.induction_zero, map_pure,
      runToRound_zero_of_prover_first, suffixFromState, liftM_pure]
    exact congrArg (fun T => pure (T, state)) (Subsingleton.elim _ _)
  | succ j ih =>
    change (fun x => (suffixTranscript (j := j.succ) x.1, x.2)) <$>
      P.processRound (j.natAdd m) (P.runFromBoundary tr state j.castSucc) = _
    rw [runToRound_succ]
    conv_lhs => rw [processRound_eq_bind_current]
    conv_rhs => rw [processRound_eq_bind_current]
    simp only [map_bind, liftAppendRight_bind]
    simp_rw [suffixFromState_processRound (Stmt₂ := Stmt₂) (Wit₂ := Wit₂) P state]
    have h := congrArg (fun oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        (pSpec₂.Transcript j.castSucc × P.PrvState (j.natAdd m).castSucc) =>
      oa >>= fun a => liftAppendRight pSpec₁
        ((P.suffixFromState (Stmt₂ := Stmt₂) (Wit₂ := Wit₂) state).processRound j (pure a))) ih
    convert h using 1
    · rfl
    · simp only [bind_map_left]
      rfl
    · rfl

/-- Split any prover execution at the boundary, retaining its actual state and transcript. -/
theorem runToRound_split_boundary
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmt : Stmt₁) (wit : Wit₁) (j : Fin (k + 1)) :
    P.runToRound (j.natAdd m) stmt wit = (do
      let x ← P.runToRound ((0 : Fin (k + 1)).natAdd m) stmt wit
      P.runFromBoundary x.1 x.2 j) := by
  induction j using Fin.induction with
  | zero => simp only [runFromBoundary, Fin.induction_zero, Prod.mk.eta, bind_pure]
  | succ j ih =>
    change P.runToRound (j.natAdd m).succ stmt wit = _
    rw [runToRound_succ]
    calc
      _ = P.processRound (j.natAdd m) (do
          let x ← P.runToRound ((0 : Fin (k + 1)).natAdd m) stmt wit
          P.runFromBoundary x.1 x.2 j.castSucc) := congrArg (P.processRound (j.natAdd m)) ih
      _ = _ := by
        simp only [runFromBoundary, Fin.induction_succ, processRound, bind_assoc]

/-- Recover the complete front transcript from any transcript at or beyond the boundary. -/
def boundaryTranscript {j : Fin (k + 1)}
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (j.natAdd m)) : pSpec₁.FullTranscript :=
  fun q => cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) q)
    (tr ⟨q.val, by have := q.isLt; change q.val < m + j.val; omega⟩)

/-- A suffix round cannot change the completed front transcript. -/
theorem processRound_boundaryTranscript
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (j : Fin k)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (j.natAdd m).castSucc)
    (state : P.PrvState (j.natAdd m).castSucc)
    (x : (pSpec₁ ++ₚ pSpec₂).Transcript (j.natAdd m).succ ×
      P.PrvState (j.natAdd m).succ)
    (hx : x ∈ support (P.processRound (j.natAdd m) (pure (tr, state)))) :
    boundaryTranscript (j := j.succ) x.1 = boundaryTranscript (j := j.castSucc) tr := by
  have h := P.processRound_preserves_prefix (j.natAdd m) tr state x hx
  funext q
  have hq : q.val < m + j.val := by have := q.isLt; omega
  have hv := congrFun h ⟨q.val, hq⟩
  exact eq_of_heq ((cast_heq _ _).trans ((heq_of_eq hv).trans (cast_heq _ _).symm))

/-- Every supported continuation preserves the front transcript that initialized it. -/
theorem runFromBoundary_preserves_boundary
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m)) (j : Fin (k + 1))
    (x : (pSpec₁ ++ₚ pSpec₂).Transcript (j.natAdd m) × P.PrvState (j.natAdd m))
    (hx : x ∈ support (P.runFromBoundary tr state j)) :
    boundaryTranscript x.1 = boundaryTranscript tr := by
  induction j using Fin.induction with
  | zero =>
    simp only [runFromBoundary, Fin.induction_zero, support_pure, Set.mem_singleton_iff] at hx
    subst x
    rfl
  | succ j ih =>
    change x ∈ support (P.processRound (j.natAdd m)
      (P.runFromBoundary tr state j.castSucc)) at hx
    rw [processRound_eq_bind_current] at hx
    simp only [support_bind, Set.mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact (P.processRound_boundaryTranscript j y.1 y.2 x hxy).trans (ih y hy)

variable [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- Projecting a simulated continuation gives precisely the simulated suffix prover.
The same ambient implementation is used on both sides. -/
theorem simulateQ_runFromBoundary_suffix
    {M : Type → Type} [Monad M] [LawfulMonad M]
    [MonadLiftT ProbComp M] [LawfulMonadLiftT ProbComp M]
    (impl : QueryImpl oSpec M)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m))
    (j : Fin (k + 1)) (stmt : Stmt₂) (wit : Wit₂) :
    (fun x => (suffixTranscript (j := j) x.1, x.2)) <$>
      simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ M)
        (P.runFromBoundary tr state j) =
      simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ M)
        ((P.suffixFromState state).runToRound j stmt wit) := by
  rw [← simulateQ_map, runFromBoundary_suffix P tr state stmt wit j]
  exact simulateQ_liftAppendRight impl ((P.suffixFromState state).runToRound j stmt wit)

/-- Suffix events have the same probability in the original continuation and suffix prover. -/
theorem prEvent_runFromBoundary_suffix
    (impl : QueryImpl oSpec ProbComp)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m))
    (j : Fin (k + 1)) (stmt : Stmt₂) (wit : Wit₂)
    (event : pSpec₂.Transcript j → Prop) :
    Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
        (P.runFromBoundary tr state j)}[event (suffixTranscript x.1)] =
    Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
        ((P.suffixFromState state).runToRound j stmt wit)}[event x.1] := by
  have h := congrArg (fun draw : ProbComp (pSpec₂.Transcript j ×
      P.PrvState (j.natAdd m)) => Pr{let x ← draw}[event x.1])
    (simulateQ_runFromBoundary_suffix impl P tr state j stmt wit)
  simp only [prEvent_map] at h
  convert h using 1
  rfl

/-- Transport a suffix-prefix event together with its next independent challenge. -/
theorem prEvent_runFromBoundary_suffix_challenge
    (impl : QueryImpl oSpec ProbComp)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m))
    (i : pSpec₂.ChallengeIdx) (stmt : Stmt₂) (wit : Wit₂)
    (event : pSpec₂.Transcript i.1.castSucc → pSpec₂.Challenge i → Prop) :
    Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
         (P.runFromBoundary tr state i.1.castSucc)
       let c ← $ᵗ (pSpec₂.Challenge i)}[event (suffixTranscript x.1) c] =
    Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
         ((P.suffixFromState state).runToRound i.1.castSucc stmt wit)
       let c ← $ᵗ (pSpec₂.Challenge i)}[event x.1 c] := by
  have h := congrArg (fun draw : ProbComp (pSpec₂.Transcript i.1.castSucc ×
      P.PrvState (i.1.castSucc.natAdd m)) =>
      Pr{let x ← draw; let c ← $ᵗ (pSpec₂.Challenge i)}[event x.1 c])
    (simulateQ_runFromBoundary_suffix impl P tr state i.1.castSucc stmt wit)
  simp only [bind_map_left] at h
  convert h using 1
  rfl

/-- Uniform conditional bounds after the boundary bound the actual composed prefix game. -/
theorem prEvent_runToRound_le_of_boundary
    (impl : QueryImpl oSpec ProbComp)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmt : Stmt₁) (wit : Wit₁) (j : Fin (k + 1))
    {α : Type} (draw : ProbComp α)
    (event : (pSpec₁ ++ₚ pSpec₂).Transcript (j.natAdd m) → α → Prop)
    {ε : ENNReal}
    (h : ∀ tr state,
      Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
           (P.runFromBoundary tr state j)
         let c ← draw}[event x.1 c] ≤ ε) :
    Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
         (P.runToRound (j.natAdd m) stmt wit)
       let c ← draw}[event x.1 c] ≤ ε := by
  rw [runToRound_split_boundary]
  simp only [simulateQ_bind, bind_assoc]
  have hb := _root_.prEvent_bind_le_of_forall_le
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
      (P.runToRound ((0 : Fin (k + 1)).natAdd m) stmt wit))
    (fun b => do
      let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
        (P.runFromBoundary b.1 b.2 j)
      let c ← draw
      return event x.1 c) (fun p => p)
    (fun b => by simpa only [bind_assoc, pure_bind] using h b.1 b.2)
  simpa only [bind_assoc, pure_bind] using hb

end Prover
