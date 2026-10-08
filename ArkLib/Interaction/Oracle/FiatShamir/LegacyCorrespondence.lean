/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.LegacyFragment

/-!
# Concrete legacy transcript correspondence

The alternating legacy transcript and public native path carry the same message and challenge
values. These inverse laws make the path transport available to the legacy game bridge without
assuming a transcript match.
-/

@[expose] public section

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

private theorem hcons_head_tail {n : Nat} {α : Type} {β : Fin n → Type}
    (v : (i : Fin (n + 1)) → Fin.vcons α β i) :
    Fin.hcons (cast (Fin.vcons_zero α β) (v 0))
      (fun i => cast (Fin.vcons_succ α β i) (v i.succ)) = v := by
  funext i
  induction i using Fin.induction with
  | zero => simp
  | succ i _ => simp

private theorem fromLegacyTranscript_hcons (round : Round) (rounds : List Round)
    (message : round.Message) (challenge : round.Challenge)
    (suffix : (legacySpec rounds).FullTranscript) :
    fromLegacyTranscript (round :: rounds)
      (Fin.hcons message (Fin.hcons challenge suffix)) =
      ⟨message, challenge, fromLegacyTranscript rounds suffix⟩ := by
  simp only [fromLegacyTranscript, Fin.tail, Fin.hcons_zero, Fin.hcons_succ]
  congr 1
  congr 1
  · apply eq_of_heq
    change cast _ (cast _ challenge) ≍ challenge
    exact (cast_heq _ _).trans (cast_heq _ _)
  · congr 1
    funext i
    apply eq_of_heq
    change cast _ (cast _ (cast _ (suffix i))) ≍ suffix i
    exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _))

/-- Encoding then decoding the alternating transcript returns the concrete public path. -/
@[simp] theorem fromLegacyTranscript_toLegacyTranscript (rounds : List Round)
    (path : (publicProtocol rounds).tree.ExecutionPath) :
    fromLegacyTranscript rounds (toLegacyTranscript rounds path) = path := by
  induction rounds with
  | nil => cases path; rfl
  | cons round rounds ih =>
      rcases path with ⟨message, challenge, suffix⟩
      change round.Message at message
      change round.Challenge at challenge
      change (publicProtocol rounds).tree.ExecutionPath at suffix
      change fromLegacyTranscript (round :: rounds)
        (Fin.hcons message (Fin.hcons challenge (toLegacyTranscript rounds suffix))) =
          ⟨message, challenge, suffix⟩
      rw [fromLegacyTranscript_hcons, ih]

/-- Decoding then encoding returns every entry in the alternating legacy transcript. -/
@[simp] theorem toLegacyTranscript_fromLegacyTranscript (rounds : List Round)
    (transcript : (legacySpec rounds).FullTranscript) :
    toLegacyTranscript rounds (fromLegacyTranscript rounds transcript) = transcript := by
  induction rounds with
  | nil => funext i; exact i.elim0
  | cons round rounds ih =>
      simp only [toLegacyTranscript, fromLegacyTranscript]
      rw [ih]
      refine Eq.trans ?_ (hcons_head_tail transcript)
      congr 1
      refine Eq.trans ?_ (hcons_head_tail (fun i =>
        cast (Fin.vcons_succ round.Message
          (Fin.vcons round.Challenge (legacySpec rounds).Type) i)
          (transcript i.succ)))
      congr 1

/-- At the first challenge, the legacy prefix contains precisely the first public message. -/
def firstLegacyPrefixEquiv (round : Round) (rounds : List Round) :
    round.Message ≃
      (legacySpec (round :: rounds)).MessagesUpTo
        (⟨1, by simp [legacySteps]⟩ : Fin (legacySteps (round :: rounds) + 1)) where
  toFun := fun message i => by
    rcases i with ⟨index, direction⟩
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    have hmod : 1 % (legacySteps rounds + 2 + 1) = 1 :=
      Nat.mod_eq_of_lt (by omega)
    simpa [ProtocolSpec.MessagesUpTo, ProtocolSpec.MessageUpTo,
      SliceLT.sliceLT, ProtocolSpec.take, legacySpec, legacySteps, Fin.take, Fin.castLE,
      Fin.vcons_zero, hmod] using message
  invFun := fun msgs =>
    msgs ⟨0, by
      simp [SliceLT.sliceLT, ProtocolSpec.take, legacySpec, legacySteps,
        Fin.take, Fin.castLE, Fin.vcons_zero]⟩
  left_inv := by
    intro message
    rfl
  right_inv := by
    intro msgs
    funext i
    rcases i with ⟨index, direction⟩
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    rfl

/-- After an arbitrary suffix cutoff, the legacy prefix is the first public message
followed by the message prefix of the remaining rounds. -/
def shiftedLegacyPrefixEquiv (round : Round) (rounds : List Round)
    (cut : Fin (legacySteps rounds + 1)) :
    round.Message × (legacySpec rounds).MessagesUpTo cut ≃
      (legacySpec (round :: rounds)).MessagesUpTo
        (Fin.succ (Fin.succ cut)) where
  toFun := fun ⟨message, suffix⟩ idx => by
    rcases idx with ⟨j, hdir⟩
    revert hdir
    induction j using Fin.induction with
    | zero =>
        intro hdir
        simpa [ProtocolSpec.MessageUpTo, SliceLT.sliceLT, ProtocolSpec.take,
          legacySpec, Fin.take, Fin.vcons_zero] using message
    | succ j _ =>
        induction j using Fin.induction with
        | zero =>
            intro hdir
            have hfalse : False := by
              simp only [SliceLT.sliceLT, ProtocolSpec.take, Fin.take_apply,
                legacySpec, Fin.castLE_succ,
                Fin.castLE_zero, Fin.vcons_succ, Fin.vcons_zero] at hdir
              cases hdir
            exact hfalse.elim
        | succ k _ =>
            intro hdir
            have htail : (legacySpec rounds).dir
                (Fin.castLE (by omega) k) = .P_to_V := by
              simpa [ProtocolSpec.MessageIdxUpTo, SliceLT.sliceLT, ProtocolSpec.take,
                legacySpec, Fin.take, Fin.vcons_succ] using hdir
            simpa [ProtocolSpec.MessageUpTo, SliceLT.sliceLT, ProtocolSpec.take,
              legacySpec, Fin.take, Fin.vcons_succ] using
              suffix ⟨k, htail⟩
  invFun := fun msgs =>
    ⟨msgs ⟨⟨0, by simp only [Fin.val_succ]; omega⟩,
      by simp [SliceLT.sliceLT, ProtocolSpec.take, legacySpec,
        Fin.take, Fin.vcons_zero]⟩,
      fun idx => by
        let j : Fin (Fin.succ (Fin.succ cut)).val :=
          Fin.succ (Fin.succ idx.1)
        have hj : j = Fin.succ (Fin.succ idx.1) := rfl
        have hle : (Fin.succ (Fin.succ cut)).val ≤
            legacySteps (round :: rounds) := by
          simp only [Fin.val_succ, legacySteps]
          omega
        have htailLe : cut.val ≤ legacySteps rounds := by
          have hcut := cut.isLt
          omega
        have hindex : Fin.castLE hle j =
            Fin.succ (Fin.succ (Fin.castLE htailLe idx.1)) := by
          apply Fin.ext
          simp [j, Fin.val_succ]
        have htailDir : (legacySpec rounds).dir
            (Fin.castLE htailLe idx.1) = .P_to_V := by
          simpa [ProtocolSpec.MessageIdxUpTo, SliceLT.sliceLT,
            ProtocolSpec.take, Fin.take] using idx.2
        have hdir : ((legacySpec (round :: rounds)).take _ hle).dir j =
            .P_to_V := by
          change (legacySpec (round :: rounds)).dir (Fin.castLE hle j) = .P_to_V
          rw [hindex]
          simpa only [legacySpec, Fin.vcons_succ] using htailDir
        simpa [ProtocolSpec.MessageUpTo, SliceLT.sliceLT, ProtocolSpec.take,
          legacySpec, Fin.take, hj, Fin.vcons_succ] using msgs ⟨j, hdir⟩⟩
  left_inv := by
    intro pair
    rcases pair with ⟨message, suffix⟩
    apply Prod.ext
    · rfl
    · funext idx
      simp only [Fin.induction_succ]
      rcases idx with ⟨idx, hidx⟩
      apply eq_of_heq
      simp only [eq_mpr_eq_cast]
      repeat first | exact HEq.rfl | apply (cast_heq _ _).trans
  right_inv := by
    intro msgs
    funext idx
    rcases idx with ⟨j, hdir⟩
    induction j using Fin.induction with
    | zero => rfl
    | succ j _ =>
        induction j using Fin.induction with
        | zero =>
            have hfalse : False := by
              simp only [SliceLT.sliceLT, ProtocolSpec.take, Fin.take_apply,
                legacySpec, Fin.castLE_succ, Fin.castLE_zero,
                Fin.vcons_succ, Fin.vcons_zero] at hdir
              cases hdir
            exact hfalse.elim
        | succ k _ =>
            simp only [Fin.induction_succ]
            apply eq_of_heq
            simp only [eq_mpr_eq_cast]
            repeat first | exact HEq.rfl | apply (cast_heq _ _).trans

/-- At a later challenge, the shifted message prefix is exactly the first public message
and the previous rounds' prefix. -/
def laterLegacyPrefixEquiv (round : Round) (rounds : List Round)
    (i : (legacySpec rounds).ChallengeIdx) :
    round.Message × (legacySpec rounds).MessagesUpTo i.1.castSucc ≃
      (legacySpec (round :: rounds)).MessagesUpTo
        (Fin.succ (Fin.succ i.1)).castSucc := by
  simpa only [Fin.castSucc_succ] using
    (shiftedLegacyPrefixEquiv round rounds i.1.castSucc)

/-- The legacy prover-message carrier is exactly the native public message tuple. -/
def fullLegacyMessagesEquiv : (rounds : List Round) →
    PublicMessages rounds ≃ (legacySpec rounds).Messages
  | [] =>
      { toFun := fun _ i => i.1.elim0
        invFun := fun _ => PUnit.unit
        left_inv := by intro x; cases x; rfl
        right_inv := by intro x; funext i; exact i.1.elim0 }
  | round :: rounds =>
      (Equiv.prodCongr (Equiv.refl round.Message)
        (fullLegacyMessagesEquiv rounds)).trans
          (shiftedLegacyPrefixEquiv round rounds (Fin.last (legacySteps rounds)))

/-- Taking the first legacy message prefix exposes the head public message. -/
theorem fullLegacyMessagesEquiv_take_first (round : Round) (rounds : List Round)
    (message : round.Message) (suffix : PublicMessages rounds) :
    (fullLegacyMessagesEquiv (round :: rounds) (message, suffix)).take
      (⟨1, by simp [legacySteps]⟩ : Fin (legacySteps (round :: rounds) + 1)) =
      firstLegacyPrefixEquiv round rounds message := by
  funext idx
  rcases idx with ⟨j, hdir⟩
  have hj : j = 0 := Fin.eq_zero j
  subst j
  rfl

/-- Taking a later legacy prefix keeps the head message and the tail prefix. -/
theorem fullLegacyMessagesEquiv_take_later (round : Round) (rounds : List Round)
    (i : (legacySpec rounds).ChallengeIdx) (message : round.Message)
    (suffix : PublicMessages rounds) :
    (fullLegacyMessagesEquiv (round :: rounds) (message, suffix)).take
      (Fin.succ (Fin.succ i.1)).castSucc =
      laterLegacyPrefixEquiv round rounds i
        (message, (fullLegacyMessagesEquiv rounds suffix).take i.1.castSucc) := by
  funext idx
  rcases idx with ⟨j, hdir⟩
  induction j using Fin.induction with
  | zero => rfl
  | succ j _ =>
      induction j using Fin.induction with
      | zero =>
          have hfalse : False := by
            simp [SliceLT.sliceLT, ProtocolSpec.take, legacySpec,
              Fin.take, Fin.castLE, Fin.vcons_zero] at hdir
          exact hfalse.elim
      | succ k _ =>
          rfl

/-- The public-message projection of a concrete path, before legacy encoding. -/
def publicPathMessages : (rounds : List Round) →
    (publicProtocol rounds).tree.ExecutionPath → PublicMessages rounds
  | [], _ => PUnit.unit
  | _ :: rounds, path => ⟨path.1, publicPathMessages rounds path.2.2⟩

/-- Encoding the path preserves every prover message in the alternating transcript. -/
theorem toLegacyTranscript_messages (rounds : List Round)
    (path : (publicProtocol rounds).tree.ExecutionPath) :
    (toLegacyTranscript rounds path).toMessagesChallenges.1 =
      fullLegacyMessagesEquiv rounds (publicPathMessages rounds path) := by
  induction rounds with
  | nil => funext i; exact i.1.elim0
  | cons round rounds ih =>
      rcases path with ⟨message, challenge, suffix⟩
      change (toLegacyTranscript (round :: rounds) ⟨message, challenge, suffix⟩)
        |>.toMessagesChallenges.1 =
          (shiftedLegacyPrefixEquiv round rounds (Fin.last (legacySteps rounds)))
            ⟨message, (fullLegacyMessagesEquiv rounds) (publicPathMessages rounds suffix)⟩
      funext idx
      rcases idx with ⟨j, hdir⟩
      induction j using Fin.induction with
      | zero => rfl
      | succ j _ =>
          induction j using Fin.induction with
          | zero =>
              have hfalse : False := by
                simp only [legacySpec, Fin.vcons_succ, Fin.vcons_zero] at hdir
                cases hdir
              exact hfalse.elim
          | succ k _ =>
              have htail : (legacySpec rounds).dir k = .P_to_V := by
                simpa only [legacySpec, Fin.vcons_succ] using hdir
              have h := congrFun (ih suffix) ⟨k, htail⟩
              have hleft :
                  (Fin.hcons message (Fin.hcons challenge
                    (toLegacyTranscript rounds suffix))) (Fin.succ (Fin.succ k)) ≍
                    (toLegacyTranscript rounds suffix) k := by
                have houter := Fin.hcons_succ message
                  (Fin.hcons challenge (toLegacyTranscript rounds suffix)) (Fin.succ k)
                have hinner := Fin.hcons_succ challenge
                  (toLegacyTranscript rounds suffix) k
                exact (heq_of_eq houter).trans ((cast_heq _ _).trans
                  ((heq_of_eq hinner).trans (cast_heq _ _)))
              simp only [ProtocolSpec.FullTranscript.toMessagesChallenges,
                ProtocolSpec.Transcript.toMessagesChallenges,
                ProtocolSpec.Transcript.toMessagesUpTo, toLegacyTranscript,
                shiftedLegacyPrefixEquiv, Equiv.coe_fn_mk]
              apply eq_of_heq
              simp only [eq_mpr_eq_cast]
              simp only [Fin.induction_succ]
              exact hleft.trans ((heq_of_eq h).trans (cast_heq _ _).symm)

end Interaction.Oracle.FiatShamir
