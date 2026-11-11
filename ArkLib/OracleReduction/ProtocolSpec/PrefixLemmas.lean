/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Orrù, Chung Thai Nguyen, Yuxi Zheng
-/
module

public import ArkLib.OracleReduction.ProtocolSpec.Basic

/-!
# Protocol prefix lemmas

Evaluation and truncation of message and challenge tuples, and their compatibility with
appending a round to a transcript.
-/

@[expose] public section

namespace ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n}

namespace Messages

/-- The explicit full-prefix view preserves every message. -/
@[simp]
lemma asUpTo_apply (messages : Messages pSpec) (i : Fin n) (hi : pSpec.dir i = .P_to_V) :
    asUpTo messages ⟨i, hi⟩ = get messages i hi := by
  rfl

end Messages

namespace MessagesUpTo

/-- Evaluating a concatenated message tuple strictly below the appended round. -/
lemma concat_apply_castSucc {k : Fin n}
    (ms : pSpec.MessagesUpTo k.castSucc) (h : pSpec.dir k = .P_to_V)
    (m : pSpec.Message ⟨k, h⟩) (l : Fin k.1) (hl) :
    ProtocolSpec.MessagesUpTo.concat ms h m ⟨l.castSucc, hl⟩ = ms ⟨l, hl⟩ := by
  exact congrFun (Fin.dconcat_castSucc
      (motive := fun x : Fin (k.1 + 1) => pSpec.dir (Fin.castLE k.isLt x) = .P_to_V →
        pSpec.«Type» (Fin.castLE k.isLt x))
    (fun i hi => ms ⟨i, hi⟩) (fun _ => m) l) hl

/-- Evaluating a concatenated message tuple at the appended round. -/
lemma concat_apply_last {k : Fin n}
    (ms : pSpec.MessagesUpTo k.castSucc) (h : pSpec.dir k = .P_to_V)
    (m : pSpec.Message ⟨k, h⟩) (hl) :
    ProtocolSpec.MessagesUpTo.concat ms h m ⟨Fin.last k.1, hl⟩ = m := by
  exact congrFun (Fin.dconcat_last
      (motive := fun x : Fin (k.1 + 1) => pSpec.dir (Fin.castLE k.isLt x) = .P_to_V →
        pSpec.«Type» (Fin.castLE k.isLt x))
    (fun i hi => ms ⟨i, hi⟩) (fun _ => m)) hl

/-- Evaluating an extended message tuple strictly below the appended (verifier message) round. -/
lemma extend_apply_castSucc {k : Fin n}
    (ms : pSpec.MessagesUpTo k.castSucc) (h : pSpec.dir k = .V_to_P)
    (l : Fin k.1) (hl) :
    ProtocolSpec.MessagesUpTo.extend ms h ⟨l.castSucc, hl⟩ = ms ⟨l, hl⟩ := by
  exact congrFun (Fin.dconcat_castSucc
      (motive := fun x : Fin (k.1 + 1) => pSpec.dir (Fin.castLE k.isLt x) = .P_to_V →
        pSpec.«Type» (Fin.castLE k.isLt x))
    (fun i hi => ms ⟨i, hi⟩) _ l) hl

/-- Extending a complete message prefix by a verifier step preserves its full message tuple. -/
theorem completeMessages_extend (j : Fin n) (hd : pSpec.dir j = .V_to_P)
    (messages : pSpec.MessagesUpTo j.castSucc)
    (h : ∀ k : pSpec.MessageIdx, k.1.val < j.val)
    (h' : ∀ k : pSpec.MessageIdx, k.1.val < j.val + 1) :
    MessagesUpTo.completeMessages j.succ (messages.extend hd) h' =
      MessagesUpTo.completeMessages j.castSucc messages h := by
  funext k
  let motive : Fin (j.val + 1) → Type := fun k =>
    pSpec.dir (k.castLE (by omega)) = .P_to_V → pSpec.«Type» (k.castLE (by omega))
  let v : (k : Fin j.val) → motive k.castSucc := fun k hk => messages ⟨k, hk⟩
  change (Fin.dconcat (motive := motive) v _
    (⟨k.1.val, h k⟩ : Fin j.val).castSucc) k.2 = _
  rw [Fin.dconcat_castSucc]
  rfl

end MessagesUpTo

/-- A full tuple with a given concatenated prefix has the preceding prefix. -/
theorem Messages.take_castSucc_of_take_succ_eq_concat {i : Fin n}
    (m : pSpec.MessagesUpTo i.castSucc) (h : pSpec.dir i = .P_to_V)
    (a : pSpec.Message ⟨i, h⟩) (messages : pSpec.Messages)
    (hm : messages.take i.succ = m.concat h a) :
    messages.take i.castSucc = m := by
  funext j
  have hj := congrFun hm ⟨j.1.castSucc, j.2⟩
  let motive : Fin (i.1 + 1) → Type := fun k =>
    pSpec.dir (k.castLE (by omega)) = .P_to_V → pSpec.«Type» (k.castLE (by omega))
  let v : (k : Fin i.1) → motive k.castSucc := fun k hk => m ⟨k, hk⟩
  let last : motive (Fin.last i.1) := fun _ => a
  exact hj.trans (congrFun (Fin.dconcat_castSucc v last j.1) j.2)

/-- A verifier step adds no prover message to the preceding prefix. -/
theorem Messages.take_castSucc_of_take_succ_eq_extend {i : Fin n}
    (m : pSpec.MessagesUpTo i.castSucc) (h : pSpec.dir i = .V_to_P)
    (messages : pSpec.Messages) (hm : messages.take i.succ = m.extend h) :
    messages.take i.castSucc = m := by
  funext j
  have hj := congrFun hm ⟨j.1.castSucc, j.2⟩
  let motive : Fin (i.1 + 1) → Type := fun k =>
    pSpec.dir (k.castLE (by omega)) = .P_to_V → pSpec.«Type» (k.castLE (by omega))
  let v : (k : Fin i.1) → motive k.castSucc := fun k hk => m ⟨k, hk⟩
  exact hj.trans (congrFun (Fin.dconcat_castSucc v _ j.1) j.2)

/-- The final message of a concatenated prefix agrees with the full message tuple. -/
theorem Messages.get_of_take_succ_eq_concat {i : Fin n}
    (m : pSpec.MessagesUpTo i.castSucc) (h : pSpec.dir i = .P_to_V)
    (a : pSpec.Message ⟨i, h⟩) (messages : pSpec.Messages)
    (hm : messages.take i.succ = m.concat h a) : messages ⟨i, h⟩ = a := by
  have hl : (pSpec.take i.succ i.succ.is_le).dir (Fin.last i.1) = .P_to_V := by
    change pSpec.dir ((Fin.last i.1).castLE (by omega)) = .P_to_V
    have heq : (Fin.last i.1).castLE (by omega) = i := by ext; rfl
    rw [heq]
    exact h
  have hj := congrFun hm ⟨Fin.last i.1, hl⟩
  let motive : Fin (i.1 + 1) → Type := fun k =>
    pSpec.dir (k.castLE (by omega)) = .P_to_V → pSpec.«Type» (k.castLE (by omega))
  let v : (k : Fin i.1) → motive k.castSucc := fun k hk => m ⟨k, hk⟩
  let last : motive (Fin.last i.1) := fun _ => a
  exact hj.trans (congrFun (Fin.dconcat_last v last) hl)

namespace ChallengesUpTo

/-- Evaluating a concatenated challenge tuple strictly below the appended round. -/
lemma concat_apply_castSucc {k : Fin n}
    (cs : ChallengesUpTo k.castSucc pSpec) (h : pSpec.dir k = .V_to_P)
    (c : pSpec.Challenge ⟨k, h⟩) (l : Fin k.1) (hl) :
    concat cs h c ⟨l.castSucc, hl⟩ = cs ⟨l, hl⟩ := by
  let motive : Fin (k.1 + 1) → Type _ := fun i =>
    pSpec.dir (i.castLE (by omega)) = .V_to_P → pSpec.«Type» (i.castLE (by omega))
  let v : (i : Fin k.1) → motive i.castSucc := fun i hi => cs ⟨i, hi⟩
  let a : motive (Fin.last k.1) := fun _ => c
  change
    (Fin.dconcat (motive := motive) v a l.castSucc) hl = v l hl
  exact congrFun (Fin.dconcat_castSucc v a l) hl

/-- Evaluating a concatenated challenge tuple at the appended round. -/
lemma concat_apply_last {k : Fin n}
    (cs : ChallengesUpTo k.castSucc pSpec) (h : pSpec.dir k = .V_to_P)
    (c : pSpec.Challenge ⟨k, h⟩) (hl) :
    concat cs h c ⟨Fin.last k.1, hl⟩ = c := by
  let motive : Fin (k.1 + 1) → Type _ := fun i =>
    pSpec.dir (i.castLE (by omega)) = .V_to_P → pSpec.«Type» (i.castLE (by omega))
  let v : (i : Fin k.1) → motive i.castSucc := fun i hi => cs ⟨i, hi⟩
  let a : motive (Fin.last k.1) := fun _ => c
  change
    (Fin.dconcat (motive := motive) v a (Fin.last k.1)) hl = a hl
  exact congrFun (Fin.dconcat_last v a) hl

/-- Reading the last challenge after concatenation returns the appended challenge. -/
@[simp]
lemma last_concat {k : Fin n}
    (cs : ChallengesUpTo k.castSucc pSpec) (h : pSpec.dir k = .V_to_P)
    (c : pSpec.Challenge ⟨k, h⟩) : last (concat cs h c) h = c := by
  unfold last
  exact concat_apply_last cs h c (by
    change pSpec.dir ((Fin.last k.1).castLE (by omega)) = .V_to_P
    have hlast : (Fin.last k.1).castLE (by omega) = k := by ext; rfl
    rw [hlast]
    exact h)

/-- Evaluating an extended challenge tuple strictly below the appended (message) round. -/
lemma extend_apply_castSucc {k : Fin n}
    (cs : ChallengesUpTo k.castSucc pSpec) (h : pSpec.dir k = .P_to_V)
    (l : Fin k.1) (hl) :
    extend cs h ⟨l.castSucc, hl⟩ = cs ⟨l, hl⟩ := by
  let motive : Fin (k.1 + 1) → Type _ := fun i =>
    pSpec.dir (i.castLE (by omega)) = .V_to_P → pSpec.«Type» (i.castLE (by omega))
  let v : (i : Fin k.1) → motive i.castSucc := fun i hi => cs ⟨i, hi⟩
  let a : motive (Fin.last k.1) := fun h' => by
    have hlast : (Fin.last k.1).castLE (by omega) = k := by ext; rfl
    rw [hlast] at h'
    simp [h] at h'
  change
    (Fin.dconcat (motive := motive) v a l.castSucc) hl = v l hl
  exact congrFun (Fin.dconcat_castSucc v a l) hl

/-- Taking the strict prefix of a concatenated challenge tuple recovers the original tuple. -/
lemma take_concat {k : Fin n}
    (cs : ChallengesUpTo k.castSucc pSpec) (h : pSpec.dir k = .V_to_P)
    (c : pSpec.Challenge ⟨k, h⟩) :
    take (k := k.succ) (Fin.last k.1).castSucc (concat cs h c) = cs := by
  funext l
  exact concat_apply_castSucc cs h c ⟨l.1.1, l.1.2⟩ _

/-- Taking the strict prefix of an extended challenge tuple recovers the original tuple. -/
lemma take_extend {k : Fin n}
    (cs : ChallengesUpTo k.castSucc pSpec) (h : pSpec.dir k = .P_to_V) :
    take (k := k.succ) (Fin.last k.1).castSucc (extend cs h) = cs := by
  funext l
  exact extend_apply_castSucc cs h ⟨l.1.1, l.1.2⟩ _

end ChallengesUpTo

namespace Transcript

/-- Building the transcript from a message prefix and challenges commutes with appending a
challenge round: `Transcript.concat` with a challenge corresponds to `ChallengesUpTo.concat`
(with the message prefix unchanged). -/
lemma ofMessagesChallenges_concat_challenge (m : pSpec.Messages) {i : Fin n}
    (cs : ChallengesUpTo i.castSucc pSpec) (h : pSpec.dir i = .V_to_P)
    (c : pSpec.Challenge ⟨i, h⟩) :
    (ofMessagesChallenges (m.take i.succ)
        (ChallengesUpTo.concat cs h c) : Transcript i.succ pSpec)
      = appendRound (pSpec := pSpec) (m := i) c
          (ofMessagesChallenges (m.take i.castSucc) cs) := by
  unfold appendRound
  funext pos
  by_cases hpos : pos.val < i.1
  · have hp : pos = Fin.castSucc ⟨pos.val, hpos⟩ := by ext; simp
    rw [hp]
    rw [concat_castSucc]
    simp only [ofMessagesChallenges]
    split <;> split
    · rfl
    · rename_i h1 h2
      exact absurd (h2.symm.trans h1) (by simp)
    · rename_i h1 h2
      exact absurd (h2.symm.trans h1) (by simp)
    · exact ChallengesUpTo.concat_apply_castSucc cs h c ⟨↑pos, hpos⟩ _
  · have hp : pos = Fin.last i.1 := by
      have hb : (i.succ : Fin (n + 1)).val = i.1 + 1 := rfl
      ext; simp; omega
    rw [hp]
    rw [concat_last]
    simp only [ofMessagesChallenges]
    split
    · rename_i h1
      exact absurd (h.symm.trans h1) (by simp)
    · exact ChallengesUpTo.concat_apply_last cs h c _

/-- Building the transcript from a message prefix and challenges commutes with appending a
message round: `Transcript.concat` with a message corresponds to `ChallengesUpTo.extend`
(reading the appended message off the message tuple). -/
lemma ofMessagesChallenges_concat_message (m : pSpec.Messages) {i : Fin n}
    (cs : ChallengesUpTo i.castSucc pSpec) (h : pSpec.dir i = .P_to_V) :
    (ofMessagesChallenges (m.take i.succ)
        (ChallengesUpTo.extend cs h) : Transcript i.succ pSpec)
      = appendRound (pSpec := pSpec) (m := i) (Messages.get m i h)
          (ofMessagesChallenges (m.take i.castSucc) cs) := by
  unfold appendRound
  funext pos
  by_cases hpos : pos.val < i.1
  · have hp : pos = Fin.castSucc ⟨pos.val, hpos⟩ := by ext; simp
    rw [hp]
    rw [concat_castSucc]
    simp only [ofMessagesChallenges]
    split <;> split
    · rfl
    · rename_i h1 h2
      exact absurd (h2.symm.trans h1) (by simp)
    · rename_i h1 h2
      exact absurd (h2.symm.trans h1) (by simp)
    · exact ChallengesUpTo.extend_apply_castSucc cs h ⟨↑pos, hpos⟩ _
  · have hp : pos = Fin.last i.1 := by
      have hb : (i.succ : Fin (n + 1)).val = i.1 + 1 := rfl
      ext; simp; omega
    rw [hp]
    rw [concat_last]
    simp only [ofMessagesChallenges]
    split
    · rfl
    · rename_i h1
      exact absurd (h1.symm.trans (show pSpec.dir _ = Direction.P_to_V from h)) (by simp)

end Transcript

end ProtocolSpec
