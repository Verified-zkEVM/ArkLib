/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.BigOperators.Fin
import ArkLib.OracleReduction.ProtocolSpec
import ArkLib.OracleReduction.Cast

/-! # Sequential Composition of Protocol Specifications

This file collects all definitions and theorems about sequentially composing `ProtocolSpec`s and
their associated data. -/

namespace ProtocolSpec

/-! ### Composition of Two Protocol Specifications -/

variable {m n : ℕ}

/-- Adding a round with direction `dir` and type `Message` to the beginning of a `ProtocolSpec` -/
abbrev cons (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) := Fin.cons ⟨dir, Message⟩ pSpec

/-- Adding a round with direction `dir` and type `Message` to the end of a `ProtocolSpec` -/
abbrev snoc (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) := Fin.snoc pSpec ⟨dir, Message⟩

/-- Appending two `ProtocolSpec`s -/
abbrev append (pSpec : ProtocolSpec m) (pSpec' : ProtocolSpec n) : ProtocolSpec (m + n) :=
  Fin.append pSpec pSpec'

@[inline, reducible]
def mkSingle (dir : Direction) (Message : Type) : ProtocolSpec 1 := fun _ => ⟨dir, Message⟩

@[inherit_doc]
infixl : 65 " ++ₚ " => ProtocolSpec.append

@[simp]
theorem append_cast_left {n m : ℕ} {pSpec : ProtocolSpec n} {pSpec' : ProtocolSpec m} (n' : ℕ)
    (h : n + m = n' + m) :
      dcast h (pSpec ++ₚ pSpec') = (dcast (Nat.add_right_cancel h) pSpec) ++ₚ pSpec' := by
  simp [append, dcast, ProtocolSpec.cast, Fin.append_cast_left]

@[simp]
theorem append_cast_right {n m : ℕ} (pSpec : ProtocolSpec n) (pSpec' : ProtocolSpec m) (m' : ℕ)
    (h : n + m = n + m') :
      dcast h (pSpec ++ₚ pSpec') = pSpec ++ₚ (dcast (Nat.add_left_cancel h) pSpec') := by
  simp [append, dcast, ProtocolSpec.cast, Fin.append_cast_right]

@[simp]
theorem append_left {n m : ℕ} {pSpec : ProtocolSpec n} {pSpec' : ProtocolSpec m} (i : Fin n) :
    (pSpec ++ₚ pSpec') (Fin.castAdd m i) = pSpec i := by
  simp [append, Fin.append_left]

@[simp]
theorem append_right {n m : ℕ} {pSpec : ProtocolSpec n} {pSpec' : ProtocolSpec m} (i : Fin m) :
    (pSpec ++ₚ pSpec') (Fin.natAdd n i) = pSpec' i := by
  simp [append, Fin.append_right]

theorem append_left_injective {pSpec : ProtocolSpec n} :
    Function.Injective (@ProtocolSpec.append m n · pSpec) :=
  Fin.append_left_injective pSpec

theorem append_right_injective {pSpec : ProtocolSpec m} :
    Function.Injective (@ProtocolSpec.append m n pSpec) :=
  Fin.append_right_injective pSpec

@[simp]
theorem append_left_cancel_iff {pSpec : ProtocolSpec n} {p1 p2 : ProtocolSpec m} :
    p1 ++ₚ pSpec = p2 ++ₚ pSpec ↔ p1 = p2 :=
  ⟨fun h => append_left_injective h, fun h => by rw [h]⟩

@[simp]
theorem append_right_cancel_iff {pSpec : ProtocolSpec m} {p1 p2 : ProtocolSpec n} :
    pSpec ++ₚ p1 = pSpec ++ₚ p2 ↔ p1 = p2 :=
  ⟨fun h => append_right_injective h, fun h => by rw [h]⟩

@[simp]
theorem snoc_take {pSpec : ProtocolSpec n} (k : ℕ) (h : k < n) :
    (pSpec.take k (Nat.le_of_succ_le h) ++ₚ (fun (_ : Fin 1) => pSpec ⟨k, h⟩))
      = pSpec.take (k + 1) h := by
  simp only [append, take, Fin.append_right_eq_snoc, Fin.take_succ_eq_snoc]

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

@[simp]
theorem take_append_left :
    (pSpec₁ ++ₚ pSpec₂).take m (Nat.le_add_right m n) = pSpec₁ := by
  ext i : 1
  have : Fin.castLE (by omega) i = Fin.castAdd n i := rfl
  simp [Fin.take_apply, Fin.append_left, this]

@[simp]
theorem rtake_append_right :
    (pSpec₁ ++ₚ pSpec₂).rtake n (Nat.le_add_left n m) = pSpec₂ := by
  ext i : 1
  simp [Fin.rtake_apply, Fin.append_right]

namespace Transcript

variable {k : Fin (m + n + 1)}

/-- The first half of a partial transcript for a concatenated protocol. -/
def fst (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) : pSpec₁.Transcript ⟨min k m, by omega⟩ :=
  fun i => sorry
  -- cast T i

/-- The second half of a partial transcript for a concatenated protocol. -/
def snd (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) : pSpec₂.Transcript ⟨k - m, by omega⟩ :=
  fun i => sorry
  -- cast T i

end Transcript

namespace FullTranscript

/-- Appending two transcripts for two `ProtocolSpec`s -/
def append (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    FullTranscript (pSpec₁ ++ₚ pSpec₂) :=
  fun i => (Fin.append_comp' Prod.snd i).mp (Fin.addCases' T₁ T₂ i)

@[inherit_doc]
infixl : 65 " ++ₜ " => append

/-- Adding a message with a given direction and type to the end of a `Transcript` -/
def snoc {pSpec : ProtocolSpec n} {NextMessage : Type}
    (T : FullTranscript pSpec) (dir : Direction) (msg : NextMessage) :
        FullTranscript (pSpec ++ₚ .mkSingle dir NextMessage) :=
  append T fun _ => msg

-- TODO: fill

-- @[simp]
-- theorem append_cast_left {n m : ℕ} {pSpec₁ pSpec₂ : ProtocolSpec n} {pSpec' : ProtocolSpec m}
--     {T₁ : FullTranscript pSpec₁} {T₂ : FullTranscript pSpec'} (n' : ℕ)
--     (h : n + m = n' + m) (hSpec : dcast h pSpec₁ = pSpec₂) :
--       dcast₂ h (by simp) (T₁ ++ₜ T₂) = (dcast₂ (Nat.add_right_cancel h) (by simp) T₁) ++ₜ T₂ :=
-- by
--   simp [append, dcast₂, ProtocolSpec.cast, Fin.append_cast_left]

-- @[simp]
-- theorem append_cast_right {n m : ℕ} (pSpec : ProtocolSpec n) (pSpec' : ProtocolSpec m) (m' : ℕ)
--     (h : n + m = n + m') :
--       dcast h (pSpec ++ₚ pSpec') = pSpec ++ₚ (dcast (Nat.add_left_cancel h) pSpec') := by
--   simp [append, dcast, ProtocolSpec.cast, Fin.append_cast_right]

@[simp]
theorem take_append_left (T : FullTranscript pSpec₁) (T' : FullTranscript pSpec₂) :
    (T ++ₜ T').take m (Nat.le_add_right m n) =
      T.cast rfl (by simp) := by
  ext i
  simp [take, append, ProtocolSpec.append, Fin.castLE, Fin.addCases', Fin.addCases,
    FullTranscript.cast, Transcript.cast]

@[simp]
theorem rtake_append_right (T : FullTranscript pSpec₁) (T' : FullTranscript pSpec₂) :
    (T ++ₜ T').rtake n (Nat.le_add_left n m) =
      T'.cast rfl (by simp) := by
  ext i
  simp only [ProtocolSpec.append, getType, Fin.rtake_apply, Fin.natAdd, Fin.cast_mk, rtake, append,
    Fin.addCases', Fin.addCases, add_tsub_cancel_right, add_lt_iff_neg_left, not_lt_zero',
    ↓reduceDIte, Fin.subNat_mk, Fin.natAdd_mk, eq_mpr_eq_cast, eq_mp_eq_cast, FullTranscript.cast,
    Transcript.cast, Fin.val_last, Fin.cast_eq_self, Fin.castLE_refl]
  have : m + n - n + i.val - m = i.val := by omega
  rw! (castMode := .all) [this]
  simp [eqRec_eq_cast]

/-- The first half of a transcript for a concatenated protocol -/
def fst (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₁ :=
  fun i => by simpa using T (Fin.castAdd n i)

/-- The second half of a transcript for a concatenated protocol -/
def snd (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₂ :=
  fun i => by simpa using T (Fin.natAdd m i)

@[simp]
theorem append_fst (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (T₁ ++ₜ T₂).fst = T₁ := by
  funext i
  simp [fst, append, eqRec_eq_cast]

@[simp]
theorem append_snd (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (T₁ ++ₜ T₂).snd = T₂ := by
  funext i
  simp [snd, append, eqRec_eq_cast]

end FullTranscript

namespace MessageIdx

def inl (i : MessageIdx pSpec₁) : MessageIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, by simpa using i.2⟩

def inr (i : MessageIdx pSpec₂) : MessageIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, by simpa using i.2⟩

@[simps!]
def sumEquiv :
    MessageIdx (pSpec₁ ++ₚ pSpec₂) ≃ MessageIdx pSpec₁ ⊕ MessageIdx pSpec₂ where
  toFun := fun ⟨i, h⟩ => by
    by_cases hi : i < m
    · simp only [append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inl ⟨⟨i, hi⟩, h⟩
    · simp only [append, Fin.append, Fin.addCases, hi, eq_rec_constant] at h
      exact Sum.inr ⟨⟨i - m, by omega⟩, h⟩
  invFun := Sum.elim inl inr
  left_inv := fun ⟨i, h⟩ => by
    by_cases hi : i < m <;>
    simp [inl, inr, hi]
    congr; omega
  right_inv := fun i => by
    rcases i with ⟨⟨i, isLt⟩, h⟩ | ⟨⟨i, isLt⟩, h⟩ <;>
    simp [inl, inr, isLt]

end MessageIdx

namespace Messages

/-- The first half of the messages for a concatenated protocol -/
def fst (m : (pSpec₁ ++ₚ pSpec₂).Messages) : pSpec₁.Messages :=
  fun i => by simpa [MessageIdx.inl] using m (MessageIdx.inl i)

/-- The second half of the messages for a concatenated protocol -/
def snd (m : (pSpec₁ ++ₚ pSpec₂).Messages) : pSpec₂.Messages :=
  fun i => by simpa [MessageIdx.inr] using m (MessageIdx.inr i)

/-- The equivalence between the messages for a concatenated protocol and the tuple of messages for
    the two protocols -/
def prodEquiv :
    (pSpec₁ ++ₚ pSpec₂).Messages ≃ pSpec₁.Messages × pSpec₂.Messages where
  toFun := fun m => ⟨m.fst, m.snd⟩
  invFun := fun ⟨m₁, m₂⟩ => fun ⟨i, h⟩ => by
    by_cases hi : i < m
    · haveI : i = Fin.castAdd n ⟨i.val, hi⟩ := rfl
      rw! [this] at h ⊢
      simp only [ProtocolSpec.Message, ProtocolSpec.append_left] at h ⊢
      exact m₁ ⟨⟨i.val, hi⟩, h⟩
    · haveI : i = Fin.natAdd m ⟨i.val - m, by omega⟩ := by ext; simp; omega
      rw! [this] at h ⊢
      simp only [ProtocolSpec.Message, ProtocolSpec.append_right] at h ⊢
      exact m₂ ⟨⟨i.val - m, by omega⟩, h⟩
  left_inv := fun msgs => by
    funext ⟨i, h⟩
    by_cases hi : i.val < m
    · simp [hi, fst, MessageIdx.inl]
    · simp only [hi, ↓reduceDIte, snd, Message, MessageIdx.inr, Fin.natAdd_mk]
      rw! [Nat.add_sub_of_le (Nat.le_of_not_lt hi)]
      simp
  right_inv := fun ⟨m₁, m₂⟩ => by
    simp only [MessageIdx, Message, Prod.mk.injEq]
    constructor
    · funext i; simp [fst, MessageIdx.inl]
    · funext i; simp only [snd, MessageIdx.inr]; rw! [Nat.add_sub_self_left]; simp

end Messages

namespace ChallengeIdx

def inl (i : ChallengeIdx pSpec₁) : ChallengeIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, by simpa only [Fin.append_left] using i.2⟩

def inr (i : ChallengeIdx pSpec₂) : ChallengeIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, by simpa only [Fin.append_right] using i.2⟩

@[simps!]
def sumEquiv :
    ChallengeIdx (pSpec₁ ++ₚ pSpec₂) ≃ ChallengeIdx pSpec₁ ⊕ ChallengeIdx pSpec₂ where
  toFun := fun ⟨i, h⟩ => by
    by_cases hi : i < m
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inl ⟨⟨i, hi⟩, h⟩
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inr ⟨⟨i - m, by omega⟩, h⟩
  invFun := Sum.elim inl inr
  left_inv := fun ⟨i, h⟩ => by
    by_cases hi : i < m <;>
    simp [inl, inr, hi]
    congr; omega
  right_inv := fun i => by
    rcases i with ⟨⟨i, isLt⟩, h⟩ | ⟨⟨i, isLt⟩, h⟩ <;>
    simp [inl, inr, isLt]

end ChallengeIdx

namespace Challenges

/-- The first half of the challenges for a concatenated protocol -/
def fst (c : (pSpec₁ ++ₚ pSpec₂).Challenges) : pSpec₁.Challenges :=
  fun i => by simpa [ChallengeIdx.inl] using c (ChallengeIdx.inl i)

/-- The second half of the challenges for a concatenated protocol -/
def snd (c : (pSpec₁ ++ₚ pSpec₂).Challenges) : pSpec₂.Challenges :=
  fun i => by simpa [ChallengeIdx.inr] using c (ChallengeIdx.inr i)

/-- The equivalence between the challenges for a concatenated protocol and the tuple of challenges
  for the two protocols -/
def prodEquiv :
    (pSpec₁ ++ₚ pSpec₂).Challenges ≃ pSpec₁.Challenges × pSpec₂.Challenges where
  toFun := fun c => ⟨c.fst, c.snd⟩
  invFun := fun ⟨c₁, c₂⟩ => fun ⟨i, h⟩ => by
    by_cases hi : i < m
    · haveI : i = Fin.castAdd n ⟨i.val, hi⟩ := rfl
      rw! [this] at h ⊢
      simp only [ProtocolSpec.Challenge, ProtocolSpec.append_left] at h ⊢
      exact c₁ ⟨⟨i.val, hi⟩, h⟩
    · haveI : i = Fin.natAdd m ⟨i.val - m, by omega⟩ := by ext; simp; omega
      rw! [this] at h ⊢
      simp only [ProtocolSpec.Challenge, ProtocolSpec.append_right] at h ⊢
      exact c₂ ⟨⟨i.val - m, by omega⟩, h⟩
  left_inv := fun challs => by
    funext ⟨i, h⟩
    by_cases hi : i.val < m
    · simp [hi, fst, ChallengeIdx.inl]
    · simp only [hi, ↓reduceDIte, snd, Challenge, ChallengeIdx.inr, Fin.natAdd_mk]
      rw! [Nat.add_sub_of_le (Nat.le_of_not_lt hi)]
      simp
  right_inv := fun ⟨c₁, c₂⟩ => by
    simp only [ChallengeIdx, Challenge, Prod.mk.injEq]
    constructor
    · funext i; simp [fst, ChallengeIdx.inl]
    · funext i; simp only [snd, ChallengeIdx.inr]; rw! [Nat.add_sub_self_left]; simp

end Challenges

/-- Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`.

Defined by (dependent) folding over `Fin`, starting from the empty protocol specification `![]`.

TODO: add notation `∑ i, pSpec i` for `seqCompose` -/
def seqCompose {m : ℕ} {n : Fin m → ℕ} (pSpec : ∀ i, ProtocolSpec (n i)) :
    ProtocolSpec (∑ i, n i) :=
  Fin.dfoldl m (fun i => ProtocolSpec (∑ j : Fin i, n (j.castLE (by omega))))
    (fun i acc => dcast (by simp [Fin.sum_univ_castSucc, Fin.castLE]) (acc ++ₚ pSpec i))
      ![]

@[simp]
theorem seqCompose_zero {n : ℕ} {pSpec : ProtocolSpec n} :
    seqCompose (fun _ : Fin 0=> pSpec) = ![] := by
  simp [seqCompose]

/-- Sequential composition of `i + 1` protocol specifications equals the sequential composition of
  `i` first protocol specifications appended with the `i + 1`-th protocol specification.
-/
theorem seqCompose_append {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} (i : Fin m) :
    seqCompose (Fin.take (i + 1) (by omega) pSpec)
    = dcast (by simp [Fin.sum_univ_castSucc, Fin.castLE])
        (seqCompose (Fin.take i (by omega) pSpec) ++ₚ pSpec i) := by
  simp only [seqCompose, Fin.coe_castSucc, Fin.val_succ, Fin.take_apply, Fin.dfoldl_succ_last,
    Fin.val_last, Fin.castLE_refl, Function.comp_apply, Fin.castLE_castSucc]
  unfold Function.comp Fin.castSucc Fin.castAdd Fin.castLE Fin.last
  simp

namespace FullTranscript

/-- Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`.

TODO: add notation `∑ i, T i` for `seqCompose` -/
def seqCompose {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (T : ∀ i, FullTranscript (pSpec i)) : FullTranscript (seqCompose pSpec) :=
  Fin.dfoldl m
    (fun i => FullTranscript (ProtocolSpec.seqCompose (Fin.take i (by omega) pSpec)))
    (fun i acc => by
      refine dcast₂ ?_ ?_ (acc ++ₜ (T i))
      · simp [Fin.sum_univ_castSucc, Fin.castLE]
      · simp [ProtocolSpec.seqCompose_append])
    (fun i => Fin.elim0 i)

@[simp]
theorem seqCompose_zero {n : ℕ} {pSpec : ProtocolSpec n} {transcript : pSpec.FullTranscript} :
    seqCompose (fun _ : Fin 0 => transcript) = (fun i => Fin.elim0 i) := rfl

/-- Sequential composition of `i + 1` transcripts equals the sequential composition of `i` first
  transcripts appended with the `i + 1`-th transcript. -/
theorem seqCompose_append {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    {T : ∀ i, FullTranscript (pSpec i)} (i : Fin m) :
    seqCompose (Fin.take (i + 1) (by omega) T)
    = dcast₂ (by simp [Fin.sum_univ_castSucc, Fin.castLE]) (by sorry)
        (seqCompose (Fin.take i (by omega) T) ++ₜ T i) := by
  simp [seqCompose]
  sorry

end FullTranscript

end ProtocolSpec
