/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.BigOperators.Fin
import ArkLib.OracleReduction.ProtocolSpec
import ArkLib.OracleReduction.Cast
import ArkLib.Data.Fin.Tuple.Lemmas

/-! # Sequential Composition of Protocol Specifications

This file collects all definitions and theorems about sequentially composing `ProtocolSpec`s and
their associated data. -/

namespace ProtocolSpec

/-! ### Composition of Two Protocol Specifications -/

variable {m n : ℕ}

/-- Adding a round with direction `dir` and type `Message` to the beginning of a `ProtocolSpec` -/
abbrev cons (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) :=
  ⟨FinVec.cons dir pSpec.dir, FinVec.cons Message pSpec.Type⟩

/-- Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec` -/
abbrev concat (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) :=
  ⟨FinVec.concat pSpec.dir dir, FinVec.concat pSpec.Type Message⟩

/-- Appending two `ProtocolSpec`s -/
abbrev append (pSpec : ProtocolSpec m) (pSpec' : ProtocolSpec n) : ProtocolSpec (m + n) :=
  ⟨FinVec.append pSpec.dir pSpec'.dir, FinVec.append pSpec.Type pSpec'.Type⟩

@[inherit_doc]
infixl : 65 " ++ₚ " => ProtocolSpec.append

@[simp]
theorem append_cast_left {n m : ℕ} {pSpec : ProtocolSpec n} {pSpec' : ProtocolSpec m} (n' : ℕ)
    (h : n + m = n' + m) :
      dcast h (pSpec ++ₚ pSpec') = (dcast (Nat.add_right_cancel h) pSpec) ++ₚ pSpec' := by
  simp only [append, dcast, ProtocolSpec.cast, FinVec.append_eq_fin_append]
  simp

@[simp]
theorem append_cast_right {n m : ℕ} (pSpec : ProtocolSpec n) (pSpec' : ProtocolSpec m) (m' : ℕ)
    (h : n + m = n + m') :
      dcast h (pSpec ++ₚ pSpec') = pSpec ++ₚ (dcast (Nat.add_left_cancel h) pSpec') := by
  simp only [append, dcast, ProtocolSpec.cast, FinVec.append_eq_fin_append, Fin.append_cast_right]

theorem append_left_injective {pSpec : ProtocolSpec n} :
    Function.Injective (@ProtocolSpec.append m n · pSpec) := by
  simp only [append, FinVec.append_eq_fin_append]
  intro x y h
  simp at h
  obtain ⟨hDir, hType⟩ := h
  ext i
  · simp [Fin.append_left_injective pSpec.dir hDir]
  · simp [Fin.append_left_injective pSpec.Type hType]

theorem append_right_injective {pSpec : ProtocolSpec m} :
    Function.Injective (@ProtocolSpec.append m n pSpec) := by
  unfold ProtocolSpec.append
  simp only [FinVec.append_eq_fin_append]
  intro x y h
  simp at h
  obtain ⟨hDir, hType⟩ := h
  ext i
  · simp [Fin.append_right_injective pSpec.dir hDir]
  · simp [Fin.append_right_injective pSpec.Type hType]

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
    (pSpec.take k (Nat.le_of_succ_le h) ++ₚ ⟨![pSpec.dir ⟨k, h⟩], ![pSpec.Type ⟨k, h⟩]⟩)
      = pSpec.take (k + 1) h := by
  simp only [append, take, FinVec.append_eq_fin_append, Fin.append_right_eq_snoc,
    Fin.take_succ_eq_snoc]
  ext : 1 <;> simp

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

@[simp]
theorem take_append_left :
    (pSpec₁ ++ₚ pSpec₂).take m (Nat.le_add_right m n) = pSpec₁ := by
  simp only [take, FinVec.append_eq_fin_append]
  ext <;> simp [Fin.take_apply]

@[simp]
theorem rtake_append_right :
    (pSpec₁ ++ₚ pSpec₂).rtake n (Nat.le_add_left n m) = pSpec₂ := by
  simp only [rtake, FinVec.append_eq_fin_append]
  ext i : 2 <;> simp [Fin.rtake, Fin.append_right]

namespace Transcript

variable {k : Fin (m + n + 1)}

/-- The first half of a partial transcript for a concatenated protocol, up to round `k < m + n + 1`.

This is defined to be the full transcript for the first half if `k ≥ m`. -/
def fst (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) : pSpec₁.Transcript ⟨min k m, by omega⟩ :=
  if hk : k ≤ m then
    fun i => by
    dsimp [take]; have := T ⟨i, lt_of_lt_of_le i.isLt (inf_le_left)⟩; simp at this; sorry
    -- dcast (by sorry) (T ⟨i, lt_of_lt_of_le i.isLt (inf_le_left)⟩)
  else
    fun i => sorry
    -- dcast (by sorry) (T ⟨i, by omega⟩)

/-- The second half of a partial transcript for a concatenated protocol. -/
def snd (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) : pSpec₂.Transcript ⟨k - m, by omega⟩ :=
  if hk : k ≤ m then
    fun i => Fin.elim0 (by simpa [hk] using i)
  else
    fun i => sorry
    -- dcast (by sorry) (T ⟨m + i, by simp_all; dsimp at i; have := i.isLt; omega⟩)

end Transcript

namespace FullTranscript

/-- Appending two transcripts for two `ProtocolSpec`s -/
def append (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    FullTranscript (pSpec₁ ++ₚ pSpec₂) := by
  dsimp [FullTranscript]
  convert FinTuple.append T₁ T₂
  -- fun i => (FinVec.append Prod.snd i).mp (Fin.addCases' T₁ T₂ i)

@[inherit_doc]
infixl : 65 " ++ₜ " => append

/-- Adding a message with a given direction and type to the end of a `Transcript` -/
def concat {pSpec : ProtocolSpec n} {NextMessage : Type}
    (T : FullTranscript pSpec) (dir : Direction) (msg : NextMessage) :
        FullTranscript (pSpec ++ₚ ⟨!v[dir], !v[NextMessage]⟩) :=
  append T (fun _ => msg)

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
      T.cast rfl (by simp [ProtocolSpec.append]) := by
  ext i
  simp [take, append, ProtocolSpec.append, Fin.castLE,
    FullTranscript.cast, Transcript.cast]; sorry

@[simp]
theorem rtake_append_right (T : FullTranscript pSpec₁) (T' : FullTranscript pSpec₂) :
    (T ++ₜ T').rtake n (Nat.le_add_left n m) =
      T'.cast rfl (by simp [ProtocolSpec.append]) := by
  ext i
  simp [rtake, Fin.rtake, append, Fin.cast, FullTranscript.cast, Transcript.cast]
  sorry
  -- have : m + n - n + i.val - m = i.val := by omega
  -- rw! (castMode := .all) [this]
  -- simp [eqRec_eq_cast]

/-- The first half of a transcript for a concatenated protocol -/
def fst (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₁ :=
  fun i => by
    simpa [ProtocolSpec.append, FinVec.append_eq_fin_append, Fin.append_left]
      using T (Fin.castAdd n i)

/-- The second half of a transcript for a concatenated protocol -/
def snd (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₂ :=
  fun i => by
    simpa [ProtocolSpec.append, FinVec.append_eq_fin_append, Fin.append_right]
      using T (Fin.natAdd m i)

@[simp]
theorem append_fst (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (T₁ ++ₜ T₂).fst = T₁ := by
  funext i
  simp [fst, append]; sorry

@[simp]
theorem append_snd (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (T₁ ++ₜ T₂).snd = T₂ := by
  funext i
  simp [snd, append]; sorry

end FullTranscript

def MessageIdx.inl (i : MessageIdx pSpec₁) : MessageIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, by simpa only [FinVec.append_eq_fin_append, Fin.append_left] using i.2⟩

def MessageIdx.inr (i : MessageIdx pSpec₂) : MessageIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, by simpa only [FinVec.append_eq_fin_append, Fin.append_right] using i.2⟩

@[simps!]
def MessageIdx.sumEquiv :
    MessageIdx pSpec₁ ⊕ MessageIdx pSpec₂ ≃ MessageIdx (pSpec₁ ++ₚ pSpec₂) where
  toFun := Sum.elim (MessageIdx.inl) (MessageIdx.inr)
  invFun := fun ⟨i, h⟩ => by
    by_cases hi : i < m
    · simp [FinVec.append_eq_fin_append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inl ⟨⟨i, hi⟩, h⟩
    · simp [FinVec.append_eq_fin_append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inr ⟨⟨i - m, by omega⟩, h⟩
  left_inv := fun i => by
    rcases i with ⟨⟨i, isLt⟩, h⟩ | ⟨⟨i, isLt⟩, h⟩ <;>
    simp [MessageIdx.inl, MessageIdx.inr, isLt]
  right_inv := fun ⟨i, h⟩ => by
    by_cases hi : i < m <;>
    simp [MessageIdx.inl, MessageIdx.inr, hi]
    congr; omega

def ChallengeIdx.inl (i : ChallengeIdx pSpec₁) : ChallengeIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, by simpa only [FinVec.append_eq_fin_append, Fin.append_left] using i.2⟩

def ChallengeIdx.inr (i : ChallengeIdx pSpec₂) : ChallengeIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, by simpa only [FinVec.append_eq_fin_append, Fin.append_right] using i.2⟩

@[simps!]
def ChallengeIdx.sumEquiv :
    ChallengeIdx pSpec₁ ⊕ ChallengeIdx pSpec₂ ≃ ChallengeIdx (pSpec₁ ++ₚ pSpec₂) where
  toFun := Sum.elim (ChallengeIdx.inl) (ChallengeIdx.inr)
  invFun := fun ⟨i, h⟩ => by
    by_cases hi : i < m
    · simp [FinVec.append_eq_fin_append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inl ⟨⟨i, hi⟩, h⟩
    · simp [FinVec.append_eq_fin_append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inr ⟨⟨i - m, by omega⟩, h⟩
  left_inv := fun i => by
    rcases i with ⟨⟨i, isLt⟩, h⟩ | ⟨⟨i, isLt⟩, h⟩ <;>
    simp [ChallengeIdx.inl, ChallengeIdx.inr, isLt]
  right_inv := fun ⟨i, h⟩ => by
    by_cases hi : i < m <;>
    simp [ChallengeIdx.inl, ChallengeIdx.inr, hi]
    congr; omega

/-- Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`.

Defined by (dependent) folding over `Fin`, starting from the empty protocol specification `![]`.

TODO: add notation `∑ i, pSpec i` for `seqCompose` -/
def seqCompose {m : ℕ} {n : Fin m → ℕ} (pSpec : ∀ i, ProtocolSpec (n i)) :
    ProtocolSpec (∑ i, n i) :=
  Fin.dfoldl m (fun i => ProtocolSpec (∑ j : Fin i, n (j.castLE (by omega))))
    (fun i acc => dcast (by simp [Fin.sum_univ_castSucc, Fin.castLE]) (acc ++ₚ pSpec i))
      !p[]

@[simp]
theorem seqCompose_zero {n : ℕ} {pSpec : ProtocolSpec n} :
    seqCompose (fun _ : Fin 0=> pSpec) = !p[] := by
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
