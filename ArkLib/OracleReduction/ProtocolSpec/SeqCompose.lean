/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Sigma
import ArkLib.OracleReduction.ProtocolSpec.Cast

/-! # Sequential Composition of Protocol Specifications

This file collects all definitions and theorems about sequentially composing `ProtocolSpec`s and
their associated data. -/

universe u v

open OracleComp OracleSpec

namespace ProtocolSpec

/-! ### Composition of Two Protocol Specifications -/

variable {m n : ℕ}

/-- Adding a round with direction `dir` and type `Message` to the beginning of a `ProtocolSpec` -/
abbrev cons (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) :=
  ⟨Fin.vcons dir pSpec.dir, Fin.vcons Message pSpec.Type⟩

/-- Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec` -/
abbrev concat (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) :=
  ⟨Fin.vconcat pSpec.dir dir, Fin.vconcat pSpec.Type Message⟩

/-- Appending two `ProtocolSpec`s -/
abbrev append (pSpec : ProtocolSpec m) (pSpec' : ProtocolSpec n) : ProtocolSpec (m + n) :=
  ⟨Fin.vappend pSpec.dir pSpec'.dir, Fin.vappend pSpec.Type pSpec'.Type⟩

@[inherit_doc]
infixl : 65 " ++ₚ " => ProtocolSpec.append

@[simp]
theorem append_cast_left {n m : ℕ} {pSpec : ProtocolSpec n} {pSpec' : ProtocolSpec m} (n' : ℕ)
    (h : n + m = n' + m) :
      dcast h (pSpec ++ₚ pSpec') = (dcast (Nat.add_right_cancel h) pSpec) ++ₚ pSpec' := by
  simp only [append, dcast, ProtocolSpec.cast, Fin.vappend_eq_append]
  simp

@[simp]
theorem append_cast_right {n m : ℕ} (pSpec : ProtocolSpec n) (pSpec' : ProtocolSpec m) (m' : ℕ)
    (h : n + m = n + m') :
      dcast h (pSpec ++ₚ pSpec') = pSpec ++ₚ (dcast (Nat.add_left_cancel h) pSpec') := by
  simp only [append, dcast, ProtocolSpec.cast, Fin.vappend_eq_append, Fin.append_cast_right]

theorem append_left_injective {pSpec : ProtocolSpec n} :
    Function.Injective (@ProtocolSpec.append m n · pSpec) := by
  simp only [append, Fin.vappend_eq_append]
  intro x y h
  simp at h
  obtain ⟨hDir, hType⟩ := h
  ext i
  · simp [Fin.append_left_injective pSpec.dir hDir]
  · simp [Fin.append_left_injective pSpec.Type hType]

theorem append_right_injective {pSpec : ProtocolSpec m} :
    Function.Injective (@ProtocolSpec.append m n pSpec) := by
  unfold ProtocolSpec.append
  simp only [Fin.vappend_eq_append]
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
  simp only [append, take, Fin.vappend_eq_append, Fin.append_right_eq_snoc,
    Fin.take_succ_eq_snoc]
  ext : 1 <;> simp

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

@[simp]
theorem take_append_left :
    (pSpec₁ ++ₚ pSpec₂).take m (Nat.le_add_right m n) = pSpec₁ := by
  simp only [take, Fin.vappend_eq_append]
  ext <;> simp [Fin.take_apply]

@[simp]
theorem take_append_left' : (pSpec₁ ++ₚ pSpec₂)⟦:m⟧ = pSpec₁ :=
  take_append_left

@[simp]
theorem rtake_append_right :
    (pSpec₁ ++ₚ pSpec₂).rtake n (Nat.le_add_left n m) = pSpec₂ := by
  simp only [rtake, Fin.vappend_eq_append]
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
    FullTranscript (pSpec₁ ++ₚ pSpec₂) :=
  Fin.happend T₁ T₂

@[inherit_doc]
infixl : 65 " ++ₜ " => append

/-- Adding a message with a given direction and type to the end of a `Transcript` -/
def concat {pSpec : ProtocolSpec n} {NextMessage : Type}
    (T : FullTranscript pSpec) (dir : Direction) (msg : NextMessage) :
        FullTranscript (pSpec ++ₚ ⟨!v[dir], !v[NextMessage]⟩) :=
  Fin.hconcat T msg

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
    FullTranscript.cast, Transcript.cast]
  have : ⟨i.val, by omega⟩ = Fin.castAdd n i := by ext; simp
  rw! (castMode := .all) [this, Fin.happend_left]

@[simp]
theorem rtake_append_right (T : FullTranscript pSpec₁) (T' : FullTranscript pSpec₂) :
    (T ++ₜ T').rtake n (Nat.le_add_left n m) =
      T'.cast rfl (by simp [ProtocolSpec.append]) := by
  ext i
  simp [rtake, Fin.rtake, append, Fin.cast, FullTranscript.cast, Transcript.cast]
  have : ⟨m + n - n + i.val, by omega⟩ = Fin.natAdd m i := by ext; simp
  rw! (castMode := .all) [this, Fin.happend_right]
  sorry

/-- The first half of a transcript for a concatenated protocol -/
def fst (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₁ :=
  fun i => by
    simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left]
      using T (Fin.castAdd n i)

/-- The second half of a transcript for a concatenated protocol -/
def snd (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₂ :=
  fun i => by
    simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right]
      using T (Fin.natAdd m i)

@[simp]
theorem append_fst (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (T₁ ++ₜ T₂).fst = T₁ := by
  funext i
  simp [fst, append]

@[simp]
theorem append_snd (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (T₁ ++ₜ T₂).snd = T₂ := by
  funext i
  simp [snd, append]

end FullTranscript

def MessageIdx.inl (i : MessageIdx pSpec₁) : MessageIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, by simpa only [Fin.vappend_eq_append, Fin.append_left] using i.2⟩

def MessageIdx.inr (i : MessageIdx pSpec₂) : MessageIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, by simpa only [Fin.vappend_eq_append, Fin.append_right] using i.2⟩

@[simps!]
def MessageIdx.sumEquiv :
    MessageIdx pSpec₁ ⊕ MessageIdx pSpec₂ ≃ MessageIdx (pSpec₁ ++ₚ pSpec₂) where
  toFun := Sum.elim (MessageIdx.inl) (MessageIdx.inr)
  invFun := fun ⟨i, h⟩ => by
    by_cases hi : i < m
    · simp [Fin.vappend_eq_append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inl ⟨⟨i, hi⟩, h⟩
    · simp [Fin.vappend_eq_append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inr ⟨⟨i - m, by omega⟩, h⟩
  left_inv := fun i => by
    rcases i with ⟨⟨i, isLt⟩, h⟩ | ⟨⟨i, isLt⟩, h⟩ <;>
    simp [MessageIdx.inl, MessageIdx.inr, isLt]
  right_inv := fun ⟨i, h⟩ => by
    by_cases hi : i < m <;>
    simp [MessageIdx.inl, MessageIdx.inr, hi]
    congr; omega

def ChallengeIdx.inl (i : ChallengeIdx pSpec₁) : ChallengeIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, by simpa only [Fin.vappend_eq_append, Fin.append_left] using i.2⟩

def ChallengeIdx.inr (i : ChallengeIdx pSpec₂) : ChallengeIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, by simpa only [Fin.vappend_eq_append, Fin.append_right] using i.2⟩

@[simps!]
def ChallengeIdx.sumEquiv :
    ChallengeIdx pSpec₁ ⊕ ChallengeIdx pSpec₂ ≃ ChallengeIdx (pSpec₁ ++ₚ pSpec₂) where
  toFun := Sum.elim (ChallengeIdx.inl) (ChallengeIdx.inr)
  invFun := fun ⟨i, h⟩ => by
    by_cases hi : i < m
    · simp [Fin.vappend_eq_append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inl ⟨⟨i, hi⟩, h⟩
    · simp [Fin.vappend_eq_append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inr ⟨⟨i - m, by omega⟩, h⟩
  left_inv := fun i => by
    rcases i with ⟨⟨i, isLt⟩, h⟩ | ⟨⟨i, isLt⟩, h⟩ <;>
    simp [ChallengeIdx.inl, ChallengeIdx.inr, isLt]
  right_inv := fun ⟨i, h⟩ => by
    by_cases hi : i < m <;>
    simp [ChallengeIdx.inl, ChallengeIdx.inr, hi]
    congr; omega

/-- Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`.

Defined for definitional equality, so that:
- `seqCompose !v[] = !p[]`
- `seqCompose !v[pSpec₁] = pSpec₁`
- `seqCompose !v[pSpec₁, pSpec₂] = pSpec₁ ++ₚ pSpec₂`
- `seqCompose !v[pSpec₁, pSpec₂, pSpec₃] = pSpec₁ ++ₚ (pSpec₂ ++ₚ pSpec₃)`
- and so on.

TODO: add notation `∑ i, pSpec i` for `seqCompose` -/
@[inline]
def seqCompose {m : ℕ} {n : Fin m → ℕ} (pSpec : ∀ i, ProtocolSpec (n i)) :
    ProtocolSpec (Fin.vsum n) where
  dir := Fin.vflatten (fun i => (pSpec i).dir)
  «Type» := Fin.vflatten (fun i => (pSpec i).Type)

@[simp]
lemma seqCompose_dir {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} :
    (seqCompose pSpec).dir = Fin.vflatten (fun i => (pSpec i).dir) := by
  rfl

@[simp]
lemma seqCompose_type {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} :
    (seqCompose pSpec).Type = Fin.vflatten (fun i => (pSpec i).Type) := by
  rfl

@[simp]
theorem seqCompose_zero {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} :
    seqCompose pSpec = !p[] := by
  rfl

@[simp]
theorem seqCompose_one {n : Fin 1 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} :
    seqCompose pSpec = pSpec 0 := by
  rfl

@[simp]
theorem seqCompose_two_eq_append {n : Fin 2 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} :
    seqCompose pSpec = append (pSpec 0) (pSpec 1) := by
  rfl

@[simp]
theorem seqCompose_succ_eq_append {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} :
    seqCompose pSpec = append (pSpec 0) (seqCompose (fun i => pSpec (Fin.succ i))) := by
  rfl

@[simp]
theorem seqCompose_succ_dir {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} :
    (seqCompose pSpec).dir = Fin.vflatten (fun i => (pSpec i).dir) := by
  rfl

@[simp]
theorem seqCompose_succ_type {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} :
    (seqCompose pSpec).Type = Fin.vflatten (fun i => (pSpec i).Type) := by
  rfl

namespace FullTranscript

/-- Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`.

Defined for definitional equality, so that the following holds definitionally:
- `seqCompose !h[] = !h[]`
- `seqCompose !h[T₁] = T₁`
- `seqCompose !h[T₁, T₂] = T₁ ++ₜ T₂`
- `seqCompose !h[T₁, T₂, T₃] = T₁ ++ₜ (T₂ ++ₜ T₃)`
- and so on.

TODO: add notation `∑ i, T i` for `seqCompose` -/
@[inline]
def seqCompose {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (T : ∀ i, FullTranscript (pSpec i)) : FullTranscript (seqCompose pSpec) :=
  Fin.hflatten T

@[simp]
theorem seqCompose_zero {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    {T : ∀ i, FullTranscript (pSpec i)} :
    seqCompose T = !h[] := rfl

@[simp]
theorem seqCompose_succ_eq_append {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    {T : ∀ i, FullTranscript (pSpec i)} :
    seqCompose T = append (T 0) (seqCompose (fun i => T (Fin.succ i))) := by
  rfl

@[simp]
theorem seqCompose_embedSum {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    {T : ∀ i, FullTranscript (pSpec i)} (i : Fin m) (j : Fin (n i)) :
    seqCompose T (Fin.embedSum i j) = cast (by simp) (T i j) := by
  simp [seqCompose, cast]

end FullTranscript

section Append

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- If two protocols have sampleable challenges, then their concatenation also has sampleable
  challenges. -/
@[inline]
instance [h₁ : ∀ i, SelectableType (pSpec₁.Challenge i)]
    [h₂ : ∀ i, SelectableType (pSpec₂.Challenge i)] :
    ∀ i, SelectableType ((pSpec₁ ++ₚ pSpec₂).Challenge i) :=
  fun ⟨i, h⟩ => Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → SelectableType type)
    (α₁ := pSpec₁.dir) (β₁ := pSpec₂.dir)
    (α₂ := pSpec₁.Type) (β₂ := pSpec₂.Type) (fun i h => h₁ ⟨i, h⟩) (fun i h => h₂ ⟨i, h⟩) i h

/-- If two protocols' messages have oracle representations, then their concatenation's messages also
    have oracle representations. -/
instance [O₁ : ∀ i, OracleInterface.{0, u, v} (pSpec₁.Message i)]
    [O₂ : ∀ i, OracleInterface.{0, u, v} (pSpec₂.Message i)] :
    ∀ i, OracleInterface.{0, u, v} ((pSpec₁ ++ₚ pSpec₂).Message i) :=
  fun ⟨i, h⟩ => Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .P_to_V) → OracleInterface type)
    (α₁ := pSpec₁.dir) (β₁ := pSpec₂.dir)
    (α₂ := pSpec₁.Type) (β₂ := pSpec₂.Type) (fun i h => O₁ ⟨i, h⟩) (fun i h => O₂ ⟨i, h⟩) i h

instance : ∀ i, OracleInterface ((pSpec₁ ++ₚ pSpec₂).Challenge i) := challengeOracleInterface

@[simp]
lemma challengeOracleInterface_append_domain_inl (j : pSpec₁.ChallengeIdx) :
    [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.domain (.inl j) = Unit := by
  simp [OracleSpec.domain, ChallengeIdx.inl, ProtocolSpec.append, OracleInterface.toOracleSpec,
    instOracleInterfaceChallengeAppend, challengeOracleInterface]

@[simp]
lemma challengeOracleInterface_append_range_inl (j : pSpec₁.ChallengeIdx) :
    [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.range (.inl j) = pSpec₁.Challenge j := by
  simp [OracleSpec.range, ChallengeIdx.inl, ProtocolSpec.append, OracleInterface.toOracleSpec,
    instOracleInterfaceChallengeAppend, challengeOracleInterface]

@[simp]
lemma challengeOracleInterface_append_domain_inr (j : pSpec₂.ChallengeIdx) :
    [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.domain (.inr j) = Unit := by
  simp [OracleSpec.domain, ChallengeIdx.inr, ProtocolSpec.append, OracleInterface.toOracleSpec,
    instOracleInterfaceChallengeAppend, challengeOracleInterface]

@[simp]
lemma challengeOracleInterface_append_range_inr (j : pSpec₂.ChallengeIdx) :
    [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.range (.inr j) = pSpec₂.Challenge j := by
  simp [OracleSpec.range, ChallengeIdx.inr, ProtocolSpec.append, OracleInterface.toOracleSpec,
    instOracleInterfaceChallengeAppend, challengeOracleInterface]

variable [∀ i, SelectableType (pSpec₁.Challenge i)] [∀ i, SelectableType (pSpec₂.Challenge i)]

instance instSubSpecOfProtocolSpecAppendChallenge :
    SubSpec ([pSpec₁.Challenge]ₒ ++ₒ [pSpec₂.Challenge]ₒ) ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
  monadLift | query i t => match i with
    | Sum.inl j => by
      simpa using query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) j.inl ()
    | Sum.inr j => by
      simpa using query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) j.inr ()

instance : SubSpec [pSpec₁.Challenge]ₒ ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
  monadLift | query i t => instSubSpecOfProtocolSpecAppendChallenge.monadLift (query (Sum.inl i) t)

instance : SubSpec [pSpec₂.Challenge]ₒ ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
  monadLift | query i t => instSubSpecOfProtocolSpecAppendChallenge.monadLift (query (Sum.inr i) t)

end Append

section SeqCompose

def sigmaChallengeIdxToSeqCompose {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (i : Fin m) (j : (pSpec i).ChallengeIdx) : (seqCompose pSpec).ChallengeIdx :=
  ⟨Fin.embedSum i j.1, by simp [j.property]⟩

def seqComposeChallengeIdxToSigma {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (k : (seqCompose pSpec).ChallengeIdx) : (i : Fin m) × (pSpec i).ChallengeIdx :=
  let ij := Fin.splitSum k.1
  ⟨ij.1, ⟨ij.2, by
    simp [ij]; have := k.property; simp at this
    have hk : k.1 = Fin.embedSum ij.1 ij.2 := by simp [ij]
    simp [hk] at this
    exact this⟩⟩

/-- The equivalence between the challenge indices of the individual protocols and the challenge
    indices of the sequential composition. -/
def seqComposeChallengeEquiv {m : ℕ} {n : Fin m → ℕ} (pSpec : ∀ i, ProtocolSpec (n i)) :
    (i : Fin m) × (pSpec i).ChallengeIdx ≃ (seqCompose pSpec).ChallengeIdx where
  -- TODO: write lemmas about `finSigmaFinEquiv` in mathlib with the one defined via `Fin.dfoldl`
  toFun := fun ⟨i, j⟩ => sigmaChallengeIdxToSeqCompose i j
  invFun := seqComposeChallengeIdxToSigma
  left_inv := by
    intro ⟨_, _⟩; simp [seqComposeChallengeIdxToSigma, sigmaChallengeIdxToSeqCompose]
    sorry
  right_inv := by intro; simp [seqComposeChallengeIdxToSigma, sigmaChallengeIdxToSeqCompose]

def sigmaMessageIdxToSeqCompose {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (i : Fin m) (j : (pSpec i).MessageIdx) : (seqCompose pSpec).MessageIdx :=
  ⟨Fin.embedSum i j.1, by simp [j.property]⟩

def seqComposeMessageIdxToSigma {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (k : (seqCompose pSpec).MessageIdx) : (i : Fin m) × (pSpec i).MessageIdx :=
  let ij := Fin.splitSum k.1
  ⟨ij.1, ⟨ij.2, by
    simp [ij]; have := k.property; simp at this
    have hk : k.1 = Fin.embedSum ij.1 ij.2 := by simp [ij]
    simp [hk] at this
    exact this⟩⟩

/-- The equivalence between the message indices of the individual protocols and the message
    indices of the sequential composition. -/
def seqComposeMessageEquiv {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} :
    (i : Fin m) × (pSpec i).MessageIdx ≃ (seqCompose pSpec).MessageIdx where
  toFun := fun ⟨i, msgIdx⟩ => sigmaMessageIdxToSeqCompose i msgIdx
  invFun := seqComposeMessageIdxToSigma
  left_inv := by
    intro ⟨i, ⟨j, h⟩⟩ ; simp [seqComposeMessageIdxToSigma, sigmaMessageIdxToSeqCompose]
    sorry
  right_inv := by intro; simp [seqComposeMessageIdxToSigma, sigmaMessageIdxToSeqCompose]

instance {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [inst : ∀ i, ∀ j, SelectableType ((pSpec i).Challenge j)] :
    ∀ k, SelectableType ((seqCompose pSpec).Challenge k) :=
  fun ⟨k, h⟩ => Fin.fflatten₂
    (A := Direction) (B := Type) (F := fun dir type => (h : dir = .V_to_P) → SelectableType type)
    (fun i' j' h' => inst i' ⟨j', h'⟩) k h

/-- If all protocols' messages have oracle interfaces, then the messages of their sequential
  composition also have oracle interfaces. -/
instance {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface.{0, u, v} ((pSpec i).Message j)] :
    ∀ k, OracleInterface.{0, u, v} ((seqCompose pSpec).Message k) :=
  fun ⟨k, h⟩ => Fin.fflatten₂
    (A := Direction) (B := Type) (F := fun dir type => (h : dir = .P_to_V) → OracleInterface type)
    (fun i' j' h' => Oₘ i' ⟨j', h'⟩) k h

end SeqCompose

end ProtocolSpec
