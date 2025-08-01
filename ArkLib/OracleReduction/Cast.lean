/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Casting for structures of oracle reductions

  We define custom dependent casts (registered as `DCast` instances) for the following structures:
  - `ProtocolSpec`
  - `(Full)Transcript`
  - `(Oracle)Prover`
  - `(Oracle)Verifier`
  - `(Oracle)Reduction`
-/


namespace ProtocolSpec

variable {n₁ n₂ : ℕ} (hn : n₁ = n₂)

/-! ### Casting Protocol Specifications -/

/-- Casting a `ProtocolSpec` across an equality of the number of rounds

One should use the type-class function `dcast` instead of this one. -/
protected def cast (pSpec : ProtocolSpec n₁) : ProtocolSpec n₂ :=
  pSpec ∘ (Fin.cast hn.symm)

@[simp]
theorem cast_id : ProtocolSpec.cast (Eq.refl n₁) = id := rfl

instance instDCast : DCast Nat ProtocolSpec where
  dcast h := ProtocolSpec.cast h
  dcast_id := cast_id

theorem cast_eq_dcast {h : n₁ = n₂} {pSpec : ProtocolSpec n₁} :
    pSpec.cast h = dcast h pSpec := rfl

/-! ### Casting (Partial) Transcripts -/

variable {pSpec₁ : ProtocolSpec n₁} {pSpec₂ : ProtocolSpec n₂}

@[simp]
theorem cast_idx (hSpec : pSpec₁.cast hn = pSpec₂) {i : Fin n₁} :
    pSpec₂ (Fin.cast hn i) = pSpec₁ i := by
  simp [← hSpec, ProtocolSpec.cast]

@[simp]
theorem cast_idx_symm {hn} (hSpec : pSpec₁.cast hn = pSpec₂) {i : Fin n₂} :
    pSpec₁ (Fin.cast hn.symm i) = pSpec₂ i := funext_iff.mp hSpec i

theorem cast_symm {hn} (hSpec : pSpec₁.cast hn = pSpec₂) : pSpec₂.cast hn.symm = pSpec₁ := by
  rw [cast_eq_dcast] at hSpec ⊢
  exact dcast_symm hn hSpec

variable (hSpec : pSpec₁.cast hn = pSpec₂)

namespace MessageIdx

/-- Casting a message index across an equality of `ProtocolSpec`s. -/
protected def cast (i : MessageIdx pSpec₁) : MessageIdx pSpec₂ :=
  ⟨Fin.cast hn i.1, by simp [← hSpec, ProtocolSpec.cast, i.property]⟩

@[simp]
theorem cast_id : MessageIdx.cast (Eq.refl n₁) rfl = (id : pSpec₁.MessageIdx → _) := rfl

theorem cast_injective : Function.Injective (MessageIdx.cast hn hSpec) := by
  intro i j h'
  simp [MessageIdx.cast] at h'
  ext : 1
  exact h'

instance instDCast₂ : DCast₂ Nat ProtocolSpec (fun _ pSpec => MessageIdx pSpec) where
  dcast₂ h := MessageIdx.cast h
  dcast₂_id := cast_id

theorem cast_eq_dcast₂ {hn} {hSpec : pSpec₁.cast hn = pSpec₂} {i : MessageIdx pSpec₁}:
    i.cast hn hSpec = dcast₂ hn hSpec i := rfl

end MessageIdx

namespace Message

@[simp]
theorem cast_idx {i : MessageIdx pSpec₂} :
    pSpec₁.Message (i.cast hn.symm (cast_symm hSpec)) = pSpec₂.Message i := by
  simp [MessageIdx.cast]
  exact congrArg Prod.snd (cast_idx_symm hSpec)

instance [inst : ∀ i, OracleInterface (pSpec₁.Message i)] :
    ∀ i, OracleInterface ((pSpec₁.cast hn).Message i) :=
  fun i => inst (dcast₂ hn.symm (by rw [dcast_symm hn]; rfl) i)

end Message

namespace ChallengeIdx

/-- Casting a challenge index across an equality of `ProtocolSpec`s. -/
protected def cast (i : ChallengeIdx pSpec₁) : ChallengeIdx pSpec₂ :=
  ⟨Fin.cast hn i.1, by simp [← hSpec, ProtocolSpec.cast, i.property]⟩

@[simp]
theorem cast_id : ChallengeIdx.cast (Eq.refl n₁) rfl = (id : pSpec₁.ChallengeIdx → _) := rfl

theorem cast_injective : Function.Injective (ChallengeIdx.cast hn hSpec) := by
  intro i j h'
  simp [ChallengeIdx.cast] at h'
  ext : 1
  exact h'

instance instDCast₂ : DCast₂ Nat ProtocolSpec (fun _ pSpec => ChallengeIdx pSpec) where
  dcast₂ h := ChallengeIdx.cast h
  dcast₂_id := cast_id

theorem cast_eq_dcast₂ {hn} {hSpec : pSpec₁.cast hn = pSpec₂} {i : ChallengeIdx pSpec₁}:
    i.cast hn hSpec = dcast₂ hn hSpec i := rfl

end ChallengeIdx

@[simp]
theorem Challenge.cast_idx {i : ChallengeIdx pSpec₂} :
    pSpec₁.Challenge (i.cast hn.symm (cast_symm hSpec)) = pSpec₂.Challenge i := by
  simp [ChallengeIdx.cast]
  exact congrArg Prod.snd (cast_idx_symm hSpec)

variable {k : Fin (n₁ + 1)} {l : Fin (n₂ + 1)}

namespace Transcript

/-- Casting two partial transcripts across an equality of `ProtocolSpec`s, where the cutoff indices
  are equal. -/
protected def cast (hIdx : k.val = l.val) (hSpec : pSpec₁.cast hn = pSpec₂)
    (T : pSpec₁.Transcript k) : pSpec₂.Transcript l :=
  fun i => _root_.cast (by rw [← hSpec]; rfl) (T (Fin.cast hIdx.symm i))

@[simp]
theorem cast_id : Transcript.cast rfl rfl rfl = (id : pSpec₁.Transcript k → _) := rfl

instance instDCast₃ : DCast₃ Nat (fun n => Fin (n + 1)) (fun n _ => ProtocolSpec n)
    (fun _ k pSpec => pSpec.Transcript k) where
  dcast₃ h h' h'' T := Transcript.cast h
    (by simp only [dcast] at h'; rw [← h']; sorry)
    (by simp [ProtocolSpec.cast_eq_dcast, dcast_eq_root_cast]; exact h'')
    T
  dcast₃_id := cast_id

-- theorem cast_eq_dcast₃ (h : m = n) (hIdx : k.val = l.val) (hSpec : pSpec₁.cast h = pSpec₂)
--     (T : Transcript pSpec₁ k) :
--     T.cast h hIdx hSpec  = (dcast₃ h (by sorry) sorry T : pSpec₂.Transcript l) := rfl

end Transcript

namespace FullTranscript

/-! ### Casting Full Transcripts -/

/-- Casting a transcript across an equality of `ProtocolSpec`s.

Internally invoke `Transcript.cast` with the last indices. -/
protected def cast (T : FullTranscript pSpec₁) :
    FullTranscript pSpec₂ :=
  Transcript.cast (k := Fin.last n₁) (l := Fin.last n₂) hn hn hSpec T

@[simp]
theorem cast_id : FullTranscript.cast rfl rfl = (id : pSpec₁.FullTranscript → _) := rfl

instance instDCast₂ : DCast₂ Nat ProtocolSpec (fun _ pSpec => FullTranscript pSpec) where
  dcast₂ h h' T := FullTranscript.cast h h' T
  dcast₂_id := cast_id

theorem cast_eq_dcast₂ {T : FullTranscript pSpec₁} :
    dcast₂ hn hSpec T = FullTranscript.cast hn hSpec T := rfl

end FullTranscript

end ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n₁ n₂ : ℕ} {pSpec₁ : ProtocolSpec n₁} {pSpec₂ : ProtocolSpec n₂}
  (hn : n₁ = n₂) (hSpec : pSpec₁.cast hn = pSpec₂)

open ProtocolSpec

namespace Prover

/-- Casting the prover of a non-oracle reduction across an equality of `ProtocolSpec`s. -/
protected def cast (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₂ where
  PrvState := P.PrvState ∘ Fin.cast (congrArg (· + 1) hn.symm)
  input := P.input
  sendMessage := fun i st => do
    let ⟨msg, newSt⟩ ← P.sendMessage (i.cast hn.symm (cast_symm hSpec)) st
    return ⟨(Message.cast_idx hn hSpec) ▸ msg, newSt⟩
  receiveChallenge := fun i st => do
    let f ← P.receiveChallenge (i.cast hn.symm (cast_symm hSpec)) st
    return fun chal => f (Challenge.cast_idx hn hSpec ▸ chal)
  output := P.output ∘ (fun st => _root_.cast (by simp) st)

@[simp]
theorem cast_id :
    Prover.cast rfl rfl = (id : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁ → _) := by
  funext; simp [Prover.cast]; ext <;> simp; rfl

instance instDCast₂ : DCast₂ Nat ProtocolSpec
    (fun _ pSpec => Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  dcast₂ := Prover.cast
  dcast₂_id := Prover.cast_id

end Prover

namespace OracleProver

/-- Casting the oracle prover of a non-oracle reduction across an equality of `ProtocolSpec`s.

Internally invokes the `Prover.cast` function. -/
protected def cast (P : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁) :
    OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₂ :=
  Prover.cast hn hSpec P

@[simp]
theorem cast_id :
    OracleProver.cast rfl rfl =
      (id : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁ → _) := by
  sorry

instance instDCast₂OracleProver : DCast₂ Nat ProtocolSpec
    (fun _ pSpec => OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) where
  dcast₂ := OracleProver.cast
  dcast₂_id := OracleProver.cast_id

end OracleProver

namespace Verifier

/-- Casting the verifier of a non-oracle reduction across an equality of `ProtocolSpec`s.

This boils down to casting the (full) transcript. -/
protected def cast (V : Verifier oSpec StmtIn StmtOut pSpec₁) :
    Verifier oSpec StmtIn StmtOut pSpec₂ where
  verify := fun stmt transcript => V.verify stmt (dcast₂ hn.symm (dcast_symm hn hSpec) transcript)

@[simp]
theorem cast_id : Verifier.cast rfl rfl = (id : Verifier oSpec StmtIn StmtOut pSpec₁ → _) := by
  ext; simp [Verifier.cast]

instance instDCast₂Verifier :
    DCast₂ Nat ProtocolSpec (fun _ pSpec => Verifier oSpec StmtIn StmtOut pSpec) where
  dcast₂ := Verifier.cast
  dcast₂_id := by intros; funext; simp

theorem cast_eq_dcast₂ {V : Verifier oSpec StmtIn StmtOut pSpec₁} :
    V.cast hn hSpec = dcast₂ hn hSpec V := rfl

end Verifier

namespace OracleVerifier

open OracleComp Function

variable [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, OracleInterface (pSpec₂.Message i)]

/-- Casting the oracle verifier of a non-oracle reduction across an equality of `ProtocolSpec`s.

TODO: need a cast of the oracle interfaces as well (i.e. the oracle interface instance is not
necessarily unique for every type) -/
protected def cast (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁) :
    OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₂ where
  verify := fun stmt challenges =>
    simulateQ sorry (V.verify stmt (dcast₂ hn.symm (dcast_symm hn hSpec) challenges))
  embed := V.embed.trans
    (Embedding.sumMap
      (Equiv.refl _).toEmbedding
      ⟨MessageIdx.cast hn hSpec, MessageIdx.cast_injective hn hSpec⟩)
  hEq := fun i => by
    simp [Embedding.sumMap, Equiv.refl]
    have := V.hEq i
    rw [this]
    split
    next a b h' => simp [h']
    next a b h' => simp [h', MessageIdx.cast]; congr; exact (cast_idx hn hSpec).symm

@[simp]
theorem cast_id :
    OracleVerifier.cast rfl rfl =
      (id : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁ → _) := by
  sorry

-- Need to cast oracle interface as well
-- instance instDCast₂OracleVerifier : DCast₃ Nat ProtocolSpec
--     (fun _ pSpec => OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) where
--   dcast₂ := OracleVerifier.cast
--   dcast₂_id := OracleVerifier.cast_id

end OracleVerifier

namespace Reduction

/-- Casting the reduction of a non-oracle reduction across an equality of `ProtocolSpec`s, which
  casts the underlying prover and verifier. -/
protected def cast (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₂ where
  prover := R.prover.cast hn hSpec
  verifier := R.verifier.cast hn hSpec

@[simp]
theorem cast_id :
    Reduction.cast rfl rfl = (id : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁ → _) := by
  funext; simp [Reduction.cast]

instance instDCast₂Reduction :
    DCast₂ Nat ProtocolSpec (fun _ pSpec => Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  dcast₂ := Reduction.cast
  dcast₂_id := Reduction.cast_id

end Reduction

namespace OracleReduction

variable [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, OracleInterface (pSpec₂.Message i)]

/-- Casting the oracle reduction across an equality of `ProtocolSpec`s, which casts the underlying
  prover and verifier. -/
protected def cast (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁) :
    OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₂ where
  prover := R.prover.cast hn hSpec
  verifier := R.verifier.cast hn hSpec

@[simp]
theorem cast_id :
    OracleReduction.cast rfl rfl =
      (id : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁ → _) := by
  ext : 2 <;> simp [OracleReduction.cast]

-- Need to cast oracle interface as well
-- instance instDCast₂OracleReduction :
--     DCast₂ Nat ProtocolSpec
--     (fun _ pSpec => OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
-- where
--   dcast₂ := OracleReduction.cast
--   dcast₂_id := OracleReduction.cast_id

end OracleReduction
