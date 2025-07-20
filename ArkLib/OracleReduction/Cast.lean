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

variable {m n : ℕ} (h : m = n)

/-! ### Casting Protocol Specifications -/

/-- Casting a `ProtocolSpec` across an equality of the number of rounds

One should use the type-class function `dcast` instead of this one. -/
protected def cast (pSpec : ProtocolSpec m) : ProtocolSpec n :=
  pSpec ∘ (Fin.cast h.symm)

@[simp]
theorem cast_id : ProtocolSpec.cast (Eq.refl m) = id := rfl

instance instDCast : DCast Nat ProtocolSpec where
  dcast h := ProtocolSpec.cast h
  dcast_id := cast_id

theorem cast_eq_dcast {h : m = n} {pSpec : ProtocolSpec m} :
    pSpec.cast h = dcast h pSpec := rfl

/-! ### Casting (Partial) Transcripts -/

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

@[simp]
theorem cast_funext {h} (hSpec : pSpec₁.cast h = pSpec₂) {i : Fin n} :
    pSpec₁ (Fin.cast h.symm i) = pSpec₂ i := funext_iff.mp hSpec i

alias cast_idx := cast_funext

theorem cast_symm {h} (hSpec : pSpec₁.cast h = pSpec₂) : pSpec₂.cast h.symm = pSpec₁ := by
  rw [cast_eq_dcast] at hSpec ⊢
  exact dcast_symm h hSpec

variable (hSpec : pSpec₁.cast h = pSpec₂)

namespace MessageIdx

/-- Casting a message index across an equality of `ProtocolSpec`s. -/
protected def cast (i : MessageIdx pSpec₁) : MessageIdx pSpec₂ :=
  ⟨Fin.cast h i.1, by simp [← hSpec, ProtocolSpec.cast, i.property]⟩

@[simp]
theorem cast_id : MessageIdx.cast (Eq.refl m) rfl = (id : pSpec₁.MessageIdx → _) := rfl

instance instDCast₂ : DCast₂ Nat ProtocolSpec (fun _ pSpec => MessageIdx pSpec) where
  dcast₂ h := MessageIdx.cast h
  dcast₂_id := cast_id

theorem cast_eq_dcast₂ {h} {hSpec : pSpec₁.cast h = pSpec₂} {i : MessageIdx pSpec₁}:
    i.cast h hSpec = dcast₂ h hSpec i := rfl

end MessageIdx

@[simp]
theorem Message.cast_idx {i : MessageIdx pSpec₂} :
    pSpec₁.Message (i.cast h.symm (cast_symm hSpec)) = pSpec₂.Message i := by
  simp [MessageIdx.cast]
  exact congrArg Prod.snd (cast_funext hSpec)

namespace ChallengeIdx

/-- Casting a challenge index across an equality of `ProtocolSpec`s. -/
protected def cast (i : ChallengeIdx pSpec₁) : ChallengeIdx pSpec₂ :=
  ⟨Fin.cast h i.1, by simp [← hSpec, ProtocolSpec.cast, i.property]⟩

@[simp]
theorem cast_id : ChallengeIdx.cast (Eq.refl m) rfl = (id : pSpec₁.ChallengeIdx → _) := rfl

instance instDCast₂ : DCast₂ Nat ProtocolSpec (fun _ pSpec => ChallengeIdx pSpec) where
  dcast₂ h := ChallengeIdx.cast h
  dcast₂_id := cast_id

theorem cast_eq_dcast₂ {h : m = n} {hSpec : pSpec₁.cast h = pSpec₂} {i : ChallengeIdx pSpec₁}:
    i.cast h hSpec = dcast₂ h hSpec i := rfl

end ChallengeIdx

@[simp]
theorem Challenge.cast_idx {i : ChallengeIdx pSpec₂} :
    pSpec₁.Challenge (i.cast h.symm (cast_symm hSpec)) = pSpec₂.Challenge i := by
  simp [ChallengeIdx.cast]
  exact congrArg Prod.snd (cast_funext hSpec)

variable {k : Fin (m + 1)} {l : Fin (n + 1)}

namespace Transcript

/-- Casting two partial transcripts across an equality of `ProtocolSpec`s, where the cutoff indices
  are equal. -/
protected def cast (hIdx : k.val = l.val) (hSpec : pSpec₁.cast h = pSpec₂)
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
  Transcript.cast (k := Fin.last m) (l := Fin.last n) h h hSpec T

@[simp]
theorem cast_id : FullTranscript.cast rfl rfl = (id : pSpec₁.FullTranscript → _) := rfl

instance instDCast₂ : DCast₂ Nat ProtocolSpec (fun _ pSpec => FullTranscript pSpec) where
  dcast₂ h h' T := FullTranscript.cast h h' T
  dcast₂_id := cast_id

theorem cast_eq_dcast₂ {T : FullTranscript pSpec₁} :
    dcast₂ h hSpec T = FullTranscript.cast h hSpec T := rfl

end FullTranscript

end ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
variable (h : m = n) (hSpec : pSpec₁.cast h = pSpec₂)

open ProtocolSpec

/-! ### Casting Provers -/

namespace Prover

/-- Casting the prover of a non-oracle reduction across an equality of `ProtocolSpec`s. -/
protected def cast (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₂ where
  PrvState := P.PrvState ∘ Fin.cast (congrArg (· + 1) h.symm)
  input := P.input
  sendMessage := fun i st => do
    let ⟨msg, newSt⟩ ← P.sendMessage (i.cast h.symm (cast_symm hSpec)) st
    return ⟨(Message.cast_idx h hSpec) ▸ msg, newSt⟩
  receiveChallenge := fun i st chal =>
    P.receiveChallenge (i.cast h.symm (cast_symm hSpec)) st ((Challenge.cast_idx h hSpec) ▸ chal)
  output := P.output ∘ (fun st => _root_.cast (by simp) st)

end Prover

/-! ### Casting Verifiers -/

namespace Verifier

/-- Casting the verifier of a non-oracle reduction across an equality of `ProtocolSpec`s.

This boils down to casting the (full) transcript. -/
protected def cast (V : Verifier oSpec StmtIn StmtOut pSpec₁) :
    Verifier oSpec StmtIn StmtOut pSpec₂ where
  verify := fun stmt transcript => V.verify stmt (dcast₂ h.symm (dcast_symm h hSpec) transcript)

@[simp]
theorem cast_id : Verifier.cast rfl rfl = (id : Verifier oSpec StmtIn StmtOut pSpec₁ → _) := by
  ext; simp [Verifier.cast]

instance instDCast₂Verifier :
    DCast₂ Nat ProtocolSpec (fun _ pSpec => Verifier oSpec StmtIn StmtOut pSpec) where
  dcast₂ := Verifier.cast
  dcast₂_id := by intros; funext; simp

theorem cast_eq_dcast₂ {V : Verifier oSpec StmtIn StmtOut pSpec₁} :
    V.cast h hSpec = dcast₂ h hSpec V := rfl

end Verifier

namespace Reduction

/-- Casting the reduction of a non-oracle reduction across an equality of `ProtocolSpec`s, which
  casts the underlying prover and verifier. -/
protected def cast (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₂ where
  prover := R.prover.cast h hSpec
  verifier := R.verifier.cast h hSpec

@[simp]
def cast_id {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁} :
      R.cast rfl rfl = R := by
  ext : 1 <;> simp [Reduction.cast, Prover.cast, Verifier.cast]
  rfl

instance instDCast₂Verifier :
    DCast₂ Nat ProtocolSpec (fun _ pSpec => Verifier oSpec StmtIn StmtOut pSpec) where
  dcast₂ := Verifier.cast
  dcast₂_id := by intros; funext; simp

end Reduction
