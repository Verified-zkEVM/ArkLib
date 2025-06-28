/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Casting for structures of oracle reductions

  We define custom dependent casts (registered as `DepCast` instances) for the following structures:
  - `ProtocolSpec`
  - `(Full)Transcript`
  - `(Oracle)Prover`
  - `(Oracle)Verifier`
  - `(Oracle)Reduction`
-/

/-! ### Casting Protocol Specifications -/

namespace ProtocolSpec

variable {m n : ℕ}

/-- Casting a `ProtocolSpec` across an equality of the number of rounds

One should use the type-class function `dcast` instead of this one. -/
protected def cast (h : m = n) (pSpec : ProtocolSpec m) : ProtocolSpec n :=
  pSpec ∘ (Fin.cast h.symm)

@[simp]
theorem cast_id : ProtocolSpec.cast (Eq.refl n) = id := rfl

instance instDepCast : DepCast Nat ProtocolSpec where
  dcast h := ProtocolSpec.cast h
  dcast_id := cast_id

theorem cast_eq_dcast (h : m = n) (pSpec : ProtocolSpec m) :
    dcast h pSpec = ProtocolSpec.cast h pSpec := rfl

/-! ### Casting (Partial) Transcripts -/

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} {k : Fin (m + 1)} {l : Fin (n + 1)}

namespace Transcript

/-- Casting two partial transcripts across an equality of `ProtocolSpec`s, where the cutoff indices
  are equal. -/
protected def cast (h : m = n) (hIdx : k.val = l.val) (hSpec : dcast h pSpec₁ = pSpec₂)
    (T : pSpec₁.Transcript k) : pSpec₂.Transcript l :=
  fun i => _root_.cast (by rw [← hSpec]; rfl) (T (Fin.cast hIdx.symm i))

@[simp]
theorem cast_id : Transcript.cast rfl rfl rfl = (id : pSpec₁.Transcript k → _) := rfl

instance instDepCast₃ : DepCast₃ Nat Fin (fun n _ => ProtocolSpec n)
    (fun _ k pSpec => pSpec.Transcript k) where
  dcast₃ h h' h'' T := Transcript.cast h
    (by simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc]; simp only [dcast] at h'; rw [← h']; rfl)
    (by simp [← ProtocolSpec.cast_eq_dcast, dcast_eq_root_cast]; exact h'')
    T
  dcast₃_id := cast_id

-- theorem cast_eq_dcast₃ (h : m = n) (hIdx : k.val = l.val) (hSpec : dcast h pSpec₁ = pSpec₂)
--     (T : Transcript pSpec₁ k) :
--     (dcast₃ h (by sorry) sorry T : pSpec₂.Transcript l) = Transcript.cast h hIdx hSpec T := rfl

end Transcript

namespace FullTranscript

/-! ### Casting Full Transcripts -/

/-- Casting a transcript across an equality of `ProtocolSpec`s.

Internally invoke `Transcript.cast` with the last indices. -/
protected def cast (h : m = n) (hSpec : dcast h pSpec₁ = pSpec₂) (T : FullTranscript pSpec₁) :
    FullTranscript pSpec₂ :=
  Transcript.cast (k := Fin.last m) (l := Fin.last n) h h hSpec T

@[simp]
theorem cast_id : FullTranscript.cast rfl rfl = (id : pSpec₁.FullTranscript → _) := rfl

instance instDepCast₂ : DepCast₂ Nat ProtocolSpec (fun _ pSpec => FullTranscript pSpec) where
  dcast₂ h h' T := FullTranscript.cast h h' T
  dcast₂_id := cast_id

theorem cast_eq_dcast₂ (h : m = n) (hSpec : dcast h pSpec₁ = pSpec₂) (T : FullTranscript pSpec₁) :
    dcast₂ h hSpec T = FullTranscript.cast h hSpec T := rfl

end FullTranscript

end ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-! ### Casting Provers -/

namespace Prover

/-- Casting the prover of a non-oracle reduction across an equality of `ProtocolSpec`s. -/
def cast
    (h : m = n) (hSpec : dcast h pSpec₁ = pSpec₂)
    (V : Verifier oSpec StmtIn StmtOut pSpec₁) :
    Verifier oSpec StmtIn StmtOut pSpec₂ where
  verify := fun stmt transcript => V.verify stmt (dcast₂ h.symm (dcast_symm h hSpec) transcript)


end Prover

/-! ### Casting Verifiers -/

namespace Verifier

/-- Casting the verifier of a non-oracle reduction across an equality of `ProtocolSpec`s.

This boils down to casting the (full) transcript. -/
def cast
    (h : m = n) (hSpec : dcast h pSpec₁ = pSpec₂)
    (V : Verifier oSpec StmtIn StmtOut pSpec₁) :
    Verifier oSpec StmtIn StmtOut pSpec₂ where
  verify := fun stmt transcript => V.verify stmt (dcast₂ h.symm (dcast_symm h hSpec) transcript)

@[simp]
def cast_id
    (V : Verifier oSpec StmtIn StmtOut pSpec₁) :
      V.cast rfl rfl = V := by
  ext; simp [Verifier.cast]

instance instDepCast₂Verifier :
    DepCast₂ Nat ProtocolSpec (fun _ pSpec => Verifier oSpec StmtIn StmtOut pSpec) where
  dcast₂ := Verifier.cast
  dcast₂_id := by intros; funext; simp

end Verifier
