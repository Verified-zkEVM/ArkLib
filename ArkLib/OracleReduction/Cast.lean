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

section Cast

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

end Cast

namespace FullTranscript

/-! ### Casting Full Transcripts -/

section Cast

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Casting a transcript across an equality of `ProtocolSpec`s -/
protected def cast (h : m = n) (hSpec : dcast h pSpec₁ = pSpec₂) (T : FullTranscript pSpec₁) :
    FullTranscript pSpec₂ :=
  fun i => _root_.cast (congrFun (congrArg getType hSpec) i) (T (Fin.cast h.symm i))

@[simp]
theorem cast_id : FullTranscript.cast rfl rfl = (id : pSpec₁.FullTranscript → _) := rfl

instance instDepCast₂ : DepCast₂ Nat ProtocolSpec (fun _ pSpec => FullTranscript pSpec) where
  dcast₂ h h' T := FullTranscript.cast h h' T
  dcast₂_id := cast_id

theorem cast_eq_dcast₂ (h : m = n) (hSpec : dcast h pSpec₁ = pSpec₂) (T : FullTranscript pSpec₁) :
    dcast₂ h hSpec T = FullTranscript.cast h hSpec T := rfl

end Cast

end FullTranscript

end ProtocolSpec

/-! ### Casting Verifiers -/

section Cast

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- To cast the verifier, we only need to cast the transcript. -/
def Verifier.cast
    (h : m = n) (hSpec : dcast h pSpec₁ = pSpec₂)
    (V : Verifier oSpec StmtIn StmtOut pSpec₁) :
    Verifier oSpec StmtIn StmtOut pSpec₂ where
  verify := fun stmt transcript => V.verify stmt (dcast₂ h.symm (dcast_symm h hSpec) transcript)

@[simp]
def Verifier.cast_id
    (V : Verifier oSpec StmtIn StmtOut pSpec₁) :
      V.cast rfl rfl = V := by
  ext; simp [Verifier.cast]

instance instDepCast₂Verifier :
    DepCast₂ Nat ProtocolSpec (fun _ pSpec => Verifier oSpec StmtIn StmtOut pSpec) where
  dcast₂ := Verifier.cast
  dcast₂_id := by intros; funext; simp

end Cast
