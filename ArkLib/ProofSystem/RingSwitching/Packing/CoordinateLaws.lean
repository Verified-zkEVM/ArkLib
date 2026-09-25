/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude

/-!
# Proved coordinate conditions for tensor packing

These conditions are separate from the general profile data. The tensor profile satisfies
them; generic packing clients need not supply them unless they use the corresponding proofs.
They are DP24 tensor-coordinate conditions, not universal ring-switching laws. In particular,
Hachi's trace/automorphism switch requires different reconstruction identities and is not
claimed to satisfy these conditions.
-/

@[expose] public section

namespace RingSwitching

open Module TensorProduct

/-- Coordinate identities needed by tensor-packing proofs, not by arbitrary profile data. -/
structure CoordinateLaws {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    {κ : ℕ} (P : RingSwitchingProfile K L κ) : Prop where
  rows_add : ∀ x y, P.decomposeRows (x + y) = P.decomposeRows x + P.decomposeRows y
  columns_add : ∀ x y,
    P.decomposeColumns (x + y) = P.decomposeColumns x + P.decomposeColumns y
  rows_mul : ∀ x y, P.decomposeRows (P.φ₀ x * P.φ₁ y) =
    fun u => algebraMap K L (P.basis.repr x u) * y
  columns_mul : ∀ x y, P.decomposeColumns (P.φ₀ x * P.φ₁ y) =
    fun u => x * algebraMap K L (P.basis.repr y u)

namespace RingSwitchingProfile

variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
  {κ : ℕ} (P : RingSwitchingProfile K L κ)

/-- Reconstruction alone makes the row-coordinate map injective. -/
theorem rows_injective : Function.Injective P.decomposeRows := by
  intro x y h
  rw [P.decomposeRows_spec x, P.decomposeRows_spec y, h]

/-- Reconstruction alone makes the column-coordinate map injective. -/
theorem columns_injective : Function.Injective P.decomposeColumns := by
  intro x y h
  rw [P.decomposeColumns_spec x, P.decomposeColumns_spec y, h]

end RingSwitchingProfile

/-- The actual tensor coordinates satisfy the packing identities. -/
theorem tensorProductProfile_coordinateLaws (κ : ℕ) [NeZero κ] (K L : Type)
    [Field K] [Field L] [Algebra K L] (β : Basis (Fin κ → Fin 2) K L) :
    CoordinateLaws (tensorProductProfile κ K L β) where
  rows_add := by
    intro x y
    funext u
    simp [tensorProductProfile, decompose_tensor_algebra_rows]
  columns_add := by
    intro x y
    funext u
    simp [tensorProductProfile, decompose_tensor_algebra_columns]
  rows_mul := by
    intro x y
    funext u
    simp [tensorProductProfile, φ₀, φ₁, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.smul_def]
  columns_mul := by
    intro x y
    funext u
    simp [tensorProductProfile, φ₀, φ₁, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.smul_def, mul_comm]

end RingSwitching
