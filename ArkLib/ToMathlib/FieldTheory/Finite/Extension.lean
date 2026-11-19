/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.FieldTheory.Finite.Extension

/-!
# Finite extensions of finite fields with a basis of any size

Every finite field has a finite extension of each positive degree.
So it has an extension with a basis of any positive size over the base field.
Packing tuples along such a basis turns `t` rows over the base field into one row.

## Main statements

* `FiniteField.exists_basis_fin`: a finite field has a finite extension with a basis of any
  positive size.
-/

@[expose] public section

namespace FiniteField

/-- A finite field `K` has a finite extension with a basis of size `t`, for every `t ≠ 0`. -/
theorem exists_basis_fin (K : Type*) [Field K] [Finite K] {t : ℕ} (ht : t ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : Algebra K E),
      Nonempty (Module.Basis (Fin t) K E) := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have : NeZero t := ⟨ht⟩
  exact ⟨Extension K p t, inferInstance, inferInstance, inferInstance,
    ⟨Module.finBasisOfFinrankEq K _ (finrank_extension K p t)⟩⟩

end FiniteField
