/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Extensions of finite fields inside an algebraically closed field

Let `K₀` be a finite field and `k` a positive integer.
A finite field `L` of degree `k` over `K₀` exists.
It embeds over `K₀` into every algebraically closed field `E` containing `K₀`.

Mathlib's chosen extension needs the characteristic of `K₀` as an argument.
The statement here hides it.

Such an embedding makes `E` an algebra over `L`.
That algebra is a local instance, built from the embedding.
The tower `K₀ ⊆ L ⊆ E` then commutes by a Mathlib instance.
A global instance would clash with the algebra of `E` over `K₀`.

## Main statements

* `FiniteField.exists_algHom_of_finrank_eq`: a degree-`k` extension of `K₀` embeds into `E`.
-/

@[expose] public section

namespace FiniteField

/-- Let `K₀` be a finite field, `E` an algebraically closed field over `K₀`, and `k ≠ 0`.
Some finite field `L` has degree `k` over `K₀` and embeds into `E` over `K₀`. -/
theorem exists_algHom_of_finrank_eq (K₀ : Type*) [Field K₀] [Finite K₀] (E : Type*) [Field E]
    [Algebra K₀ E] [IsAlgClosed E] {k : ℕ} (hk : k ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K₀ L) (_ : Finite L),
      Module.finrank K₀ L = k ∧ Nonempty (L →ₐ[K₀] E) := by
  obtain ⟨p, hp⟩ := CharP.exists K₀
  have : Fact p.Prime := ⟨CharP.char_is_prime K₀ p⟩
  have : NeZero k := ⟨hk⟩
  exact ⟨Extension K₀ p k, inferInstance, inferInstance, inferInstance, finrank_extension K₀ p k,
    ⟨IsAlgClosed.lift⟩⟩

end FiniteField
