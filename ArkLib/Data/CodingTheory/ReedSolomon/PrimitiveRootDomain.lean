/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Evaluation domains of powers of a primitive root of unity

For a primitive `n`-th root of unity `ω`, the powers `ω ^ i` with `i < n` are pairwise distinct,
so they form an evaluation domain `Fin n ↪ M`. This is the domain of a Reed--Solomon code on the
multiplicative subgroup of order `n`.

## Main definitions

* `ReedSolomon.primitiveRootDomain`: the domain `(ωⁱ)_{i < n}`.
-/

@[expose] public section

namespace ReedSolomon

variable {M : Type*} [CommMonoid M] {ω : M} {n : ℕ}

/-- The evaluation domain `(ωⁱ)_{i < n}` of powers of a primitive `n`-th root of unity `ω`. -/
def primitiveRootDomain (hω : IsPrimitiveRoot ω n) : Fin n ↪ M :=
  ⟨fun i ↦ ω ^ (i : ℕ), fun i j h ↦ Fin.ext (hω.pow_inj i.isLt j.isLt h)⟩

/-- The `i`-th point of `primitiveRootDomain hω` is `ω ^ i`. -/
@[simp]
theorem primitiveRootDomain_apply (hω : IsPrimitiveRoot ω n) (i : Fin n) :
    primitiveRootDomain hω i = ω ^ (i : ℕ) := rfl

end ReedSolomon
