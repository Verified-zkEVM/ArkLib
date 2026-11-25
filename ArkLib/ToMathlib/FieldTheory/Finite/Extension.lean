/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.FieldTheory.Finite.Extension

/-!
# A basis of the degree-`t` extension of a finite field

Every finite field has a finite extension of each positive degree.
That extension has a basis indexed by `Fin t` over the base field.
Packing tuples along such a basis turns `t` rows over the base field into one row.

The characteristic of a finite field is prime, as an instance.
So the extension at the characteristic gets its field instances by instance search.

## Main definitions

* `FiniteField.Extension.finBasis`: a basis of the degree-`t` extension, indexed by `Fin t`.
-/

@[expose] public section

namespace FiniteField

variable (K : Type*) [Field K] [Finite K]

/-- The characteristic of a finite field is prime. -/
instance fact_prime_ringChar : Fact (ringChar K).Prime :=
  ⟨CharP.char_is_prime K _⟩

/-- A basis of the degree-`t` extension of a finite field `K`, indexed by `Fin t`. -/
noncomputable def Extension.finBasis (t : ℕ) [NeZero t] :
    Module.Basis (Fin t) K (Extension K (ringChar K) t) :=
  Module.finBasisOfFinrankEq K _ (finrank_extension K (ringChar K) t)

end FiniteField
