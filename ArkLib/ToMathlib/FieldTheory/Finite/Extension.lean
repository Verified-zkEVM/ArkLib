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

The characteristic of a finite field is prime, as a scoped instance in `FiniteField`.
After `open scoped FiniteField`, the extension at the characteristic gets its field instances by
instance search.
The instance is scoped because Mathlib's library note «fact non-instances» advises against global
`Fact` instances; Mathlib states this fact locally, as in `Mathlib.FieldTheory.Finite.Trace`.

`FiniteField.Extension.finBasis` is noncomputable.
Mathlib's `FiniteField.Extension` chooses its algebra map from the base field with
`Nonempty.some`, and `Module.finBasisOfFinrankEq` chooses a basis with classical choice.

## Main definitions

* `FiniteField.Extension.finBasis`: a basis of the degree-`t` extension, indexed by `Fin t`.
-/

@[expose] public section

namespace FiniteField

variable (K : Type*) [Field K] [Finite K]

/-- The characteristic of a finite field is prime. -/
scoped instance fact_prime_ringChar : Fact (ringChar K).Prime :=
  ⟨CharP.char_is_prime K _⟩

/-- A basis of the degree-`t` extension of a finite field `K`, indexed by `Fin t`. -/
noncomputable def Extension.finBasis (t : ℕ) [NeZero t] :
    Module.Basis (Fin t) K (Extension K (ringChar K) t) :=
  Module.finBasisOfFinrankEq K _ (finrank_extension K (ringChar K) t)

end FiniteField
