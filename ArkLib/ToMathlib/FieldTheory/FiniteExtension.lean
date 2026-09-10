/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Data.Nat.Log
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Sufficiently large extensions of finite fields

Mathlib provides `FiniteField.Extension k p n`, a chosen degree-`n` extension of a finite field
`k` of characteristic `p`. This file chooses an explicit positive degree whose extension has more
than a prescribed number of elements. The construction changes cardinality but preserves
characteristic; this distinction matters in characteristic-sensitive root-counting arguments.
-/

@[expose] public section

namespace FiniteField

noncomputable section

variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-! ### Fixed-degree extensions -/

/-- A fixed positive extension degree gives an extension of exact cardinality `|k| ^ degree`.
The explicit largeness hypothesis is retained so quantitative callers can choose `degree`
independently of the bound they ultimately prove. -/
theorem extension_spec_of_lt_pow (degree bound : ℕ) [NeZero degree]
    (hlarge : bound < Nat.card k ^ degree) :
    0 < degree ∧
      Nat.card (Extension k p degree) = Nat.card k ^ degree ∧
      bound < Nat.card (Extension k p degree) ∧
      ringChar (Extension k p degree) = ringChar k := by
  refine ⟨NeZero.pos degree, natCard_extension k p degree, ?_, ?_⟩
  · rwa [natCard_extension]
  · exact (Algebra.ringChar_eq k (Extension k p degree)).symm

/-! ### A coarse bound-dependent choice -/

/-- A positive extension degree for which the resulting finite field has cardinality strictly
larger than `bound`.

This is an existence-oriented choice. Its degree depends on `bound`, so it must not be used by
itself to claim a fixed-power quantitative estimate such as `|k| ^ (4 * d + 6)`. Such estimates
should instead choose a fixed `degree` and invoke `extension_spec_of_lt_pow`. -/
def extensionDegreeAbove (bound : ℕ) : ℕ :=
  (Nat.log (Nat.card k) bound).succ

instance (bound : ℕ) : NeZero (extensionDegreeAbove k bound) :=
  ⟨Nat.succ_ne_zero _⟩

/-- The chosen finite extension of `k` with more than `bound` elements. -/
abbrev ExtensionAbove (bound : ℕ) : Type :=
  Extension k p (extensionDegreeAbove k bound)

omit [Field k] [Finite k] in
theorem extensionDegreeAbove_pos (bound : ℕ) : 0 < extensionDegreeAbove k bound := by
  simp [extensionDegreeAbove]

/-- Exact cardinality of the chosen sufficiently large extension. -/
theorem natCard_extensionAbove (bound : ℕ) :
    Nat.card (ExtensionAbove k p bound) = Nat.card k ^ extensionDegreeAbove k bound := by
  exact natCard_extension k p (extensionDegreeAbove k bound)

/-- The chosen extension has strictly more elements than the requested bound. -/
theorem lt_natCard_extensionAbove (bound : ℕ) :
    bound < Nat.card (ExtensionAbove k p bound) := by
  rw [natCard_extensionAbove]
  exact Nat.lt_pow_succ_log_self Finite.one_lt_card bound

/-- Exact degree of the chosen sufficiently large extension. -/
theorem finrank_extensionAbove (bound : ℕ) :
    Module.finrank k (ExtensionAbove k p bound) = extensionDegreeAbove k bound := by
  exact finrank_extension k p (extensionDegreeAbove k bound)

/-- Passing to the chosen extension preserves the base field's characteristic. -/
theorem charP_extensionAbove (bound : ℕ) : CharP (ExtensionAbove k p bound) p := by
  exact charP_of_injective_algebraMap (algebraMap k (ExtensionAbove k p bound)).injective p

/-! ### Boundary canaries -/

/-- The successor in `extensionDegreeAbove` is essential even at the zero bound. -/
example : extensionDegreeAbove (ZMod 2) 0 = 1 := by
  simp [extensionDegreeAbove, Nat.log_zero_right]

/-- The first extension strictly larger than `2` over `ZMod 2` has degree two and four elements. -/
example : Nat.card (ExtensionAbove (ZMod 2) 2 2) = 4 := by
  have hlog : Nat.log 2 2 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [natCard_extensionAbove, Nat.card_zmod]
  simp [extensionDegreeAbove, hlog]

/-- Enlarging a field never improves characteristic: this four-element extension still has
characteristic two. -/
example : ringChar (ExtensionAbove (ZMod 2) 2 2) = 2 := by
  rw [← Algebra.ringChar_eq (ZMod 2) (ExtensionAbove (ZMod 2) 2 2)]
  exact ZMod.ringChar_zmod_n 2

end

end FiniteField
