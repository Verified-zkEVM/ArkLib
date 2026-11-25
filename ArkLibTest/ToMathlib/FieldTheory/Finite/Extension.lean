/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.ToMathlib.FieldTheory.Finite.Extension

/-! # Acceptance cases for the basis of a finite-field extension -/

-- Over any finite field, the field and module instances of the extension are found,
-- and the basis gives it `q³` elements.
example (K : Type) [Field K] [Fintype K] [Fintype (FiniteField.Extension K (ringChar K) 3)] :
    Fintype.card (FiniteField.Extension K (ringChar K) 3) = Fintype.card K ^ 3 := by
  rw [Module.card_fintype (FiniteField.Extension.finBasis K 3), Fintype.card_fin]

/-- info: 'FiniteField.Extension.finBasis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.Extension.finBasis
