/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.TranslateSpec
import Mathlib.Data.ZMod.Basic
/-!
# Local translation and coefficient lookup canaries

Zero scalar entries remain materialized. T truncation is strict and does not confuse the U
exponent with the displacement exponent. The final example distinguishes this intermediate
translation from the pending low-contact projection.
-/

namespace ReedSolomon.HiddenDerivative.LocalColumnTranslationMachine

/-- Both affine factors contribute, with all retained zero entries and pair order preserved. -/
example : (translate (2 : ℤ) 3 1 1 3).1 = .done
    [⟨6, 0, 0⟩, ⟨2, 1, 1⟩, ⟨0, 2, 2⟩, ⟨3, 1, 0⟩, ⟨1, 2, 1⟩, ⟨0, 2, 0⟩] := by decide

/-- The term of T-degree exactly m is dropped, while T*U survives this preliminary stage. -/
example : (translate (2 : ℤ) 3 1 1 2).1 = .done
    [⟨6, 0, 0⟩, ⟨2, 1, 1⟩, ⟨3, 1, 0⟩] := by decide

/-- Cancellation in characteristic two is reflected in actual materialized coefficients. -/
example : (translate (1 : ZMod 2) 1 2 1 3).1 = .done
    [⟨1, 0, 0⟩, ⟨1, 1, 1⟩, ⟨0, 2, 2⟩, ⟨0, 1, 0⟩, ⟨0, 2, 1⟩, ⟨1, 2, 0⟩] := by decide

/-- Constant columns still receive the fixed materialized output shape. -/
example : (translate (0 : ℤ) 0 0 0 2).1 = .done
    [⟨1, 0, 0⟩, ⟨0, 1, 1⟩, ⟨0, 1, 0⟩] := by decide

/-- A zero truncation width has no output terms. -/
example : (translate (2 : ℤ) 3 4 2 0).1 = .done [] := by decide

/-- Duplicate coordinates add; entries sharing just one coordinate do not contribute. -/
example : lookup 1 2 ([⟨3, 1, 2⟩, ⟨4, 1, 1⟩, ⟨-5, 1, 2⟩] : List (Term ℤ)) =
    (-2, 128) := by decide

/-- This intermediate coefficient is nonzero, but its order-one low-contact projection is zero. -/
example : lookup 1 1 ([⟨6, 0, 0⟩, ⟨2, 1, 1⟩, ⟨3, 1, 0⟩] : List (Term ℤ)) = (2, 128) ∧
    MvPolynomial.coeff (exponent (0 : LocalVariable 1 →₀ ℕ) 1 1)
      (projectLowContact 2 (atom (0 : LocalVariable 1 →₀ ℕ) 1 1 (2 : ℤ))) = 0 := by
  constructor
  · decide
  · rw [projectLowContact, coeff_filterLocalMonomials]
    simp [localContactOrder, Finsupp.weight_apply, Finsupp.sum_fintype,
      exponent, localContactWeight, localT, localU, localAux, Fintype.sum_option]

end ReedSolomon.HiddenDerivative.LocalColumnTranslationMachine
