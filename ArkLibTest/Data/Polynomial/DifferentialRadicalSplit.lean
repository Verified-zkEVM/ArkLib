/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.Basic
import ArkLib.ToMathlib.MvPolynomial.RadicalSplit

/-! # Radical split under differential specialization -/

namespace PolynomialDifferential

open MvPolynomial Polynomial

variable {F : Type*} [Field F] {d : ℕ}

-- This pins the zero-locus split used by the future `TailBound` port.
example (Q : DifferentialPolynomial F d) (i : JetVariable d) (P : F[X]) (hQ : Q ≠ 0) :
    differentialSpecialization Q P = 0 ↔
      differentialSpecialization (radicalContent i Q) P = 0 ∨
        differentialSpecialization (radicalPrimPart i Q) P = 0 := by
  have h := MvPolynomial.map_radicalContent_mul_radicalPrimPart_eq_zero_iff
    (differentialSpecializationHom P) i hQ
  rw [map_mul, mul_eq_zero] at h
  simp only [differentialSpecializationHom_apply] at h
  exact h.symm

end PolynomialDifferential
