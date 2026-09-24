/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.Basic
public import ArkLib.ToMathlib.MvPolynomial.RadicalSplit

/-!
# Radical factorization under differential specialization

This file connects the generic content and positive-degree radical split to differential
specialization. For any finite jet order and selected variable, a nonzero equation vanishes after
specialization exactly when one of its two radical factors vanishes.

## Main statements

* `differentialSpecialization_eq_zero_iff_radicalSplit`: the zero-locus decomposition after
  differential specialization.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

open MvPolynomial Polynomial

variable {F : Type*} [Field F] {d : ℕ}

/-- A nonzero differential polynomial vanishes after specialization exactly when one of its
radical content and positive-degree factors vanishes. -/
theorem differentialSpecialization_eq_zero_iff_radicalSplit
    (Q : DifferentialPolynomial F d) (i : JetVariable d) (P : F[X]) (hQ : Q ≠ 0) :
    differentialSpecialization Q P = 0 ↔
      differentialSpecialization (radicalContent i Q) P = 0 ∨
        differentialSpecialization (radicalPrimPart i Q) P = 0 := by
  have h := MvPolynomial.map_radicalContent_mul_radicalPrimPart_eq_zero_iff
    (differentialSpecializationHom P).toRingHom i hQ
  rw [map_mul, mul_eq_zero] at h
  change differentialSpecializationHom P (radicalContent i Q) = 0 ∨
      differentialSpecializationHom P (radicalPrimPart i Q) = 0 ↔
    differentialSpecializationHom P Q = 0 at h
  change differentialSpecializationHom P Q = 0 ↔
    differentialSpecializationHom P (radicalContent i Q) = 0 ∨
      differentialSpecializationHom P (radicalPrimPart i Q) = 0
  exact h.symm

end PolynomialDifferential
