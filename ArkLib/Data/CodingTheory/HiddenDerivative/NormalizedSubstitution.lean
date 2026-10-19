/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Substitution

/-!
# The normalized hidden-derivative substitution

The unscaled local substitution `unscaledLocalSubstitution d center received` sends `Y₀` to
`received + localCorrection d + T E`. For an actual polynomial the hidden error is divisible by
`T^d` (see `Polynomial.X_pow_dvd_normalizedBackwardTaylorError`), and the normalized substitution
records this by writing the error as `T^d E`:

```text
X   = center + T,
Y₀  = received + sum_{j=1}^d (-1)^(j-1) T^j Y_j + T^(d+1) E,
Y_j = Y_j                         (1 ≤ j ≤ d).
```

It is the unscaled substitution followed by `normalizeError d`, the substitution `E ↦ T^d E`
that fixes `T` and every visible jet. Both hold over every commutative ring.

## Main statements

* `normalizedLocalSubstitution_eq_normalize_comp_unscaled`: the normalized substitution is
  `normalizeError d ∘ unscaledLocalSubstitution d center received`.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], Equation (16).
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

/-- Generator images of `normalizeError`: `E ↦ T^d E`, fixing `T` and every `Y_j`. -/
def normalizeErrorImage (d : ℕ) : LocalVariable d → LocalPolynomial R d
  | none => X (localT d)
  | some none => X (localT d) ^ d * X (localE d)
  | some (some j) => X (localY j)

/-- Rescale the error variable by `E ↦ T^d E`, fixing `T` and every visible jet. -/
def normalizeError (d : ℕ) : LocalPolynomial R d →ₐ[R] LocalPolynomial R d :=
  bind₁ (normalizeErrorImage d)

/-- `normalizeError` fixes `T`. -/
@[simp]
theorem normalizeError_T (d : ℕ) :
    normalizeError (R := R) d (X (localT d)) = X (localT d) := by
  simp [normalizeError, normalizeErrorImage, localT]

/-- `normalizeError` sends `E` to `T^d E`. -/
@[simp]
theorem normalizeError_E (d : ℕ) :
    normalizeError (R := R) d (X (localE d)) = X (localT d) ^ d * X (localE d) := by
  simp [normalizeError, normalizeErrorImage, localE, localAux]

/-- `normalizeError` fixes every visible jet `Y_(j+1)`. -/
@[simp]
theorem normalizeError_Y (j : Fin d) :
    normalizeError (R := R) d (X (localY j)) = X (localY j) := by
  simp [normalizeError, normalizeErrorImage, localY]

/-- The correction involves only `T` and the visible jets, so normalization fixes it. -/
@[simp]
theorem normalizeError_localCorrection (d : ℕ) :
    normalizeError (R := R) d (localCorrection d) = localCorrection d := by
  simp [localCorrection]

/-- Generator images of the normalized local substitution. -/
def normalizedLocalImage (d : ℕ) (center received : R) : JetVariable d → LocalPolynomial R d
  | none => C center + X (localT d)
  | some j => Fin.cases (C received + localCorrection d + X (localT d) ^ (d + 1) * X (localE d))
      (fun highOrder => X (localY highOrder)) j

/-- The normalized local substitution, in which the error variable `E` appears only as
`T^(d+1) E`. -/
def normalizedLocalSubstitution (d : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₐ[R] LocalPolynomial R d :=
  bind₁ (normalizedLocalImage d center received)

/-- The normalized substitution sends `X` to `center + T`. -/
@[simp]
theorem normalizedLocalSubstitution_X (d : ℕ) (center received : R) :
    normalizedLocalSubstitution d center received (X none) = C center + X (localT d) := by
  simp [normalizedLocalSubstitution, normalizedLocalImage]

/-- The normalized substitution sends `Y₀` to `received + localCorrection d + T^(d+1) E`. -/
@[simp]
theorem normalizedLocalSubstitution_Y_zero (d : ℕ) (center received : R) :
    normalizedLocalSubstitution d center received (X (some 0)) =
      C received + localCorrection d + X (localT d) ^ (d + 1) * X (localE d) := by
  simp [normalizedLocalSubstitution, normalizedLocalImage]

/-- The normalized substitution sends `Y_(j+1)` to the local variable `Y_(j+1)`. -/
@[simp]
theorem normalizedLocalSubstitution_Y_succ (d : ℕ) (center received : R) (j : Fin d) :
    normalizedLocalSubstitution d center received (X (some j.succ)) = X (localY j) := by
  simp [normalizedLocalSubstitution, normalizedLocalImage]

/-- The normalized substitution is the unscaled substitution followed by `E ↦ T^d E`. At `Y₀`
this is `T · T^d E = T^(d+1) E`. -/
theorem normalizedLocalSubstitution_eq_normalize_comp_unscaled (d : ℕ) (center received : R) :
    normalizedLocalSubstitution d center received =
      (normalizeError d).comp (unscaledLocalSubstitution d center received) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with _ | j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [normalizedLocalSubstitution_Y_zero, AlgHom.coe_comp, Function.comp_apply,
        unscaledLocalSubstitution_Y_zero, map_add, map_mul, algHom_C, algebraMap_eq,
        normalizeError_localCorrection, normalizeError_T, normalizeError_E]
      ring
    · simp

end ReedSolomon.HiddenDerivative
