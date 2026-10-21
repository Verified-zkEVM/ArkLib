/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Variables
public import ArkLib.Data.Polynomial.Differential.Types
public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# The unscaled hidden-derivative substitution

This file defines the change of variables that moves a differential polynomial
`Q(X, Y₀, ..., Y_d)` to a received point `(center, received)`, as the composition of two
substitutions. The first is

```text
X   = center + T,
Y₀  = received + T U,
Y_j = Y_j                         (1 ≤ j ≤ d),
```

and the second rewrites the auxiliary variable as

```text
U = E + sum_{j=1}^d (-1)^(j-1) T^(j-1) Y_j.
```

Their composition is `unscaledLocalSubstitution`, in which `Y₀` becomes
`received + sum_{j=1}^d (-1)^(j-1) T^j Y_j + T E`. Both steps are formal: they involve no Taylor
expansion of an actual polynomial, and they hold over every commutative ring.

## Main statements

* `unscaledLocalSubstitution_eq_rewrite_comp_translate`: the direct substitution is the
  composition `rewriteUToE ∘ translateToU`.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26],
  Equations (14) and (25).
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

/-- The visible-jet part of the auxiliary variable, `∑_{r<d} (-1)^r T^r Y_(r+1)`. -/
def localJetSum (d : ℕ) : LocalPolynomial R d :=
  ∑ j : Fin d, C ((-1 : R) ^ j.val) * X (localT d) ^ j.val * X (localY j)

/-- The signed correction that appears directly in `Y₀`, `∑_{r<d} (-1)^r T^(r+1) Y_(r+1)`. -/
def localCorrection (d : ℕ) : LocalPolynomial R d :=
  ∑ j : Fin d, C ((-1 : R) ^ j.val) * X (localT d) ^ (j.val + 1) * X (localY j)

/-- Multiplying the jet sum by `T` gives the direct correction. -/
theorem T_mul_localJetSum (d : ℕ) :
    X (localT d) * localJetSum (R := R) d = localCorrection d := by
  rw [localJetSum, localCorrection, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ]
  ring

/-- Generator images of `translateToU`: `X ↦ center + T`, `Y₀ ↦ received + T U`, and
`Y_(j+1) ↦ Y_(j+1)`. -/
def translateToUImage (d : ℕ) (center received : R) : JetVariable d → LocalPolynomial R d
  | none => C center + X (localT d)
  | some j => Fin.cases (C received + X (localT d) * X (localU d))
      (fun highOrder => X (localY highOrder)) j

/-- The first local change of variables, which introduces the auxiliary variable `U`. -/
def translateToU (d : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₐ[R] LocalPolynomial R d :=
  bind₁ (translateToUImage d center received)

/-- Generator images of `rewriteUToE`: `U ↦ E + localJetSum d`, fixing `T` and every `Y_j`. -/
def rewriteUToEImage (d : ℕ) : LocalVariable d → LocalPolynomial R d
  | none => X (localT d)
  | some none => X (localE d) + localJetSum d
  | some (some j) => X (localY j)

/-- The second local change of variables, which rewrites `U` as the error `E` plus the visible
jet sum. -/
def rewriteUToE (d : ℕ) : LocalPolynomial R d →ₐ[R] LocalPolynomial R d :=
  bind₁ (rewriteUToEImage d)

/-- Generator images of the complete unscaled local substitution. -/
def unscaledLocalImage (d : ℕ) (center received : R) : JetVariable d → LocalPolynomial R d
  | none => C center + X (localT d)
  | some j => Fin.cases (C received + localCorrection d + X (localT d) * X (localE d))
      (fun highOrder => X (localY highOrder)) j

/-- The complete unscaled local substitution. Its error variable `E` appears only as `T E`. -/
def unscaledLocalSubstitution (d : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₐ[R] LocalPolynomial R d :=
  bind₁ (unscaledLocalImage d center received)

/-- The unscaled substitution sends `X` to `center + T`. -/
@[simp]
theorem unscaledLocalSubstitution_X (d : ℕ) (center received : R) :
    unscaledLocalSubstitution d center received (X none) = C center + X (localT d) := by
  simp [unscaledLocalSubstitution, unscaledLocalImage]

/-- The unscaled substitution sends `Y₀` to `received + localCorrection d + T E`. -/
@[simp]
theorem unscaledLocalSubstitution_Y_zero (d : ℕ) (center received : R) :
    unscaledLocalSubstitution d center received (X (some 0)) =
      C received + localCorrection d + X (localT d) * X (localE d) := by
  simp [unscaledLocalSubstitution, unscaledLocalImage]

/-- The unscaled substitution sends `Y_(j+1)` to the local variable `Y_(j+1)`. -/
@[simp]
theorem unscaledLocalSubstitution_Y_succ (d : ℕ) (center received : R) (j : Fin d) :
    unscaledLocalSubstitution d center received (X (some j.succ)) = X (localY j) := by
  simp [unscaledLocalSubstitution, unscaledLocalImage]

/-- The direct unscaled substitution is the composition of the two primitive changes of
variables. At `Y₀` this is the identity `T (E + localJetSum d) = T E + localCorrection d`. -/
theorem unscaledLocalSubstitution_eq_rewrite_comp_translate (d : ℕ) (center received : R) :
    unscaledLocalSubstitution d center received =
      (rewriteUToE d).comp (translateToU d center received) := by
  apply MvPolynomial.algHom_ext
  rintro (_ | j)
  · simp [translateToU, translateToUImage, rewriteUToE, rewriteUToEImage, localT]
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [unscaledLocalSubstitution_Y_zero, AlgHom.coe_comp, Function.comp_apply,
        translateToU, translateToUImage, bind₁_X_right, Fin.cases_zero, map_add, map_mul,
        rewriteUToE, rewriteUToEImage, bind₁_C_right, localT, localU, localE, localAux]
      have hcorrection : X (none : LocalVariable d) * localJetSum (R := R) d =
          localCorrection (R := R) d := by
        simpa [localT] using T_mul_localJetSum (R := R) d
      rw [mul_add, hcorrection]
      ring
    · simp [translateToU, translateToUImage, rewriteUToE, rewriteUToEImage, localY]

end ReedSolomon.HiddenDerivative
