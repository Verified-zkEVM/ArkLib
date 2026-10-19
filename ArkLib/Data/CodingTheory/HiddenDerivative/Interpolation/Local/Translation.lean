/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap
public import ArkLib.Data.CodingTheory.HiddenDerivative.NormalizedSubstitution
public import ArkLib.Data.MvPolynomial.WeightAtMost

/-!
# Translation of the point coordinates

`globalPointTranslation center received` is the substitution of differential polynomials

```text
X ↦ center + X,   Y₀ ↦ received + Y₀,   Y_j ↦ Y_j   (1 ≤ j ≤ d).
```

Translations compose by adding their offsets, and the translation by `(0, 0)` is the identity,
so translation by the opposite offsets is the inverse. The local substitutions at a point
factor through translation: substituting at `(center, received)` after translating by
`(center', received')` is substituting at `(center' + center, received' + received)`. In
particular every local constraint map is the constraint map at `(0, 0)` after a translation.

Translation preserves every support bound whose weight is nonnegative on `X` and `Y₀`, with
weights in any ordered additive commutative monoid. All statements hold over every commutative
ring.

## Main statements

* `globalPointTranslation_comp`, `globalPointTranslation_neg_comp`: composition and inverse.
* `globalPointTranslation_mem_restrictWeightAtMost`: preservation of weight bounds.
* `unscaledLocalSubstitution_comp_globalPointTranslation` and its normalized analogue.
* `localConstraintAt_eq_zero_globalPointTranslation`: the constraint map at a point is the
  constraint map at `(0, 0)` after translation.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d m : ℕ}

/-- Generator images of `globalPointTranslation`: `X ↦ center + X`, `Y₀ ↦ received + Y₀`, and
`Y_(j+1) ↦ Y_(j+1)`. -/
def globalPointTranslationImage (d : ℕ) (center received : R) :
    JetVariable d → DifferentialPolynomial R d
  | none => C center + X none
  | some j => Fin.cases (C received + X (some 0)) (fun i => X (some i.succ)) j

/-- Translate the point coordinates `X` and `Y₀` of a differential polynomial by
`(center, received)`. -/
def globalPointTranslation (center received : R) :
    DifferentialPolynomial R d →ₐ[R] DifferentialPolynomial R d :=
  bind₁ (globalPointTranslationImage d center received)

/-- `globalPointTranslation center received` sends `X` to `center + X`. -/
@[simp]
theorem globalPointTranslation_X (center received : R) :
    globalPointTranslation (d := d) center received (X none) = C center + X none := by
  simp [globalPointTranslation, globalPointTranslationImage]

/-- `globalPointTranslation center received` sends `Y₀` to `received + Y₀`. -/
@[simp]
theorem globalPointTranslation_Y_zero (center received : R) :
    globalPointTranslation (d := d) center received (X (some 0)) = C received + X (some 0) := by
  simp [globalPointTranslation, globalPointTranslationImage]

/-- `globalPointTranslation center received` fixes `Y_(j+1)`. -/
@[simp]
theorem globalPointTranslation_Y_succ (center received : R) (j : Fin d) :
    globalPointTranslation (d := d) center received (X (some j.succ)) = X (some j.succ) := by
  simp [globalPointTranslation, globalPointTranslationImage]

/-! ### Composition -/

/-- Translation by `(0, 0)` is the identity. -/
@[simp]
theorem globalPointTranslation_zero :
    globalPointTranslation (R := R) (d := d) 0 0 = AlgHom.id R _ := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with _ | j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) j <;> simp

/-- Translating by `(center', received')` and then by `(center, received)` translates by the
sums of the offsets. -/
theorem globalPointTranslation_comp (center received center' received' : R) :
    (globalPointTranslation (d := d) center received).comp
        (globalPointTranslation center' received') =
      globalPointTranslation (center' + center) (received' + received) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with _ | j
  · simp only [AlgHom.coe_comp, Function.comp_apply, globalPointTranslation_X, map_add,
      algHom_C, algebraMap_eq]
    ring
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [AlgHom.coe_comp, Function.comp_apply, globalPointTranslation_Y_zero, map_add,
        algHom_C, algebraMap_eq]
      ring
    · simp

/-- Translation by the opposite offsets is a left inverse of translation. -/
theorem globalPointTranslation_neg_comp (center received : R) :
    (globalPointTranslation (d := d) (-center) (-received)).comp
      (globalPointTranslation center received) = AlgHom.id R _ := by
  rw [globalPointTranslation_comp, add_neg_cancel, add_neg_cancel, globalPointTranslation_zero]

/-! ### Weight bounds -/

/-- Translation preserves a bound on a weight with values in an ordered additive commutative
monoid, provided the weights of `X` and `Y₀` are nonnegative. The hypotheses are needed because
the translate of `X` contains the constant monomial `center`, of weight zero, and similarly for
`Y₀`: with a negative weight on `X`, the polynomial `X` has weight at most `w X < 0`, while its
translate `center + X` does not when `center ≠ 0`. -/
theorem globalPointTranslation_mem_restrictWeightAtMost {M : Type*} [AddCommMonoid M]
    [PartialOrder M] [IsOrderedAddMonoid M] {w : JetVariable d → M} (hX : 0 ≤ w none)
    (hY₀ : 0 ≤ w (some 0)) (center received : R) {a : M} {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ restrictWeightAtMost (R := R) w a) :
    globalPointTranslation center received Q ∈ restrictWeightAtMost (R := R) w a := by
  refine bind₁_mem_restrictWeightAtMost (fun v => ?_) hQ
  rcases v with _ | j
  · exact add_mem (C_mem_restrictWeightAtMost w hX _) (X_mem_restrictWeightAtMost w _ le_rfl)
  · refine Fin.cases ?_ (fun i => ?_) j
    · exact add_mem (C_mem_restrictWeightAtMost w hY₀ _) (X_mem_restrictWeightAtMost w _ le_rfl)
    · simpa [globalPointTranslationImage] using
        X_mem_restrictWeightAtMost (R := R) w (some i.succ) le_rfl

/-! ### Local substitutions after translation -/

/-- The unscaled local substitution at `(center, received)` after translation by
`(center', received')` is the unscaled substitution at `(center' + center, received' + received)`.
-/
theorem unscaledLocalSubstitution_comp_globalPointTranslation
    (center received center' received' : R) :
    (unscaledLocalSubstitution d center received).comp
        (globalPointTranslation center' received') =
      unscaledLocalSubstitution d (center' + center) (received' + received) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with _ | j
  · simp only [AlgHom.coe_comp, Function.comp_apply, globalPointTranslation_X, map_add,
      algHom_C, algebraMap_eq, unscaledLocalSubstitution_X]
    ring
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [AlgHom.coe_comp, Function.comp_apply, globalPointTranslation_Y_zero, map_add,
        algHom_C, algebraMap_eq, unscaledLocalSubstitution_Y_zero]
      ring
    · simp

/-- The normalized analogue of `unscaledLocalSubstitution_comp_globalPointTranslation`. -/
theorem normalizedLocalSubstitution_comp_globalPointTranslation
    (center received center' received' : R) :
    (normalizedLocalSubstitution d center received).comp
        (globalPointTranslation center' received') =
      normalizedLocalSubstitution d (center' + center) (received' + received) := by
  rw [normalizedLocalSubstitution_eq_normalize_comp_unscaled,
    normalizedLocalSubstitution_eq_normalize_comp_unscaled, AlgHom.comp_assoc,
    unscaledLocalSubstitution_comp_globalPointTranslation]

/-- The local constraint map at `(center, received)` applied to a translate by
`(center', received')` is the constraint map at `(center' + center, received' + received)`. -/
theorem localConstraintAt_globalPointTranslation (center received center' received' : R)
    (Q : DifferentialPolynomial R d) :
    localConstraintAt m center received (globalPointTranslation center' received' Q) =
      localConstraintAt m (center' + center) (received' + received) Q := by
  simp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [← AlgHom.comp_apply, unscaledLocalSubstitution_comp_globalPointTranslation]

/-- The local constraint map at `(center, received)` is the constraint map at `(0, 0)` after
translation by `(center, received)`. -/
theorem localConstraintAt_eq_zero_globalPointTranslation (center received : R)
    (Q : DifferentialPolynomial R d) :
    localConstraintAt m center received Q =
      localConstraintAt m 0 0 (globalPointTranslation center received Q) := by
  rw [localConstraintAt_globalPointTranslation, add_zero, add_zero]

end ReedSolomon.HiddenDerivative
