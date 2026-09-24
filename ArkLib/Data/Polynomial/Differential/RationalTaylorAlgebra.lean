/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RationalTaylor

/-!
# Rational Taylor numerators over an algebra

Let `F` be a field and `A` a commutative `F`-algebra, for example a polynomial ring `F[X]` whose
variable is a symbolic parameter. For a differential polynomial `Q` over `A`, the recursion that
defines `rationalTaylorNumerator` over a field makes sense in `A`: its only division is by the
binomial pivot `(l choose r)`, and that inverse can be taken in `F` and mapped into `A`. The
separant is never inverted; it appears as a cleared denominator.

`rationalTaylorNumeratorOver F center Q l` is this numerator. It commutes with every `F`-algebra
map on the coefficients, with no hypothesis on the separant. So the numerator can be computed
once with the parameters kept symbolic and then specialized, also at parameter values where the
separant vanishes. Over a field `E` containing `F` it is `rationalTaylorNumerator`.

`commonTaylorNumeratorOver F center Q τ l` pads the numerator of `c_l` with separant powers up to
an exponent `τ`, so that all coefficients `c_l` with `2(l - r) - 1 ≤ τ` share the denominator
`S ^ τ`.

## Main statements

* `PolynomialDifferential.rationalTaylorNumeratorOver` and `map_rationalTaylorNumeratorOver`: the
  numerator commutes with `F`-algebra maps.
* `rationalTaylorNumeratorOver_eq`: over a field extension of `F` it is
  `rationalTaylorNumerator`.
* `map_rationalTaylorNumeratorOver_eq`: field specialization along any `F`-algebra map.
* `PolynomialDifferential.commonTaylorNumeratorOver` and `map_commonTaylorNumeratorOver`.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

variable (F : Type*) {A B : Type*} [Field F] [CommRing A] [CommRing B] [Algebra F A] {r : ℕ}

/-- The numerator of the rational Taylor coefficient `c_l` over an `F`-algebra `A`, a polynomial
in the initial jet with coefficients in `A`.

For `l ≤ r` it is the coordinate `Y_l`. For `l > r` it is `-(l choose r)⁻¹` times the cleared
substitution of the earlier numerators, with denominator exponents `2(i - r) - 1` and budget
`2(l - r) - 2`, into the coefficient of `ξ ^ (l - r)` of the universal residual on the chart of
length `l`. The inverse `(l choose r)⁻¹` is taken in `F`, and it is zero when `(l choose r) = 0`
in `F`. -/
def rationalTaylorNumeratorOver (center : A) (Q : DifferentialPolynomial A r)
    (l : ℕ) : MvPolynomial (Fin (r + 1)) A :=
  if hl : l < r + 1 then X ⟨l, hl⟩ else
    -C (algebraMap F A ((l.choose r : F)⁻¹)) *
      clearedSubstitution C (initialJetSeparant center Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
        ((optionEquivLeft A (Fin l) (universalTaylorResidual l center Q)).coeff (l - r))
termination_by l

/-- An `F`-algebra map `φ` on the coefficients sends the numerator of `Q` at `center` to the
numerator of the mapped polynomial at `φ center`. There is no hypothesis on the separant. -/
theorem map_rationalTaylorNumeratorOver [Algebra F B] (φ : A →ₐ[F] B)
    (center : A) (Q : DifferentialPolynomial A r) (l : ℕ) :
    map φ.toRingHom (rationalTaylorNumeratorOver F center Q l) =
      rationalTaylorNumeratorOver F (φ center) (map φ.toRingHom Q) l := by
  change map φ.toRingHom (rationalTaylorNumeratorOver F center Q l) =
    rationalTaylorNumeratorOver F (φ.toRingHom center) (map φ.toRingHom Q) l
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver, rationalTaylorNumeratorOver]
    split_ifs with hl
    · simp
    · rw [map_mul, map_neg, map_C, ringHom_clearedSubstitution]
      have hscalar : φ.toRingHom (algebraMap F A ((l.choose r : F)⁻¹)) =
          algebraMap F B ((l.choose r : F)⁻¹) := φ.commutes _
      rw [hscalar, map_initialJetSeparant,
        ← map_universalTaylorResidual_coeff φ.toRingHom l center Q (l - r),
        clearedSubstitution_map]
      have hC : (map (σ := Fin (r + 1)) φ.toRingHom).comp C = C.comp φ.toRingHom := by
        ext a
        simp
      rw [hC]
      congr 2
      funext i
      exact ih i.val i.isLt

/-- Over a field `E` containing `F`, the numerator is `rationalTaylorNumerator`: the inverse of
`(l choose r)` taken in `F` maps to its inverse in `E`. -/
theorem rationalTaylorNumeratorOver_eq {E : Type*} [Field E] [Algebra F E]
    (center : E) (Q : DifferentialPolynomial E r) (l : ℕ) :
    rationalTaylorNumeratorOver F center Q l = rationalTaylorNumerator center Q l := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver, rationalTaylorNumerator]
    split_ifs with hl
    · rfl
    · simp only [map_inv₀, map_natCast]
      congr 2
      funext i
      exact ih i.val i.isLt

/-- Specializing an algebra-valued numerator into a field gives the rational Taylor numerator of
the specialized equation. -/
theorem map_rationalTaylorNumeratorOver_eq {E : Type*} [Field E] [Algebra F E]
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (l : ℕ) :
    map φ.toRingHom (rationalTaylorNumeratorOver F center Q l) =
      rationalTaylorNumerator (φ center) (map φ.toRingHom Q) l := by
  rw [map_rationalTaylorNumeratorOver, rationalTaylorNumeratorOver_eq]

/-- The numerator of `c_l` padded to the common denominator `S ^ τ`, where `S` is the initial
separant: `rationalTaylorNumeratorOver F center Q l * S ^ (τ - (2(l - r) - 1))`. The padding is
exact when `2(l - r) - 1 ≤ τ`; otherwise natural subtraction truncates it. -/
def commonTaylorNumeratorOver (center : A) (Q : DifferentialPolynomial A r) (τ l : ℕ) :
    MvPolynomial (Fin (r + 1)) A :=
  rationalTaylorNumeratorOver F center Q l *
    initialJetSeparant center Q ^ (τ - (2 * (l - r) - 1))

/-- An `F`-algebra map on the coefficients commutes with the common numerators. -/
theorem map_commonTaylorNumeratorOver [Algebra F B] (φ : A →ₐ[F] B)
    (center : A) (Q : DifferentialPolynomial A r) (τ l : ℕ) :
    map φ.toRingHom (commonTaylorNumeratorOver F center Q τ l) =
      commonTaylorNumeratorOver F (φ center) (map φ.toRingHom Q) τ l := by
  simp only [commonTaylorNumeratorOver, map_mul, map_pow, map_rationalTaylorNumeratorOver,
    map_initialJetSeparant]
  rfl

end

end PolynomialDifferential
