/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.MapExponents

/-!
# Relabelling exponents

Doubling every exponent sends `X₀` to `X₀²`, and the substitution form `mapExponents_eq_bind₁`
gives the same image. The zero exponent map sends `X₀` and `1` to the same polynomial, so the
injectivity hypothesis of `mapExponents_injective` cannot be dropped. Truncating by degree after
doubling exponents is doubling after truncating by twice the degree.
-/

open MvPolynomial

/-- Doubling exponents sends `X₀` to `X₀²`. -/
example : mapExponents (2 • AddMonoidHom.id (Fin 1 →₀ ℕ)) (X 0 : MvPolynomial (Fin 1) ℚ) =
    X 0 ^ 2 := by
  simp only [X, mapExponents_monomial, monomial_pow, one_pow]
  simp [Finsupp.smul_single]

/-- The substitution form: `X₀` goes to the monomial of exponent `f (single 0 1)`. -/
example : mapExponents (2 • AddMonoidHom.id (Fin 1 →₀ ℕ)) (X 0 : MvPolynomial (Fin 1) ℚ) =
    monomial (Finsupp.single 0 2) 1 := by
  rw [mapExponents_eq_bind₁, bind₁_X_right]
  simp [Finsupp.smul_single]

/-- Injectivity of the exponent map is needed: the zero map identifies `X₀` with `1`. -/
example : mapExponents (0 : (Fin 1 →₀ ℕ) →+ (Fin 1 →₀ ℕ)) (X 0 : MvPolynomial (Fin 1) ℚ) =
      mapExponents (0 : (Fin 1 →₀ ℕ) →+ (Fin 1 →₀ ℕ)) (1 : MvPolynomial (Fin 1) ℚ) ∧
      (X 0 : MvPolynomial (Fin 1) ℚ) ≠ 1 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [X, ← C_1, ← monomial_zero', mapExponents_monomial, mapExponents_monomial]
    rfl
  · have h1 := congrArg (fun p => p.coeff (Finsupp.single 0 1)) h
    simp [coeff_X, coeff_one] at h1
    exact Finsupp.single_ne_zero.mpr one_ne_zero h1.symm

/-- Doubling exponents doubles the standard degree, so truncating below degree `m` after the
relabelling is relabelling after truncating by the doubled weight. -/
example (m : ℕ) (F : MvPolynomial (Fin 1) ℚ) :
    weightedTruncation (fun _ => 1) m (mapExponents (2 • AddMonoidHom.id (Fin 1 →₀ ℕ)) F) =
      mapExponents (2 • AddMonoidHom.id _) (weightedTruncation (fun _ => 2) m F) :=
  weightedTruncation_mapExponents _ (fun e => by simp [Finsupp.weight_apply, Finsupp.sum,
    two_mul, mul_two]) m F

/-- A filter on a single monomial keeps it exactly when the predicate holds. -/
example : filterSupport (fun e : Fin 1 →₀ ℕ => e 0 < 2) (monomial (Finsupp.single 0 3) (5 : ℚ)) =
    0 := by
  rw [filterSupport_monomial]
  simp
