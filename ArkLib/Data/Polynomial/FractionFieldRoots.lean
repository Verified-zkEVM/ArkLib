/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Polynomial roots over a fraction field

Separability for a polynomial over a domain is stronger than separability after passage to its
fraction field. The latter is the relevant condition for function-field factorization in BCHKS25.
These lemmas keep that passage explicit. They also isolate the rational root of a linear factor;
they do not assert that this rational root is a polynomial or bound its degrees.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.
-/

namespace Polynomial

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/-- For a factor irreducible over the fraction field, separability is exactly nonvanishing of
the original derivative. No perfectness or characteristic restriction is needed. -/
theorem separable_map_fractionField_iff {p : R[X]}
    (hp : Irreducible (p.map (algebraMap R K))) :
    (p.map (algebraMap R K)).Separable ↔ p.derivative ≠ 0 := by
  rw [separable_iff_derivative_ne_zero hp, derivative_map]
  exact not_congr (Polynomial.map_eq_zero_iff (IsFractionRing.injective R K))

/-- A primitive irreducible factor is separable over the fraction field precisely when its
derivative is nonzero. Primitivity explicitly excludes nonunit constant content factors. -/
theorem IsPrimitive.separable_map_fractionField_iff [IsGCDMonoid R] {p : R[X]}
    (hprim : p.IsPrimitive) (hp : Irreducible p) :
    (p.map (algebraMap R K)).Separable ↔ p.derivative ≠ 0 := by
  exact Polynomial.separable_map_fractionField_iff
    ((hprim.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hp)

omit [IsDomain R] in
/-- A linear factor has a unique fraction-field root when its leading coefficient is nonzero.
The denominator is retained: polynomiality requires an additional divisibility argument. -/
theorem eval₂_linear_eq_zero_iff (a b : R) (ha : a ≠ 0) (y : K) :
    (C a * X + C b).eval₂ (algebraMap R K) y = 0 ↔
      y = -algebraMap R K b / algebraMap R K a := by
  have ha' : algebraMap R K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
  simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
  rw [eq_div_iff ha']
  constructor <;> intro h <;> linear_combination h

omit [IsDomain R] in
/-- A rational root coming from the coefficient domain is characterized by a denominator-cleared
equation in that domain. This is the algebraic obligation for extracting a polynomial family. -/
theorem eval₂_linear_algebraMap_eq_zero_iff (a b c : R) :
    (C a * X + C b).eval₂ (algebraMap R K) (algebraMap R K c) = 0 ↔
      a * c + b = 0 := by
  simpa only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, ← map_mul, ← map_add] using
    (map_eq_zero_iff (algebraMap R K) (IsFractionRing.injective R K)
      (x := a * c + b))

omit [IsDomain R] in
/-- A linear factor has a root in the coefficient domain exactly when its leading coefficient
divides its constant coefficient. This includes the degenerate zero-leading-coefficient case. -/
theorem exists_eval₂_linear_algebraMap_eq_zero_iff (a b : R) :
    (∃ c : R, (C a * X + C b).eval₂ (algebraMap R K) (algebraMap R K c) = 0) ↔
      a ∣ b := by
  simp only [eval₂_linear_algebraMap_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨-c, ?_⟩
    rw [mul_neg]
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hc)
  · rintro ⟨c, rfl⟩
    exact ⟨-c, by simp⟩

end Polynomial
