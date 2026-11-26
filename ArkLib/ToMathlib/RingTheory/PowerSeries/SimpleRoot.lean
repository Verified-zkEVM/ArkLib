/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.ToMathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Power series roots over a simple root

Let `Φ` be a polynomial with power series coefficients over a commutative ring `R`.
Reducing every coefficient to its constant term gives a polynomial over `R`.
A simple root `a` of the reduction lifts to a unique power series root with constant term `a`.

This is Hensel's lemma, with uniqueness, in the `X`-adically complete ring of power series.

## Main statements

* `PowerSeries.constantCoeff_aeval`: the constant term of a multivariate substitution.
* `PowerSeries.existsUnique_constantCoeff_eq_and_eval_eq_zero`: simple roots lift uniquely.
* `PowerSeries.coeff_eval_trunc_eq_zero`: truncations of a root are roots up to their length.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The constant term of `p(g)` is `p` evaluated at the constant terms of `g`. -/
theorem constantCoeff_aeval {σ : Type*} (g : σ → PowerSeries R) (p : MvPolynomial σ R) :
    constantCoeff (MvPolynomial.aeval g p) = MvPolynomial.eval (fun i ↦ constantCoeff (g i)) p := by
  rw [MvPolynomial.map_aeval]; simp

/-- Let `Φ` be a polynomial with power series coefficients over a commutative ring.

Reduce its coefficients to their constant terms.
Let `a` be a root of the reduction at which the derivative of the reduction is a unit.
Then `Φ` has exactly one power series root with constant term `a`. -/
theorem existsUnique_constantCoeff_eq_and_eval_eq_zero (Φ : Polynomial (PowerSeries R)) (a : R)
    (h₀ : (Φ.map constantCoeff).eval a = 0)
    (h₁ : IsUnit ((Φ.map constantCoeff).derivative.eval a)) :
    ∃! E : PowerSeries R, constantCoeff E = a ∧ Φ.eval E = 0 := by
  have hmem : ∀ E : PowerSeries R, E - C a ∈ Ideal.span {X} ↔ constantCoeff E = a := fun E ↦ by
    rw [Ideal.mem_span_singleton, X_dvd_iff, map_sub, constantCoeff_C, sub_eq_zero]
  have hunit : IsUnit (Φ.derivative.eval (C a)) := by
    rw [isUnit_iff_constantCoeff, ← Polynomial.eval_map_apply, constantCoeff_C,
      ← Polynomial.derivative_map]
    exact h₁
  obtain ⟨E, ⟨hE, hEa⟩, huniq⟩ :=
    IsAdicComplete.existsUnique_isRoot_sub_mem (I := Ideal.span {X}) Φ (C a)
      (by rw [Ideal.mem_span_singleton, X_dvd_iff, ← Polynomial.eval_map_apply, constantCoeff_C,
        h₀])
      (hunit.map _)
  exact ⟨E, ⟨(hmem E).mp hEa, hE⟩, fun F ⟨hFa, hF⟩ ↦ huniq F ⟨hF, (hmem F).mpr hFa⟩⟩

/-- A truncation of a root is a root up to its length.

Let `Φ(F) = 0`, let `m < n`, and let `T` be the truncation of `F` below degree `n`.
Then the coefficient of `X ^ m` in `Φ(T)` is zero. -/
theorem coeff_eval_trunc_eq_zero {Φ : Polynomial (PowerSeries R)} {F : PowerSeries R}
    (hF : Φ.eval F = 0) {m n : ℕ} (hmn : m < n) :
    coeff m (Φ.eval (trunc n F : PowerSeries R)) = 0 := by
  have hX : X ^ n ∣ (trunc n F : PowerSeries R) - F := by
    refine X_pow_dvd_iff.mpr fun i hi ↦ ?_
    simp [coeff_trunc, hi]
  obtain ⟨G, hG⟩ := hX.trans (Polynomial.sub_dvd_eval_sub _ _ Φ)
  rw [hF, sub_zero] at hG
  rw [hG, coeff_X_pow_mul']
  simp [Nat.not_le.mpr hmn]

end PowerSeries
