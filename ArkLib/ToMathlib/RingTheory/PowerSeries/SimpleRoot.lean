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

Existence is Hensel's lemma in the `X`-adically complete ring of power series.
Uniqueness holds because `Φ(F) - Φ(E)` is `F - E` times a unit for two such roots.

## Main statements

* `PowerSeries.constantCoeff_eval`: the constant term of an evaluation.
* `PowerSeries.constantCoeff_aeval`: the constant term of a multivariate substitution.
* `PowerSeries.existsUnique_constantCoeff_eq_and_eval_eq_zero`: simple roots lift uniquely.
* `PowerSeries.coeff_eval_trunc_eq_zero`: truncations of a root are roots up to their length.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The constant term of `Φ(E)` is the reduction of `Φ` evaluated at the constant term of `E`. -/
theorem constantCoeff_eval (Φ : Polynomial (PowerSeries R)) (E : PowerSeries R) :
    constantCoeff (Φ.eval E) = (Φ.map constantCoeff).eval (constantCoeff E) := by
  rw [Polynomial.eval_map]
  exact Polynomial.hom_eval₂ _ _ _ _

/-- The constant term of `p(g)` is `p` evaluated at the constant terms of `g`. -/
theorem constantCoeff_aeval {σ : Type*} (g : σ → PowerSeries R) (p : MvPolynomial σ R) :
    constantCoeff (MvPolynomial.aeval g p) = MvPolynomial.eval (fun i ↦ constantCoeff (g i)) p := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, MvPolynomial.eval]
  congr 1

/-- Let `Φ` be a polynomial with power series coefficients over a commutative ring.

Reduce its coefficients to their constant terms.
Let `a` be a root of the reduction at which the derivative of the reduction is a unit.
Then `Φ` has exactly one power series root with constant term `a`. -/
theorem existsUnique_constantCoeff_eq_and_eval_eq_zero (Φ : Polynomial (PowerSeries R)) (a : R)
    (h₀ : (Φ.map constantCoeff).eval a = 0)
    (h₁ : IsUnit ((Φ.map constantCoeff).derivative.eval a)) :
    ∃! E : PowerSeries R, constantCoeff E = a ∧ Φ.eval E = 0 := by
  have hunit : ∀ E : PowerSeries R, constantCoeff E = a →
      IsUnit (Φ.derivative.eval E) := fun E hE ↦ by
    rw [isUnit_iff_constantCoeff, constantCoeff_eval, hE, ← Polynomial.derivative_map]
    exact h₁
  obtain ⟨E, hE, hEa⟩ := IsAdicComplete.exists_isRoot_sub_mem (I := Ideal.span {X}) Φ (C a)
    (by rw [Ideal.mem_span_singleton, X_dvd_iff, constantCoeff_eval, constantCoeff_C, h₀])
    ((hunit _ (constantCoeff_C a)).map _)
  rw [Ideal.mem_span_singleton, X_dvd_iff, map_sub, constantCoeff_C, sub_eq_zero] at hEa
  refine ⟨E, ⟨hEa, hE⟩, fun F ⟨hFa, hF⟩ ↦ ?_⟩
  obtain ⟨c, hc⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add Φ E (F - E)
  rw [add_sub_cancel, hF, hE.eq_zero, add_zero] at hc
  have hu : IsUnit (c * (F - E) + Φ.derivative.eval E) := by
    rw [isUnit_iff_constantCoeff, map_add, map_mul, map_sub, hFa, hEa, sub_self, mul_zero,
      zero_add, ← isUnit_iff_constantCoeff]
    exact hunit E hEa
  rw [← sub_eq_zero, ← hu.mul_right_eq_zero]
  linear_combination hc

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
