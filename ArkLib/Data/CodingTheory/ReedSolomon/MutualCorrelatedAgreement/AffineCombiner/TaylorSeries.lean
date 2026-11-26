/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.TaylorChart
public import ArkLib.ToMathlib.RingTheory.PowerSeries.SimpleRoot

/-!
# The formal power series root along an affine challenge line

Fix `R ∈ K[X, Y, Z]`, a center `t₀` and a challenge `(α, β)`, and write `W = X - t₀`.
Let `z` be a simple root of `R(t₀, α + β t₀, Z)`.
Then `R(X, α + β X, Z) = 0` has exactly one series solution `z + E(W)` with `E(0) = 0`.
A polynomial root through `(t₀, z)` is this series.
For `j ≥ 1`, the coefficient of `W ^ j` is `N_j / S^(2j - 1)`, with `S = R_Z(t₀, α + β t₀, z)`.

Existence and uniqueness come from Hensel's lemma for power series.
The coefficient formula and the polynomial-root case hold for any root `E` with `E(0) = 0`.
In particular they hold for the unique one.
The paper's `P = z + E(X - t₀)` is stated through the Taylor expansion of `P` at `t₀` in `W`.
The paper's degree bound on `N_j` is the numerator degree bound of the Taylor chart module.
The series equation is a noncomputable view of a polynomial ring over power series.

This is Lemma 3.11 of [CWYZ26].
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main definitions

* `ReedSolomon.affineSeriesEquation`: the equation `R(t₀ + W, α + β (t₀ + W), U)` in `U`.

## Main statements

* `ReedSolomon.eval_affineSeriesEquation`,
  `ReedSolomon.eval_map_constantCoeff_affineSeriesEquation` and
  `ReedSolomon.derivative_affineSeriesEquation`: evaluation, reduction and derivative.
* `ReedSolomon.coe_taylor_multiplierEval_affineMultiplier`: Taylor expansion along a line.
* `ReedSolomon.existsUnique_powerSeries_root`: existence and uniqueness of the series root.
* `ReedSolomon.coe_taylor_eq_C_add_of_multiplierEval_eq_zero`: a polynomial root is the
  series root.
* `ReedSolomon.coeff_C_add_eq_chartCoefficient`: the series coefficients are the chart
  coefficients.
* `ReedSolomon.coeff_eq_chartNumerator_div_of_constantCoeff_eq_zero`: the coefficient
  formula (3.5).

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26], Lemma 3.11.
-/

@[expose] public section

namespace ReedSolomon

open MvPolynomial PolynomialDifferential

variable {K : Type*} [Field K]

/-- The polynomial `R(t₀ + W, α + β (t₀ + W), U)` in `U` over the power series in `W`. -/
noncomputable def affineSeriesEquation (t₀ α β : K) (R : MvPolynomial AffineVar K) :
    Polynomial (PowerSeries K) :=
  aeval (fun v ↦ v.elim Polynomial.X ![Polynomial.C (PowerSeries.C t₀ + PowerSeries.X),
    Polynomial.C (PowerSeries.C (α + β * t₀) + PowerSeries.C β * PowerSeries.X)]) R

/-- Evaluating the series equation at `F` substitutes `F` for `Z`. -/
theorem eval_affineSeriesEquation (t₀ α β : K) (R : MvPolynomial AffineVar K)
    (F : PowerSeries K) :
    (affineSeriesEquation t₀ α β R).eval F =
      aeval (fun v ↦ v.elim F ![PowerSeries.C t₀ + PowerSeries.X,
        PowerSeries.C (α + β * t₀) + PowerSeries.C β * PowerSeries.X]) R := by
  rw [affineSeriesEquation, ← Polynomial.coe_aeval_eq_eval,
    ← AlgHom.restrictScalars_apply K, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext v
  rcases v with _ | ⟨i⟩
  · simp
  · fin_cases i <;> simp

/-- At `W = 0` the series equation is `R(t₀, α + β t₀, U)`. -/
theorem eval_map_constantCoeff_affineSeriesEquation (t₀ α β : K) (R : MvPolynomial AffineVar K)
    (z : K) :
    ((affineSeriesEquation t₀ α β R).map PowerSeries.constantCoeff).eval z =
      eval (fun v ↦ v.elim z ![t₀, α + β * t₀]) R := by
  rw [← PowerSeries.constantCoeff_C z, Polynomial.eval_map_apply,
    eval_affineSeriesEquation, PowerSeries.constantCoeff_aeval, PowerSeries.constantCoeff_C]
  congr 2
  funext v
  rcases v with _ | ⟨i⟩
  · simp
  · fin_cases i <;> simp

/-- The derivative of the series equation in `U` is the series equation of `R_Z`. -/
theorem derivative_affineSeriesEquation (t₀ α β : K) (R : MvPolynomial AffineVar K) :
    Polynomial.derivative (affineSeriesEquation t₀ α β R) =
      affineSeriesEquation t₀ α β (pderiv none R) := by
  unfold affineSeriesEquation
  generalize hg : (fun v : AffineVar ↦ v.elim Polynomial.X
    ![Polynomial.C (PowerSeries.C t₀ + PowerSeries.X),
      Polynomial.C (PowerSeries.C (α + β * t₀) + PowerSeries.C β * PowerSeries.X)]) = g
  have hnone : g none = Polynomial.X := by rw [← hg]; rfl
  have hsome : ∀ i, Polynomial.derivative (g (some i)) = 0 := by
    intro i
    rw [← hg]
    fin_cases i <;> simp
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, hp, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      map_add, map_mul, map_mul, aeval_X]
    rcases v with _ | ⟨i⟩
    · simp [pderiv_X, hnone]
      ring
    · simp [pderiv_X, hsome]
      ring

/-- A simple root at the center determines a unique power series root.

Let `R ∈ K[X, Y, Z]` over a field `K` and fix `t₀, α, β, z ∈ K`.
Suppose `R(t₀, α + β t₀, z) = 0` and `R_Z(t₀, α + β t₀, z) ≠ 0`.
Write `W = X - t₀`.
Consider power series `E` in `W` with zero constant term.
Exactly one of them satisfies `R(t₀ + W, α + β (t₀ + W), z + E(W)) = 0`. -/
theorem existsUnique_powerSeries_root (R : MvPolynomial AffineVar K) (t₀ α β z : K)
    (hz : eval (fun v ↦ v.elim z ![t₀, α + β * t₀]) R = 0)
    (hS : eval (fun v ↦ v.elim z ![t₀, α + β * t₀]) (pderiv none R) ≠ 0) :
    ∃! E : PowerSeries K, PowerSeries.constantCoeff E = 0 ∧
      (affineSeriesEquation t₀ α β R).eval (PowerSeries.C z + E) = 0 := by
  obtain ⟨F, ⟨hF0, hF⟩, huniq⟩ :=
    PowerSeries.existsUnique_constantCoeff_eq_and_eval_eq_zero (affineSeriesEquation t₀ α β R) z
      (by rw [eval_map_constantCoeff_affineSeriesEquation]; exact hz)
      (by
        rw [Polynomial.derivative_map, derivative_affineSeriesEquation,
          eval_map_constantCoeff_affineSeriesEquation]
        exact hS.isUnit)
  refine ⟨F - PowerSeries.C z, ⟨by simp [hF0], by rwa [add_sub_cancel]⟩, fun E ⟨hE0, hE⟩ ↦ ?_⟩
  rw [← huniq (PowerSeries.C z + E) ⟨by simp [hE0], hE⟩, add_sub_cancel_left]

/-- The Taylor expansion at `t₀` of `R(X, α + β X, P)` substitutes the expansion of `P`. -/
theorem coe_taylor_multiplierEval_affineMultiplier (t₀ α β : K) (P : Polynomial K)
    (R : MvPolynomial AffineVar K) :
    (↑(Polynomial.taylor t₀ (multiplierEval (affineMultiplier α β) P R)) : PowerSeries K) =
      aeval (fun v ↦ v.elim (Polynomial.taylor t₀ P : PowerSeries K)
        ![PowerSeries.C t₀ + PowerSeries.X,
          PowerSeries.C (α + β * t₀) + PowerSeries.C β * PowerSeries.X]) R := by
  have h := DFunLike.congr_fun (comp_aeval (R := K)
    (fun v : AffineVar ↦ v.elim P ![Polynomial.X, affineMultiplier α β])
    ((Polynomial.coeToPowerSeries.algHom K).comp (Polynomial.taylorAlgHom t₀))) R
  simp only [AlgHom.comp_apply, Polynomial.coeToPowerSeries.algHom_apply,
    Algebra.algebraMap_self, PowerSeries.map_id, id] at h
  rw [multiplierEval]
  refine h.trans ?_
  congr 2
  funext v
  rcases v with _ | ⟨i⟩
  · simp
  · fin_cases i
    · simp [add_comm]
    · simp [affineMultiplier]
      ring

/-- A polynomial root through `(t₀, z)` is the power series root.

Let `R ∈ K[X, Y, Z]` over a field `K` and let `P ∈ K[X]` satisfy `R(X, α + β X, P) = 0`.
Let `z = P(t₀)` with `R_Z(t₀, α + β t₀, z) ≠ 0`, and write `W = X - t₀`.
Let `E` be a power series with zero constant term and `R(t₀ + W, α + β (t₀ + W), z + E) = 0`.
Then the Taylor expansion of `P` at `t₀`, read as a power series in `W`, is `z + E`. -/
theorem coe_taylor_eq_C_add_of_multiplierEval_eq_zero (R : MvPolynomial AffineVar K)
    (t₀ α β z : K) {P : Polynomial K} (hP : multiplierEval (affineMultiplier α β) P R = 0)
    (hPz : P.eval t₀ = z)
    (hS : eval (fun v ↦ v.elim z ![t₀, α + β * t₀]) (pderiv none R) ≠ 0)
    {E : PowerSeries K} (hE0 : PowerSeries.constantCoeff E = 0)
    (hE : (affineSeriesEquation t₀ α β R).eval (PowerSeries.C z + E) = 0) :
    ((Polynomial.taylor t₀ P : Polynomial K) : PowerSeries K) = PowerSeries.C z + E := by
  have hz : eval (fun v ↦ v.elim z ![t₀, α + β * t₀]) R = 0 := by
    have h := eval_multiplierEval t₀ (affineMultiplier α β) P R
    rw [hP, Polynomial.eval_zero, hPz, eval_affineMultiplier] at h
    simpa [coe_aeval_eq_eval, mul_comm] using h.symm
  have h0 : PowerSeries.constantCoeff
      ((Polynomial.taylor t₀ P : PowerSeries K) - PowerSeries.C z) = 0 := by
    rw [map_sub, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.taylor_coeff_zero, hPz, PowerSeries.constantCoeff_C, sub_self]
  have hroot := coe_taylor_multiplierEval_affineMultiplier t₀ α β P R
  rw [hP, map_zero, Polynomial.coe_zero] at hroot
  have := (existsUnique_powerSeries_root R t₀ α β z hz hS).unique
    ⟨h0, by rw [add_sub_cancel, eval_affineSeriesEquation]; exact hroot.symm⟩ ⟨hE0, hE⟩
  rw [← this, add_sub_cancel]

/-- The coefficients of the power series root are the chart coefficients.

Let `R ∈ K[X, Y, Z]` over a field `K` with `R_Z(t₀, α + β t₀, z) ≠ 0`, and write `W = X - t₀`.
Let `E` be a power series with zero constant term and `R(t₀ + W, α + β (t₀ + W), z + E) = 0`.
Then for every `j`, the coefficient of `W ^ j` in `z + E` is the chart coefficient `c_j`.
This coefficient is taken at center `t₀` and chart point `(z, α, β)`. -/
theorem coeff_C_add_eq_chartCoefficient (R : MvPolynomial AffineVar K) (t₀ α β z : K)
    (hS : eval (fun v ↦ v.elim z ![t₀, α + β * t₀]) (pderiv none R) ≠ 0)
    {E : PowerSeries K} (hE0 : PowerSeries.constantCoeff E = 0)
    (hE : (affineSeriesEquation t₀ α β R).eval (PowerSeries.C z + E) = 0) (j : ℕ) :
    PowerSeries.coeff j (PowerSeries.C z + E) =
      chartCoefficient t₀ affineFamily R (Sum.elim (fun _ ↦ z) ![α, β]) j := by
  set F := PowerSeries.C z + E
  set Q := specializedFamilyEquation affineFamily R ![α, β]
  have hF0 : PowerSeries.coeff 0 F = z := by
    simp [F, hE0]
  have hSQ : aeval (fun _ : Fin 1 ↦ z) (initialJetSeparant t₀ Q) ≠ 0 := by
    have h := aeval_chartSeparant t₀ affineFamily R (Sum.elim (fun _ ↦ z) ![α, β])
    rw [aeval_chartSeparant_eq] at h
    change aeval (fun _ : Fin 1 ↦ z) (initialJetSeparant t₀ Q) = _ at h
    rw [h]
    simpa [Function.comp_def, coe_aeval_eq_eval, familyMultiplier_affineFamily, mul_comm] using hS
  refine eq_rationalTaylorCoefficient_of_residual t₀ Q (fun _ ↦ z)
    (fun l ↦ PowerSeries.coeff l F) j (fun i ↦ by rw [Fin.fin_one_eq_zero i]; exact hF0) hSQ
    (fun l _ _ ↦ by simp) (fun l hl _ ↦ ?_) j le_rfl
  set P := Polynomial.taylor (-t₀) (PowerSeries.trunc (l + 1) F)
  have hTP : Polynomial.taylor t₀ P = PowerSeries.trunc (l + 1) F := by
    rw [Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero]
  have hcoef : ∀ i ≤ l, (Polynomial.taylor t₀ P).coeff i = PowerSeries.coeff i F := by
    intro i hi
    simp [hTP, PowerSeries.coeff_trunc, Nat.lt_succ_of_le hi]
  have hjet : polynomialJet t₀ P = fun _ : Fin 1 ↦ z := by
    funext i
    rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff, Fin.fin_one_eq_zero i, Fin.val_zero,
      hcoef 0 (Nat.zero_le _), hF0]
  have hres := taylorCoefficient_residual_eq t₀ Q P hl
  rw [hjet, ← aeval_initialJetSeparant, hcoef l le_rfl,
    differentialSpecialization_specializedFamilyEquation, familyMultiplier_affineFamily] at hres
  have hprefix : (fun i : Fin l ↦ (Polynomial.taylor t₀ P).coeff i.val) =
      fun i ↦ PowerSeries.coeff i.val F := funext fun i ↦ hcoef i.val i.isLt.le
  rw [hprefix] at hres
  rw [hres, ← Polynomial.coeff_coe, Nat.sub_zero]
  rw [coe_taylor_multiplierEval_affineMultiplier, hTP, ← eval_affineSeriesEquation]
  exact PowerSeries.coeff_eval_trunc_eq_zero hE (Nat.lt_succ_self l)

/-- Positive-order coefficients are quotients of chart numerators by separant powers.

Let `R ∈ K[X, Y, Z]` over a field `K` and write `S(α, β, z) = R_Z(t₀, α + β t₀, z)`.
Suppose `S(α, β, z) ≠ 0`, and write `W = X - t₀`.
Let `E` be a power series with zero constant term and `R(t₀ + W, α + β (t₀ + W), z + E) = 0`.
For `j ≥ 1`, the coefficient of `W ^ j` in `E` is `N_j(α, β, z) / S(α, β, z)^(2j - 1)`.
Here `N_j` is the chart numerator at center `t₀` with separant exponent `2j - 1`. -/
theorem coeff_eq_chartNumerator_div_of_constantCoeff_eq_zero (R : MvPolynomial AffineVar K)
    (t₀ α β z : K)
    (hS : eval (fun v ↦ v.elim z ![t₀, α + β * t₀]) (pderiv none R) ≠ 0)
    {E : PowerSeries K} (hE0 : PowerSeries.constantCoeff E = 0)
    (hE : (affineSeriesEquation t₀ α β R).eval (PowerSeries.C z + E) = 0)
    {j : ℕ} (hj : 1 ≤ j) :
    PowerSeries.coeff j E =
      aeval (Sum.elim (fun _ ↦ z) ![α, β]) (chartNumerator t₀ affineFamily R (2 * j - 1) j) /
        aeval (Sum.elim (fun _ ↦ z) ![α, β]) (chartSeparant t₀ affineFamily R) ^ (2 * j - 1) := by
  have hpt : aeval (Sum.elim (fun _ ↦ z) ![α, β]) (chartSeparant t₀ affineFamily R) ≠ 0 := by
    rw [aeval_chartSeparant]
    simpa [Function.comp_def, coe_aeval_eq_eval, familyMultiplier_affineFamily, mul_comm] using hS
  rw [aeval_chartNumerator t₀ affineFamily R _ le_rfl hpt,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hpt),
    ← coeff_C_add_eq_chartCoefficient R t₀ α β z hS hE0 hE j, map_add,
    PowerSeries.coeff_C]
  simp [Nat.one_le_iff_ne_zero.mp hj]

end ReedSolomon
