/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.RegularLift
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for regular lifting

* The field form, with the hypotheses `(k + r choose r) ≠ 0` and `S ≠ 0`,
  and its variant below a prime characteristic, follow from the unit form.
* For `y' = y` (`Q = Y₁ - Y₀`) at center `0` over `ℚ`, the residual of `P = 1 + X` is `-X`, and
  the unique lift coefficient of order `2` is `1 / 2`, the next Taylor coefficient of `exp`.
* Over `ZMod 2` the binomial `(2 choose 1)` vanishes and no coefficient lifts `1 + X`, so the
  unit hypothesis is needed.
* For `Q = Y₀ ^ 2 - 1` with `r = k = 0` over `ℚ`, both `γ = 1` and `γ = -1` lift `P = 0`, so the
  hypothesis `0 < k` is needed.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- The field form: the two nonvanishing hypotheses give the unit slope. -/
example {F : Type*} [Field F] {r k : ℕ} (hk : 0 < k) (Q : DifferentialPolynomial F r)
    (center : F) (P : Polynomial F)
    (hresidual : Polynomial.X ^ k ∣ shiftedJetSubstitution center P Q)
    (hbin : ((k + r).choose r : F) ≠ 0)
    (hsep : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0) :
    ∃! γ : F, Polynomial.X ^ (k + 1) ∣
      shiftedJetSubstitution center (P + Polynomial.hassePerturbation center γ (k + r)) Q :=
  existsUnique_regularLiftCoefficient hk Q center P hresidual
    (isUnit_iff_ne_zero.mpr (mul_ne_zero hbin hsep))

/-- Below a prime characteristic `p > k + r`, only the separant hypothesis remains. -/
example {F : Type*} [Field F] {p r k : ℕ} [CharP F p] (hp : p.Prime) (hkr : k + r < p)
    (hk : 0 < k) (Q : DifferentialPolynomial F r) (center : F) (P : Polynomial F)
    (hresidual : (Polynomial.X - Polynomial.C center) ^ k ∣ differentialSpecialization Q P)
    (hsep : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0) :
    ∃! γ : F, (Polynomial.X - Polynomial.C center) ^ (k + 1) ∣
      differentialSpecialization Q (P + Polynomial.hassePerturbation center γ (k + r)) :=
  existsUnique_regularLiftCoefficient_centered hk Q center P hresidual
    (isUnit_iff_ne_zero.mpr (mul_ne_zero
      (Polynomial.natCast_choose_ne_zero_of_lt_charP hp hkr (Nat.le_add_left r k)) hsep))

/-- The equation `y' = y`, as the differential polynomial `Y₁ - Y₀`. -/
private abbrev expEquation (F : Type*) [CommRing F] : DifferentialPolynomial F 1 :=
  X (some 1) - X (some 0)

private theorem jetEvaluation_separant_expEquation (F : Type*) [CommRing F] [Nontrivial F]
    (jet : Fin 2 → F) :
    jetEvaluation (separant (expEquation F) (Fin.last 1)) 0 jet = 1 := by
  simp [separant, jetEvaluation, expEquation, pderiv_X, Fin.last]

/-- The residual of `y' = y` at center `0` is `P' - P`. -/
private theorem shiftedJetSubstitution_expEquation (F : Type*) [CommRing F] (P : Polynomial F) :
    shiftedJetSubstitution 0 P (expEquation F) = Polynomial.derivative P - P := by
  simp [expEquation, Polynomial.hasseDeriv_one]

/-- The residual of `1 + X` for `y' = y` is `-X`. -/
private theorem shiftedJetSubstitution_expEquation_one_add_X (F : Type*) [CommRing F] :
    shiftedJetSubstitution 0 (1 + Polynomial.X) (expEquation F) = -Polynomial.X := by
  rw [shiftedJetSubstitution_expEquation]
  simp

/-- Over `ℚ`, the unique coefficient that lifts `1 + X` for `y' = y` is `1 / 2`. -/
example (γ : ℚ) :
    Polynomial.X ^ (1 + 1) ∣ shiftedJetSubstitution 0
        (1 + Polynomial.X + Polynomial.hassePerturbation 0 γ (1 + 1)) (expEquation ℚ) ↔
      γ = 1 / 2 := by
  have hlift := existsUnique_regularLiftCoefficient (k := 1) one_pos (expEquation ℚ) 0
    (1 + Polynomial.X) (by rw [shiftedJetSubstitution_expEquation_one_add_X]; simp)
    (by rw [jetEvaluation_separant_expEquation]; norm_num)
  have hhalf : Polynomial.X ^ (1 + 1) ∣ shiftedJetSubstitution 0
      (1 + Polynomial.X + Polynomial.hassePerturbation 0 (1 / 2) (1 + 1)) (expEquation ℚ) := by
    rw [shiftedJetSubstitution_expEquation]
    refine ⟨-Polynomial.C (1 / 2), ?_⟩
    simp only [Polynomial.hassePerturbation, map_zero, sub_zero, Polynomial.derivative_add,
      Polynomial.derivative_one, Polynomial.derivative_X, Polynomial.derivative_C_mul_X_pow]
    norm_num
  exact ⟨fun h ↦ hlift.unique h hhalf, fun h ↦ h ▸ hhalf⟩

/-- Over `ZMod 2`, `(2 choose 1) = 0` and no coefficient lifts `1 + X` for `y' = y`. -/
example : ¬∃ γ : ZMod 2, Polynomial.X ^ (1 + 1) ∣ shiftedJetSubstitution 0
    (1 + Polynomial.X + Polynomial.hassePerturbation 0 γ (1 + 1)) (expEquation (ZMod 2)) := by
  rintro ⟨γ, hγ⟩
  have hcoeff := Polynomial.X_pow_dvd_iff.mp hγ 1 (by norm_num)
  have hchoose : ((Nat.choose (1 + 1) 1 : ℕ) : ZMod 2) = 0 := by decide
  rw [coeff_shiftedJetSubstitution_add_hassePerturbation one_pos, hchoose,
    shiftedJetSubstitution_expEquation_one_add_X] at hcoeff
  simp at hcoeff

/-- `Y₀ ^ 2 - 1` as a differential polynomial of order `0`. -/
private abbrev squareEquation : DifferentialPolynomial ℚ 0 :=
  X (some 0) ^ 2 - 1

private theorem X_dvd_squareEquation_iff (γ : ℚ) :
    Polynomial.X ^ (0 + 1) ∣ shiftedJetSubstitution 0
        (0 + Polynomial.hassePerturbation 0 γ (0 + 0)) squareEquation ↔ γ ^ 2 = 1 := by
  have h : shiftedJetSubstitution 0 (0 + Polynomial.hassePerturbation 0 γ (0 + 0))
      squareEquation = Polynomial.C (γ ^ 2 - 1) := by
    simp [squareEquation, Polynomial.hassePerturbation]
  rw [h, zero_add, pow_one, Polynomial.X_dvd_iff, Polynomial.coeff_C_zero, sub_eq_zero]

/-- The hypothesis `0 < k` is needed: at `k = 0` the lift of `P = 0` is not unique. -/
example : ¬∃! γ : ℚ, Polynomial.X ^ (0 + 1) ∣ shiftedJetSubstitution 0
    (0 + Polynomial.hassePerturbation 0 γ (0 + 0)) squareEquation := by
  rintro ⟨γ, -, huniq⟩
  have h1 := huniq 1 ((X_dvd_squareEquation_iff 1).mpr (by norm_num))
  have h2 := huniq (-1) ((X_dvd_squareEquation_iff (-1)).mpr (by norm_num))
  linarith

end

end PolynomialDifferential
