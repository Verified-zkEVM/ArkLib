/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.LocalIdentity
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.DifferentialEquation
import ArkLib.ToMathlib.MvPolynomial.FirstOrderTaylor
import ArkLib.ToMathlib.Polynomial.HasseTaylor.Lifting

/-!
# Regular coefficient lifting for polynomial differential equations

This file formalizes the regular power-series step at the core of [Kop15, Theorem 4.4].
For a differential polynomial in `X, Y₀, ..., Y_r`, changing a candidate by
`gamma * (X - alpha)^(k+r)` changes its highest Hasse derivative first in shifted degree `k`.
All lower derivative coordinates change only in degrees at least `k+1`.  A first-order Taylor
congruence therefore makes the degree-`k` residual coefficient affine in `gamma`, with slope

```text
choose (k+r) r * separant(alpha, initialJet).
```

When that slope is nonzero, there is exactly one coefficient that raises residual divisibility
from `(X-alpha)^k` to `(X-alpha)^(k+1)`.  The generic theorem assumes the exact binomial
nonvanishing condition from the source; the below-characteristic corollary discharges it from
`k+r < ringChar F`, the specialization used by the all-rate Reed--Solomon development.

The result is stated after Taylor shifting, using `shiftedJetSubstitution`, so the modulus is
`X^k`.  This is equivalent to the paper's centered modulus `(X-alpha)^k`; the adapter
`taylor_differentialSpecialization` identifies this presentation with
the root solver's unshifted `differentialSpecialization` without changing its algebraic content.

This file does not formalize the singular recursion or the general-characteristic branching count
of [Kop15, Corollary 4.5].  Its pivot is the literal top coordinate `Fin.last r`; applying it to
the root solver's arbitrary highest active coordinate requires restriction or reindexing of the
active jet prefix.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15]
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} [Field F] {r k : ℕ}

/-! ### Shifted jets and their lift increment -/

/-- Values substituted for `X, Y₀, ..., Y_r` after translating the center to the origin. -/
def shiftedJetValues (center : F) (P : F[X]) : JetVariable r → F[X]
  | none => C center + X
  | some j => taylor center (hasseDeriv j P)

/-- Coordinate-wise change in a shifted Hasse jet after adding
`gamma * (X-center)^(k+r)` to the candidate. -/
def regularLiftIncrement (gamma : F) (k r : ℕ) : JetVariable r → F[X]
  | none => 0
  | some j => C (((k + r).choose j : F) * gamma) * X ^ (k + r - j)

/-- Add the centered coefficient used in a regular lift of residual order `k`. -/
def regularLiftCandidate (center gamma : F) (k r : ℕ) (P : F[X]) : F[X] :=
  P + hassePerturbation center gamma (k + r)

/-- `shiftedJetSubstitution` is evaluation at the explicitly named shifted jet values. -/
theorem shiftedJetSubstitution_eq_eval₂Hom (Q : DifferentialPolynomial F r)
    (center : F) (P : F[X]) :
    shiftedJetSubstitution center P Q =
      MvPolynomial.eval₂Hom Polynomial.C (shiftedJetValues center P) Q := by
  rfl

/-- The constant term of a shifted separant is its scalar evaluation on the initial Hasse jet. -/
theorem eval_zero_shiftedJetSubstitution_separant (Q : DifferentialPolynomial F r)
    (center : F) (P : F[X]) :
    (shiftedJetSubstitution center P (separant Q (Fin.last r))).eval 0 =
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) := by
  rw [← taylor_differentialSpecialization]
  rw [← coeff_zero_eq_eval_zero, taylor_coeff_zero]
  exact
    eval_differentialSpecialization (separant Q (Fin.last r)) P center

/-- A regular candidate lift changes its shifted jet by `regularLiftIncrement`. -/
theorem shiftedJetValues_regularLiftCandidate (center gamma : F) (k r : ℕ) (P : F[X]) :
    shiftedJetValues center (regularLiftCandidate center gamma k r P) =
      shiftedJetValues center P + regularLiftIncrement gamma k r := by
  funext v
  rcases v with _ | j
  · simp [shiftedJetValues, regularLiftIncrement]
  · rw [shiftedJetValues, regularLiftCandidate,
      hasseDeriv_add_hassePerturbation P center gamma (k + r) j.val]
    change taylor center
        (hasseDeriv j.val P +
          hassePerturbation center (((k + r).choose j.val : F) * gamma)
            (k + r - j.val)) =
      taylor center (hasseDeriv j.val P) +
        C (((k + r).choose j.val : F) * gamma) * X ^ (k + r - j.val)
    rw [map_add, taylor_hassePerturbation]

/-- The highest-derivative coordinate changes first in degree `k`. -/
theorem regularLiftIncrement_top (gamma : F) (k r : ℕ) :
    regularLiftIncrement gamma k r (some (Fin.last r)) =
      C (((k + r).choose r : F) * gamma) * X ^ k := by
  simp [regularLiftIncrement]

/-- The highest-derivative increment is divisible by `X^k`. -/
theorem X_pow_dvd_regularLiftIncrement_top (gamma : F) (k r : ℕ) :
    X ^ k ∣ regularLiftIncrement gamma k r (some (Fin.last r)) := by
  rw [regularLiftIncrement_top]
  exact dvd_mul_left _ _

/-- Every non-pivot coordinate increment is already divisible by `X^(k+1)`. -/
theorem X_pow_succ_dvd_regularLiftIncrement_of_ne_top (gamma : F) (k r : ℕ)
    (v : JetVariable r) (hv : v ≠ some (Fin.last r)) :
    X ^ (k + 1) ∣ regularLiftIncrement gamma k r v := by
  rcases v with _ | j
  · simp [regularLiftIncrement]
  · have hjr : j.val < r := by
      have hjle : j.val ≤ r := Nat.le_of_lt_succ j.isLt
      have hjne : j.val ≠ r := by
        intro h
        apply hv
        simp only [Option.some.injEq]
        apply Fin.ext
        simpa using h
      omega
    exact dvd_mul_of_dvd_right (pow_dvd_pow X (by omega : k + 1 ≤ k + r - j.val)) _

/-! ### The affine residual law -/

/-- Modulo `X^(k+1)`, a regular lift changes the differential residual only through the
highest-variable partial derivative. -/
theorem X_pow_succ_dvd_shiftedJetSubstitution_regularLiftCandidate_sub (hk : 0 < k)
    (Q : DifferentialPolynomial F r) (center gamma : F) (P : F[X]) :
    X ^ (k + 1) ∣
      shiftedJetSubstitution center (regularLiftCandidate center gamma k r P) Q -
        shiftedJetSubstitution center P Q -
      shiftedJetSubstitution center P (MvPolynomial.pderiv (some (Fin.last r)) Q) *
            regularLiftIncrement gamma k r (some (Fin.last r)) := by
  rw [shiftedJetSubstitution_eq_eval₂Hom, shiftedJetSubstitution_eq_eval₂Hom,
    shiftedJetSubstitution_eq_eval₂Hom, shiftedJetValues_regularLiftCandidate]
  apply MvPolynomial.pow_succ_dvd_eval₂Hom_add_sub_pderiv Polynomial.C
      (shiftedJetValues center P) (regularLiftIncrement gamma k r) Finset.univ Q
      (some (Fin.last r)) X k hk
  · simp
  · exact X_pow_dvd_regularLiftIncrement_top gamma k r
  · intro v _ hv
    exact X_pow_succ_dvd_regularLiftIncrement_of_ne_top gamma k r v hv
  · simp

/-- The first unresolved residual coefficient depends affinely on the lifted candidate
coefficient.  Its slope is the source's binomial multiplier times the separant at the initial
jet. -/
theorem coeff_shiftedJetSubstitution_regularLiftCandidate (hk : 0 < k)
    (Q : DifferentialPolynomial F r) (center gamma : F) (P : F[X]) :
    (shiftedJetSubstitution center (regularLiftCandidate center gamma k r P) Q).coeff k =
      (shiftedJetSubstitution center P Q).coeff k +
        (((k + r).choose r : F) * gamma) *
          jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) := by
  have hdiv := X_pow_succ_dvd_shiftedJetSubstitution_regularLiftCandidate_sub
    (k := k) hk Q center gamma P
  have hcoeff := Polynomial.X_pow_dvd_iff.mp hdiv k (by omega)
  rw [regularLiftIncrement_top] at hcoeff
  simp only [coeff_sub, ← mul_assoc, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
    coeff_mul_C] at hcoeff
  change
    (shiftedJetSubstitution center (regularLiftCandidate center gamma k r P) Q).coeff k -
        (shiftedJetSubstitution center P Q).coeff k -
      (shiftedJetSubstitution center P (separant Q (Fin.last r))).coeff 0 *
          ((k + r).choose r : F) * gamma = 0 at hcoeff
  rw [coeff_zero_eq_eval_zero, eval_zero_shiftedJetSubstitution_separant] at hcoeff
  rw [sub_eq_zero, sub_eq_iff_eq_add] at hcoeff
  simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hcoeff

/-! ### Unique one-step lifting -/

/-- A polynomial already divisible by `X^k` gains one more factor exactly when its coefficient
in degree `k` vanishes. -/
theorem X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd (p : F[X]) (k : ℕ)
    (hp : X ^ k ∣ p) : X ^ (k + 1) ∣ p ↔ p.coeff k = 0 := by
  constructor
  · intro h
    exact Polynomial.X_pow_dvd_iff.mp h k (by omega)
  · intro hk
    rw [Polynomial.X_pow_dvd_iff]
    intro i hi
    by_cases hik : i < k
    · exact Polynomial.X_pow_dvd_iff.mp hp i hik
    · have : i = k := by omega
      simpa [this] using hk

/-- A regular candidate lift preserves the already established residual divisibility. -/
theorem X_pow_dvd_shiftedJetSubstitution_regularLiftCandidate (hk : 0 < k)
    (Q : DifferentialPolynomial F r) (center gamma : F) (P : F[X])
    (hresidual : X ^ k ∣ shiftedJetSubstitution center P Q) :
    X ^ k ∣ shiftedJetSubstitution center (regularLiftCandidate center gamma k r P) Q := by
  let pivot : JetVariable r := some (Fin.last r)
  let linearTerm : F[X] :=
    shiftedJetSubstitution center P (separant Q (Fin.last r)) *
      regularLiftIncrement gamma k r pivot
  have hnext := X_pow_succ_dvd_shiftedJetSubstitution_regularLiftCandidate_sub
    (k := k) hk Q center gamma P
  have hremainder :
      X ^ k ∣
        shiftedJetSubstitution center (regularLiftCandidate center gamma k r P) Q -
          shiftedJetSubstitution center P Q - linearTerm := by
    exact (pow_dvd_pow X (Nat.le_succ k)).trans (by simpa [linearTerm, pivot, separant] using hnext)
  have hincrement : X ^ k ∣ regularLiftIncrement gamma k r pivot := by
    simpa [pivot] using X_pow_dvd_regularLiftIncrement_top gamma k r
  have hlinear : X ^ k ∣ linearTerm := by
    exact dvd_mul_of_dvd_right hincrement _
  have hsum := hremainder.add (hresidual.add hlinear)
  have heq :
      shiftedJetSubstitution center (regularLiftCandidate center gamma k r P) Q =
        (shiftedJetSubstitution center (regularLiftCandidate center gamma k r P) Q -
            shiftedJetSubstitution center P Q - linearTerm) +
          (shiftedJetSubstitution center P Q + linearTerm) := by
    ring
  rw [heq]
  exact hsum

/-- Exact nonresonant form of the regular one-step lift.

This is the formal counterpart of [Kop15, Theorem 4.4].  The binomial hypothesis is stated
directly, as in the source, so the theorem also applies in characteristic zero and at any
nonresonant step in positive characteristic. -/
theorem existsUnique_regularLiftCoefficient (hk : 0 < k)
    (Q : DifferentialPolynomial F r) (center : F) (P : F[X])
    (hresidual : X ^ k ∣ shiftedJetSubstitution center P Q)
    (hbinomial : ((k + r).choose r : F) ≠ 0)
    (hseparant :
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0) :
    ∃! gamma : F,
      X ^ (k + 1) ∣
        shiftedJetSubstitution center (regularLiftCandidate center gamma k r P) Q := by
  let beta := (shiftedJetSubstitution center P Q).coeff k
  let slope := ((k + r).choose r : F) *
    jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P)
  have hslope : slope ≠ 0 := mul_ne_zero hbinomial hseparant
  let gamma₀ := -slope⁻¹ * beta
  have hcoeff₀ :
      (shiftedJetSubstitution center (regularLiftCandidate center gamma₀ k r P) Q).coeff k =
        0 := by
    rw [coeff_shiftedJetSubstitution_regularLiftCandidate (k := k) hk]
    change beta + ((k + r).choose r : F) * gamma₀ *
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) = 0
    calc
      beta + ((k + r).choose r : F) * gamma₀ *
          jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) =
          beta - (slope * slope⁻¹) * beta := by
            simp only [gamma₀]
            dsimp only [slope]
            ring
      _ = 0 := by rw [mul_inv_cancel₀ hslope]; ring
  have hresidual₀ := X_pow_dvd_shiftedJetSubstitution_regularLiftCandidate
    (k := k) hk Q center gamma₀ P hresidual
  have hlift₀ :
      X ^ (k + 1) ∣
        shiftedJetSubstitution center (regularLiftCandidate center gamma₀ k r P) Q :=
    (X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd _ k hresidual₀).2 hcoeff₀
  refine ⟨gamma₀, hlift₀, ?_⟩
  intro gamma hgamma
  have hcoeff :
      (shiftedJetSubstitution center (regularLiftCandidate center gamma k r P) Q).coeff k =
        0 := Polynomial.X_pow_dvd_iff.mp hgamma k (by omega)
  have heq :
      (shiftedJetSubstitution center (regularLiftCandidate center gamma k r P) Q).coeff k =
        (shiftedJetSubstitution center (regularLiftCandidate center gamma₀ k r P) Q).coeff k := by
    rw [hcoeff, hcoeff₀]
  rw [coeff_shiftedJetSubstitution_regularLiftCandidate (k := k) hk,
    coeff_shiftedJetSubstitution_regularLiftCandidate (k := k) hk,
    add_left_cancel_iff] at heq
  apply mul_left_cancel₀ hslope
  simpa [slope, mul_comm, mul_left_comm, mul_assoc] using heq

/-- Below the characteristic, every lift step whose new candidate coefficient has degree at most
`D` is nonresonant and therefore has a unique continuation coefficient. -/
theorem existsUnique_regularLiftCoefficient_of_le_of_lt_ringChar (hk : 0 < k)
    (Q : DifferentialPolynomial F r) (center : F) (P : F[X]) (D : ℕ)
    (hdegree : k + r ≤ D) (hD : D < ringChar F)
    (hresidual : X ^ k ∣ shiftedJetSubstitution center P Q)
    (hseparant :
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0) :
    ∃! gamma : F,
      X ^ (k + 1) ∣
        shiftedJetSubstitution center (regularLiftCandidate center gamma k r P) Q := by
  apply existsUnique_regularLiftCoefficient (k := k) hk Q center P hresidual
  · exact Polynomial.natCast_choose_ne_zero_of_lt_ringChar
      (hdegree.trans_lt hD) (by omega)
  · exact hseparant

/-! ### Centered source-facing statements -/

/-- Taylor translation identifies divisibility by `X^m` with divisibility by the centered
factor `(X - C center)^m`. -/
theorem X_pow_dvd_taylor_iff_X_sub_C_pow_dvd (p : F[X]) (center : F) (m : ℕ) :
    X ^ m ∣ taylor center p ↔ (X - C center) ^ m ∣ p := by
  rw [X_pow_dvd_taylor_iff, X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero]

/-- Source-facing centered form of [Kop15, Theorem 4.4]. -/
theorem existsUnique_regularLiftCoefficient_centered (hk : 0 < k)
    (Q : DifferentialPolynomial F r) (center : F) (P : F[X])
    (hresidual : (X - C center) ^ k ∣ differentialSpecialization Q P)
    (hbinomial : ((k + r).choose r : F) ≠ 0)
    (hseparant :
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0) :
    ∃! gamma : F,
      (X - C center) ^ (k + 1) ∣
        differentialSpecialization Q (regularLiftCandidate center gamma k r P) := by
  have hshifted : X ^ k ∣ shiftedJetSubstitution center P Q := by
    rw [← taylor_differentialSpecialization,
      X_pow_dvd_taylor_iff_X_sub_C_pow_dvd]
    exact hresidual
  obtain ⟨gamma, hgamma, hunique⟩ :=
    existsUnique_regularLiftCoefficient (k := k) hk Q center P hshifted hbinomial hseparant
  refine ⟨gamma, ?_, ?_⟩
  · change (X - C center) ^ (k + 1) ∣
      differentialSpecialization Q (regularLiftCandidate center gamma k r P)
    rw [← X_pow_dvd_taylor_iff_X_sub_C_pow_dvd,
      taylor_differentialSpecialization]
    exact hgamma
  · intro gamma' hgamma'
    apply hunique gamma'
    change (X - C center) ^ (k + 1) ∣
      differentialSpecialization Q (regularLiftCandidate center gamma' k r P) at hgamma'
    rw [← taylor_differentialSpecialization,
      X_pow_dvd_taylor_iff_X_sub_C_pow_dvd]
    exact hgamma'

/-- Below-characteristic specialization of the centered one-step lift used by the all-rate
Reed--Solomon proof. -/
theorem existsUnique_regularLiftCoefficient_centered_of_le_of_lt_ringChar (hk : 0 < k)
    (Q : DifferentialPolynomial F r) (center : F) (P : F[X]) (D : ℕ)
    (hdegree : k + r ≤ D) (hD : D < ringChar F)
    (hresidual : (X - C center) ^ k ∣ differentialSpecialization Q P)
    (hseparant :
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0) :
    ∃! gamma : F,
      (X - C center) ^ (k + 1) ∣
        differentialSpecialization Q (regularLiftCandidate center gamma k r P) := by
  apply existsUnique_regularLiftCoefficient_centered (k := k) hk Q center P hresidual
  · exact Polynomial.natCast_choose_ne_zero_of_lt_ringChar
      (hdegree.trans_lt hD) (by omega)
  · exact hseparant

/-- Regular-jet packaged form of the exact centered lift.  The equation-at-the-center conjunct
belongs to the root-counting interface; the one-step algebra uses its separant conjunct. -/
theorem existsUnique_regularLiftCoefficient_centered_of_isRegularJet (hk : 0 < k)
    (Q : DifferentialPolynomial F r) (center : F) (P : F[X])
    (hregular : IsRegularJet Q (Fin.last r) center (polynomialJet center P))
    (hresidual : (X - C center) ^ k ∣ differentialSpecialization Q P)
    (hbinomial : ((k + r).choose r : F) ≠ 0) :
    ∃! gamma : F,
      (X - C center) ^ (k + 1) ∣
        differentialSpecialization Q (regularLiftCandidate center gamma k r P) := by
  exact existsUnique_regularLiftCoefficient_centered hk Q center P hresidual hbinomial hregular.2

/-- Regular-jet packaged form used below the characteristic bound. -/
theorem existsUnique_regularLiftCoefficient_centered_of_isRegularJet_of_le_of_lt_ringChar
    (hk : 0 < k) (Q : DifferentialPolynomial F r) (center : F) (P : F[X]) (D : ℕ)
    (hregular : IsRegularJet Q (Fin.last r) center (polynomialJet center P))
    (hdegree : k + r ≤ D) (hD : D < ringChar F)
    (hresidual : (X - C center) ^ k ∣ differentialSpecialization Q P) :
    ∃! gamma : F,
      (X - C center) ^ (k + 1) ∣
        differentialSpecialization Q (regularLiftCandidate center gamma k r P) := by
  exact existsUnique_regularLiftCoefficient_centered_of_le_of_lt_ringChar
    hk Q center P D hdegree hD hresidual hregular.2

end

end ReedSolomon.HiddenDerivative
