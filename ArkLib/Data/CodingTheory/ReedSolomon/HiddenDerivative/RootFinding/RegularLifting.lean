/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.LocalIdentity
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
`X^k`.  This is equivalent to the paper's centered modulus `(X-alpha)^k`; a separate adapter to
the root solver's unshifted `differentialSpecialization` can transport the theorem without
changing its algebraic content.

This file does not formalize the singular recursion or the general-characteristic branching count
of [Kop15, Corollary 4.5].

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

end

end ReedSolomon.HiddenDerivative
