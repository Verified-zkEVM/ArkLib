/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RegularIteration

/-!
# Direct regular lifting

Let `Q(X, Y₀, ..., Y_r)` be a differential polynomial over a commutative ring and `center` a
point. For `0 < k`, the coefficient of `X ^ k` in the residual of `P + γ (X - center) ^ (k + r)`
is `β + σ γ`, where `β` is that coefficient for `P` and `σ = (k + r choose r) S` is the slope,
`S` being the separant value at the Hasse jet of `P`. When `σ` is a unit the root `-σ⁻¹ β` is the
unique lift coefficient, so each lifting step is a division rather than a search over the ring.

`regularLift` performs this step and `regularIterate` repeats it at residual orders
`1, 2, ..., n`. Every step leaves the Hasse jet through order `r` unchanged, so all slopes along
the iteration are computed from the initial jet. When that jet lies on `Q = 0` and the slopes are
units, the `n`-th iterate has residual divisible by `X ^ (n + 1)`.

The main result, `solution_iff_eq_regularIterate`, identifies the solutions: if `P₀` has degree at
most `r`, then a polynomial of degree at most `D` solves `Q = 0` and has the Hasse jet of `P₀`
through order `r` exactly when it equals the iterate of `P₀` at step `D - r` and that iterate is a
solution of degree at most `D`. The final degree and solution checks cannot be omitted: the
iteration only controls the residual below order `D - r + 1`.

## Main statements

* `regularLiftCoefficient`, `regularLift` and `regularIterate`: the lifting step and its
  iteration.
* `coeff_shiftedJetSubstitution_add_hassePerturbation_eq_iff` and
  `X_pow_succ_dvd_shiftedJetSubstitution_regularLift`: the lift coefficient is the unique root.
* `polynomialJet_regularIterate`, `coeff_taylor_regularIterate_succ` and
  `X_pow_succ_dvd_shiftedJetSubstitution_regularIterate`: invariants of the iteration.
* `eq_regularIterate_of_polynomialJet_eq` and `solution_iff_eq_regularIterate`: the solutions
  with a given initial jet.

## References

This file ports the semantic content of `RootFinding/Regular/DirectRegularCoefficient.lean` and
`RootFinding/Regular/DirectRegularIteration.lean` under
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source defined executable versions over a field,
on `CompPoly` polynomials, and compared them with an exhaustive scan over a finite field. Here the
definitions are noncomputable, on `Polynomial`, over a commutative ring, and a unit slope replaces
the nonzero slope:

* `effectiveDirectRegularCoefficient` (`none` for a zero slope, otherwise `-β / σ`) corresponds to
  `regularLiftCoefficient`, which uses `Ring.inverse` and is correct whenever `σ` is a unit.
  `effectiveDirectRegularCoefficient_sound_unique` corresponds to
  `coeff_shiftedJetSubstitution_add_hassePerturbation_eq_iff`.
* `effectiveResidualCoeff_affine` and `effectiveRegularSlope_eq` are
  `coeff_shiftedJetSubstitution_add_hassePerturbation` in
  `ArkLib.Data.Polynomial.Differential.RegularLift`.
* `directRegularIteration` corresponds to `regularIterate`; its degree bound
  `directRegularIteration_natDegree_le` to `natDegree_regularIterate_le`.
* `directRegularSolution_eq_some_iff` corresponds to `solution_iff_eq_regularIterate`, with unit
  slopes in place of `IsRegularJet` and `D < ringChar F`, and without `Finite F`.

Deferred: the `CompPoly` definitions, the two-evaluation slope recovery, and the comparison with
the exhaustive coefficient scan (`effectiveRegularCoefficients_eq_singleton_of_direct`,
`effectiveDirectRegularCoefficient_exists_of_survivor`,
`directRegularIteration_eq_some_and_candidates`, `directRegularSolution_toFinset_eq`). They
depend on the executable root-finding layer `ReedSolomon/Computation/RootFinding/Lifting/`, which
is not ported.

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Theorem 4.4 and Corollary 4.5.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R] {r k : ℕ}

/-! ### One step -/

/-- The candidate lift coefficient at residual order `k`: `-σ⁻¹ β`, where `β` is the coefficient
of `X ^ k` in the residual of `P` and `σ = (k + r choose r) S` is the slope. `Ring.inverse` sends
a non-unit to `0`, so the value is meaningful only when `σ` is a unit. -/
def regularLiftCoefficient (Q : DifferentialPolynomial R r) (center : R) (k : ℕ) (P : R[X]) : R :=
  -(Ring.inverse (((k + r).choose r : R) *
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P)) *
    (shiftedJetSubstitution center P Q).coeff k)

/-- One direct lifting step: add `γ (X - center) ^ (k + r)` with `γ = regularLiftCoefficient`. -/
def regularLift (Q : DifferentialPolynomial R r) (center : R) (k : ℕ) (P : R[X]) : R[X] :=
  P + hassePerturbation center (regularLiftCoefficient Q center k P) (k + r)

/-- For `0 < k` and a unit slope, the coefficient of `X ^ k` in the residual of
`P + γ (X - center) ^ (k + r)` vanishes exactly when `γ = regularLiftCoefficient Q center k P`.
The hypothesis `0 < k` is needed because the affine law fails at `k = 0`. -/
theorem coeff_shiftedJetSubstitution_add_hassePerturbation_eq_iff (hk : 0 < k)
    (Q : DifferentialPolynomial R r) (center : R) (P : R[X]) (γ : R)
    (hslope : IsUnit (((k + r).choose r : R) *
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P))) :
    (shiftedJetSubstitution center (P + hassePerturbation center γ (k + r)) Q).coeff k = 0 ↔
      γ = regularLiftCoefficient Q center k P := by
  rw [coeff_shiftedJetSubstitution_add_hassePerturbation hk, regularLiftCoefficient,
    mul_right_comm]
  constructor
  · intro h
    rw [eq_neg_of_add_eq_zero_left h, mul_neg, neg_neg, Ring.inverse_mul_cancel_left _ _ hslope]
  · rintro rfl
    rw [mul_neg, Ring.mul_inverse_cancel_left _ _ hslope, add_neg_cancel]

/-- If `0 < k`, `X ^ k` divides the residual of `P` and the slope is a unit, then `X ^ (k + 1)`
divides the residual of `regularLift Q center k P`. -/
theorem X_pow_succ_dvd_shiftedJetSubstitution_regularLift (hk : 0 < k)
    (Q : DifferentialPolynomial R r) (center : R) (P : R[X])
    (hresidual : X ^ k ∣ shiftedJetSubstitution center P Q)
    (hslope : IsUnit (((k + r).choose r : R) *
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P))) :
    X ^ (k + 1) ∣ shiftedJetSubstitution center (regularLift Q center k P) Q := by
  rw [regularLift, X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd
    (X_pow_dvd_shiftedJetSubstitution_add_hassePerturbation Q center _ P hresidual),
    coeff_shiftedJetSubstitution_add_hassePerturbation_eq_iff hk Q center P _ hslope]

/-- For `0 < k` the lift leaves the Hasse jet through order `r` unchanged. -/
theorem polynomialJet_regularLift (hk : 0 < k) (Q : DifferentialPolynomial R r) (center : R)
    (P : R[X]) :
    polynomialJet (d := r) center (regularLift Q center k P) = polynomialJet center P :=
  hasseJet_add_hassePerturbation_of_le P center _ (by omega)

/-! ### Iteration -/

/-- Apply `regularLift` at residual orders `1, 2, ..., n`, starting from `P`. -/
def regularIterate (Q : DifferentialPolynomial R r) (center : R) (P : R[X]) : ℕ → R[X]
  | 0 => P
  | n + 1 => regularLift Q center (n + 1) (regularIterate Q center P n)

@[simp]
theorem regularIterate_zero (Q : DifferentialPolynomial R r) (center : R) (P : R[X]) :
    regularIterate Q center P 0 = P :=
  rfl

theorem regularIterate_succ (Q : DifferentialPolynomial R r) (center : R) (P : R[X]) (n : ℕ) :
    regularIterate Q center P (n + 1) =
      regularLift Q center (n + 1) (regularIterate Q center P n) :=
  rfl

/-- Every iterate has the Hasse jet of the starting polynomial through order `r`. -/
theorem polynomialJet_regularIterate (Q : DifferentialPolynomial R r) (center : R) (P : R[X])
    (n : ℕ) :
    polynomialJet (d := r) center (regularIterate Q center P n) = polynomialJet center P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [regularIterate_succ, polynomialJet_regularLift n.succ_pos, ih]

/-- Step `n + 1` changes only the Taylor coefficient of order `n + 1 + r`, by the lift
coefficient. -/
theorem coeff_taylor_regularIterate_succ (Q : DifferentialPolynomial R r) (center : R)
    (P : R[X]) (n i : ℕ) :
    (taylor center (regularIterate Q center P (n + 1))).coeff i =
      (taylor center (regularIterate Q center P n)).coeff i +
        if i = n + 1 + r then
          regularLiftCoefficient Q center (n + 1) (regularIterate Q center P n) else 0 := by
  rw [regularIterate_succ, regularLift, map_add, coeff_add, taylor_hassePerturbation,
    coeff_C_mul_X_pow]

/-- If `P` has degree at most `r`, the `n`-th iterate has degree at most `r + n`. -/
theorem natDegree_regularIterate_le (Q : DifferentialPolynomial R r) (center : R) {P : R[X]}
    (hP : P.natDegree ≤ r) (n : ℕ) : (regularIterate Q center P n).natDegree ≤ r + n := by
  rw [← natDegree_taylor _ center, natDegree_le_iff_coeff_eq_zero]
  induction n with
  | zero =>
      intro i hi
      exact coeff_eq_zero_of_natDegree_lt ((natDegree_taylor P center).trans_lt (by omega))
  | succ n ih =>
      intro i hi
      rw [coeff_taylor_regularIterate_succ, ih i (by omega), ite_eq_right (by omega), add_zero]

/-- If the initial jet lies on `Q = 0` and the slopes at orders `1, ..., n` are units, then
`X ^ (n + 1)` divides the residual of the `n`-th iterate. All slopes use the initial jet, since
the iteration does not change it. -/
theorem X_pow_succ_dvd_shiftedJetSubstitution_regularIterate (Q : DifferentialPolynomial R r)
    (center : R) (P : R[X]) (n : ℕ)
    (hzero : jetEvaluation Q center (polynomialJet center P) = 0)
    (hslope : ∀ k, 0 < k → k ≤ n → IsUnit (((k + r).choose r : R) *
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P))) :
    X ^ (n + 1) ∣ shiftedJetSubstitution center (regularIterate Q center P n) Q := by
  induction n with
  | zero =>
      rw [zero_add, pow_one, X_dvd_iff, regularIterate_zero, coeff_zero_shiftedJetSubstitution,
        hzero]
  | succ n ih =>
      rw [regularIterate_succ]
      refine X_pow_succ_dvd_shiftedJetSubstitution_regularLift n.succ_pos Q center _
        (ih fun k hk hkn ↦ hslope k hk (by omega)) ?_
      rw [polynomialJet_regularIterate]
      exact hslope (n + 1) n.succ_pos le_rfl

/-! ### Solutions with a given initial jet -/

/-- Let `P` have degree at most `D`, satisfy `Q(X, P, D¹P, ...) = 0`, and have the Hasse jet of
`P₀` through order `r`, where `P₀` has degree at most `r`. If the slopes `(k + r choose r) S`
for `0 < k`, `k + r ≤ D` are units, where `S` is the separant value at that jet, then `P` is the
iterate `regularIterate Q center P₀ (D - r)`.

The proof shows by induction on `n ≤ D - r` that `P` and the `n`-th iterate have the same Taylor
coefficients through order `n + r`. The hypothesis on the degree of `P₀` bounds the degree of the
iterate; without it the iterate keeps the coefficients of `P₀` above order `r`. -/
theorem eq_regularIterate_of_polynomialJet_eq (Q : DifferentialPolynomial R r) (center : R)
    {P₀ P : R[X]} {D : ℕ} (hP₀ : P₀.natDegree ≤ r) (hdegree : P.degree ≤ D)
    (hsolution : differentialSpecialization Q P = 0)
    (hjet : polynomialJet (d := r) center P = polynomialJet center P₀)
    (hslope : ∀ k, 0 < k → k + r ≤ D → IsUnit (((k + r).choose r : R) *
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P₀))) :
    P = regularIterate Q center P₀ (D - r) := by
  have hres : shiftedJetSubstitution center P Q = 0 := by
    rw [← taylor_differentialSpecialization, hsolution, map_zero]
  -- Stage `n` agrees with `P` in all Taylor coefficients of order at most `n + r`.
  have hstage : ∀ n ≤ D - r, ∀ i ≤ n + r,
      (taylor center P).coeff i = (taylor center (regularIterate Q center P₀ n)).coeff i := by
    intro n hn
    induction n with
    | zero =>
        intro i hi
        have h := congrFun (hjet.trans (polynomialJet_regularIterate Q center P₀ 0).symm)
          ⟨i, by omega⟩
        rwa [polynomialJet, polynomialJet, hasseJet_eq_taylor_coeff,
          hasseJet_eq_taylor_coeff] at h
    | succ n ih =>
        have ih := ih (by omega)
        intro i hi
        rw [coeff_taylor_regularIterate_succ]
        rcases Nat.lt_or_ge i (n + 1 + r) with hlt | hge
        · rw [ite_eq_right hlt.ne, add_zero]
          exact ih i (by omega)
        · have hi : i = n + 1 + r := by omega
          subst hi
          have hjetn := polynomialJet_regularIterate Q center P₀ n
          have hunit := hslope (n + 1) n.succ_pos (by omega)
          rw [← hjetn] at hunit
          have hdiff := coeff_shiftedJetSubstitution_sub_eq_of_taylor_coeff_eq (k := n + 1)
            (by omega) Q center (P := regularIterate Q center P₀ n) (P' := P)
            (fun j hj ↦ (ih j (by omega)).symm)
          rw [hres, coeff_zero, zero_sub, neg_eq_iff_eq_neg] at hdiff
          rw [ite_eq_left rfl, regularLiftCoefficient, hdiff, mul_neg, neg_neg,
            Ring.inverse_mul_cancel_left _ _ hunit]
          ring
  have hhigh (S : R[X]) (hS : S.natDegree ≤ D - r + r) (i : ℕ) (hi : D - r + r < i) :
      (taylor center S).coeff i = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [natDegree_taylor]; omega)
  apply taylor_injective center
  ext i
  rcases Nat.lt_or_ge (D - r + r) i with hi | hi
  · rw [hhigh P ((natDegree_le_of_degree_le hdegree).trans (by omega)) i hi,
      hhigh _ ((natDegree_regularIterate_le Q center hP₀ _).trans (by omega)) i hi]
  · exact hstage (D - r) le_rfl i hi

/-- The solutions with a given initial jet. Let `P₀` have degree at most `r` and suppose the
slopes `(k + r choose r) S` for `0 < k`, `k + r ≤ D` are units, where `S` is the separant value
at the Hasse jet of `P₀`. Then `P` has degree at most `D`, solves `Q = 0` and has the Hasse jet of
`P₀` through order `r` exactly when `P` is the iterate `regularIterate Q center P₀ (D - r)`, has
degree at most `D` and solves `Q = 0`.

So there is at most one such solution, and it is found by `D - r` divisions followed by one check.
The check is needed: the iteration only makes the residual vanish below order `D - r + 1`, and for
`D < r` no step runs and `P₀` itself may have degree above `D`. -/
theorem solution_iff_eq_regularIterate (Q : DifferentialPolynomial R r) (center : R)
    {P₀ : R[X]} {D : ℕ} (hP₀ : P₀.natDegree ≤ r)
    (hslope : ∀ k, 0 < k → k + r ≤ D → IsUnit (((k + r).choose r : R) *
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P₀)))
    (P : R[X]) :
    P.degree ≤ D ∧ differentialSpecialization Q P = 0 ∧
        polynomialJet (d := r) center P = polynomialJet center P₀ ↔
      P = regularIterate Q center P₀ (D - r) ∧ P.degree ≤ D ∧
        differentialSpecialization Q P = 0 := by
  constructor
  · rintro ⟨hdegree, hsolution, hjet⟩
    exact ⟨eq_regularIterate_of_polynomialJet_eq Q center hP₀ hdegree hsolution hjet hslope,
      hdegree, hsolution⟩
  · rintro ⟨rfl, hdegree, hsolution⟩
    exact ⟨hdegree, hsolution, polynomialJet_regularIterate Q center P₀ _⟩

end

end PolynomialDifferential
