/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.JetPrefix
public import ArkLib.Data.Polynomial.Differential.RegularLift

/-!
# Uniqueness of solutions with a fixed regular initial jet

Let `Q(X, Y₀, ..., Y_r)` be a differential polynomial over a commutative ring, let `center` be a
point, and write `c_i(P)` for the coefficient of `(X - center) ^ i` in `P` and
`S(P) = (∂Q/∂Y_r)(center, c₀(P), ..., c_r(P))` for the separant value at the Hasse jet of `P`.

If `P` and `P'` have the same coefficients `c_i` for `i < k + r`, with `0 < k`, then the
coefficients of `X ^ k` in their residuals `Q(center + X, P(center + X), ...)` differ by
`(k + r choose r) S(P) (c_(k+r)(P') - c_(k+r)(P))`. This is the affine law of
`ArkLib.Data.Polynomial.Differential.RegularLift` applied to the perturbation that moves
`c_(k+r)(P)` to `c_(k+r)(P')`, together with the fact that residuals of polynomials agreeing to
order `k + r + 1` agree to order `k + 1`.

So when the slope `(k + r choose r) S(P)` is left-regular, two polynomials with the same residual
that agree below order `k + r` also agree in order `k + r`. By induction, two polynomials of
degree at most `D` with the same residual (for example two solutions of `Q = 0`) and the same
jet `c₀, ..., c_r` are equal, provided the slopes for `r < k + r ≤ D` are left-regular. Over a
field of characteristic `0` or `p > D` this holds whenever `S(P) ≠ 0`, which is the uniqueness
part of [Kop15, Corollary 4.5].

The theorems give uniqueness only. They do not assert that a solution with a given jet exists;
for the construction of the candidate see `ArkLib.Data.Polynomial.Differential.DirectRegularLift`.

## Main statements

* `coeff_shiftedJetSubstitution_sub_eq_of_taylor_coeff_eq`: the exact difference of the `k`-th
  residual coefficients of two polynomials that agree below order `k + r`.
* `taylor_coeff_eq_of_taylor_coeff_eq_of_isLeftRegular`: one coefficient is forced.
* `eq_of_polynomialJet_eq_of_isLeftRegular`: fixed-jet uniqueness at the top variable.
* `eq_of_polynomialJet_eq_of_isHighestActiveJet` and
  `BoundedSolution.eq_of_polynomialJet_eq_of_isHighestActiveJet`: the same at an arbitrary
  highest active jet variable.
* `existsUnique_regularLiftCoefficient_centered_of_isHighestActiveJet`: the one-step regular lift
  at an arbitrary highest active jet variable.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Theorem 4.4 and Corollary 4.5.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R] {r d k : ℕ}

/-! ### One coefficient -/

/-- Let `0 < k` and suppose the Taylor coefficients of `P` and `P'` at `center` agree below order
`k + r`. Then the coefficients of `X ^ k` in their residuals differ by
`(k + r choose r) S (c' - c)`, where `c` and `c'` are the Taylor coefficients of order `k + r` and
`S` is the separant value at the Hasse jet of `P`.

The hypothesis `0 < k` is needed for the same reason as in
`coeff_shiftedJetSubstitution_add_hassePerturbation`: at `k = 0` the residual need not be affine
in the coefficient of order `r`. -/
theorem coeff_shiftedJetSubstitution_sub_eq_of_taylor_coeff_eq (hk : 0 < k)
    (Q : DifferentialPolynomial R r) (center : R) {P P' : R[X]}
    (hagree : ∀ i < k + r, (taylor center P).coeff i = (taylor center P').coeff i) :
    (shiftedJetSubstitution center P' Q).coeff k - (shiftedJetSubstitution center P Q).coeff k =
      ((k + r).choose r : R) *
          jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) *
        ((taylor center P').coeff (k + r) - (taylor center P).coeff (k + r)) := by
  set γ := (taylor center P').coeff (k + r) - (taylor center P).coeff (k + r)
  have hdiv : X ^ ((k + 1) + r) ∣
      taylor center (P + hassePerturbation center γ (k + r)) - taylor center P' := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [coeff_sub, map_add, coeff_add, taylor_hassePerturbation, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge i (k + r) with hlt | hge
    · rw [ite_eq_right hlt.ne, hagree i hlt]
      ring
    · rw [ite_eq_left (by omega), show i = k + r by omega]
      ring
  have hcoeff := X_pow_dvd_iff.mp
    (X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd Q _ P' center (k + 1) hdiv) k
    (Nat.lt_succ_self k)
  rw [coeff_sub, sub_eq_zero, coeff_shiftedJetSubstitution_add_hassePerturbation hk] at hcoeff
  rw [← hcoeff]
  ring

/-- If `P` and `P'` agree below order `k + r` at `center`, with `0 < k`, their residuals have the
same coefficient of `X ^ k`, and the slope `(k + r choose r) S` is left-regular, then they also
agree in order `k + r`. Here `S` is the separant value at the Hasse jet of `P`.

Over a field, left-regularity means `(k + r choose r) ≠ 0` and `S ≠ 0`. Neither can be dropped:
if the slope is zero, the `k`-th residual coefficient does not depend on the coefficient of
order `k + r`. -/
theorem taylor_coeff_eq_of_taylor_coeff_eq_of_isLeftRegular (hk : 0 < k)
    (Q : DifferentialPolynomial R r) (center : R) {P P' : R[X]}
    (hagree : ∀ i < k + r, (taylor center P).coeff i = (taylor center P').coeff i)
    (hres : (shiftedJetSubstitution center P Q).coeff k =
      (shiftedJetSubstitution center P' Q).coeff k)
    (hslope : IsLeftRegular (((k + r).choose r : R) *
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P))) :
    (taylor center P).coeff (k + r) = (taylor center P').coeff (k + r) := by
  have h := coeff_shiftedJetSubstitution_sub_eq_of_taylor_coeff_eq hk Q center hagree
  rw [hres, sub_self, eq_comm, hslope.mul_left_eq_zero_iff, sub_eq_zero] at h
  exact h.symm

/-! ### Fixed-jet uniqueness -/

/-- Two polynomials of degree at most `D` with the same differential specialization and the same
Hasse jet through order `r` at `center` are equal, provided every slope
`(k + r choose r) S` with `0 < k` and `k + r ≤ D` is left-regular. Here `S` is the separant value
at the common Hasse jet.

Taking both specializations to be zero gives uniqueness of a solution of `Q = 0` with a given
initial jet. The theorem asserts no existence. The slope hypotheses are needed: for `y' = 0` over
`ZMod 2` the solutions `1` and `1 + X ^ 2` have the same jet through order `1`, and the slope
`(2 choose 1) * 1` vanishes. -/
theorem eq_of_polynomialJet_eq_of_isLeftRegular (Q : DifferentialPolynomial R r)
    (center : R) {P P' : R[X]} {D : ℕ} (hdegree : P.degree ≤ D) (hdegree' : P'.degree ≤ D)
    (hres : differentialSpecialization Q P = differentialSpecialization Q P')
    (hjet : polynomialJet (d := r) center P = polynomialJet (d := r) center P')
    (hslope : ∀ k, 0 < k → k + r ≤ D → IsLeftRegular (((k + r).choose r : R) *
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P))) :
    P = P' := by
  have hshift : shiftedJetSubstitution center P Q = shiftedJetSubstitution center P' Q := by
    rw [← taylor_differentialSpecialization, ← taylor_differentialSpecialization, hres]
  have hhigh (S : R[X]) (hS : S.degree ≤ D) (i : ℕ) (hi : D < i) : (taylor center S).coeff i = 0 :=
    coeff_eq_zero_of_natDegree_lt (by
      rw [natDegree_taylor]
      exact (natDegree_le_of_degree_le hS).trans_lt hi)
  apply taylor_injective center
  ext i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      by_cases hiD : D < i
      · rw [hhigh P hdegree i hiD, hhigh P' hdegree' i hiD]
      by_cases hir : i ≤ r
      · have h := congrFun hjet ⟨i, Nat.lt_succ_of_le hir⟩
        rwa [polynomialJet, polynomialJet, hasseJet_eq_taylor_coeff,
          hasseJet_eq_taylor_coeff] at h
      · have hkr : i - r + r = i := by omega
        rw [← hkr]
        exact taylor_coeff_eq_of_taylor_coeff_eq_of_isLeftRegular (by omega) Q center
          (fun j hj ↦ ih j (by omega)) (by rw [hshift])
          (hslope (i - r) (by omega) (by omega))

/-- Fixed-jet uniqueness at an arbitrary highest active jet variable `Y_s` of an equation stored
at depth `d`. The jets are compared through order `s`, and the slopes use the separant in `Y_s`.
The equation is first restricted to its variables through `Y_s`. -/
theorem eq_of_polynomialJet_eq_of_isHighestActiveJet (Q : DifferentialPolynomial R d)
    {s : Fin (d + 1)} (hs : IsHighestActiveJet Q s) (center : R) {P P' : R[X]} {D : ℕ}
    (hdegree : P.degree ≤ D) (hdegree' : P'.degree ≤ D)
    (hres : differentialSpecialization Q P = differentialSpecialization Q P')
    (hjet : polynomialJet (d := s.val) center P = polynomialJet (d := s.val) center P')
    (hslope : ∀ k, 0 < k → k + s.val ≤ D → IsLeftRegular (((k + s.val).choose s.val : R) *
      jetEvaluation (separant Q s) center (polynomialJet center P))) :
    P = P' := by
  obtain ⟨Q', rfl⟩ := exists_prefixDifferentialPolynomial Q hs
  simp only [differentialSpecialization_rename_jetPrefixEmbedding] at hres
  simp only [jetEvaluation_separant_rename_jetPrefixEmbedding] at hslope
  exact eq_of_polynomialJet_eq_of_isLeftRegular Q' center hdegree hdegree' hres hjet hslope

/-- Two bounded solutions with the same Hasse jet through the highest active jet variable `Y_s`
are equal when the slopes `(k + s choose s) S` for `0 < k`, `k + s ≤ D` are left-regular. -/
theorem BoundedSolution.eq_of_polynomialJet_eq_of_isHighestActiveJet
    {Q : DifferentialPolynomial R d} {D : ℕ} {s : Fin (d + 1)} (hs : IsHighestActiveJet Q s)
    (center : R) {P P' : BoundedSolution Q D}
    (hjet : polynomialJet (d := s.val) center P.polynomial =
      polynomialJet (d := s.val) center P'.polynomial)
    (hslope : ∀ k, 0 < k → k + s.val ≤ D → IsLeftRegular (((k + s.val).choose s.val : R) *
      jetEvaluation (separant Q s) center (polynomialJet center P.polynomial))) :
    P = P' :=
  Subtype.ext <| Subtype.ext <|
    PolynomialDifferential.eq_of_polynomialJet_eq_of_isHighestActiveJet Q hs center
    P.degree_le P'.degree_le (P.equation.trans P'.equation.symm) hjet hslope

/-! ### One-step lift at a highest active jet -/

/-- The one-step regular lift at an arbitrary highest active jet variable `Y_s`: if `0 < k`,
`(X - center) ^ k` divides `Q(X, P, D¹P, ...)`, and `(k + s choose s) S` is a unit, where `S` is
the separant in `Y_s` at the Hasse jet of `P`, then exactly one `γ` makes `(X - center) ^ (k + 1)`
divide the specialization at `P + γ (X - center) ^ (k + s)`. The perturbation degree is `k + s`
because only `Y₀, ..., Y_s` occur in `Q`. -/
theorem existsUnique_regularLiftCoefficient_centered_of_isHighestActiveJet (hk : 0 < k)
    (Q : DifferentialPolynomial R d) {s : Fin (d + 1)} (hs : IsHighestActiveJet Q s)
    (center : R) (P : R[X]) (hresidual : (X - C center) ^ k ∣ differentialSpecialization Q P)
    (hslope : IsUnit (((k + s.val).choose s.val : R) *
      jetEvaluation (separant Q s) center (polynomialJet center P))) :
    ∃! γ : R, (X - C center) ^ (k + 1) ∣
      differentialSpecialization Q (P + hassePerturbation center γ (k + s.val)) := by
  obtain ⟨Q', rfl⟩ := exists_prefixDifferentialPolynomial Q hs
  simp only [differentialSpecialization_rename_jetPrefixEmbedding] at hresidual ⊢
  rw [jetEvaluation_separant_rename_jetPrefixEmbedding] at hslope
  exact existsUnique_regularLiftCoefficient_centered hk Q' center P hresidual hslope

end

end PolynomialDifferential
