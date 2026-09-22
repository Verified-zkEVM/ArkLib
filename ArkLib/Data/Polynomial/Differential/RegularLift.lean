/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.JetDegree
public import ArkLib.Data.Polynomial.Differential.ShiftedJet
public import ArkLib.Data.Polynomial.TaylorPrefix
public import ArkLib.ToMathlib.MvPolynomial.FirstOrderTaylor
public import ArkLib.ToMathlib.Polynomial.HasseTaylor.Lifting

/-!
# Regular coefficient lifting for polynomial differential equations

Let `Q(X, Y₀, ..., Y_r)` be a differential polynomial over a commutative ring and let `P` be a
polynomial. Write `Res_a(P) = Q(a + X, P(a + X), (D¹P)(a + X), ..., (DʳP)(a + X))`, the
shifted-jet substitution; it is the Taylor expansion at `a` of `Q(X, P, D¹P, ..., DʳP)`.

Replace `P` by `P + γ (X - a) ^ (k + r)`. The Hasse derivative of order `j` changes by
`(k + r choose j) γ X ^ (k + r - j)` after shifting, so only `Y_r` changes in degree `k`, and all
lower jet coordinates change in degree at least `k + 1`. When `0 < k`, the first-order Taylor
congruence then gives

```text
Res_a(P + γ (X - a)^(k+r)) ≡ Res_a(P) + (k + r choose r) γ X^k S   (mod X^(k+1)),
```

where `S` is the separant `∂Q/∂Y_r` evaluated at `a` and the Hasse jet of `P`. So the coefficient
of `X ^ k` in the residual is affine in `γ` with slope `(k + r choose r) S`. If `X ^ k` already
divides the residual and the slope is a unit, exactly one `γ` makes `X ^ (k + 1)` divide it. This
is the regular step of [Kop15, Theorem 4.4].

The file also proves the zero-order counterpart: if `P` and `P'` agree to centered order `m + r`,
then their residuals agree to order `m`. Combining both, the Taylor coefficient of order `l - r`
of the residual of any `P` (with `r < l`) is the residual of its degree-`< l` Taylor prefix plus
`(l choose r) c_l S`, where `c_l` is the next Taylor coefficient of `P`.

## Main statements

* `shiftedJetValues_add_hassePerturbation`: the change of the shifted jet under a perturbation.
* `X_pow_succ_dvd_shiftedJetSubstitution_add_hassePerturbation_sub` and
  `coeff_shiftedJetSubstitution_add_hassePerturbation`: the affine law for the residual.
* `X_pow_dvd_shiftedJetSubstitution_add_hassePerturbation`: the perturbation keeps `X ^ k`
  divisibility.
* `existsUnique_regularLiftCoefficient` and `existsUnique_regularLiftCoefficient_centered`: the
  unique one-step lift when the slope is a unit.
* `X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd` and
  `X_sub_C_pow_dvd_differentialSpecialization_sub_of_X_sub_C_pow_add_dvd`: agreement to order
  `m + r` gives residual agreement to order `m`.
* `coeff_shiftedJetSubstitution_eq_centeredCoefficientPrefix_add`: the Taylor coefficient of
  order `l - r` of a residual in terms of the residual of a Taylor prefix.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Regular/` at ArkLib
revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, where everything was stated over a field in
the namespace `ReedSolomon.HiddenDerivative`. None of it mentions a Reed–Solomon object, so it is
stated here over a commutative ring in the namespace `PolynomialDifferential`, next to
`shiftedJetSubstitution`.

From `Lifting.lean`:

* `shiftedJetValues`, `regularLiftIncrement`, `shiftedJetSubstitution_eq_eval₂Hom`,
  `X_pow_succ_dvd_regularLiftIncrement_of_ne_top` (here `_of_ne_last`) and
  `regularLiftIncrement_top` (here `_last`) keep their statements.
* The source's `regularLiftCandidate center γ k r P` is not defined; statements use
  `P + hassePerturbation center γ (k + r)` directly. Accordingly
  `shiftedJetValues_regularLiftCandidate`,
  `X_pow_succ_dvd_shiftedJetSubstitution_regularLiftCandidate_sub`,
  `coeff_shiftedJetSubstitution_regularLiftCandidate` and
  `X_pow_dvd_shiftedJetSubstitution_regularLiftCandidate` become the `_add_hassePerturbation`
  statements. The last one no longer assumes `0 < k`.
* `existsUnique_regularLiftCoefficient` replaces the two field hypotheses
  `(k + r choose r) ≠ 0` and `S ≠ 0` by the single hypothesis that their product is a unit.
  `existsUnique_regularLiftCoefficient_centered` is the source's `_centered` form.
* `eval_zero_shiftedJetSubstitution_separant` is `coeff_zero_shiftedJetSubstitution` in
  `ArkLib.Data.Polynomial.Differential.ShiftedJet`; `X_pow_dvd_regularLiftIncrement_top` is
  inlined; `X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd` and
  `X_pow_dvd_taylor_iff_X_sub_C_pow_dvd` are in `ArkLib.ToMathlib.Polynomial.HasseTaylor.Lifting`.
* The `ringChar` wrappers `existsUnique_regularLiftCoefficient_of_le_of_lt_ringChar`,
  `existsUnique_regularLiftCoefficient_centered_of_le_of_lt_ringChar` and the wrappers taking
  `IsRegularJet` are not ported. `Polynomial.natCast_choose_ne_zero_of_lt_charP` gives the
  binomial hypothesis below a prime characteristic.

From `Iteration.lean`: `X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd` and
`X_sub_C_pow_dvd_differentialSpecialization_sub_of_X_sub_C_pow_add_dvd` keep their statements;
its private evaluation lemma is `MvPolynomial.dvd_eval₂Hom_sub_eval₂Hom`. The uniqueness theorems
of `Iteration.lean` are deferred; they need `IsRegularJet`, `IsHighestActiveJet` and
`BoundedSolution` from `RootFinding/Regular/JetPrefix.lean` and the root-finding core.

`coeff_shiftedJetSubstitution_eq_centeredCoefficientPrefix_add` is the argument of the source's
`solution_taylorCoefficient_residual` (`RootFinding/Taylor/Numerator.lean`) without the
assumption that `P` is a solution.

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Theorem 4.4.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R] {r k : ℕ}

/-! ### Shifted jets and their change under a perturbation -/

/-- The values substituted for `X, Y₀, ..., Y_r` by `shiftedJetSubstitution center P`:
`X ↦ center + X` and `Y_j ↦ (DʲP)(center + X)`. -/
def shiftedJetValues (center : R) (P : R[X]) : JetVariable r → R[X]
  | none => C center + X
  | some j => taylor center (hasseDeriv j.val P)

/-- `shiftedJetSubstitution` is evaluation at `shiftedJetValues`. -/
theorem shiftedJetSubstitution_eq_eval₂Hom (Q : DifferentialPolynomial R r) (center : R)
    (P : R[X]) :
    shiftedJetSubstitution center P Q = MvPolynomial.eval₂Hom C (shiftedJetValues center P) Q :=
  rfl

/-- The change of each shifted jet coordinate after adding `γ (X - center) ^ (k + r)`: zero on
`X`, and `(k + r choose j) γ X ^ (k + r - j)` on `Y_j`. -/
def regularLiftIncrement (γ : R) (k r : ℕ) : JetVariable r → R[X]
  | none => 0
  | some j => C (((k + r).choose j.val : R) * γ) * X ^ (k + r - j.val)

/-- Adding `γ (X - center) ^ (k + r)` to `P` adds `regularLiftIncrement γ k r` to its shifted
jet. -/
theorem shiftedJetValues_add_hassePerturbation (center γ : R) (k : ℕ) (P : R[X]) :
    shiftedJetValues (r := r) center (P + hassePerturbation center γ (k + r)) =
      shiftedJetValues center P + regularLiftIncrement γ k r := by
  funext v
  rcases v with _ | j
  · simp [shiftedJetValues, regularLiftIncrement]
  · simp only [shiftedJetValues, regularLiftIncrement, Pi.add_apply]
    rw [hasseDeriv_add_hassePerturbation, map_add, taylor_hassePerturbation]

/-- On the top coordinate `Y_r` the increment is `(k + r choose r) γ X ^ k`. -/
theorem regularLiftIncrement_last (γ : R) (k r : ℕ) :
    regularLiftIncrement γ k r (some (Fin.last r)) =
      C (((k + r).choose r : R) * γ) * X ^ k := by
  simp [regularLiftIncrement]

/-- Every coordinate other than `Y_r` changes only in degrees at least `k + 1`. -/
theorem X_pow_succ_dvd_regularLiftIncrement_of_ne_last (γ : R) (k : ℕ) (v : JetVariable r)
    (hv : v ≠ some (Fin.last r)) :
    X ^ (k + 1) ∣ regularLiftIncrement γ k r v := by
  rcases v with _ | j
  · simp [regularLiftIncrement]
  · have hjr : j.val < r := by
      have hne : j ≠ Fin.last r := fun h ↦ hv (h ▸ rfl)
      exact Fin.val_lt_last hne
    exact dvd_mul_of_dvd_right (pow_dvd_pow X (by omega)) _

/-! ### The affine residual law -/

/-- Modulo `X ^ (k + 1)`, with `0 < k`, adding `γ (X - center) ^ (k + r)` changes the residual by
`S(X) * (k + r choose r) γ X ^ k`, where `S(X)` is the shifted-jet substitution of the separant
`∂Q/∂Y_r`.

The hypothesis `0 < k` is needed. For `Q = Y₀ ^ 2`, `r = 0`, `k = 0` and `P = 0`, the residual
changes by `γ ^ 2`, which is not linear in `γ`. -/
theorem X_pow_succ_dvd_shiftedJetSubstitution_add_hassePerturbation_sub (hk : 0 < k)
    (Q : DifferentialPolynomial R r) (center γ : R) (P : R[X]) :
    X ^ (k + 1) ∣
      shiftedJetSubstitution center (P + hassePerturbation center γ (k + r)) Q -
        shiftedJetSubstitution center P Q -
        shiftedJetSubstitution center P (separant Q (Fin.last r)) *
          (C (((k + r).choose r : R) * γ) * X ^ k) := by
  rw [shiftedJetSubstitution_eq_eval₂Hom, shiftedJetSubstitution_eq_eval₂Hom,
    shiftedJetSubstitution_eq_eval₂Hom, shiftedJetValues_add_hassePerturbation,
    ← regularLiftIncrement_last, separant]
  have h := MvPolynomial.pow_succ_dvd_eval₂Hom_add_sub_pderiv C (shiftedJetValues center P)
    (regularLiftIncrement γ k r) Finset.univ Q (some (Fin.last r)) X k hk (Finset.mem_univ _)
    (by rw [regularLiftIncrement_last]; exact dvd_mul_left _ _)
    (fun v _ hv ↦ X_pow_succ_dvd_regularLiftIncrement_of_ne_last γ k v hv)
    (fun v hv ↦ absurd (Finset.mem_univ v) hv)
  exact h

/-- Coefficient form of the affine law: for `0 < k`, the coefficient of `X ^ k` in the residual
of `P + γ (X - center) ^ (k + r)` is that of `P` plus `(k + r choose r) γ S`, where `S` is the
separant evaluated at `center` and the Hasse jet of `P`. The hypothesis `0 < k` is needed as in
`X_pow_succ_dvd_shiftedJetSubstitution_add_hassePerturbation_sub`. -/
theorem coeff_shiftedJetSubstitution_add_hassePerturbation (hk : 0 < k)
    (Q : DifferentialPolynomial R r) (center γ : R) (P : R[X]) :
    (shiftedJetSubstitution center (P + hassePerturbation center γ (k + r)) Q).coeff k =
      (shiftedJetSubstitution center P Q).coeff k +
        (((k + r).choose r : R) * γ) *
          jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) := by
  have h := X_pow_dvd_iff.mp
    (X_pow_succ_dvd_shiftedJetSubstitution_add_hassePerturbation_sub hk Q center γ P) k
    (Nat.lt_succ_self k)
  rw [coeff_sub, coeff_sub, ← mul_assoc, coeff_mul_X_pow', ite_eq_left (le_refl k),
    Nat.sub_self, coeff_mul_C, coeff_zero_shiftedJetSubstitution, sub_sub,
    sub_eq_zero] at h
  rw [h, mul_comm]

/-- The perturbation `γ (X - center) ^ (k + r)` keeps divisibility of the residual by `X ^ k`.
For `k = 0` this is trivial. -/
theorem X_pow_dvd_shiftedJetSubstitution_add_hassePerturbation
    (Q : DifferentialPolynomial R r) (center γ : R) (P : R[X])
    (hresidual : X ^ k ∣ shiftedJetSubstitution center P Q) :
    X ^ k ∣ shiftedJetSubstitution center (P + hassePerturbation center γ (k + r)) Q := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero]
    exact one_dvd _
  have h := (pow_dvd_pow X k.le_succ).trans
    (X_pow_succ_dvd_shiftedJetSubstitution_add_hassePerturbation_sub hk Q center γ P)
  have hlin : X ^ k ∣ shiftedJetSubstitution center P (separant Q (Fin.last r)) *
      (C (((k + r).choose r : R) * γ) * X ^ k) :=
    dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  convert (h.add hresidual).add hlin using 1
  ring

/-! ### Unique one-step lifting -/

/-- The regular one-step lift of [Kop15, Theorem 4.4]. Let `0 < k`, suppose `X ^ k` divides the
residual of `P`, and suppose the slope `(k + r choose r) S` is a unit, where `S` is the separant
evaluated at `center` and the Hasse jet of `P`. Then exactly one `γ` makes `X ^ (k + 1)` divide
the residual of `P + γ (X - center) ^ (k + r)`.

Over a field the unit hypothesis says `(k + r choose r) ≠ 0` and `S ≠ 0`; both are needed, since
otherwise the coefficient of `X ^ k` does not depend on `γ`. The hypothesis `0 < k` is needed:
for `Q = Y₀ ^ 2 - 1`, `r = k = 0` and `P = 0` over `ℚ`, both `γ = 1` and `γ = -1` work. -/
theorem existsUnique_regularLiftCoefficient (hk : 0 < k) (Q : DifferentialPolynomial R r)
    (center : R) (P : R[X]) (hresidual : X ^ k ∣ shiftedJetSubstitution center P Q)
    (hslope : IsUnit (((k + r).choose r : R) *
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P))) :
    ∃! γ : R,
      X ^ (k + 1) ∣ shiftedJetSubstitution center (P + hassePerturbation center γ (k + r)) Q := by
  have hiff (γ : R) :
      X ^ (k + 1) ∣ shiftedJetSubstitution center (P + hassePerturbation center γ (k + r)) Q ↔
        (shiftedJetSubstitution center P Q).coeff k +
          ((k + r).choose r : R) *
            jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) * γ = 0 := by
    rw [X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd
      (X_pow_dvd_shiftedJetSubstitution_add_hassePerturbation Q center γ P hresidual),
      coeff_shiftedJetSubstitution_add_hassePerturbation hk, mul_right_comm]
  refine ⟨↑hslope.unit⁻¹ * -(shiftedJetSubstitution center P Q).coeff k, (hiff _).mpr ?_,
    fun γ hγ ↦ ?_⟩
  · rw [← mul_assoc, hslope.mul_val_inv, one_mul, add_neg_cancel]
  · rw [← eq_neg_of_add_eq_zero_right ((hiff γ).mp hγ), ← mul_assoc, hslope.val_inv_mul,
      one_mul]

/-- `existsUnique_regularLiftCoefficient` stated with the centered modulus `(X - center) ^ k` and
the differential specialization `Q(X, P, D¹P, ..., DʳP)`. -/
theorem existsUnique_regularLiftCoefficient_centered (hk : 0 < k)
    (Q : DifferentialPolynomial R r) (center : R) (P : R[X])
    (hresidual : (X - C center) ^ k ∣ differentialSpecialization Q P)
    (hslope : IsUnit (((k + r).choose r : R) *
      jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P))) :
    ∃! γ : R, (X - C center) ^ (k + 1) ∣
      differentialSpecialization Q (P + hassePerturbation center γ (k + r)) := by
  simp only [← X_pow_dvd_taylor_iff_X_sub_C_pow_dvd, taylor_differentialSpecialization]
    at hresidual ⊢
  exact existsUnique_regularLiftCoefficient hk Q center P hresidual hslope

/-! ### Agreement to finite order -/

/-- If the Taylor expansions of `P` and `P'` at `center` agree below order `m + r`, the residuals
of `P` and `P'` agree below order `m`. The loss of `r` orders comes from the Hasse derivatives
of order up to `r`. -/
theorem X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd
    (Q : DifferentialPolynomial R r) (P P' : R[X]) (center : R) (m : ℕ)
    (h : X ^ (m + r) ∣ taylor center P - taylor center P') :
    X ^ m ∣ shiftedJetSubstitution center P Q - shiftedJetSubstitution center P' Q := by
  rw [shiftedJetSubstitution_eq_eval₂Hom, shiftedJetSubstitution_eq_eval₂Hom]
  refine MvPolynomial.dvd_eval₂Hom_sub_eval₂Hom C (shiftedJetValues center P)
    (shiftedJetValues center P') (X ^ m) (fun v ↦ ?_) Q
  rcases v with _ | j
  · simp [shiftedJetValues]
  · have hj := j.isLt
    exact X_pow_dvd_taylor_hasseDeriv_sub_of_X_pow_add_dvd P P' center m j.val
      ((pow_dvd_pow X (by omega)).trans h)

/-- Centered form of `X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd`: if
`(X - center) ^ (m + r)` divides `P - P'`, then `(X - center) ^ m` divides the difference of
their differential specializations. -/
theorem X_sub_C_pow_dvd_differentialSpecialization_sub_of_X_sub_C_pow_add_dvd
    (Q : DifferentialPolynomial R r) (P P' : R[X]) (center : R) (m : ℕ)
    (h : (X - C center) ^ (m + r) ∣ P - P') :
    (X - C center) ^ m ∣ differentialSpecialization Q P - differentialSpecialization Q P' := by
  rw [← X_pow_dvd_taylor_iff_X_sub_C_pow_dvd, map_sub] at h ⊢
  rw [taylor_differentialSpecialization, taylor_differentialSpecialization]
  exact X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd Q P P' center m h

/-! ### Taylor coefficients of a residual -/

/-- Let `r < l` and let `c = (taylor center P).coeff` be the Taylor coefficients of `P` at
`center`. The coefficient of `X ^ (l - r)` in the residual of `P` equals the same coefficient in
the residual of the Taylor prefix `c₀ + ... + c_(l-1) (X - center) ^ (l - 1)`, plus
`(l choose r) c_l S`, where `S` is the separant evaluated at `center` and the Hasse jet of `P`.

The hypothesis `r < l` is needed: the prefix must contain the jet `c₀, ..., c_r` at which `S` is
evaluated, and the perturbation order `l - r` must be positive. -/
theorem coeff_shiftedJetSubstitution_eq_centeredCoefficientPrefix_add
    (Q : DifferentialPolynomial R r) (center : R) (P : R[X]) {l : ℕ} (hl : r < l) :
    (shiftedJetSubstitution center P Q).coeff (l - r) =
      (shiftedJetSubstitution center
          (centeredCoefficientPrefix center (taylor center P).coeff l) Q).coeff (l - r) +
        (((l.choose r : R) * (taylor center P).coeff l) *
          jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P)) := by
  have hl' : l - r + r = l := by omega
  have hprefix : X ^ ((l - r + 1) + r) ∣
      taylor center (centeredCoefficientPrefix center (taylor center P).coeff (l + 1)) -
        taylor center P := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [coeff_sub, coeff_taylor_centeredCoefficientPrefix, ite_eq_left (by omega), sub_self]
  have hc := X_pow_dvd_iff.mp (X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd Q _ P
    center (l - r + 1) hprefix) (l - r) (Nat.lt_succ_self _)
  rw [coeff_sub, sub_eq_zero] at hc
  have hsucc : centeredCoefficientPrefix center (taylor center P).coeff (l + 1) =
      centeredCoefficientPrefix center (taylor center P).coeff l +
        hassePerturbation center ((taylor center P).coeff l) (l - r + r) := by
    rw [hl', centeredCoefficientPrefix_succ]
    rfl
  have hjet : polynomialJet (d := r) center
      (centeredCoefficientPrefix center (taylor center P).coeff l) = polynomialJet center P := by
    rw [polynomialJet, polynomialJet, hasseJet_centeredCoefficientPrefix_of_le center _
      (by omega : r + 1 ≤ l)]
    funext i
    rw [hasseJet_eq_taylor_coeff]
  have hlin := coeff_shiftedJetSubstitution_add_hassePerturbation (by omega : 0 < l - r) Q center
    ((taylor center P).coeff l) (centeredCoefficientPrefix center (taylor center P).coeff l)
  rw [← hsucc, hc, hl', hjet] at hlin
  exact hlin

end

end PolynomialDifferential
