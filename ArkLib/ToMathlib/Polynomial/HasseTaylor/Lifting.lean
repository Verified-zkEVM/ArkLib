/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift
public import Mathlib.Data.Nat.Choose.Dvd

/-!
# Hasse--Taylor coefficient perturbations

Adding `γ * (X - a) ^ i` to a polynomial changes exactly its Hasse coefficient of order `i` at
`a`. After taking the Hasse derivative of order `s ≤ i`, the first changed coefficient has order
`i - s` and changes by `(i choose s) * γ`. So when `(i choose s)` is a unit, there is exactly one
`γ` that gives that coefficient a prescribed value.

These are the univariate facts behind the regular power-series lift of [Kop15, Theorem 4.4]; the
multivariate step is `PolynomialDifferential.existsUnique_regularLiftCoefficient`. Everything
holds over a commutative ring. The only arithmetic input is that the binomial coefficient is a
unit, or nonzero in a field; `natCast_choose_ne_zero_of_lt_charP` supplies this below a prime
characteristic.

## Main statements

* `Polynomial.hassePerturbation`: the polynomial `C γ * (X - C a) ^ i`.
* `Polynomial.hasseCoeffAt_hassePerturbation`: it has exactly one nonzero Hasse coefficient at
  `a`.
* `Polynomial.hasseDeriv_hassePerturbation`: its Hasse derivative of order `s` is the
  perturbation of order `i - s` with coefficient `(i choose s) * γ`.
* `Polynomial.hasseCoeffAt_hasseDeriv_add_hassePerturbation`: the first exposed coefficient after
  differentiation changes by `(i choose s) * γ`, and
  `hasseCoeffAt_hasseDeriv_add_hassePerturbation_of_lt`: lower coefficients do not change.
* `Polynomial.existsUnique_hasseCoeffAt_hasseDeriv_add_hassePerturbation_eq`: unique choice of
  `γ` when `(i choose s)` is a unit.
* `Polynomial.natCast_choose_ne_zero_of_lt_charP`: `(i choose s) ≠ 0` below a prime
  characteristic.
* `Polynomial.X_pow_dvd_taylor_hasseDeriv_sub_of_X_pow_add_dvd`: agreement to centered order
  `m + s` gives agreement of Hasse derivatives of order `s` to centered order `m`.
* `Polynomial.X_pow_dvd_taylor_iff_X_sub_C_pow_dvd` and
  `X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd`: divisibility bookkeeping used by the lift.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Definition 2.1 and Theorem 4.4.
-/

@[expose] public section

namespace Polynomial

noncomputable section

variable {R : Type*}

section CommRing

variable [CommRing R]

/-! ### A single centered coefficient perturbation -/

/-- The polynomial `γ * (X - a) ^ i`: in coordinates centered at `a`, the single monomial of
degree `i` with coefficient `γ`. -/
def hassePerturbation (a γ : R) (i : ℕ) : R[X] :=
  C γ * (X - C a) ^ i

/-- Translating a centered perturbation to the origin gives the monomial `γ * X ^ i`. -/
@[simp]
theorem taylor_hassePerturbation (a γ : R) (i : ℕ) :
    taylor a (hassePerturbation a γ i) = C γ * X ^ i := by
  simp [hassePerturbation, taylor_apply]

/-- A centered perturbation has exactly one nonzero Hasse coefficient at its center. -/
@[simp]
theorem hasseCoeffAt_hassePerturbation (a γ : R) (i j : ℕ) :
    hasseCoeffAt a j (hassePerturbation a γ i) = if j = i then γ else 0 := by
  rw [hasseCoeffAt_apply, ← taylor_coeff, taylor_hassePerturbation, coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp

/-- Adding a centered perturbation of order `i` adds `γ` to the Hasse coefficient of order `i`
and changes no other Hasse coefficient at the center. -/
theorem hasseCoeffAt_add_hassePerturbation (p : R[X]) (a γ : R) (i j : ℕ) :
    hasseCoeffAt a j (p + hassePerturbation a γ i) =
      hasseCoeffAt a j p + if j = i then γ else 0 := by
  rw [map_add, hasseCoeffAt_hassePerturbation]

/-- Hasse coefficients below the perturbed order are unchanged. -/
theorem hasseCoeffAt_add_hassePerturbation_of_lt (p : R[X]) (a γ : R) {i j : ℕ}
    (hji : j < i) :
    hasseCoeffAt a j (p + hassePerturbation a γ i) = hasseCoeffAt a j p := by
  rw [hasseCoeffAt_add_hassePerturbation, ite_eq_right hji.ne, add_zero]

/-- The Hasse coefficient of the perturbed order increases by `γ`. -/
theorem hasseCoeffAt_add_hassePerturbation_self (p : R[X]) (a γ : R) (i : ℕ) :
    hasseCoeffAt a i (p + hassePerturbation a γ i) = hasseCoeffAt a i p + γ := by
  rw [hasseCoeffAt_add_hassePerturbation, ite_eq_left rfl]

/-- A perturbation of order `i` leaves the length-`m` Hasse jet unchanged when `m ≤ i`. -/
theorem hasseJet_add_hassePerturbation_of_le (p : R[X]) (a γ : R) {m i : ℕ} (hmi : m ≤ i) :
    hasseJet m a (p + hassePerturbation a γ i) = hasseJet m a p := by
  ext j
  exact hasseCoeffAt_add_hassePerturbation_of_lt p a γ (j.isLt.trans_le hmi)

/-! ### Effect of Hasse differentiation -/

/-- The Hasse derivative of order `s` of `γ * (X - a) ^ i` is
`(i choose s) * γ * (X - a) ^ (i - s)`. For `s > i` both sides are zero, since
`i choose s = 0`. -/
theorem hasseDeriv_hassePerturbation (a γ : R) (i s : ℕ) :
    hasseDeriv s (hassePerturbation a γ i) =
      hassePerturbation a ((i.choose s : R) * γ) (i - s) := by
  apply taylor_injective a
  rw [← hasseDeriv_taylor, taylor_hassePerturbation, taylor_hassePerturbation]
  simp only [C_mul_X_pow_eq_monomial, hasseDeriv_monomial]

/-- `hasseDeriv_hassePerturbation` after adding the perturbation to a polynomial `p`. -/
theorem hasseDeriv_add_hassePerturbation (p : R[X]) (a γ : R) (i s : ℕ) :
    hasseDeriv s (p + hassePerturbation a γ i) =
      hasseDeriv s p + hassePerturbation a ((i.choose s : R) * γ) (i - s) := by
  rw [LinearMap.map_add, hasseDeriv_hassePerturbation]

/-- After Hasse differentiation of order `s`, coefficients of order `j` with `j + s < i` do not see
a perturbation of order `i`. The hypothesis is the subtraction-free form of `j < i - s`. -/
theorem hasseCoeffAt_hasseDeriv_add_hassePerturbation_of_lt
    (p : R[X]) (a γ : R) {i j s : ℕ} (hjs : j + s < i) :
    hasseCoeffAt a j (hasseDeriv s (p + hassePerturbation a γ i)) =
      hasseCoeffAt a j (hasseDeriv s p) := by
  rw [hasseDeriv_add_hassePerturbation, map_add, hasseCoeffAt_hassePerturbation,
    ite_eq_right (by omega), add_zero]

/-- After Hasse differentiation of order `s`, the coefficient of order `i - s` changes by
`(i choose s) * γ`. No hypothesis `s ≤ i` is needed: for `s > i` the derivative of the
perturbation is zero and so is `i choose s`. -/
theorem hasseCoeffAt_hasseDeriv_add_hassePerturbation (p : R[X]) (a γ : R) (i s : ℕ) :
    hasseCoeffAt a (i - s) (hasseDeriv s (p + hassePerturbation a γ i)) =
      hasseCoeffAt a (i - s) (hasseDeriv s p) + (i.choose s : R) * γ := by
  rw [hasseDeriv_add_hassePerturbation, map_add, hasseCoeffAt_hassePerturbation, ite_eq_left rfl]

/-! ### Unique choice of the perturbation coefficient -/

/-- If `(i choose s)` is left-regular in `R`, the coefficient of order `i - s` after Hasse
differentiation of order `s` determines the perturbation coefficient `γ`. Over a field the
hypothesis is `(i choose s : F) ≠ 0`, which forces `s ≤ i`. -/
theorem hasseCoeffAt_hasseDeriv_add_hassePerturbation_injective
    (p : R[X]) (a : R) {i s : ℕ} (hchoose : IsLeftRegular (i.choose s : R)) :
    Function.Injective fun γ ↦
      hasseCoeffAt a (i - s) (hasseDeriv s (p + hassePerturbation a γ i)) := by
  intro γ γ' h
  simp only [hasseCoeffAt_hasseDeriv_add_hassePerturbation, add_right_inj] at h
  exact hchoose h

/-- If `(i choose s)` is a unit in `R`, exactly one perturbation coefficient `γ` gives the
coefficient of order `i - s` after Hasse differentiation of order `s` any prescribed value `y`.

The unit hypothesis is needed for existence: over `ℤ`, with `p = 0`, `i = 2`, `s = 1`, the
reachable values are the even integers `2 * γ`. -/
theorem existsUnique_hasseCoeffAt_hasseDeriv_add_hassePerturbation_eq
    (p : R[X]) (a y : R) {i s : ℕ} (hchoose : IsUnit (i.choose s : R)) :
    ∃! γ : R, hasseCoeffAt a (i - s) (hasseDeriv s (p + hassePerturbation a γ i)) = y := by
  have hex : hasseCoeffAt a (i - s) (hasseDeriv s (p + hassePerturbation a
      (↑hchoose.unit⁻¹ * (y - hasseCoeffAt a (i - s) (hasseDeriv s p))) i)) = y := by
    rw [hasseCoeffAt_hasseDeriv_add_hassePerturbation, ← mul_assoc, hchoose.mul_val_inv,
      one_mul, add_sub_cancel]
  exact ⟨_, hex, fun γ hγ ↦
    hasseCoeffAt_hasseDeriv_add_hassePerturbation_injective p a hchoose.isRegular.left
      (hγ.trans hex.symm)⟩

/-! ### Centered divisibility and agreement to finite order -/

/-- Divisibility by `(X - a) ^ m` is divisibility of the Taylor expansion at `a` by `X ^ m`. -/
theorem X_pow_dvd_taylor_iff_X_sub_C_pow_dvd (p : R[X]) (a : R) (m : ℕ) :
    X ^ m ∣ taylor a p ↔ (X - C a) ^ m ∣ p := by
  rw [X_sub_C_pow_dvd_iff, taylor_apply]

/-- If the Taylor expansions of `p` and `q` at `a` agree below order `m + s`, then those of their
Hasse derivatives of order `s` agree below order `m`. Equivalently, `(X - a) ^ (m + s) ∣ p - q`
implies `(X - a) ^ m ∣ Dˢp - Dˢq`. -/
theorem X_pow_dvd_taylor_hasseDeriv_sub_of_X_pow_add_dvd (p q : R[X]) (a : R) (m s : ℕ)
    (h : X ^ (m + s) ∣ taylor a p - taylor a q) :
    X ^ m ∣ taylor a (hasseDeriv s p) - taylor a (hasseDeriv s q) := by
  rw [← LinearMap.map_sub] at h
  rw [← LinearMap.map_sub, ← LinearMap.map_sub, ← hasseDeriv_taylor, X_pow_dvd_iff]
  intro i hi
  rw [hasseDeriv_coeff, X_pow_dvd_iff.mp h (i + s) (by omega), mul_zero]

end CommRing

section Semiring

variable [Semiring R]

/-- If `X ^ k ∣ p`, then `X ^ (k + 1) ∣ p` exactly when the coefficient of `X ^ k` in `p`
vanishes. -/
theorem X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd {p : R[X]} {k : ℕ} (hp : X ^ k ∣ p) :
    X ^ (k + 1) ∣ p ↔ p.coeff k = 0 := by
  refine ⟨fun h ↦ X_pow_dvd_iff.mp h k (Nat.lt_succ_self k), fun hk ↦ X_pow_dvd_iff.mpr ?_⟩
  intro i hi
  rcases (Nat.lt_succ_iff.mp hi).lt_or_eq with hik | rfl
  · exact X_pow_dvd_iff.mp hp i hik
  · exact hk

end Semiring

section AddMonoidWithOne

variable [AddMonoidWithOne R]

/-! ### Binomial coefficients below a prime characteristic -/

/-- If `R` has prime characteristic `p` and `s ≤ i < p`, then `(i choose s)` is nonzero in `R`.
The bound `i < p` is needed: `(p choose 1) = p` vanishes in characteristic `p`. -/
theorem natCast_choose_ne_zero_of_lt_charP {p i s : ℕ} [CharP R p]
    (hp : p.Prime) (hip : i < p) (hsi : s ≤ i) : (i.choose s : R) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff R p]
  exact hp.coprime_iff_not_dvd.mp (hp.coprime_choose_of_lt hip hsi)

end AddMonoidWithOne

end

end Polynomial
