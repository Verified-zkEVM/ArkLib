/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Hasse--Taylor coefficient lifting

This file isolates the univariate algebra behind regular power-series lifting.  Adding
`gamma * (X - a) ^ i` changes exactly coefficient `i` of the Hasse--Taylor expansion at `a`.
After taking Hasse derivative `s`, the newly exposed coefficient at order `i - s` is multiplied
by `Nat.choose i s`.  Over a field of characteristic greater than `i`, that multiplier is a unit.

These facts supply the generic polynomial and characteristic layer used in [Kop15, Theorem 4.4]:
the theorem there applies them to a multivariate differential equation whose highest derivative is
regular.  This file does not formalize that multivariate substitution or claim the complete lifting
theorem.  [Kop15, Definition 2.1] fixes the Hasse-derivative convention, and [Kop15, Corollary 4.5]
iterates the one-coefficient step in the finite-field root-counting algorithm.

The strict characteristic bound is deliberately separate from field cardinality.  It is also sharp
for this interface: at degree equal to the characteristic, a binomial multiplier can vanish.

## Main declarations

* `Polynomial.hassePerturbation`: add one coefficient in coordinates centered at `a`;
* `Polynomial.hasseCoeffAt_hassePerturbation`: the perturbation changes exactly one Hasse
  coefficient;
* `Polynomial.hasseDeriv_add_hassePerturbation`: the exact whole-polynomial effect after Hasse
  differentiation;
* `Polynomial.hasseCoeffAt_hasseDeriv_add_hassePerturbation_of_lt`: coefficients below the newly
  exposed order are unchanged after Hasse differentiation;
* `Polynomial.hasseCoeffAt_hasseDeriv_add_hassePerturbation`: the newly exposed coefficient changes
  by the explicit binomial multiple;
* `Polynomial.natCast_choose_ne_zero_of_lt_ringChar`: binomial coefficients below the
  characteristic are nonzero in a field;
* `Polynomial.isUnit_natCast_choose_of_lt_ringChar`: the corresponding unit statement used by
  unique lifting.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15]
-/

namespace Polynomial

noncomputable section

variable {R F : Type*}

section CommRing

variable [CommRing R]

/-! ### A single centered coefficient perturbation -/

/-- The polynomial that adds coefficient `gamma` in degree `i` in coordinates centered at `a`. -/
def hassePerturbation (a gamma : R) (i : ℕ) : R[X] :=
  C gamma * (X - C a) ^ i

/-- Shifting a centered perturbation to the origin produces the corresponding monomial. -/
@[simp]
theorem taylor_hassePerturbation (a gamma : R) (i : ℕ) :
    taylor a (hassePerturbation a gamma i) = C gamma * X ^ i := by
  simp [hassePerturbation, taylor_apply]

/-- A centered perturbation changes exactly one Hasse coefficient at its center. -/
@[simp]
theorem hasseCoeffAt_hassePerturbation (a gamma : R) (i j : ℕ) :
    hasseCoeffAt a j (hassePerturbation a gamma i) = if j = i then gamma else 0 := by
  rw [hasseCoeffAt_apply, ← taylor_coeff, taylor_hassePerturbation, coeff_C_mul,
    coeff_X_pow]
  split_ifs with h
  · subst j
    simp
  · simp

/-- Adding a centered perturbation changes a Hasse coefficient by the corresponding delta term. -/
theorem hasseCoeffAt_add_hassePerturbation (p : R[X]) (a gamma : R) (i j : ℕ) :
    hasseCoeffAt a j (p + hassePerturbation a gamma i) =
      hasseCoeffAt a j p + if j = i then gamma else 0 := by
  rw [map_add, hasseCoeffAt_hassePerturbation]

/-- Hasse coefficients below the perturbed order are unchanged. -/
theorem hasseCoeffAt_add_hassePerturbation_of_lt (p : R[X]) (a gamma : R) {i j : ℕ}
    (hji : j < i) :
    hasseCoeffAt a j (p + hassePerturbation a gamma i) = hasseCoeffAt a j p := by
  rw [hasseCoeffAt_add_hassePerturbation, if_neg hji.ne, add_zero]

/-- The Hasse coefficient at the perturbed order increases by `gamma`. -/
theorem hasseCoeffAt_add_hassePerturbation_self (p : R[X]) (a gamma : R) (i : ℕ) :
    hasseCoeffAt a i (p + hassePerturbation a gamma i) = hasseCoeffAt a i p + gamma := by
  rw [hasseCoeffAt_add_hassePerturbation, if_pos rfl]

/-- A centered degree-`i` perturbation leaves the order-`m` jet unchanged when `m ≤ i`. -/
theorem hasseJet_add_hassePerturbation_of_le (p : R[X]) (a gamma : R) {m i : ℕ}
    (hmi : m ≤ i) :
    hasseJet m a (p + hassePerturbation a gamma i) = hasseJet m a p := by
  ext j
  exact hasseCoeffAt_add_hassePerturbation_of_lt p a gamma
    (j.isLt.trans_le hmi)

/-! ### Effect after Hasse differentiation -/

/-- Hasse differentiation lowers a centered perturbation and multiplies its coefficient by the
corresponding binomial coefficient. -/
theorem hasseDeriv_hassePerturbation (a gamma : R) (i s : ℕ) :
    hasseDeriv s (hassePerturbation a gamma i) =
      C ((i.choose s : R) * gamma) * (X - C a) ^ (i - s) := by
  apply taylor_injective a
  change taylor a (hasseDeriv s (hassePerturbation a gamma i)) =
    taylor a (hassePerturbation a ((i.choose s : R) * gamma) (i - s))
  rw [← hasseDeriv_taylor, taylor_hassePerturbation, taylor_hassePerturbation]
  simp only [C_mul_X_pow_eq_monomial, hasseDeriv_monomial]

/-- Whole-polynomial form of the Hasse derivative perturbation identity.  This is the form used
when a lifting argument reasons modulo a power of `X - a`, rather than only at one coefficient. -/
theorem hasseDeriv_add_hassePerturbation (p : R[X]) (a gamma : R) (i s : ℕ) :
    hasseDeriv s (p + hassePerturbation a gamma i) =
      hasseDeriv s p + C ((i.choose s : R) * gamma) * (X - C a) ^ (i - s) := by
  rw [LinearMap.map_add, hasseDeriv_hassePerturbation]

/-- Below the newly exposed order, Hasse differentiation does not reveal a centered perturbation.

The hypothesis `j + s < i` is the additive, subtraction-free form of `j < i - s`. -/
theorem hasseCoeffAt_hasseDeriv_add_hassePerturbation_of_lt
    (p : R[X]) (a gamma : R) {i j s : ℕ} (hjs : j + s < i) :
    hasseCoeffAt a j (hasseDeriv s (p + hassePerturbation a gamma i)) =
      hasseCoeffAt a j (hasseDeriv s p) := by
  rw [LinearMap.map_add, map_add, hasseCoeffAt_hasseDeriv,
    hasseCoeffAt_hasseDeriv a j s (hassePerturbation a gamma i),
    hasseCoeffAt_hassePerturbation, if_neg hjs.ne, mul_zero, add_zero]

/-- The first coefficient exposed by taking Hasse derivative `s` changes by
`Nat.choose i s * gamma`.

This is the explicit recurrence multiplier in regular coefficient lifting.  The assumption `s ≤ i`
also covers the boundary cases `s = 0` and `s = i`. -/
theorem hasseCoeffAt_hasseDeriv_add_hassePerturbation
    (p : R[X]) (a gamma : R) {i s : ℕ} (hsi : s ≤ i) :
    hasseCoeffAt a (i - s) (hasseDeriv s (p + hassePerturbation a gamma i)) =
      hasseCoeffAt a (i - s) (hasseDeriv s p) + (i.choose s : R) * gamma := by
  rw [LinearMap.map_add, map_add, hasseCoeffAt_hasseDeriv,
    hasseCoeffAt_hasseDeriv a (i - s) s (hassePerturbation a gamma i),
    hasseCoeffAt_hassePerturbation, Nat.sub_add_cancel hsi, if_pos rfl,
    Nat.choose_symm hsi]

end CommRing

section AddMonoidWithOne

variable [AddMonoidWithOne R]

/-! ### Binomial coefficients in a prime characteristic -/

/-- A binomial coefficient whose upper index is below a prime characteristic remains nonzero after
casting to any additive monoid with one of that characteristic. -/
theorem natCast_choose_ne_zero_of_lt_charP {p i s : ℕ} [CharP R p]
    (hp : p.Prime) (hip : i < p) (hsi : s ≤ i) : (i.choose s : R) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff R p]
  exact hp.coprime_iff_not_dvd.mp (hp.coprime_choose_of_lt hip hsi)

end AddMonoidWithOne

section Field

variable [Field F]

/-! ### Characteristic-safe binomial multipliers -/

/-- A binomial coefficient whose upper index is below the field characteristic is nonzero. -/
theorem natCast_choose_ne_zero_of_lt_ringChar {i s : ℕ}
    (hi : i < ringChar F) (hsi : s ≤ i) : (i.choose s : F) ≠ 0 := by
  exact natCast_choose_ne_zero_of_lt_charP
    (CharP.char_prime_of_ne_zero F (by omega)) hi hsi

/-- A binomial coefficient below the field characteristic is a unit. -/
theorem isUnit_natCast_choose_of_lt_ringChar {i s : ℕ}
    (hi : i < ringChar F) (hsi : s ≤ i) : IsUnit (i.choose s : F) := by
  rw [isUnit_iff_ne_zero]
  exact natCast_choose_ne_zero_of_lt_ringChar hi hsi

/-- An ambient degree bound below the characteristic makes every relevant binomial coefficient a
unit.  This is the form consumed when solutions have degree at most `D`. -/
theorem isUnit_natCast_choose_of_le_of_lt_ringChar {D i s : ℕ}
    (hiD : i ≤ D) (hD : D < ringChar F) (hsi : s ≤ i) : IsUnit (i.choose s : F) :=
  isUnit_natCast_choose_of_lt_ringChar (hiD.trans_lt hD) hsi

/-! ### Unique choice of a lifted coefficient -/

/-- Below the characteristic, the newly exposed Hasse coefficient is injective as a function of
the perturbation coefficient. -/
theorem hasseCoeffAt_hasseDeriv_add_hassePerturbation_injective
    (p : F[X]) (a : F) {i s : ℕ} (hsi : s ≤ i) (hi : i < ringChar F) :
    Function.Injective fun gamma ↦
      hasseCoeffAt a (i - s) (hasseDeriv s (p + hassePerturbation a gamma i)) := by
  intro gamma gamma' h
  change hasseCoeffAt a (i - s) (hasseDeriv s (p + hassePerturbation a gamma i)) =
    hasseCoeffAt a (i - s) (hasseDeriv s (p + hassePerturbation a gamma' i)) at h
  rw [hasseCoeffAt_hasseDeriv_add_hassePerturbation p a gamma hsi,
    hasseCoeffAt_hasseDeriv_add_hassePerturbation p a gamma' hsi,
    add_left_cancel_iff] at h
  exact mul_left_cancel₀ (natCast_choose_ne_zero_of_lt_ringChar hi hsi) h

/-- Below the characteristic, there is a unique centered perturbation producing any prescribed
new Hasse coefficient after differentiation.

This is the one-variable affine equation solved inside a regular lift.  A differential-equation
consumer additionally multiplies `Nat.choose i s` by the nonzero highest-variable partial
derivative. -/
theorem existsUnique_hasseCoeffAt_hasseDeriv_add_hassePerturbation_eq
    (p : F[X]) (a y : F) {i s : ℕ} (hsi : s ≤ i) (hi : i < ringChar F) :
    ∃! gamma : F,
      hasseCoeffAt a (i - s) (hasseDeriv s (p + hassePerturbation a gamma i)) = y := by
  let b := hasseCoeffAt a (i - s) (hasseDeriv s p)
  let c : F := i.choose s
  have hc : c ≠ 0 := natCast_choose_ne_zero_of_lt_ringChar hi hsi
  refine ⟨c⁻¹ * (y - b), ?_, ?_⟩
  · change hasseCoeffAt a (i - s)
      (hasseDeriv s (p + hassePerturbation a (c⁻¹ * (y - b)) i)) = y
    rw [hasseCoeffAt_hasseDeriv_add_hassePerturbation p a _ hsi]
    change b + c * (c⁻¹ * (y - b)) = y
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, add_sub_cancel]
  · intro gamma hgamma
    apply hasseCoeffAt_hasseDeriv_add_hassePerturbation_injective p a hsi hi
    change hasseCoeffAt a (i - s) (hasseDeriv s (p + hassePerturbation a gamma i)) =
      hasseCoeffAt a (i - s)
        (hasseDeriv s (p + hassePerturbation a (c⁻¹ * (y - b)) i))
    rw [hgamma]
    rw [hasseCoeffAt_hasseDeriv_add_hassePerturbation p a _ hsi]
    symm
    change b + c * (c⁻¹ * (y - b)) = y
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, add_sub_cancel]

end Field

end

end Polynomial
