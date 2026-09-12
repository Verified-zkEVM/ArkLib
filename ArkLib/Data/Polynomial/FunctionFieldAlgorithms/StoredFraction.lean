/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Univariate.EuclideanAlgorithm
public import Mathlib.FieldTheory.RatFunc.Basic
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.ToPoly.Degree

/-!
# Stored rational-function arithmetic

`Fraction` is an executable numerator/denominator representative over CompPoly's
existing polynomial storage. Its semantic target is Mathlib's `RatFunc`, rather
than a second mathematical rational-function field. Validity excludes a zero
denominator. Equality of representatives is deliberately not field equality.

The gcd cancellation and checked polynomial exact division reuse CompPoly's
Euclidean algorithm. A field dictionary and univariate Euclid over these stored
coefficients are separate remaining obligations.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms

open CompPoly CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Stored computational representative; denominators are certified by `Valid`. -/
structure Fraction (F : Type*) [Zero F] [BEq F] where
  /-- Numerator in the existing canonical dense polynomial representation. -/
  num : CPolynomial F
  /-- Denominator in that same representation. -/
  den : CPolynomial F

/-- The stored denominator is a nonzero polynomial. -/
def Fraction.Valid (a : Fraction F) : Prop := a.den.toPoly ≠ 0

/-- Interpretation into the existing mathematical function field. -/
noncomputable def Fraction.value (a : Fraction F) : RatFunc F :=
  algebraMap (Polynomial F) (RatFunc F) a.num.toPoly /
    algebraMap (Polynomial F) (RatFunc F) a.den.toPoly

/-- Embed a stored polynomial with denominator one. -/
def Fraction.ofPolynomial (p : CPolynomial F) : Fraction F := ⟨p, 1⟩

/-- Cross-multiplication addition; no canonicality claim is made. -/
def Fraction.add (a b : Fraction F) : Fraction F :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩

/-- Multiply numerators and denominators. -/
def Fraction.mul (a b : Fraction F) : Fraction F := ⟨a.num * b.num, a.den * b.den⟩

/-- Negate only the numerator. -/
def Fraction.neg (a : Fraction F) : Fraction F := ⟨-a.num, a.den⟩

/-- Total field inverse: the zero numerator maps to the representative `0/1`. -/
def Fraction.inv (a : Fraction F) : Fraction F :=
  if a.num == 0 then Fraction.ofPolynomial 0 else ⟨a.den, a.num⟩

/-- Division uses the total inverse, including the field convention at zero. -/
def Fraction.div (a b : Fraction F) : Fraction F := a.mul b.inv

@[simp] theorem Fraction.valid_ofPolynomial (p : CPolynomial F) :
    (Fraction.ofPolynomial p).Valid := by simp [Valid, ofPolynomial, toPoly_one]

/-- Addition preserves nonzero denominators. -/
theorem Fraction.valid_add {a b : Fraction F} (ha : a.Valid) (hb : b.Valid) :
    (a.add b).Valid := by simpa [Valid, add, toPoly_mul] using mul_ne_zero ha hb

/-- Multiplication preserves nonzero denominators. -/
theorem Fraction.valid_mul {a b : Fraction F} (ha : a.Valid) (hb : b.Valid) :
    (a.mul b).Valid := by simpa [Valid, mul, toPoly_mul] using mul_ne_zero ha hb

/-- The total inverse always has a nonzero denominator. -/
theorem Fraction.valid_inv (a : Fraction F) : a.inv.Valid := by
  unfold inv
  split
  · exact valid_ofPolynomial 0
  · rename_i h
    exact (toPoly_eq_zero_iff a.num).not.mpr (by simpa using h)

@[simp] theorem Fraction.value_ofPolynomial (p : CPolynomial F) :
    (Fraction.ofPolynomial p).value = algebraMap (Polynomial F) (RatFunc F) p.toPoly := by
  simp [value, ofPolynomial, toPoly_one]

/-- The executed addition refines addition in `RatFunc`. -/
theorem Fraction.value_add {a b : Fraction F} (ha : a.Valid) (hb : b.Valid) :
    (a.add b).value = a.value + b.value := by
  simp only [value, add, toPoly_add, toPoly_mul, map_add, map_mul]
  simpa only [mul_comm] using (div_add_div
    (algebraMap (Polynomial F) (RatFunc F) a.num.toPoly)
    (algebraMap (Polynomial F) (RatFunc F) b.num.toPoly)
    (RatFunc.algebraMap_ne_zero ha) (RatFunc.algebraMap_ne_zero hb)).symm

/-- The executed multiplication refines multiplication in `RatFunc`. -/
theorem Fraction.value_mul (a b : Fraction F) :
    (a.mul b).value = a.value * b.value := by
  simp only [value, mul, toPoly_mul, map_mul]
  exact (div_mul_div_comm _ _ _ _).symm

@[simp] theorem Fraction.value_neg (a : Fraction F) : (a.neg).value = -a.value := by
  simp [value, neg, toPoly_neg, neg_div]

/-- The executed inverse refines the total inverse in `RatFunc`. -/
theorem Fraction.value_inv (a : Fraction F) : a.inv.value = a.value⁻¹ := by
  unfold inv
  split
  · rename_i h
    have hn : a.num = 0 := by simpa using h
    simp [value, ofPolynomial, hn, toPoly_zero, toPoly_one]
  · simp [value, inv_div]

/-- The executed division refines total field division. -/
theorem Fraction.value_div (a b : Fraction F) :
    (a.div b).value = a.value / b.value := by
  rw [div, value_mul, value_inv, div_eq_mul_inv]

/-- Checked exact polynomial division. Zero divisors and inexact inputs return `none`. -/
def exactDivide (p q : CPolynomial F) : Option (CPolynomial F) :=
  if q == 0 then none else
    let r := p.div q
    if r * q == p then some r else none

/-- The actual checked producer succeeds exactly for nonzero divisors with the
specified product identity, and returns the uniquely determined quotient. -/
theorem exactDivide_eq_some_iff (p q r : CPolynomial F) :
    exactDivide p q = some r ↔ q ≠ 0 ∧ r * q = p := by
  unfold exactDivide
  by_cases hq : q = 0
  · simp [hq]
  · simp only [beq_iff_eq, hq, ↓reduceIte]
    constructor
    · split
      · intro h
        have heq := Option.some.inj h
        subst r
        exact ⟨hq, by simpa using ‹(p.div q * q == p) = true›⟩
      · simp
    · rintro ⟨_, hr⟩
      have heq : p.div q = r := by
        apply toPolyLinearEquiv.injective
        change (p.div q).toPoly = r.toPoly
        rw [div_toPoly_eq_div, ← hr, toPoly_mul]
        exact mul_div_cancel_right₀ _ ((toPoly_eq_zero_iff q).not.mpr hq)
      simp [heq, hr]

/-- Successful exact division has the polynomial semantic product identity. -/
theorem exactDivide_sound {p q r : CPolynomial F} (h : exactDivide p q = some r) :
    p.toPoly = r.toPoly * q.toPoly := by
  have hr := ((exactDivide_eq_some_iff p q r).mp h).2
  rw [← hr, toPoly_mul]

/-- Cancel the computed polynomial gcd from numerator and denominator. This is
an arithmetic simplification, not geometric removal of denominator-zero fibers. -/
def Fraction.cancelGcd (a : Fraction F) : Fraction F :=
  let g := (gcdMonic a.num a.den)
  ⟨a.num.div g, a.den.div g⟩

/-- The gcd used by the concrete cancellation is the semantic Euclidean gcd. -/
theorem Fraction.cancelGcd_gcd [DecidableEq F] (a : Fraction F) :
    (gcdMonic a.num a.den).toPoly = normalize (EuclideanDomain.gcd a.num.toPoly a.den.toPoly) :=
  gcdMonic_toPoly_eq_normalize_gcd a.num a.den

private theorem quotient_mul (p g : CPolynomial F) (hg : g.toPoly ≠ 0)
    (hd : g.toPoly ∣ p.toPoly) :
    (p.div g).toPoly * g.toPoly = p.toPoly := by
  rw [div_toPoly_eq_div, mul_comm]
  exact EuclideanDomain.mul_div_cancel' hg hd

/-- Gcd cancellation preserves the denominator validity condition. -/
theorem Fraction.valid_cancelGcd {a : Fraction F} (ha : a.Valid) :
    a.cancelGcd.Valid := by
  classical
  have hg : (gcdMonic a.num a.den).toPoly ≠ 0 := by
    rw [gcdMonic_toPoly_eq_normalize_gcd]
    intro h
    have hd := normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_right a.num.toPoly a.den.toPoly)
    rw [h, zero_dvd_iff] at hd
    exact ha hd
  have hd : (a.den.div (gcdMonic a.num a.den)).toPoly *
      (gcdMonic a.num a.den).toPoly = a.den.toPoly :=
    quotient_mul _ _ hg (by
      rw [gcdMonic_toPoly_eq_normalize_gcd, normalize_dvd_iff]
      exact EuclideanDomain.gcd_dvd_right _ _)
  intro h
  apply ha
  change (a.den.div (gcdMonic a.num a.den)).toPoly = 0 at h
  simp only [h, MulZeroClass.zero_mul] at hd
  exact hd.symm

/-- The executed gcd-and-division producer preserves the represented rational function. -/
theorem Fraction.value_cancelGcd {a : Fraction F} (ha : a.Valid) :
    a.cancelGcd.value = a.value := by
  classical
  let g := (gcdMonic a.num a.den)
  have hg : g.toPoly ≠ 0 := by
    dsimp [g]
    rw [gcdMonic_toPoly_eq_normalize_gcd]
    intro h
    have hd := normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_right a.num.toPoly a.den.toPoly)
    rw [h, zero_dvd_iff] at hd
    exact ha hd
  have hn := quotient_mul a.num g hg (by
    dsimp [g]
    rw [gcdMonic_toPoly_eq_normalize_gcd, normalize_dvd_iff]
    exact EuclideanDomain.gcd_dvd_left _ _)
  have hd := quotient_mul a.den g hg (by
    dsimp [g]
    rw [gcdMonic_toPoly_eq_normalize_gcd, normalize_dvd_iff]
    exact EuclideanDomain.gcd_dvd_right _ _)
  change algebraMap (Polynomial F) (RatFunc F) (a.num.div g).toPoly /
    algebraMap (Polynomial F) (RatFunc F) (a.den.div g).toPoly = a.value
  unfold value
  rw [← hn, ← hd, map_mul, map_mul]
  exact (mul_div_mul_right _ _ (RatFunc.algebraMap_ne_zero hg)).symm

end Polynomial.FunctionFieldAlgorithms
