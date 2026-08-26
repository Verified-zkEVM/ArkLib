/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Rq
import CompPoly.Univariate.EuclideanAlgorithm
import Mathlib.RingTheory.EuclideanDomain

/-!
# `Rq.inv` — Computable Inversion in the Cyclotomic Ring

`Rq Φ` is a *computable* `CommRing` (`ArkLib/Data/Lattices/CyclotomicRing/Rq.lean`), but
Mathlib's `Ring.inverse` is not: it dispatches on the undecidable `IsUnit` predicate through
classical choice. Any algorithm that divides in `Rq Φ` — notably the subtract-and-divide
extraction in `ArkLib/Commitments/Functional/Hachi/QuadEval/Soundness.lean` — therefore stops
being executable the moment it names `Ring.inverse`.

This file supplies the executable replacement. Since `φ` is monic and `R` is a field,
`R[X]` is a Euclidean domain, so the extended Euclidean algorithm on `(a, φ)` produces a
Bézout identity `g = s·a + t·φ`; CompPoly ships that algorithm (`CPolynomial.normXgcd`) with
its correctness proofs. Normalizing `g` to be monic makes `g = 1` exactly when `a` is
invertible modulo `φ`, and then `s` *is* the inverse. So the inverse is just the normalized
Bézout cofactor — no unit test and no case split are needed in the definition, which keeps it
total and `#eval`-able.

Correctness is stated only where it is meaningful, i.e. on units; off the units `Rq.inv`
returns whatever the Bézout cofactor happens to be, and callers are expected to carry an
`IsUnit` hypothesis — as [LS18] invertibility of short nonzero elements supplies
(`ArkLib/Data/Lattices/CyclotomicRing/NormBounds/`).

## Main definitions

* `CyclotomicModulus.Rq.inv` — the computable inverse, the normalized Bézout cofactor.

## Main results

* `CyclotomicModulus.Rq.isCoprime_of_isUnit` — a unit of `Rq Φ` is coprime to `φ` in `R[X]`.
* `CyclotomicModulus.Rq.inv_mul_cancel` / `mul_inv_cancel` — `inv` inverts units.
* `CyclotomicModulus.Rq.inv_eq_ringInverse` — on units it agrees with `Ring.inverse`, so
  every `Ring.inverse` lemma transfers.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings and Applications to Lattice-Based Zero-Knowledge Proofs*][LS18]
-/

open Polynomial CompPoly CompPoly.CPolynomial

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-! ## The inverse -/

/-- **The computable inverse on `Rq Φ`**: the cofactor of `a` in the monic-normalized Bézout
identity `g = s·a + t·φ` produced by the extended Euclidean algorithm. When `a` is a unit the
normalized `g` is `1`, so `s·a ≡ 1 (mod φ)` and `s` is the inverse (`inv_mul_cancel`); off the
units the value is unconstrained junk. Total and executable — no `IsUnit` test at the
definition, matching the totality of `Ring.inverse`, which it agrees with on units
(`inv_eq_ringInverse`). -/
def Rq.inv (a : Rq Φ) : Rq Φ := Rq.mk Φ (CPolynomial.normXgcd a.1 Φ.φ).2.1

/-! ## Correctness on units -/

/-- A unit of `Rq Φ` is coprime to the modulus in `R[X]`: an inverse `b` gives
`a·b − 1 ∈ (φ)`, which is a Bézout witness. This is the input to the gcd computation being
trivial, hence to `normXgcd` returning `1`. -/
theorem Rq.isCoprime_of_isUnit {a : Rq Φ} (ha : IsUnit a) :
    IsCoprime a.1.toPoly Φ.φ.toPoly := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
  have hq : Φ.quotientHom a.1 * Φ.quotientHom b.1 = 1 := by
    have := congrArg (Rq.toQuotientHom Φ) hb
    rwa [map_mul, map_one] at this
  have hmem : a.1.toPoly * b.1.toPoly - 1 ∈ Φ.modIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [Φ.quotientHom_apply] using sub_eq_zero.mpr hq
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨b.1.toPoly, -k, by linear_combination hk⟩

/-- On a unit, the monic-normalized gcd of `a` and `φ` is `1` — the fact that makes the
Bézout cofactor an honest inverse. -/
theorem Rq.normXgcd_fst_eq_one {a : Rq Φ} (ha : IsUnit a) :
    (CPolynomial.normXgcd a.1 Φ.φ).1 = 1 := by
  classical
  apply toPoly_injective
  rw [CPolynomial.normXgcd_fst_toPoly, toPoly_one]
  exact normalize_eq_one.mpr
    (EuclideanDomain.gcd_isUnit_iff.mpr (Rq.isCoprime_of_isUnit Φ ha))

/-- **`Rq.inv` inverts units.** Reduce the normalized Bézout identity `1 = s·a + t·φ` modulo
`φ`: the `t·φ` term dies (`quotientHom_phi`) and `s·a ≡ 1`. -/
theorem Rq.inv_mul_cancel {a : Rq Φ} (ha : IsUnit a) : Rq.inv Φ a * a = 1 := by
  set s := (CPolynomial.normXgcd a.1 Φ.φ).2.1 with hs
  set t := (CPolynomial.normXgcd a.1 Φ.φ).2.2 with ht
  have hbez : (1 : CPolynomial R) = s * a.1 + t * Φ.φ := by
    have := CPolynomial.normXgcd_bezout a.1 Φ.φ 0
    rwa [CPolynomial.Bezout, Rq.normXgcd_fst_eq_one Φ ha] at this
  have hsa : Φ.quotientHom (s * a.1) = 1 := by
    rw [show s * a.1 = 1 - t * Φ.φ by rw [hbez]; ring, map_sub, map_mul, quotientHom_phi,
      MulZeroClass.mul_zero, sub_zero, map_one]
  apply Rq.toQuotient_injective Φ
  change Rq.toQuotientHom Φ (Rq.inv Φ a * a) = Rq.toQuotientHom Φ 1
  rw [map_mul, map_one]
  change Rq.toQuotient Φ (Rq.mk Φ s) * Rq.toQuotient Φ a = 1
  rw [Rq.toQuotient_mk]
  change Φ.quotientHom s * Φ.quotientHom a.1 = 1
  rw [← map_mul]; exact hsa

/-- `Rq.inv` inverts units on the right as well. -/
theorem Rq.mul_inv_cancel {a : Rq Φ} (ha : IsUnit a) : a * Rq.inv Φ a = 1 := by
  rw [_root_.mul_comm]; exact Rq.inv_mul_cancel Φ ha

/-- **On units, `Rq.inv` is `Ring.inverse`** — by uniqueness of inverses in a monoid. Lets a
definition switch from the noncomputable `Ring.inverse` to the executable `Rq.inv` while every
`Ring.inverse` lemma in scope keeps applying. -/
theorem Rq.inv_eq_ringInverse {a : Rq Φ} (ha : IsUnit a) :
    Rq.inv Φ a = Ring.inverse a := by
  conv_lhs => rw [← mul_one (Rq.inv Φ a), ← Ring.mul_inverse_cancel a ha,
    ← _root_.mul_assoc, Rq.inv_mul_cancel Φ ha, _root_.one_mul]

end ArkLib.Lattices.CyclotomicModulus
