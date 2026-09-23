/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ZeroOrder

/-!
# Zero-order local image acceptance tests

Check the triangular coordinates and their rank bound on small instances, including the empty
constraint map at multiplicity zero. A positive derivative order has additional visible-jet
coordinates of contact order zero, so it does not satisfy the two-variable triangular support
description.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- At multiplicity zero there are no order-zero local exponents. -/
example : zeroOrderLocalExponents 0 = ∅ := by decide

/-- At multiplicity two, the triangular exponent set has at most the three coordinates `1`, `T`,
and `TE`. -/
example : (zeroOrderLocalExponents 2).card ≤ 3 := by
  exact (card_zeroOrderLocalExponents_le 2).trans (by decide)

/-- The exponent `T² E` lies in the triangle for multiplicity three. -/
example : Finsupp.single (localT 0) 2 + Finsupp.single (localE 0) 1 ∈
    zeroOrderLocalExponents 3 := by
  rw [mem_zeroOrderLocalExponents]
  simp [localT, localE, localAux]

/-- `T²` is excluded at multiplicity two by the strict cutoff `T < m`. -/
example : Finsupp.single (localT 0) 2 ∉ zeroOrderLocalExponents 2 := by
  rw [mem_zeroOrderLocalExponents]
  simp [localT, localE, localAux]

/-- `E` without a factor of `T` is excluded by the balance condition `E ≤ T`. -/
example : Finsupp.single (localE 0) 1 ∉ zeroOrderLocalExponents 2 := by
  rw [mem_zeroOrderLocalExponents]
  simp [localT, localE, localAux]

/-- At multiplicity two, the unrestricted local constraint map has rank at most three. -/
example (center received : ℚ) :
    Module.finrank ℚ (localConstraintAt (d := 0) 2 center received).range ≤ 3 := by
  exact (finrank_range_localConstraintAt_zeroOrder_le 2 center received).trans (by decide)

private noncomputable def zeroOrderReceivedValue : DifferentialPolynomial ℚ 0 := X (some 0)

private noncomputable def zeroOrderReceivedImage : LocalPolynomial ℚ 0 :=
  localConstraintAt (d := 0) 2 0 0 zeroOrderReceivedValue

private noncomputable def zeroOrderContactExponent : LocalVariable 0 →₀ ℕ :=
  Finsupp.single (localT 0) 1 + Finsupp.single (localE 0) 1

/-- At the origin, the image of `Y₀` has coefficient one at `TE`, so this local map is nonzero.
-/
example : zeroOrderReceivedImage.coeff zeroOrderContactExponent = 1 := by
  simp [zeroOrderReceivedImage, zeroOrderReceivedValue, zeroOrderContactExponent,
    localConstraintAt, LinearMap.comp_apply, projectLowContact, unscaledLocalSubstitution_Y_zero,
    localCorrection, localT, localE, localAux, Finsupp.weight_single, localContactWeight]

/-- The whole-map support bound admits the `TE` coordinate of the concrete nonzero image. -/
example : zeroOrderContactExponent ∈ zeroOrderLocalExponents 2 ∧
    zeroOrderContactExponent (localE 0) ≤ zeroOrderContactExponent (localT 0) ∧
    zeroOrderContactExponent (localT 0) < 2 := by
  have hcoeff : zeroOrderReceivedImage.coeff zeroOrderContactExponent = 1 := by
    simp [zeroOrderReceivedImage, zeroOrderReceivedValue, zeroOrderContactExponent,
      localConstraintAt, LinearMap.comp_apply, projectLowContact, unscaledLocalSubstitution_Y_zero,
      localCorrection, localT, localE, localAux, Finsupp.weight_single, localContactWeight]
  have hsupport : zeroOrderContactExponent ∈ zeroOrderReceivedImage.support :=
    MvPolynomial.mem_support_iff.mpr (by rw [hcoeff]; norm_num)
  have hrange : zeroOrderReceivedImage ∈
      (localConstraintAt (d := 0) 2 0 0).range := by
    exact ⟨zeroOrderReceivedValue, rfl⟩
  have hrestricted := range_localConstraintAt_zeroOrder_le 2 0 0 hrange
  rw [MvPolynomial.mem_restrictSupport_iff] at hrestricted
  have hmem : zeroOrderContactExponent ∈ zeroOrderLocalExponents 2 := by
    simpa only [Finset.mem_coe] using hrestricted hsupport
  exact ⟨hmem, (mem_zeroOrderLocalExponents 2 zeroOrderContactExponent).mp hmem⟩

/-- Restricting the source to the span of `Y₀` still gives a nonzero image and the triangular rank
bound. -/
example :
    let S : Submodule ℚ (DifferentialPolynomial ℚ 0) :=
      Submodule.span ℚ {zeroOrderReceivedValue}
    zeroOrderReceivedImage ∈
        ((localConstraintAt (d := 0) 2 0 0).domRestrict S).range ∧
      zeroOrderReceivedImage ≠ 0 ∧
      Module.finrank ℚ ((localConstraintAt (d := 0) 2 0 0).domRestrict S).range ≤ 3 := by
  dsimp only
  let S : Submodule ℚ (DifferentialPolynomial ℚ 0) :=
    Submodule.span ℚ {zeroOrderReceivedValue}
  have hQ : zeroOrderReceivedValue ∈ S := Submodule.subset_span (by simp)
  have hrange : zeroOrderReceivedImage ∈
      ((localConstraintAt (d := 0) 2 0 0).domRestrict S).range :=
    ⟨⟨zeroOrderReceivedValue, hQ⟩, rfl⟩
  have hnonzero : zeroOrderReceivedImage ≠ 0 := by
    intro hzero
    have hcoeff : zeroOrderReceivedImage.coeff zeroOrderContactExponent = 1 := by
      simp [zeroOrderReceivedImage, zeroOrderReceivedValue, zeroOrderContactExponent,
        localConstraintAt, LinearMap.comp_apply, projectLowContact,
        unscaledLocalSubstitution_Y_zero, localCorrection, localT, localE, localAux,
        Finsupp.weight_single, localContactWeight]
    have := congrArg (fun P : LocalPolynomial ℚ 0 => P.coeff zeroOrderContactExponent) hzero
    rw [hcoeff] at this
    norm_num at this
  exact ⟨hrange, hnonzero,
    (finrank_range_localConstraintAt_zeroOrder_domRestrict_le 2 0 0 S).trans (by decide)⟩

/-- At multiplicity zero, the local constraint range has rank zero. -/
example (center received : ℚ) :
    Module.finrank ℚ (localConstraintAt (d := 0) 0 center received).range ≤ 0 := by
  exact finrank_range_localConstraintAt_zeroOrder_le 0 center received

/-- The order-zero constraint range is finite-dimensional for every multiplicity. -/
example (m : ℕ) (center received : ℚ) :
    Module.Finite ℚ (localConstraintAt (d := 0) m center received).range :=
  finite_range_localConstraintAt_zeroOrder m center received

/-- Any source subspace has the same order-zero rank bound. -/
example (m : ℕ) (center received : ℚ)
    (S : Submodule ℚ (DifferentialPolynomial ℚ 0)) :
    Module.finrank ℚ ((localConstraintAt (d := 0) m center received).domRestrict S).range ≤
      m * (m + 1) / 2 :=
  finrank_range_localConstraintAt_zeroOrder_domRestrict_le m center received S

/-- At derivative order one, powers of the visible jet have contact order zero and are retained at
multiplicity one, showing why the order-zero support description does not extend to positive order.
-/
example (n : ℕ) :
    localContactOrder 1 (Finsupp.single (localY (0 : Fin 1)) n) = 0 := by
  simp [localContactOrder, Finsupp.weight_single, localContactWeight, localY]
