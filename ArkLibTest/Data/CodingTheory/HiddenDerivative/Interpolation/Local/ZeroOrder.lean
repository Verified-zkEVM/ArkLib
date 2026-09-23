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
