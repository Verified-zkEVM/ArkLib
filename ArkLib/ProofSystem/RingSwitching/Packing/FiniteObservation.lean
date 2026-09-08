/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Coordinates
import Mathlib.Algebra.Module.BigOperators

/-!
# Finite weighted observations in packing coordinates

Observing a finite table commutes with transposing its packing and opening coordinates.
The weights can be Boolean interpolation weights, monomials, or any opening-algebra values.
The proof uses the finite bases and linearity, without a domain or commitment assumption.
-/

noncomputable section

namespace RingSwitching.Packing.PackingData

variable {B : Type} [CommRing B] (data : PackingData B) {Y : Type*} [Fintype Y]

/-- Observe each packing coordinate of a finite table using opening-algebra weights. -/
def observe (a : Y → data.E) (v : Y → data.P) : data.ιP → data.E :=
  fun i => ∑ y, data.packBasis.repr (v y) i • a y

/-- Observe the packed table separately in each opening-basis coordinate. -/
def coordinateSlices (a : Y → data.E) (v : Y → data.P) : data.ιE → data.P :=
  fun u => ∑ y, data.openBasis.repr (a y) u • v y

/-- Finite weighted observation commutes with the faithful coordinate transpose. -/
theorem transpose_observe (a : Y → data.E) (v : Y → data.P) :
    data.transpose (data.observe a v) = data.coordinateSlices a v := by
  apply data.transpose.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext i
  rw [data.transpose_symm_apply]
  simp only [observe, coordinateSlices, map_sum, Finsupp.finsetSum_apply,
    map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  conv_lhs => rw [← data.openBasis.sum_repr (a y)]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [smul_smul, mul_comm]

/-- Reading observed slices back recovers every weighted packing coordinate. -/
theorem readback_coordinateSlices (a : Y → data.E) (v : Y → data.P) :
    data.transpose.symm (data.coordinateSlices a v) = data.observe a v := by
  rw [← data.transpose_observe, LinearEquiv.symm_apply_apply]

end RingSwitching.Packing.PackingData

end
