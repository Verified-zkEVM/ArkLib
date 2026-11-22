/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Relations
import ArkLibTest.ProofSystem.RingSwitching.Packing.Polynomial

/-!
# Packing relations over unequal-rank algebras with zero divisors

The fixture packs two one-variable `ZMod 6` components into `(ZMod 6)²` and opens them at a point
of the independent algebra `(ZMod 6)³`. Opening claims, packed slices, and the sumcheck target are
computed by hand. Each relation accepts the honest values and rejects a concrete wrong value.
-/

noncomputable section

namespace RingSwitching.Packing.Tests

open MvPolynomial Module

/-- A sum over the one-bit cube is the sum of its two points. -/
private theorem sum_one_bit {M : Type*} [AddCommMonoid M] (f : (Fin 1 → Fin 2) → M) :
    ∑ y, f y = f (fun _ => 0) + f (fun _ => 1) := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp f, Fin.sum_univ_two]
  rfl

/-- For coordinate bases, transposition is the literal matrix transpose. -/
theorem transpose_apply_apply (α : Fin 2 → Fin 3 → ZMod 6) (u : Fin 3) (i : Fin 2) :
    productData.transpose α u i = α i u := by
  simp only [PackingData.transpose, productData, Pi.basisFun_equivFun,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.refl_apply]
  rfl

/-- The opening point `r₀ = (1, 2, 3)` in the rank-three opening algebra. -/
def openingPoint : Fin 1 → productData.E := fun _ => ![1, 2, 3]

/-- Hand-computed openings `1 + 3 r₀ = (4, 1, 4)` and `4 + 2 r₀ = (0, 2, 4)` in `(ZMod 6)³`. -/
def openingClaims : productData.ιP → productData.E := ![![4, 1, 4], ![0, 2, 4]]

/-- Hand-computed packed slices `∑_y eq(r₀, y)ᵤ · packed(y)`, one per opening coordinate `u`. -/
def packedSlices : productData.ιE → productData.P := ![![4, 0], ![1, 2], ![4, 4]]

/-- Batching weights in the challenge algebra `(ZMod 6)²`, one per opening coordinate. -/
def batchWeights : productData.ιE → productData.P := ![![1, 1], ![1, 2], ![1, 3]]

/-- The honest claims are the two component openings. -/
theorem openingClaimRel_claims :
    ((openingClaims, openingPoint), components) ∈ productData.openingClaimRel 1 := by
  intro i
  funext u
  fin_cases i <;> fin_cases u <;>
    simp +decide [openingClaims, openingPoint, components, affine_aeval]

/-- Claims listed in the swapped packing order are rejected. -/
theorem openingClaimRel_swapped :
    ((![openingClaims 1, openingClaims 0], openingPoint), components) ∉
      productData.openingClaimRel 1 := by
  intro h
  have h00 := congrFun (h 0) 0
  simp +decide [openingClaims, openingPoint, components, affine_aeval] at h00

/-- The hand-computed slices are the transpose of the hand-computed claims. -/
theorem transpose_openingClaims : productData.transpose openingClaims = packedSlices := by
  funext u i
  rw [transpose_apply_apply]
  fin_cases u <;> fin_cases i <;> rfl

/-- The hand-computed slices are the equality-weighted Boolean sums of the packed polynomial. -/
theorem sliceRel_packedSlices : (packedSlices, packed) ∈ productData.sliceRel 1 openingPoint := by
  intro u
  funext i
  simp only [sum_one_bit, PackingData.eqCoord, eqTilde_eq_prod, packed, affine_eval]
  fin_cases u <;> fin_cases i <;> simp +decide

/-- Slices with one wrong coordinate in the last opening slice are rejected. -/
theorem sliceRel_wrong :
    (![packedSlices 0, packedSlices 1, ![4, 1]], packed) ∉ productData.sliceRel 1 openingPoint := by
  intro h
  have h21 := congrFun (h 2) 1
  simp only [sum_one_bit, PackingData.eqCoord, eqTilde_eq_prod, packed, affine_eval] at h21
  simp +decide at h21

/-- The hand-computed claims and slices pass the coordinate consistency check. -/
theorem claimConsistent_openingClaims :
    productData.claimConsistent openingClaims packedSlices := by
  intro i
  funext u
  fin_cases i <;> fin_cases u <;> simp +decide [Pi.single_apply]

/-- The consistency check rejects the honest slices against the swapped claims. -/
theorem claimConsistent_swapped :
    ¬ productData.claimConsistent ![openingClaims 1, openingClaims 0] packedSlices := by
  intro h
  have h00 := congrFun (h 0) 0
  simp +decide [Pi.single_apply] at h00

/-- The hand-computed sumcheck target `(3, 4)` is accepted with weights `batchWeights`. -/
theorem sumcheckClaimRel_target :
    (![3, 4], packed) ∈
      productData.sumcheckClaimRel (C := productData.P) 1 openingPoint batchWeights := by
  change _ = _
  simp only [sum_one_bit, productData.multiplier_eval_zeroOne, PackingData.eqCoord,
    eqTilde_eq_prod, packed, affine_eval]
  funext i
  fin_cases i <;> simp +decide

/-- Batching the hand-computed slices gives the same target, as the slice theorem predicts. -/
theorem batchWeights_packedSlices : ∑ u, batchWeights u * packedSlices u = ![3, 4] := by
  decide

/-- A different sumcheck target for the same packed polynomial is rejected. -/
theorem sumcheckClaimRel_wrong :
    (![3, 5], packed) ∉
      productData.sumcheckClaimRel (C := productData.P) 1 openingPoint batchWeights := by
  intro h
  have h1 := congrFun (h.trans sumcheckClaimRel_target.symm) 1
  exact absurd h1 (by decide)

/-- With no retained variables, a nonzero claim about the zero family is rejected. -/
theorem openingClaimRel_zero_variables (r : Fin 0 → productData.E) :
    ((fun _ => 1, r), fun _ => 0) ∉ productData.openingClaimRel 0 := by
  intro h
  have hzero : (1 : ZMod 6) = 0 := congrFun (h (0 : Fin 2)) (0 : Fin 3)
  exact (by decide : (1 : ZMod 6) ≠ 0) hzero

end RingSwitching.Packing.Tests

end
