/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Relations
import ArkLibTest.ProofSystem.RingSwitching.Packing.Polynomial
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Packing and opening over incompatible finite fields

The packing field has rank two and the opening field rank three over `ZMod 2`. There is no
base-compatible embedding of the packing field into the opening field. Opening relations still
accept honest claims about packed coordinate polynomials and reject shifted ones, also after
transport to packed slices, because packing uses the two independent bases.
-/

noncomputable section

namespace RingSwitching.Packing.Tests

open MvPolynomial Module

/-- Two independent finite fields over the same base, with unequal ranks. -/
abbrev separateFields : PackingData (ZMod 2) where
  P := GaloisField 2 2
  E := GaloisField 2 3
  ιP := Fin 2
  ιE := Fin 3
  packBasis := Module.finBasisOfFinrankEq _ _ (GaloisField.finrank (p := 2) (by decide))
  openBasis := Module.finBasisOfFinrankEq _ _ (GaloisField.finrank (p := 2) (by decide))

/-- No base-compatible field transport exists from the packing field to the opening field. -/
theorem noPackingToOpeningHom :
    ¬ Nonempty (GaloisField 2 2 →ₐ[ZMod 2] GaloisField 2 3) := by
  rw [FiniteField.nonempty_algHom_iff_finrank_dvd]
  simp only [GaloisField.finrank (p := 2) (n := 2) (by decide),
    GaloisField.finrank (p := 2) (n := 3) (by decide)]
  decide

/-- Both components are the coordinate `X₀`, so each opens to `r₀`. -/
theorem openingClaimRel_coordinate (r : Fin 1 → GaloisField 2 3) :
    ((fun _ => r 0, r), fun _ => affine 0 1) ∈ separateFields.openingClaimRel 1 := by
  intro i
  simp [affine_aeval]

/-- Claiming `r₀ + 1` for every component is rejected, since `1 ≠ 0` in `GF(8)`. -/
theorem openingClaimRel_shifted (r : Fin 1 → GaloisField 2 3) :
    ((fun _ => r 0 + 1, r), fun _ => affine 0 1) ∉ separateFields.openingClaimRel 1 := by
  intro h
  have h0 := h 0
  simp [affine_aeval] at h0

/-- The transported shifted claim is rejected by the slice relation of the packed family. -/
theorem sliceRel_shifted (r : Fin 1 → GaloisField 2 3) :
    (separateFields.transpose (fun _ => r 0 + 1),
        separateFields.packedMLE (fun _ => affine 0 1)) ∉ separateFields.sliceRel 1 r :=
  fun h => openingClaimRel_shifted r ((separateFields.openingClaimRel_iff_sliceRel r _ _).mpr h)

end RingSwitching.Packing.Tests

end
