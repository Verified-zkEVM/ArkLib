/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Relations
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Packing and opening over incompatible finite fields

The packing field has rank two and the opening field rank three over `ZMod 2`. There is no
base-compatible embedding of the packing field into the opening field. Coordinate packing and
full-family read-back nevertheless apply because they use the two independent bases.
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

example (r : Fin 2 → GaloisField 2 3) (α : Fin 2 → GaloisField 2 3)
    (ps : Fin 2 → (ZMod 2)⦃≤ 1⦄[X Fin 2]) :
    ((α, r), ps) ∈ separateFields.openingClaimRel 2 ↔
      (separateFields.transpose α, separateFields.packedMLE ps) ∈
        separateFields.sliceRel 2 r :=
  separateFields.openingClaimRel_iff_sliceRel r α ps

example (p : (GaloisField 2 2)⦃≤ 1⦄[X Fin 0]) :
    separateFields.packedMLE (separateFields.unpack p) = p :=
  separateFields.packedMLE_unpack p

end RingSwitching.Packing.Tests

end
