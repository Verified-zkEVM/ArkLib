/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Profile
import ArkLib.ProofSystem.RingSwitching.Packing.FiniteObservation

/-!
# Faithful tensor carriers as coordinate families

The tensor carrier message is equivalent to its row family. Its column family is
the packing transposition of those rows. These statements use the explicit two
embeddings and the profile's inverse laws, without identifying the ambient algebra
action on the carrier with either embedding.
-/

namespace RingSwitching.RingSwitchingProfile

open Module

noncomputable section

variable {B L : Type} {κ : ℕ} [CommRing B] [CommRing L] [Algebra B L]
  (P : RingSwitchingProfile B L κ)

/-- Equivalence between the tensor carrier and its complete row-coordinate family. -/
def rowEquiv : P.A ≃ ((Fin κ → Fin 2) → L) where
  toFun := P.decomposeRows
  invFun c := ∑ u, P.φ₀ (c u) * P.φ₁ (P.basis u)
  left_inv z := (P.decomposeRows_spec z).symm
  right_inv := P.decomposeRows_recompose

/-- Equivalence between the tensor carrier and its complete column-coordinate family. -/
def columnEquiv : P.A ≃ ((Fin κ → Fin 2) → L) where
  toFun := P.decomposeColumns
  invFun c := ∑ u, P.φ₁ (c u) * P.φ₀ (P.basis u)
  left_inv z := (P.decomposeColumns_spec z).symm
  right_inv := P.decomposeColumns_recompose

/-- Row coordinates commute with finite sums of carrier elements. -/
theorem decomposeRows_sum {ι : Type*} (s : Finset ι) (f : ι → P.A) :
    P.decomposeRows (∑ i ∈ s, f i) = ∑ i ∈ s, P.decomposeRows (f i) := by
  let rows : P.A →+ ((Fin κ → Fin 2) → L) :=
    { toFun := P.decomposeRows, map_zero' := P.decomposeRows_zero,
      map_add' := P.decomposeRows_add }
  exact map_sum rows f s

/-- Column coordinates commute with finite sums of carrier elements. -/
theorem decomposeColumns_sum {ι : Type*} (s : Finset ι) (f : ι → P.A) :
    P.decomposeColumns (∑ i ∈ s, f i) = ∑ i ∈ s, P.decomposeColumns (f i) := by
  let columns : P.A →+ ((Fin κ → Fin 2) → L) :=
    { toFun := P.decomposeColumns, map_zero' := P.decomposeColumns_zero,
      map_add' := P.decomposeColumns_add }
  exact map_sum columns f s

/-- Transposing a carrier's row family gives exactly its column family, for every message. -/
theorem transpose_rows (z : P.A) :
    (Packing.sameAlgebra P.basis).transpose (P.decomposeRows z) =
      P.decomposeColumns z := by
  conv_rhs => rw [P.decomposeRows_spec z]
  rw [P.decomposeColumns_sum]
  funext u
  change Fin κ → Fin 2 at u
  calc
    _ = ∑ i, P.basis.repr (P.decomposeRows z i) u • P.basis i :=
      (Packing.sameAlgebra P.basis).transpose_apply _ u
    _ = _ := by simp only [P.decomposeColumns_mul, Finset.sum_apply,
      Algebra.smul_def, mul_comm]

/-- Reading the column family back recovers the original row family. -/
theorem readback_columns (z : P.A) :
    (Packing.sameAlgebra P.basis).transpose.symm (P.decomposeColumns z) =
      P.decomposeRows z := by
  rw [← P.transpose_rows]
  exact (Packing.sameAlgebra P.basis).transpose.symm_apply_apply _

/-- Rows of a finite tensor observation are the shared weighted packing coordinates. -/
theorem rows_observation {Y : Type*} [Fintype Y] (a v : Y → L) :
    P.decomposeRows (∑ y, P.φ₀ (a y) * P.φ₁ (v y)) =
      (Packing.sameAlgebra P.basis).observe a v := by
  rw [P.decomposeRows_sum]
  funext i
  change (∑ y, P.decomposeRows (P.φ₀ (a y) * P.φ₁ (v y))) i =
    ∑ y, P.basis.repr (v y) i • a y
  simp only [P.decomposeRows_mul, Finset.sum_apply, Algebra.smul_def, mul_comm]

/-- Columns of a finite tensor observation equal the coordinate slices of its factor families. -/
theorem columns_observation {Y : Type*} [Fintype Y] (a v : Y → L) :
    P.decomposeColumns (∑ y, P.φ₀ (a y) * P.φ₁ (v y)) =
      (Packing.sameAlgebra P.basis).coordinateSlices a v := by
  rw [← P.transpose_rows, P.rows_observation]
  exact (Packing.sameAlgebra P.basis).transpose_observe a v

end

end RingSwitching.RingSwitchingProfile
