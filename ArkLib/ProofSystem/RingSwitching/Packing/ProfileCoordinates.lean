/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Profile
public import ArkLib.ProofSystem.RingSwitching.Packing.FiniteObservation
public import CompPoly.LinearAlgebra.TensorProduct.Basis

/-!
# Faithful profile carriers as coordinate families

A profile carrier is additively equivalent to each of its complete coordinate families, so a
finite carrier has `|L| ^ (2 ^ κ)` elements. Its row
family is the packing transposition of its column family, and the coordinates of a finite tensor
observation are the shared weighted observation and its coordinate slices. These statements use
the explicit embeddings `φ₀`, `φ₁` and the profile's inverse laws. The canonical ring
isomorphism `tensorEquiv` identifies every profile carrier with `L ⊗[B] L`, without
finiteness or field hypotheses. Thus the profile permits a choice of representation and
coordinates for this tensor algebra.

Orientation follows `RingSwitchingProfile`: rows carry the basis in the `φ₀` factor, columns
carry it in the `φ₁` factor.
-/

@[expose] public section

namespace RingSwitching.RingSwitchingProfile

open Module TensorProduct

noncomputable section

variable {B L : Type} {κ : ℕ} [CommRing B] [CommRing L] [Algebra B L]
  (P : RingSwitchingProfile B L κ)

/-- The canonical map from the tensor algebra to the profile carrier. Its base-ring action
is induced by `φ₀`; agreement of the embeddings makes `φ₁` linear for the same action. -/
def tensorToCarrier : L ⊗[B] L →+* P.A :=
  letI : Algebra B P.A := (P.φ₀.comp (algebraMap B L)).toAlgebra
  (Algebra.TensorProduct.productMap
    ({ P.φ₀ with commutes' := fun _ => rfl } : L →ₐ[B] P.A)
    ({ P.φ₁ with commutes' := fun b => (P.embeddings_agree b).symm } :
      L →ₐ[B] P.A)).toRingHom

/-- The canonical map multiplies the two explicitly embedded tensor factors. -/
@[simp] theorem tensorToCarrier_tmul (x y : L) :
    P.tensorToCarrier (x ⊗ₜ[B] y) = P.φ₀ x * P.φ₁ y := rfl

/-- The row inverse laws make the canonical tensor map bijective. -/
theorem tensorToCarrier_bijective : Function.Bijective P.tensorToCarrier := by
  classical
  let rightAlgebra : Algebra L (L ⊗[B] L) := Algebra.TensorProduct.rightAlgebra
  let rightModule : Module L (L ⊗[B] L) := rightAlgebra.toModule
  have rows (z : L ⊗[B] L) :
      ∃ c : (Fin κ → Fin 2) → L, z = ∑ u, P.basis u ⊗ₜ[B] c u := by
    refine ⟨fun u => (P.basis.baseChangeRight (Right := L)).repr z u, ?_⟩
    conv_lhs => rw [← (P.basis.baseChangeRight (Right := L)).sum_repr z]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Basis.baseChangeRight_apply, Algebra.smul_def]
    change (1 ⊗ₜ[B] _) * _ = _
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  constructor
  · intro x y hxy
    obtain ⟨c, rfl⟩ := rows x
    obtain ⟨d, rfl⟩ := rows y
    simp only [map_sum, tensorToCarrier_tmul] at hxy
    have hcoords := congrArg P.decomposeRows hxy
    rw [P.decomposeRows_recompose, P.decomposeRows_recompose] at hcoords
    rw [hcoords]
  · intro z
    refine ⟨∑ u, P.basis u ⊗ₜ[B] P.decomposeRows z u, ?_⟩
    simp only [map_sum, tensorToCarrier_tmul]
    exact (P.decomposeRows_spec z).symm

/-- Every profile carrier is a presentation of the tensor algebra `L ⊗[B] L`. -/
def tensorEquiv : L ⊗[B] L ≃+* P.A :=
  RingEquiv.ofBijective P.tensorToCarrier P.tensorToCarrier_bijective

/-- The presentation isomorphism preserves the two embedded tensor factors. -/
@[simp] theorem tensorEquiv_tmul (x y : L) :
    P.tensorEquiv (x ⊗ₜ[B] y) = P.φ₀ x * P.φ₁ y := rfl

/-- The inverse presentation map reconstructs a tensor from the profile's row coordinates. -/
theorem tensorEquiv_symm_apply (z : P.A) :
    P.tensorEquiv.symm z = ∑ u, P.basis u ⊗ₜ[B] P.decomposeRows z u := by
  apply P.tensorEquiv.injective
  simp only [RingEquiv.apply_symm_apply, map_sum, tensorEquiv_tmul]
  exact P.decomposeRows_spec z

/-- Additive equivalence between the carrier and its complete row-coordinate family. -/
def rowEquiv : P.A ≃+ ((Fin κ → Fin 2) → L) where
  toFun := P.decomposeRows
  invFun c := ∑ u, P.φ₀ (P.basis u) * P.φ₁ (c u)
  left_inv z := (P.decomposeRows_spec z).symm
  right_inv := P.decomposeRows_recompose
  map_add' := P.decomposeRows_add

/-- Additive equivalence between the carrier and its complete column-coordinate family. -/
def columnEquiv : P.A ≃+ ((Fin κ → Fin 2) → L) where
  toFun := P.decomposeColumns
  invFun c := ∑ v, P.φ₀ (c v) * P.φ₁ (P.basis v)
  left_inv z := (P.decomposeColumns_spec z).symm
  right_inv := P.decomposeColumns_recompose
  map_add' := P.decomposeColumns_add

/-- Row coordinates commute with finite sums of carrier elements. -/
theorem decomposeRows_sum {ι : Type*} (s : Finset ι) (f : ι → P.A) :
    P.decomposeRows (∑ i ∈ s, f i) = ∑ i ∈ s, P.decomposeRows (f i) :=
  map_sum P.rowEquiv f s

/-- Column coordinates commute with finite sums of carrier elements. -/
theorem decomposeColumns_sum {ι : Type*} (s : Finset ι) (f : ι → P.A) :
    P.decomposeColumns (∑ i ∈ s, f i) = ∑ i ∈ s, P.decomposeColumns (f i) :=
  map_sum P.columnEquiv f s

/-- A finite carrier has exactly `|L| ^ (2 ^ κ)` elements. -/
theorem card_A [Fintype L] [Fintype P.A] : Fintype.card P.A = Fintype.card L ^ 2 ^ κ := by
  classical
  rw [Fintype.card_congr P.rowEquiv.toEquiv, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

/-- Transposing a carrier's column family gives exactly its row family, for every element. -/
theorem transpose_decomposeColumns (z : P.A) :
    (Packing.PackingData.ofBasis P.basis).transpose (P.decomposeColumns z) =
      P.decomposeRows z := by
  conv_rhs => rw [P.decomposeColumns_spec z]
  rw [P.decomposeRows_sum]
  funext u
  change Fin κ → Fin 2 at u
  calc
    _ = ∑ v, P.basis.repr (P.decomposeColumns z v) u • P.basis v :=
      (Packing.PackingData.ofBasis P.basis).transpose_apply _ u
    _ = _ := by simp only [P.decomposeRows_φ₀_mul_φ₁, Finset.sum_apply, Algebra.smul_def]

/-- Reading the row family back recovers the original column family. -/
theorem transpose_symm_decomposeRows (z : P.A) :
    (Packing.PackingData.ofBasis P.basis).transpose.symm (P.decomposeRows z) =
      P.decomposeColumns z := by
  rw [← P.transpose_decomposeColumns]
  exact (Packing.PackingData.ofBasis P.basis).transpose.symm_apply_apply _

/-- Columns of a finite tensor observation are the shared weighted packing coordinates. -/
theorem decomposeColumns_observation {Y : Type*} [Fintype Y] (a v : Y → L) :
    P.decomposeColumns (∑ y, P.φ₀ (a y) * P.φ₁ (v y)) =
      (Packing.PackingData.ofBasis P.basis).observe a v := by
  rw [P.decomposeColumns_sum]
  funext i
  change (∑ y, P.decomposeColumns (P.φ₀ (a y) * P.φ₁ (v y))) i =
    ∑ y, P.basis.repr (v y) i • a y
  simp only [P.decomposeColumns_φ₀_mul_φ₁, Finset.sum_apply, Algebra.smul_def, mul_comm]

/-- Rows of a finite tensor observation are the coordinate slices of its factor families. -/
theorem decomposeRows_observation {Y : Type*} [Fintype Y] (a v : Y → L) :
    P.decomposeRows (∑ y, P.φ₀ (a y) * P.φ₁ (v y)) =
      (Packing.PackingData.ofBasis P.basis).coordinateSlices a v := by
  rw [← P.transpose_decomposeColumns, P.decomposeColumns_observation]
  exact (Packing.PackingData.ofBasis P.basis).transpose_observe a v

end

end RingSwitching.RingSwitchingProfile
