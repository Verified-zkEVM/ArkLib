/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi

/-!
# Coordinates for packing between independent algebras

`PackingData` supplies finite bases of a packing algebra `P` and an opening algebra `E`
over a common commutative ring `B`. There is no embedding assumed between `P` and `E`.
Coordinate transposition is a linear equivalence: decompose each opening value over `B`,
transpose the resulting matrix, and reassemble each row in the packing basis.

Every coordinate map is derived from a basis, with both inverse laws. Ring or field
nontriviality and probabilistic root-counting assumptions belong to protocol use sites.
The equal-algebra case is the coordinate content of the tensor presentation in [DP24].

## References

* [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers."
-/

namespace RingSwitching.Packing

open Module

/-- Finite-free packing and opening algebras over a common coefficient ring. -/
structure PackingData (B : Type) [CommRing B] where
  /-- The algebra containing packed coefficients. -/
  P : Type
  /-- The algebra containing the original opening point and values. -/
  E : Type
  /-- Packing-basis index, with arbitrary finite rank. -/
  ιP : Type
  /-- Opening-basis index, independently of the packing rank. -/
  ιE : Type
  [commP : CommRing P]
  [algP : Algebra B P]
  [commE : CommRing E]
  [algE : Algebra B E]
  [ftP : Fintype ιP]
  [ftE : Fintype ιE]
  /-- Coordinates used to pack a family of base coefficients. -/
  packBasis : Basis ιP B P
  /-- Coordinates used to decompose opening values. -/
  openBasis : Basis ιE B E

attribute [instance] PackingData.commP PackingData.algP PackingData.commE
  PackingData.algE PackingData.ftP PackingData.ftE

noncomputable section

namespace PackingData

variable {B : Type} [CommRing B] (data : PackingData B)

/-- Transpose opening-value coordinates and pack each resulting row. -/
def transpose : (data.ιP → data.E) ≃ₗ[B] (data.ιE → data.P) where
  toFun α u := data.packBasis.equivFun.symm (fun i => data.openBasis.equivFun (α i) u)
  invFun s i := data.openBasis.equivFun.symm (fun u => data.packBasis.equivFun (s u) i)
  left_inv α := by
    funext i
    simp only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  right_inv s := by
    funext u
    simp only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  map_add' α α' := by
    funext u
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' b α := by
    funext u
    simp [mul_smul, Finset.smul_sum]

/-- Explicit packing formula for coordinate transposition. -/
theorem transpose_apply (α : data.ιP → data.E) (u : data.ιE) :
    data.transpose α u = ∑ i, data.openBasis.repr (α i) u • data.packBasis i := by
  simp only [transpose, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Basis.equivFun_symm_apply, Basis.equivFun_apply]

/-- Read the original opening family back from packed slices. -/
theorem transpose_symm_apply (s : data.ιE → data.P) (i : data.ιP) :
    data.transpose.symm s i = ∑ u, data.packBasis.repr (s u) i • data.openBasis u := by
  simp only [transpose, LinearEquiv.symm_mk, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Basis.equivFun_symm_apply, Basis.equivFun_apply]

/-- Coordinates of a transposed row are the corresponding original column. -/
@[simp]
theorem repr_transpose (α : data.ιP → data.E) (u : data.ιE) (i : data.ιP) :
    data.packBasis.repr (data.transpose α u) i = data.openBasis.repr (α i) u := by
  change data.packBasis.equivFun
    (data.packBasis.equivFun.symm (fun i => data.openBasis.equivFun (α i) u)) i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The linear batching map prescribed by a choice of opening-basis weights.
The target can be any B-module; this map need not be injective. -/
def bridge {C : Type*} [AddCommMonoid C] [Module B C] (weight : data.ιE → C) :
    data.E →ₗ[B] C :=
  data.openBasis.constr B weight

/-- A batching map is the weighted sum of opening coordinates. -/
theorem bridge_apply {C : Type*} [AddCommMonoid C] [Module B C]
    (weight : data.ιE → C) (x : data.E) :
    data.bridge weight x = ∑ u, data.openBasis.repr x u • weight u := by
  simp only [bridge, Basis.constr_apply_fintype, Basis.equivFun_apply]

end PackingData

/-- The specialization with one algebra and one basis in both roles. -/
def sameAlgebra {B L : Type} [CommRing B] [CommRing L] [Algebra B L]
    {ι : Type} [Fintype ι] (basis : Basis ι B L) : PackingData B where
  P := L
  E := L
  ιP := ι
  ιE := ι
  packBasis := basis
  openBasis := basis

end

end RingSwitching.Packing
