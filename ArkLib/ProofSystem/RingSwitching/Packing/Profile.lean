/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Faithful tensor coordinates for the DP24 packing reduction

`RingSwitchingProfile` describes a free extension `L/B`, two commuting images of `L` in a
carrier `A`, and faithful coordinates for both tensor factors. Each decomposition is a
**two-sided inverse** of its corresponding recomposition map; the two embeddings agree on `B`.
These laws support the tensor relocation and batching identities used by `Packing`.

Reconstruction alone is insufficient: a carrier obtained by collapsing the two tensor factors
can reconstruct elements while losing the coordinates needed by the honest prover. In
particular, a trace or automorphism switch with carrier `A = L` is not in general an instance
of this profile. Hachi's trace head and the generic `Lift` construction have separate algebraic
interfaces. They may reuse check-then-update verifier shapes without sharing their algebraic laws.

The concrete tensor instance `binaryTowerProfile` in `Prelude.lean` derives these laws from the
left and right base-changed bases of `L ⊗[B] L`. The `Algebra L A` instance is only ambient
structure; the coordinate laws below use the explicit `φ₀` and `φ₁` actions.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24]
-/

namespace RingSwitching

open Module

/--
Finite-basis extension data with two compatible embeddings and invertible tensor-coordinate
decompositions.
-/
structure RingSwitchingProfile (B L : Type*) (κ : ℕ)
    [CommRing B] [CommRing L] [Algebra B L] where
  /-- Rank-`2^κ` `B`-basis of `L`. -/
  basis : Basis (Fin κ → Fin 2) B L
  /-- Carrier of the folded polynomial evaluation. -/
  A : Type*
  [commRingA : CommRing A]
  [algLA : Algebra L A]
  /-- Embedding of evaluation-point data. -/
  φ₀ : L →+* A
  /-- Embedding of polynomial data. -/
  φ₁ : L →+* A
  /-- Coordinates for the `φ₀` scalar action and the `φ₁`-embedded basis. -/
  decomposeRows : A → (Fin κ → Fin 2) → L
  /-- Coordinates for the `φ₁` scalar action and the `φ₀`-embedded basis. -/
  decomposeColumns : A → (Fin κ → Fin 2) → L
  /-- Every carrier element is recovered from its row coordinates. -/
  decomposeRows_spec : ∀ z : A, z = ∑ u, φ₀ (decomposeRows z u) * φ₁ (basis u)
  /-- Every carrier element is recovered from its column coordinates. -/
  decomposeColumns_spec : ∀ z : A, z = ∑ u, φ₁ (decomposeColumns z u) * φ₀ (basis u)
  /-- Recomposition preserves every row coordinate tuple, ruling out collapsed factors. -/
  decomposeRows_recompose : ∀ c : (Fin κ → Fin 2) → L,
    decomposeRows (∑ u, φ₀ (c u) * φ₁ (basis u)) = c
  /-- Recomposition preserves every column coordinate tuple. -/
  decomposeColumns_recompose : ∀ c : (Fin κ → Fin 2) → L,
    decomposeColumns (∑ u, φ₁ (c u) * φ₀ (basis u)) = c
  /-- The two copies of `L` identify the common base ring. -/
  embeddings_agree : ∀ b : B, φ₀ (algebraMap B L b) = φ₁ (algebraMap B L b)

attribute [instance] RingSwitchingProfile.commRingA RingSwitchingProfile.algLA

namespace RingSwitchingProfile

variable {B L : Type*} {κ : ℕ} [CommRing B] [CommRing L] [Algebra B L]
  (P : RingSwitchingProfile B L κ)

/-- A row tuple is determined by its recomposition. -/
theorem decomposeRows_eq_iff (z : P.A) (c : (Fin κ → Fin 2) → L) :
    P.decomposeRows z = c ↔ z = ∑ u, P.φ₀ (c u) * P.φ₁ (P.basis u) := by
  constructor
  · intro h
    simpa only [h] using P.decomposeRows_spec z
  · rintro rfl
    exact P.decomposeRows_recompose c

/-- A column tuple is determined by its recomposition. -/
theorem decomposeColumns_eq_iff (z : P.A) (c : (Fin κ → Fin 2) → L) :
    P.decomposeColumns z = c ↔ z = ∑ u, P.φ₁ (c u) * P.φ₀ (P.basis u) := by
  constructor
  · intro h
    simpa only [h] using P.decomposeColumns_spec z
  · rintro rfl
    exact P.decomposeColumns_recompose c

@[simp] theorem decomposeRows_zero : P.decomposeRows 0 = 0 := by
  apply (P.decomposeRows_eq_iff _ _).mpr
  simp

@[simp] theorem decomposeColumns_zero : P.decomposeColumns 0 = 0 := by
  apply (P.decomposeColumns_eq_iff _ _).mpr
  simp

/-- Row coordinates are additive; this is derived from the inverse laws. -/
theorem decomposeRows_add (x y : P.A) :
    P.decomposeRows (x + y) = P.decomposeRows x + P.decomposeRows y := by
  apply (P.decomposeRows_eq_iff _ _).mpr
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib,
    ← P.decomposeRows_spec]

/-- Column coordinates are additive. -/
theorem decomposeColumns_add (x y : P.A) :
    P.decomposeColumns (x + y) = P.decomposeColumns x + P.decomposeColumns y := by
  apply (P.decomposeColumns_eq_iff _ _).mpr
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib,
    ← P.decomposeColumns_spec]

/-- Row coordinates respect the explicit left embedding, independently of `algLA`. -/
theorem decomposeRows_mul_left (a : L) (z : P.A) :
    P.decomposeRows (P.φ₀ a * z) = fun u => a * P.decomposeRows z u := by
  apply (P.decomposeRows_eq_iff _ _).mpr
  conv_lhs => rw [P.decomposeRows_spec z, Finset.mul_sum]
  simp only [map_mul, mul_assoc]

/-- Column coordinates respect the explicit right embedding. -/
theorem decomposeColumns_mul_right (a : L) (z : P.A) :
    P.decomposeColumns (P.φ₁ a * z) = fun u => a * P.decomposeColumns z u := by
  apply (P.decomposeColumns_eq_iff _ _).mpr
  conv_lhs => rw [P.decomposeColumns_spec z, Finset.mul_sum]
  simp only [map_mul, mul_assoc]

/-- Rows of a pure tensor are its left factor times the base coordinates of its right factor. -/
theorem decomposeRows_mul (x y : L) :
    P.decomposeRows (P.φ₀ x * P.φ₁ y) =
      fun u => x * algebraMap B L (P.basis.repr y u) := by
  apply (P.decomposeRows_eq_iff _ _).mpr
  conv_lhs => rw [← P.basis.sum_repr y]
  simp only [map_sum, Algebra.smul_def, map_mul, Finset.mul_sum, mul_assoc,
    P.embeddings_agree]

/-- Columns of a pure tensor are its right factor times the base coordinates of its left factor. -/
theorem decomposeColumns_mul (x y : L) :
    P.decomposeColumns (P.φ₀ x * P.φ₁ y) =
      fun u => y * algebraMap B L (P.basis.repr x u) := by
  rw [mul_comm]
  apply (P.decomposeColumns_eq_iff _ _).mpr
  conv_lhs => rw [← P.basis.sum_repr x]
  simp only [map_sum, Algebra.smul_def, map_mul, Finset.mul_sum, mul_assoc,
    P.embeddings_agree]

end RingSwitchingProfile

end RingSwitching
