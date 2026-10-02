/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# The packing profile — data layer of `Packing`

`RingSwitchingProfile` is the data a `Packing` ring switch needs before any protocol is
spoken, and nothing more:

* a **basis** exhibiting the large ring `L` as free of rank `2^κ` over the small ring `B` —
  what makes packing possible in the first place: blocks of `2^κ` small-ring coefficients
  become single `L`-elements, and back;
* a **carrier** `A` — the commutative ring in which the relocation checks are computed;
* **two ring homomorphisms** `φ₀, φ₁ : L →+* A` — one transports evaluation-point data,
  the other polynomial coefficients. The structure records their reconstruction laws
  below; injectivity or other compatibility properties must be proved for each instance;
* **coordinate maps** `decomposeRows`/`decomposeColumns : A → (Fin κ → Fin 2) → L` — the
  `2^κ` `L`-coordinates of a carrier element, one per basis index, with two
  **reconstruction laws** stating that every carrier element is recovered from its
  coordinates as a `φ₀`/`φ₁`-weighted sum over the embedded basis.

Each coordinate map is moreover a **two-sided inverse** of its recomposition map, and the two
embeddings agree on `B`. Reconstruction alone is insufficient: a carrier obtained by collapsing
the two tensor factors can reconstruct every element while losing the coordinates the honest
prover needs. These are data-layer laws, not a soundness theorem: protocol proofs must still
connect the coordinates to `packMLE`, the honest folded element, and the instance's own algebraic
identities.

## Design notes

* It is a `structure` passed **explicitly** (not a `class`): distinct profiles may share the
  same carriers `(B, L, κ)` (e.g. with different bases), so instance resolution would be
  ambiguous.
* It is stated over `CommRing` (not `Field`): carriers of interest include non-field rings.
  The `Field`-only steps (Schwartz–Zippel over `|L|`) stay at the soundness use-sites, not
  here.
* This file holds only the abstract structure and the consequences of its laws, so the sibling
  `Prelude.lean` can import it and parameterize the interactive protocol over it; the
  tensor-product constructor `tensorProductProfile` lives in `Prelude.lean`, after the
  tensor-algebra definitions it is built from.
* The `Algebra L A` instance is ambient structure only; the coordinate laws use the explicit
  `φ₀` and `φ₁` actions.

## Instantiations

The implemented profile is `tensorProductProfile` ([DP24]): `A = L ⊗[B] L`, `φ₀ = · ⊗ 1`,
`φ₁ = 1 ⊗ ·`, with rows and columns the coordinates for the right- and left-factor scalar
actions. Its laws follow from `Basis.sum_repr` and `repr` of the two base-changed bases.

A trace or automorphism switch with carrier `A = L`, such as Hachi's §3 head ([NOZ26]), is not
in general an instance: `L` cannot hold `2^κ` independent `L`-coordinates. Hachi's trace head
and the `Lift` construction (`../Lift/`) have their own algebraic interfaces — see the family
umbrella `ArkLib/ProofSystem/RingSwitching/Basic.lean` for the taxonomy.

See also: the KB concept page `docs/kb/concepts/ring-switching.md` and the blueprint section
`blueprint/src/proof_systems/ring_switching.tex` for the protocol, phases, and security
statements.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over
  Binary Towers*][DP24], §2.5.
* [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J. "Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields."
-/

@[expose] public section

namespace RingSwitching

open Module

/-- The packing-layer data a ring-switching reduction abstracts over. `L` is free of rank `2^κ`
over the small ring `B` (via `basis`); `A` is the carrier of the folded element `ŝ` sent by
batching. The two coordinate maps reconstruct with the basis in opposite embedded factors. -/
structure RingSwitchingProfile (B L : Type*) (κ : ℕ)
    [CommRing B] [CommRing L] [Algebra B L] where
  /-- rank-`2^κ` `B`-basis of `L`. -/
  basis : Basis (Fin κ → Fin 2) B L
  /-- Carrier of the folded element sent in the batching phase. -/
  A : Type*
  [commRingA : CommRing A]
  [algLA : Algebra L A]
  /-- Ring homomorphism for evaluation-point data; `α ↦ α ⊗ 1` in the tensor carrier. -/
  φ₀ : L →+* A
  /-- Ring homomorphism for polynomial coefficients; `α ↦ 1 ⊗ α` in the tensor carrier. -/
  φ₁ : L →+* A
  /-- Row coordinates, used to batch the honest folded element and the final equality tensor.
  For the tensor carrier these are `baseChangeRight` coordinates: the right-factor scalar
  action, distinct from `algLA`, combines them with basis vectors in the left factor. -/
  decomposeRows : A → (Fin κ → Fin 2) → L
  /-- Column coordinates, used to reconstruct the original evaluation claim. For the tensor
  carrier these are `basis.baseChange L` coordinates, using the left-factor scalar action. -/
  decomposeColumns : A → (Fin κ → Fin 2) → L
  /-- Recover a carrier element from row coordinates with the basis in the `φ₀` factor.
  For the tensor carrier this is `z = ∑ u, basis u ⊗ decomposeRows z u`. -/
  decomposeRows_spec : ∀ z : A, z = ∑ u, φ₀ (basis u) * φ₁ (decomposeRows z u)
  /-- Recover a carrier element from column coordinates with the basis in the `φ₁` factor.
  For the tensor carrier this is `z = ∑ v, decomposeColumns z v ⊗ basis v`. -/
  decomposeColumns_spec : ∀ z : A, z = ∑ v, φ₀ (decomposeColumns z v) * φ₁ (basis v)
  /-- Recomposition preserves every row coordinate tuple, ruling out collapsed factors. -/
  decomposeRows_recompose : ∀ c : (Fin κ → Fin 2) → L,
    decomposeRows (∑ u, φ₀ (basis u) * φ₁ (c u)) = c
  /-- Recomposition preserves every column coordinate tuple. -/
  decomposeColumns_recompose : ∀ c : (Fin κ → Fin 2) → L,
    decomposeColumns (∑ v, φ₀ (c v) * φ₁ (basis v)) = c
  /-- The two copies of `L` agree on the common base ring. -/
  embeddings_agree : ∀ b : B, φ₀ (algebraMap B L b) = φ₁ (algebraMap B L b)

attribute [instance] RingSwitchingProfile.commRingA RingSwitchingProfile.algLA

namespace RingSwitchingProfile

variable {B L : Type*} {κ : ℕ} [CommRing B] [CommRing L] [Algebra B L]
  (P : RingSwitchingProfile B L κ)

/-- A row tuple is determined by its recomposition. -/
theorem decomposeRows_eq_iff (z : P.A) (c : (Fin κ → Fin 2) → L) :
    P.decomposeRows z = c ↔ z = ∑ u, P.φ₀ (P.basis u) * P.φ₁ (c u) := by
  constructor
  · intro h
    simpa only [h] using P.decomposeRows_spec z
  · rintro rfl
    exact P.decomposeRows_recompose c

/-- A column tuple is determined by its recomposition. -/
theorem decomposeColumns_eq_iff (z : P.A) (c : (Fin κ → Fin 2) → L) :
    P.decomposeColumns z = c ↔ z = ∑ v, P.φ₀ (c v) * P.φ₁ (P.basis v) := by
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
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib,
    ← P.decomposeRows_spec]

/-- Column coordinates are additive. -/
theorem decomposeColumns_add (x y : P.A) :
    P.decomposeColumns (x + y) = P.decomposeColumns x + P.decomposeColumns y := by
  apply (P.decomposeColumns_eq_iff _ _).mpr
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib,
    ← P.decomposeColumns_spec]

/-- Row coordinates respect the explicit right embedding, independently of `algLA`. -/
theorem decomposeRows_mul_right (a : L) (z : P.A) :
    P.decomposeRows (P.φ₁ a * z) = fun u => a * P.decomposeRows z u := by
  apply (P.decomposeRows_eq_iff _ _).mpr
  conv_lhs => rw [P.decomposeRows_spec z, Finset.mul_sum]
  simp only [map_mul, mul_left_comm]

/-- Column coordinates respect the explicit left embedding. -/
theorem decomposeColumns_mul_left (a : L) (z : P.A) :
    P.decomposeColumns (P.φ₀ a * z) = fun v => a * P.decomposeColumns z v := by
  apply (P.decomposeColumns_eq_iff _ _).mpr
  conv_lhs => rw [P.decomposeColumns_spec z, Finset.mul_sum]
  simp only [map_mul, mul_assoc]

/-- Rows of a pure tensor are its right factor times the base coordinates of its left factor. -/
theorem decomposeRows_mul (x y : L) :
    P.decomposeRows (P.φ₀ x * P.φ₁ y) =
      fun u => y * algebraMap B L (P.basis.repr x u) := by
  apply (P.decomposeRows_eq_iff _ _).mpr
  conv_lhs => rw [← P.basis.sum_repr x]
  simp only [map_sum, Algebra.smul_def, map_mul, Finset.sum_mul, P.embeddings_agree]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [mul_comm, mul_assoc]

/-- Columns of a pure tensor are its left factor times the base coordinates of its right
factor. -/
theorem decomposeColumns_mul (x y : L) :
    P.decomposeColumns (P.φ₀ x * P.φ₁ y) =
      fun v => x * algebraMap B L (P.basis.repr y v) := by
  apply (P.decomposeColumns_eq_iff _ _).mpr
  conv_lhs => rw [← P.basis.sum_repr y]
  simp only [map_sum, Algebra.smul_def, map_mul, Finset.mul_sum, ← P.embeddings_agree]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [mul_assoc]

end RingSwitchingProfile

end RingSwitching
