/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Layout
public import VCVio.CryptoFoundations.CoordinateFork.BlockFinder
public import Mathlib.Data.NNRat.BigOperators

/-!
  # A block and the block finder of VCVio

  VCVio's `OracleComp.blockFinder`, a generalization of the coordinate-wise extractor of [FMN24] to
  an alphabet and a threshold per coordinate, searches a block for a star: a centre and, at every
  coordinate `u`, `k u - 1` challenges that differ from the centre at `u` alone. It returns the
  star as a `Finset` (`CoordinateWise.IsBlockSpecialSound`), and `OracleComp.isFinder_blockFinder`
  gives its finder contract at error `∑ u, (k u - 1) / |X u|` and cost `1 + ∑ u, (k u - 1)`. A block
  of a layout of [DBKVBGLZT26] states the star condition on a family indexed by its children
  (`CoordinateWise.IsBlockSpecialSoundFamily`) and defines the same error sum as `Block.error`.

  This file relates the two, so that the finder's output and contract plug into the layouts.

  ## Main results

  - `CoordinateWise.isBlockSpecialSoundFamily_iff_isBlockSpecialSound`: a family of
    `1 + ∑ u, (k u - 1)` points is a star exactly when its image is a block star, and
    `CoordinateWise.Block.isStar_iff_isBlockSpecialSound` says the same for the children of a
    block.
  - `CoordinateWise.exists_isBlockSpecialSoundFamily_of_isBlockSpecialSound`: every block star,
    such as an output of the finder, is the image of a star family.
  - `CoordinateWise.Block.coe_error` and `CoordinateWise.Block.coe_arity`: on a block with nonempty
    alphabets, `Block.error` and `Block.arity` read in `ℝ≥0∞` are the error and the cost of
    `OracleComp.isFinder_blockFinder`.

  ## References

  * [Dao, Q., Bodaghi, O., Khajehpour, A., Vitto, G., Badakhshan, M., Georghiades, M., Liu, F.,
      Zhang, J., and Thaler, J., *Akita: A High-Performance Lattice-Based Polynomial Commitment
      Scheme*][DBKVBGLZT26]
  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
-/

@[expose] public section

open scoped ENNReal NNReal NNRat

namespace CoordinateWise

variable {ℓ : ℕ} {S : Fin ℓ → Type*}

/-- A family of `1 + ∑ u, (k u - 1)` points is a star exactly when its image is a block star in
VCVio's sense: the image has a centre with `k u - 1` neighbours at every coordinate `u`, and as
many members as the family. -/
theorem isBlockSpecialSoundFamily_iff_isBlockSpecialSound [∀ u, DecidableEq (S u)]
    (k : Fin ℓ → ℕ) (c : Fin (∑ u, (k u - 1) + 1) → (u : Fin ℓ) → S u) :
    IsBlockSpecialSoundFamily k c ↔ IsBlockSpecialSound k (Finset.univ.image c) := by
  constructor
  · rintro ⟨hinj, e, hJ⟩
    refine ⟨⟨c e, Finset.mem_image_of_mem c (Finset.mem_univ e), fun i => ?_⟩, ?_⟩
    · obtain ⟨J, heJ, hcard, hcoord⟩ := hJ i
      refine ⟨J.image c, fun x hx => ?_, ?_, fun y hy => ?_⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        refine Finset.mem_erase.mpr ⟨fun h => heJ ?_, Finset.mem_image_of_mem c (Finset.mem_univ j)⟩
        exact hinj h ▸ hj
      · rw [Finset.card_image_of_injective J hinj, hcard]
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        exact hcoord j hj
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · rintro ⟨⟨e', he', hJ'⟩, hcard⟩
    have hinj : Function.Injective c := by
      have h : (Finset.univ.image c).card =
          (Finset.univ : Finset (Fin (∑ u, (k u - 1) + 1))).card := by
        rw [hcard, Finset.card_univ, Fintype.card_fin]
      intro a b hab
      exact Finset.card_image_iff.mp h (Finset.mem_coe.mpr (Finset.mem_univ a))
        (Finset.mem_coe.mpr (Finset.mem_univ b)) hab
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp he'
    refine ⟨hinj, e, fun i => ?_⟩
    obtain ⟨J', hJ'sub, hcard', hdiff⟩ := hJ' i
    refine ⟨Finset.univ.filter fun j => c j ∈ J', ?_, ?_, fun j hj => ?_⟩
    · intro he
      exact (Finset.mem_erase.mp (hJ'sub (Finset.mem_filter.mp he).2)).1 rfl
    · rw [← hcard', ← Finset.card_image_of_injective _ hinj]
      congr 1
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun ⟨j, hj, hx⟩ => hx ▸ hj, fun hx => ?_⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase (hJ'sub hx))
      exact ⟨j, hx, rfl⟩
    · exact hdiff (c j) (Finset.mem_filter.mp hj).2

/-- **Every block star is the image of a star family.** A set of challenges with the neighbour
structure and `1 + ∑ u, (k u - 1)` members, such as an output of the block finder, enumerates as a
star family indexed by the children. -/
theorem exists_isBlockSpecialSoundFamily_of_isBlockSpecialSound [∀ u, DecidableEq (S u)]
    {k : Fin ℓ → ℕ} {X : Finset ((u : Fin ℓ) → S u)} (h : IsBlockSpecialSound k X) :
    ∃ c : Fin (∑ u, (k u - 1) + 1) → ((u : Fin ℓ) → S u),
      IsBlockSpecialSoundFamily k c ∧ Finset.univ.image c = X := by
  let c : Fin (∑ u, (k u - 1) + 1) → ((u : Fin ℓ) → S u) :=
    fun j => (X.equivFin.symm (Fin.cast h.2.symm j)).val
  have himage : Finset.univ.image c = X := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨fun ⟨j, hj⟩ => hj ▸ (X.equivFin.symm _).property, fun hx => ?_⟩
    refine ⟨Fin.cast h.2 (X.equivFin ⟨x, hx⟩), ?_⟩
    simp [c]
  exact ⟨c, (isBlockSpecialSoundFamily_iff_isBlockSpecialSound k c).mpr (himage ▸ h), himage⟩

namespace Block

/-- The children of a block form a star exactly when their image is a block star. -/
theorem isStar_iff_isBlockSpecialSound (B : Block) [∀ u, DecidableEq (B.Alphabet u)]
    (c : Fin B.arity → B.Point) :
    B.IsStar c ↔ IsBlockSpecialSound B.threshold (Finset.univ.image c) :=
  isBlockSpecialSoundFamily_iff_isBlockSpecialSound B.threshold c

variable (B : Block) [∀ u, Fintype (B.Alphabet u)]

/-- **The error of a block is the error of the block finder.** When every alphabet is nonempty,
the divisions of `Block.error` in `ℚ≥0` are the divisions in `ℝ≥0∞` of
`OracleComp.isFinder_blockFinder`. An admissible block has nonempty alphabets
(`Block.Admissible.nonempty`). Over an empty alphabet the two differ: `ℚ≥0` divides by zero to `0`
and `ℝ≥0∞` to `⊤`. -/
theorem coe_error (hne : ∀ u, Nonempty (B.Alphabet u)) :
    ((B.error : ℝ≥0) : ℝ≥0∞) =
      ∑ u, ((B.threshold u - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (B.Alphabet u) : ℝ≥0∞) := by
  rw [error, NNRat.cast_sum, ENNReal.ofNNReal_finsetSum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hcard : (Fintype.card (B.Alphabet u) : ℝ≥0) ≠ 0 := by
    have := (hne u)
    exact_mod_cast Fintype.card_ne_zero
  rw [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast, ENNReal.coe_div hcard]
  simp

omit [∀ u, Fintype (B.Alphabet u)] in
/-- The arity of a block, read in `ℝ≥0∞`, is the cost of the block finder. -/
theorem coe_arity : ((B.arity : ℕ) : ℝ≥0∞) = 1 + ∑ u, ((B.threshold u - 1 : ℕ) : ℝ≥0∞) := by
  rw [arity]
  push_cast
  ring

end Block

end CoordinateWise
