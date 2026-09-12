/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.SystemEnumeration

/-!
# Direct agreement selection at the actual message precision

The executable all-subsets adapter uses only received-position labels. Its rows are the supplied
hypersurface equation followed by exactly `r` agreements. The coefficient differential has exactly
`k` coordinates. The chart producer must still supply its injectivity on the hypersurface tangent
space and identify agreement differentials with the scaled evaluation map below.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer

open ReedSolomon.HiddenDerivative.SquareSystems
open scoped BigOperators

/-- Enumerate direct systems from a stored hypersurface and stored agreement equations.
Each system has exactly `r + 1` rows. Equal systems may be deduplicated; labels are positions. -/
def directSystems {P : Type*} [DecidableEq P] {n : ℕ} (r : ℕ)
    (hypersurface : P) (agreements : Fin n → P) : Finset (Fin (r + 1) → P) :=
  enumerateSquareSystems r hypersurface agreements

/-- Every output starts with the supplied hypersurface, and its other rows are agreements. -/
theorem directSystems_rows {P : Type*} [DecidableEq P] {n r : ℕ}
    (hypersurface : P) (agreements : Fin n → P)
    {system : Fin (r + 1) → P} (hsystem : system ∈ directSystems r hypersurface agreements) :
    system 0 = hypersurface ∧ ∀ j : Fin r, ∃ i : Fin n, system j.succ = agreements i := by
  obtain ⟨selected, _, rfl⟩ := Finset.mem_image.mp hsystem
  exact ⟨rfl, fun j ↦ ⟨_, rfl⟩⟩

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W]

/-- Evaluate exactly the `k` message coefficients at the `k` distinct centered nodes. -/
def directEvaluation {k : ℕ} (center : F) (points : Fin k ↪ F) :
    (Fin k → F) →ₗ[F] (Fin k → F) :=
  (LinearMap.fst F (Fin k → F) (Fin (k - k) → F)).comp
    (evaluationTailMap k k le_rfl center points)

@[simp]
theorem directEvaluation_apply {k : ℕ} (center : F) (points : Fin k ↪ F)
    (coefficients : Fin k → F) (i : Fin k) :
    directEvaluation center points coefficients i =
      ∑ j : Fin k, coefficients j * (points i - center) ^ (j : ℕ) := rfl

/-- Distinct evaluations determine a message of the actual precision `k`. -/
theorem directEvaluation_injective {k : ℕ} (center : F) (points : Fin k ↪ F) :
    Function.Injective (directEvaluation center points) := by
  intro x y hxy
  apply evaluationTailMap_injective k k le_rfl center points
  apply Prod.ext hxy
  ext j
  exact Fin.elim0 (Fin.cast (Nat.sub_self k) j)

/-- A nonzero common denominator preserves tangent capture. This is the direct-chart contract:
the supplied agreement differential equals denominator times evaluation of coefficient variation
on the tangent space. No chart or solver producer is assumed to have been constructed here. -/
theorem tangent_agreements_injective {k : ℕ} (center : F) (points : Fin k ↪ F)
    (normal : W →ₗ[F] F) (coefficients : W →ₗ[F] (Fin k → F))
    (agreements : W →ₗ[F] (Fin k → F)) (denominator : F) (hdenominator : denominator ≠ 0)
    (hcoefficients : Function.Injective (coefficients.comp normal.ker.subtype))
    (hidentity : ∀ v : normal.ker, agreements v =
      denominator • directEvaluation center points (coefficients v)) :
    Function.Injective (agreements.comp normal.ker.subtype) := by
  intro x y hxy
  apply hcoefficients
  apply directEvaluation_injective center points
  have heq : denominator • directEvaluation center points (coefficients x) =
      denominator • directEvaluation center points (coefficients y) := by
    rw [← hidentity x, ← hidentity y]
    exact hxy
  exact (smul_right_injective _ hdenominator) heq

/-- Select only agreeing positions; the hypersurface normal and these `r` rows are injective. -/
theorem exists_direct_square_selection [FiniteDimensional F W] {k r : ℕ}
    (center : F) (points : Fin k ↪ F) (normal : W →ₗ[F] F)
    (coefficients agreements : W →ₗ[F] (Fin k → F))
    (denominator : F) (hdenominator : denominator ≠ 0)
    (hdim : Module.finrank F W = r + 1) (hnormal : normal ≠ 0)
    (hcoefficients : Function.Injective (coefficients.comp normal.ker.subtype))
    (hidentity : ∀ v : normal.ker, agreements v =
      denominator • directEvaluation center points (coefficients v)) :
    ∃ selected : Fin r ↪ Fin k,
      Function.Injective (normalSelectedMap normal agreements selected) := by
  exact exists_injective_normalSelectedMap normal agreements hdim hnormal
    (tangent_agreements_injective center points normal coefficients agreements denominator
      hdenominator hcoefficients hidentity)

/-- The executed all-subsets family contains the canonical ordering of a capturing selection.
The semantic differential can be supplied separately from the stored polynomial representation. -/
theorem directSystems_contains_capture [FiniteDimensional F W]
    {P : Type*} [DecidableEq P] {n r : ℕ}
    (hypersurface : P) (equations : Fin n → P)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = r + 1) (hnormal : normal ≠ 0)
    (htangent : Function.Injective (pool.comp normal.ker.subtype)) :
    ∃ (selected : Finset (Fin n)) (hcard : selected.card = r),
      squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) ∈
        directSystems r hypersurface equations ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  obtain ⟨selected, hinjective⟩ :=
    exists_injective_normalSelectedMap normal pool hdim hnormal htangent
  refine ⟨Finset.univ.map selected, card_map_univ_embedding selected, ?_, ?_⟩
  · exact squareSystemRows_mem_enumerate hypersurface equations _ _
  · exact rowSubsetEmbedding_preserves_injective normal pool selected hinjective

/-- Restrict row selection to agreeing positions before enumerating the full received pool.
The same returned direct system both vanishes at the point and has injective square differential.
The caller supplies the interpretation and differential of its stored equations. -/
theorem directSystems_contains_commonZero_capture [FiniteDimensional F W]
    {P : Type*} [DecidableEq P] {n k r : ℕ}
    (hypersurface : P) (equations : Fin n → P) (evaluate : P → F)
    (positions : Fin k ↪ Fin n)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = r + 1) (hnormal : normal ≠ 0)
    (htangent : Function.Injective
      ((selectedCoordinateMap pool positions).comp normal.ker.subtype))
    (hzero : evaluate hypersurface = 0)
    (hagree : ∀ i, evaluate (equations (positions i)) = 0) :
    ∃ (selected : Finset (Fin n)) (hcard : selected.card = r),
      squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) ∈
        directSystems r hypersurface equations ∧
      (∀ i, evaluate
        (squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) i) = 0) ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  obtain ⟨chosen, hchosen⟩ := exists_injective_normalSelectedMap normal
    (selectedCoordinateMap pool positions) hdim hnormal htangent
  let full := chosen.trans positions
  have hfull : Function.Injective (normalSelectedMap normal pool full) := by
    exact hchosen
  let rows := Finset.univ.map full
  have hcard : rows.card = r := card_map_univ_embedding full
  refine ⟨rows, hcard, squareSystemRows_mem_enumerate _ _ _ _, ?_, ?_⟩
  · intro i
    refine Fin.cases hzero (fun j ↦ ?_) i
    change evaluate (equations (rowSubsetEmbedding rows hcard j)) = 0
    have hmem : rowSubsetEmbedding rows hcard j ∈ rows := by
      have hm : rowSubsetEmbedding rows hcard j ∈ Set.range (rows.orderEmbOfFin hcard) :=
        ⟨j, rfl⟩
      rwa [Finset.range_orderEmbOfFin] at hm
    obtain ⟨l, _, hl⟩ := Finset.mem_map.mp hmem
    rw [← hl]
    exact hagree (chosen l)
  · exact rowSubsetEmbedding_preserves_injective normal pool full hfull


end ReedSolomon.ListDecoding.HigherOrderProducer
