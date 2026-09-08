/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Relations
import ArkLib.ProofSystem.RingSwitching.Packing.Batching
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Packing acceptance cases beyond one field tower

The base ring `ZMod 6` and unequal-rank product algebras exercise read-back with zero divisors.
Rank-one packing, no retained variables, and a separate challenge algebra exercise boundaries
that should not depend on a positive-dimensional binary field tower.
-/

noncomputable section

namespace RingSwitching.Packing.Tests

open MvPolynomial Module ProbabilityTheory
open scoped NNReal ENNReal

/-- Unequal-rank algebras over a base ring with zero divisors. -/
abbrev productData : PackingData (ZMod 6) where
  P := Fin 2 → ZMod 6
  E := Fin 3 → ZMod 6
  ιP := Fin 2
  ιE := Fin 3
  packBasis := Pi.basisFun _ _
  openBasis := Pi.basisFun _ _

example : (2 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) * 3 = 0 := by
  decide

example (α : Fin 2 → Fin 3 → ZMod 6) (u : Fin 3) (i : Fin 2) :
    productData.transpose α u i = α i u := by
  simp only [PackingData.transpose, productData, Pi.basisFun_equivFun,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.refl_apply]
  rfl

example (ps : Fin 2 → (ZMod 6)⦃≤ 1⦄[X Fin 0]) :
    productData.unpack (productData.packedMLE ps) = ps :=
  productData.unpack_packedMLE ps

example (r : Fin 2 → productData.E) (α : productData.ιP → productData.E)
    (ps : productData.ιP → (ZMod 6)⦃≤ 1⦄[X Fin 2]) :
    ((α, r), ps) ∈ productData.openingClaimRel 2 ↔
      (productData.transpose α, productData.packedMLE ps) ∈ productData.sliceRel 2 r :=
  productData.openingClaimRel_iff_sliceRel r α ps

example (r : Fin 0 → productData.E) :
    ((fun _ => 1, r), fun _ => 0) ∉ productData.openingClaimRel 0 := by
  intro h
  have hzero : (1 : ZMod 6) = 0 := congrFun (h (0 : Fin 2)) (0 : Fin 3)
  exact (by decide : (1 : ZMod 6) ≠ 0) hzero

/-- One packed coefficient with three independent opening coordinates. -/
abbrev rankOneData : PackingData (ZMod 5) where
  P := ZMod 5
  E := Fin 3 → ZMod 5
  ιP := Unit
  ιE := Fin 3
  packBasis := Basis.singleton Unit (ZMod 5)
  openBasis := Pi.basisFun _ _

example (p : (ZMod 5)⦃≤ 1⦄[X Fin 0]) :
    rankOneData.packedMLE (rankOneData.unpack p) = p := rankOneData.packedMLE_unpack p

example {r : Fin 1 → rankOneData.E} {s : Fin 3 → ZMod 5}
    {p : (ZMod 5)⦃≤ 1⦄[X Fin 1]} (hs : (s, p) ∈ rankOneData.sliceRel 1 r)
    (weight : Fin 3 → Fin 2 → ZMod 5) :
    (∑ u, weight u * algebraMap (ZMod 5) (Fin 2 → ZMod 5) (s u), p) ∈
      rankOneData.sumcheckClaimRel 1 r weight :=
  rankOneData.sumcheckClaim_of_slices hs weight

example (s s' : Unit → ZMod 6) (hne : s ≠ s') :
    Pr_{ let c ←$ᵖ (BatchingStrategy.singleton (ZMod 6) Unit).Challenge }[
      ∑ u, (BatchingStrategy.singleton (ZMod 6) Unit).weight c u * s u =
        ∑ u, (BatchingStrategy.singleton (ZMod 6) Unit).weight c u * s' u] ≤ 0 :=
  (BatchingStrategy.singleton (ZMod 6) Unit).separates s s' hne

example (s s' : Fin 3 → ZMod 3) (hne : s ≠ s') :
    let : Fintype (GaloisField 3 2) := Fintype.ofFinite _
    Pr_{ let c ←$ᵖ (GaloisField 3 2) }[
      ∑ u : Fin 3, c ^ (u : ℕ) * algebraMap (ZMod 3) (GaloisField 3 2) (s u) =
        ∑ u : Fin 3, c ^ (u : ℕ) * algebraMap (ZMod 3) (GaloisField 3 2) (s' u)] ≤
      ((BatchingStrategy.gammaPowers (GaloisField 3 2) 3).error : ℝ≥0∞) := by
  let : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  exact (BatchingStrategy.gammaPowers (GaloisField 3 2) 3).separates_map
    (algebraMap (ZMod 3) (GaloisField 3 2))
    (algebraMap (ZMod 3) (GaloisField 3 2)).injective s s' hne

example : (BatchingStrategy.gammaPowers (ZMod 3) 0).error = 0 := by
  simp [BatchingStrategy.gammaPowers]

example (s s' : Fin 1 → ZMod 3) (hne : s ≠ s') :
    Pr_{ let c ←$ᵖ (ZMod 3) }[
      ∑ u : Fin 1, c ^ (u : ℕ) * s u = ∑ u : Fin 1, c ^ (u : ℕ) * s' u] ≤ 0 := by
  simpa [BatchingStrategy.gammaPowers] using
    (BatchingStrategy.gammaPowers (ZMod 3) 1).separates s s' hne

example (s s' : (Fin 0 → Fin 2) → ZMod 3) (hne : s ≠ s') :
    Pr_{ let c ←$ᵖ (Fin 0 → ZMod 3) }[
      ∑ u : Fin 0 → Fin 2, eqTilde (u : Fin 0 → ZMod 3) c * s u =
        ∑ u : Fin 0 → Fin 2, eqTilde (u : Fin 0 → ZMod 3) c * s' u] ≤ 0 := by
  simpa [BatchingStrategy.eqFold] using
    (BatchingStrategy.eqFold (ZMod 3) 0).separates s s' hne

end RingSwitching.Packing.Tests

end
