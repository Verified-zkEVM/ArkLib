/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.DerivedBatching
import ArkLibTest.ProofSystem.RingSwitching.Packing.Polynomial
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Derived batching with packing rank two and opening rank three

Over `F₅`, the coordinate polynomials `X` and `1 + X` pack into one nonconstant polynomial
in `F₂₅[X]` and open at `2` in `F₁₂₅`. The component claims are the nonzero values `2,3`.
Power batching over `F₂₅` preserves the honest source, and a list containing that source and
an incorrect zero polynomial is charged for only one candidate, with bound `2/25`.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.DerivedBatchingRanks

open MvPolynomial ProbabilityTheory
open scoped NNReal ENNReal

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F25 := GaloisField 5 2
abbrev F125 := GaloisField 5 3

local instance : Fintype F25 := Fintype.ofFinite _
local instance : SampleableType F25 := SampleableType.ofFintype F25

abbrev data : PackingData (ZMod 5) where
  P := F25
  E := F125
  ιP := Fin 2
  ιE := Fin 3
  packBasis := Module.finBasisOfFinrankEq _ _ (GaloisField.finrank (p := 5) (by decide))
  openBasis := Module.finBasisOfFinrankEq _ _ (GaloisField.finrank (p := 5) (by decide))

def components : Fin 2 → (ZMod 5)⦃≤ 1⦄[X Fin 1] := ![affine 0 1, affine 1 1]

def source : data.P⦃≤ 1⦄[X Fin 1] := data.packedMLE components

def r : Fin 1 → data.E := fun _ => 2

def claims : data.ιP → data.E := ![2, 3]

abbrev bat : BatchingStrategy F25 data.ιE := BatchingStrategy.gammaPowers F25 3

theorem ranks : Fintype.card data.ιP = 2 ∧ Fintype.card data.ιE = 3 := by decide

theorem claims_ne_zero (i : data.ιP) : claims i ≠ 0 := by
  fin_cases i
  · exact (CharP.cast_eq_zero_iff F125 5 2).not.mpr (by decide)
  · exact (CharP.cast_eq_zero_iff F125 5 3).not.mpr (by decide)

theorem source_nonconstant (a : data.P) : source.val ≠ C a := by
  intro h
  have hlinear : (data.unpack source 0).val.coeff (Finsupp.single 0 1) = 1 := by
    rw [show data.unpack source = components from data.unpack_packedMLE components]
    simp [components, affine_coeff, zero_ne_single]
  rw [data.unpack_coeff, h] at hlinear
  simp [coeff_C, zero_ne_single] at hlinear

theorem honest : ((claims, r), data.unpack source) ∈ data.openingClaimRel 1 := by
  rw [show data.unpack source = components from data.unpack_packedMLE components]
  intro i
  fin_cases i <;> norm_num [components, claims, affine_aeval, r]

theorem honest_preserved (γ : bat.Challenge) :
    (data.derivedTarget claims (bat.weight γ), source) ∈
      data.sumcheckClaimRel 1 r (bat.weight γ) :=
  data.sumcheckClaimRel_derivedTarget_of_openingClaimRel _ _ _ _ honest

theorem zero_incorrect :
    ((claims, r), data.unpack (0 : data.P⦃≤ 1⦄[X Fin 1])) ∉ data.openingClaimRel 1 := by
  intro h
  have h0 := h 0
  apply claims_ne_zero 0
  simpa [PackingData.unpack] using h0

theorem error : bat.error = 2 / 25 := by
  have hc : Fintype.card F25 = 25 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 5 2 (by decide)]
    norm_num
  simp [bat, BatchingStrategy.gammaPowers, hc]

open Classical in
/-- The correct source remains listed, but only the incorrect zero polynomial is charged. -/
theorem filtered_card :
    (({source, 0} : Finset data.P⦃≤ 1⦄[X Fin 1]).filter fun p =>
      ((claims, r), data.unpack p) ∉ data.openingClaimRel 1).card = 1 := by
  rw [Finset.filter_insert, ite_eq_right (not_not_intro honest),
    Finset.filter_singleton, ite_eq_left zero_incorrect]
  rfl

open Classical in
theorem fixed_list_bound :
    Pr{let γ ← $ᵗ bat.Challenge}[∃ p ∈ ({source, 0} : Finset data.P⦃≤ 1⦄[X Fin 1]),
      ((claims, r), data.unpack p) ∉ data.openingClaimRel 1 ∧
      (data.derivedTarget claims (bat.weight γ), p) ∈
        data.sumcheckClaimRel 1 r (bat.weight γ)] ≤ 2 / 25 := by
  classical
  have h := data.pr_exists_derivedTarget_not_openingClaimRel_le_card_filter_mul bat
    (algebraMap F25 F25).injective r claims {source, 0}
  rw [filtered_card, Nat.cast_one, one_mul, error] at h
  simpa [ENNReal.coe_div] using h

/-- An incorrect zero source is rejected at some challenge against the same nonzero claims. -/
theorem exists_reject_zero :
    ∃ γ : bat.Challenge, (data.derivedTarget claims (bat.weight γ),
      (0 : data.P⦃≤ 1⦄[X Fin 1])) ∉ data.sumcheckClaimRel 1 r (bat.weight γ) := by
  by_contra h
  have hall : ∀ γ : bat.Challenge, (data.derivedTarget claims (bat.weight γ),
      (0 : data.P⦃≤ 1⦄[X Fin 1])) ∈ data.sumcheckClaimRel 1 r (bat.weight γ) := by
    simpa using h
  have hprob := (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr hall
  have hbound := data.pr_derivedTarget_of_not_openingClaimRel_le bat
    (algebraMap F25 F25).injective r claims 0 zero_incorrect
  rw [hprob, error] at hbound
  have hfinite : (1 : ℝ≥0) ≤ 2 / 25 := ENNReal.coe_le_coe.mp hbound
  exact (not_le_of_gt ((div_lt_one (by norm_num : (0 : ℝ≥0) < 25)).mpr
    (by norm_num : (2 : ℝ≥0) < 25))) hfinite

end RingSwitching.Packing.Tests.DerivedBatchingRanks

/--
info:
'RingSwitching.Packing.BatchingStrategy.separates_finset_le_card_filter_mul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.BatchingStrategy.separates_finset_le_card_filter_mul

/--
info:
'RingSwitching.Packing.PackingData.pr_exists_derivedTarget_not_openingClaimRel_le_card_filter_mul'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  RingSwitching.Packing.PackingData.pr_exists_derivedTarget_not_openingClaimRel_le_card_filter_mul

/--
info:
'RingSwitching.Packing.Tests.DerivedBatchingRanks.source_nonconstant'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.Tests.DerivedBatchingRanks.source_nonconstant

/--
info:
'RingSwitching.Packing.Tests.DerivedBatchingRanks.honest_preserved'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.Tests.DerivedBatchingRanks.honest_preserved

/--
info:
'RingSwitching.Packing.Tests.DerivedBatchingRanks.fixed_list_bound'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.Tests.DerivedBatchingRanks.fixed_list_bound

/--
info:
'RingSwitching.Packing.Tests.DerivedBatchingRanks.exists_reject_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.Tests.DerivedBatchingRanks.exists_reject_zero

end
