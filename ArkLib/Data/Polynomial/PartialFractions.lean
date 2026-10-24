/-
Copyright (c) 2026 Thomas Coratger, ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger, ArkLib Contributors
-/
module

public import ArkLib.Data.Finset.SumFiber
public import ArkLib.Data.Fraction
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Finite partial fractions and denominator clearing

Finite weighted occurrences determine a rational sum, a common polynomial denominator, and a
cleared numerator. Repeated values are permitted: vanishing means that the total weight at each
value is zero. Neither the field nor the occurrence type needs to be finite.

The polynomial and rational-function definitions are mathematical views. Mathlib's polynomial
coefficient operations use a classical finite-support representation, and its rational functions
use a noncomputable fraction-field representation. These views are individually marked
`noncomputable`; executable fraction arithmetic is provided by `FractionPair` in
`ArkLib.Data.Fraction`. The agreement theorems identify its folded polynomial pair with the
cleared numerator and common denominator, and remain valid when evaluated at a pole.

The distinct-pole argument adapts the denominator-clearing proof by Thomas Coratger.
-/

@[expose] public section

open Finset Polynomial

namespace PartialFractions

variable {ι F : Type*} [Field F]

local notation "ιₚ" => algebraMap F[X] (RatFunc F)

/-- The sum of weighted reciprocals indexed by a finite set of occurrences. -/
noncomputable def reciprocalSum (s : Finset ι) (value weight : ι → F) : RatFunc F :=
  ∑ i ∈ s, ιₚ (C (weight i)) / ιₚ (X - C (value i))

/-- The product of the symbolic linear denominators, retaining repeated values. -/
noncomputable def commonDenominator (s : Finset ι) (value : ι → F) : F[X] :=
  ∏ i ∈ s, (X - C (value i))

/-- The numerator obtained by multiplying each summand by the other denominators. -/
noncomputable def clearedNumerator [DecidableEq ι] (s : Finset ι)
    (value weight : ι → F) : F[X] :=
  ∑ i ∈ s, C (weight i) * ∏ j ∈ s.erase i, (X - C (value j))

/-- Symbolic denominators are nonzero, even when some occurrence values coincide. -/
theorem commonDenominator_ne_zero (s : Finset ι) (value : ι → F) :
    commonDenominator s value ≠ 0 := by
  exact prod_ne_zero_iff.mpr fun i _ ↦ X_sub_C_ne_zero (value i)

/-- Clearing the nonzero symbolic denominators gives the polynomial numerator. -/
theorem map_clearedNumerator [DecidableEq ι] (s : Finset ι) (value weight : ι → F) :
    ιₚ (clearedNumerator s value weight) =
      reciprocalSum s value weight * ιₚ (commonDenominator s value) := by
  simp only [clearedNumerator, reciprocalSum, commonDenominator, map_sum, map_mul,
    map_prod, sum_mul]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [← prod_erase_mul s _ hi]
  have hne : ιₚ (X - C (value i)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2
      (X_sub_C_ne_zero (value i))
  field_simp

/-- A rational sum with distinct poles vanishes exactly when all its weights vanish. -/
theorem sum_div_X_sub_C_eq_zero_iff (s : Finset F) (weight : F → F) :
    (∑ v ∈ s, ιₚ (C (weight v)) / ιₚ (X - C v)) = 0 ↔
      ∀ v ∈ s, weight v = 0 := by
  classical
  refine ⟨fun h v₀ hv₀ ↦ ?_, fun h ↦ sum_eq_zero fun v hv ↦ by simp [h v hv]⟩
  have hP : clearedNumerator s id weight = 0 := by
    apply IsFractionRing.injective F[X] (RatFunc F)
    rw [map_clearedNumerator]
    change (∑ v ∈ s, ιₚ (C (weight v)) / ιₚ (X - C v)) * _ = ιₚ 0
    rw [h, zero_mul, map_zero]
  have heval := congrArg (eval v₀) hP
  rw [clearedNumerator, eval_finsetSum,
    sum_eq_single_of_mem v₀ hv₀ fun v _ hvne ↦ by
      rw [eval_mul, eval_prod,
        prod_eq_zero (mem_erase.mpr ⟨Ne.symm hvne, hv₀⟩) (by simp), mul_zero],
    eval_mul, eval_C, eval_prod, eval_zero] at heval
  refine (mul_eq_zero.mp heval).resolve_right ?_
  rw [prod_eq_zero_iff]
  rintro ⟨v, hv, hzero⟩
  simp only [id_eq, eval_sub, eval_X, eval_C, sub_eq_zero] at hzero
  exact (mem_erase.mp hv).1 hzero.symm

/-- Regrouping a rational sum collects all occurrences carrying the same value. -/
theorem reciprocalSum_eq_sum_fibers [DecidableEq F] (s : Finset ι)
    (value weight : ι → F) (keys : Finset F) (hkeys : ∀ i ∈ s, value i ∈ keys) :
    reciprocalSum s value weight =
      ∑ v ∈ keys, ιₚ (C (s.sumFiber value weight v)) / ιₚ (X - C v) := by
  let term : F → F →+ RatFunc F := fun v ↦
    { toFun := fun w ↦ ιₚ (C w) / ιₚ (X - C v)
      map_zero' := by simp
      map_add' := fun a b ↦ by simp [add_div] }
  change (∑ i ∈ s, term (value i) (weight i)) =
    ∑ v ∈ keys, term v (s.sumFiber value weight v)
  rw [← s.sum_sumFiber keys value (fun i ↦ term (value i) (weight i)) hkeys]
  apply sum_congr rfl
  intro v _
  rw [← s.sumFiber_map (term v) value weight v]
  unfold sumFiber
  apply sum_congr rfl
  intro i hi
  change term (value i) (weight i) = term v (weight i)
  rw [(mem_filter.mp hi).2]

/-- A rational sum vanishes exactly when each value has total weight zero. -/
theorem reciprocalSum_eq_zero_iff [DecidableEq F] (s : Finset ι) (value weight : ι → F) :
    reciprocalSum s value weight = 0 ↔ ∀ v, s.sumFiber value weight v = 0 := by
  classical
  rw [reciprocalSum_eq_sum_fibers s value weight (s.image value)
      (fun i hi ↦ mem_image_of_mem value hi), sum_div_X_sub_C_eq_zero_iff]
  refine ⟨fun h v ↦ ?_, fun h v _ ↦ h v⟩
  by_cases hv : v ∈ s.image value
  · exact h v hv
  · exact s.sumFiber_eq_zero_of_forall_ne value weight v fun i hi hvi ↦
      hv (hvi ▸ mem_image_of_mem value hi)

/-- The cleared numerator vanishes exactly when every value has total weight zero. -/
theorem clearedNumerator_eq_zero_iff [DecidableEq ι] [DecidableEq F]
    (s : Finset ι) (value weight : ι → F) :
    clearedNumerator s value weight = 0 ↔ ∀ v, s.sumFiber value weight v = 0 := by
  rw [← reciprocalSum_eq_zero_iff]
  have hinj := IsFractionRing.injective F[X] (RatFunc F)
  have hden : ιₚ (commonDenominator s value) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (commonDenominator_ne_zero s value)
  rw [← map_eq_zero_iff _ hinj, map_clearedNumerator, mul_eq_zero]
  simp [hden]

/-- Clearing a sum over `s` produces degree at most one less than its occurrence count. -/
theorem natDegree_clearedNumerator_le [DecidableEq ι] (s : Finset ι)
    (value weight : ι → F) :
    (clearedNumerator s value weight).natDegree ≤ s.card - 1 := by
  unfold clearedNumerator
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply (natDegree_mul_le).trans
  simp only [natDegree_C, zero_add]
  apply (natDegree_prod_le _ _).trans
  simp [card_erase_of_mem hi]

/-- Folding symbolic weighted fractions produces the denominator-cleared polynomial pair. -/
theorem fold_eq_clearedFraction [DecidableEq ι] (s : Finset ι) (value weight : ι → F) :
    FractionPair.sum (s.toList.map fun i ↦
      (⟨C (weight i), X - C (value i)⟩ : FractionPair F[X])) =
        ⟨clearedNumerator s value weight, commonDenominator s value⟩ := by
  classical
  let ps : List (FractionPair F[X]) := s.toList.map fun i ↦
    ⟨C (weight i), X - C (value i)⟩
  have hd : (FractionPair.sum ps).denominator = commonDenominator s value := by
    simp [ps, FractionPair.sum_denominator, commonDenominator, List.map_map]
  have hnonzero : ∀ p ∈ ps.map (FractionPair.map ιₚ), p.denominator ≠ 0 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
    exact (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2
      (X_sub_C_ne_zero (value i))
  have hrecip : FractionPair.value (FractionPair.map ιₚ (FractionPair.sum ps)) =
      reciprocalSum s value weight := by
    rw [FractionPair.map_sum, FractionPair.value_sum _ hnonzero]
    simp [ps, FractionPair.map, FractionPair.value, reciprocalSum, List.map_map, Function.comp_def]
  have hden : ιₚ (FractionPair.sum ps).denominator ≠ 0 := by
    rw [hd]
    exact (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2
      (commonDenominator_ne_zero s value)
  change ιₚ (FractionPair.sum ps).numerator / ιₚ (FractionPair.sum ps).denominator =
    reciprocalSum s value weight at hrecip
  have hn := (div_eq_iff hden).mp hrecip
  rw [hd] at hn
  apply FractionPair.ext
  · apply IsFractionRing.injective F[X] (RatFunc F)
    rw [map_clearedNumerator]
    exact hn
  · exact hd

/-- The scalar fraction fold computes the cleared numerator at every point, including poles. -/
theorem eval_clearedNumerator_eq_fold_numerator [DecidableEq ι] (s : Finset ι)
    (value weight : ι → F) (alpha : F) :
    eval alpha (clearedNumerator s value weight) =
      (FractionPair.sum (s.toList.map fun i ↦
        (⟨weight i, alpha - value i⟩ : FractionPair F))).numerator := by
  have h := congrArg (FractionPair.map (evalRingHom alpha))
    (fold_eq_clearedFraction s value weight)
  rw [FractionPair.map_sum] at h
  have hn := congrArg FractionPair.numerator h
  simpa [FractionPair.map, List.map_map, Function.comp_def] using hn.symm


end PartialFractions
