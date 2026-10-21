/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.DerivedBatching
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# Public derived-slice batching controls

Over `ZMod 5`, a rank-one packing algebra and rank-two opening algebra retain one nonconstant
variable. Two incorrect packed candidates collide at exactly the challenges `1,2`, attaining
`2/5`. A correct zero candidate is excluded; a postchallenge affine candidate always survives.
A separate coordinate-projection example shows why coefficient transport must be injective.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.DerivedBatching

open RingSwitching.Packing Module MvPolynomial ProbabilityTheory
open scoped NNReal ENNReal

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev data : PackingData (ZMod 5) where
  P := ZMod 5
  E := Fin 2 → ZMod 5
  ιP := Unit
  ιE := Fin 2
  packBasis := Basis.singleton Unit _
  openBasis := Pi.basisFun _ _

def r : Fin 1 → data.E := fun _ => ![0, 1]

def affine (a b : ZMod 5) : data.P⦃≤ 1⦄[X Fin 1] :=
  ⟨MLE (fun y => a + b * (y 0 : ZMod 5)), MLE_mem_restrictDegree _⟩

private theorem sum_one_bit {M : Type*} [AddCommMonoid M]
    (f : (Fin 1 → Fin 2) → M) :
    ∑ x, f x = f (fun _ => 0) + f (fun _ => 1) := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp f]
  simp only [Fin.sum_univ_two]
  apply congrArg₂ (· + ·) <;> apply congrArg f <;> funext i <;> fin_cases i <;> rfl

theorem actualSlices_affine (a b : ZMod 5) :
    data.actualSlices r (affine a b) = ![a, a + b] := by
  ext u
  fin_cases u <;>
    simp [PackingData.actualSlices, PackingData.coordinateSlices, data,
      Pi.basisFun_repr, sum_one_bit, affine, MLE_eval_zeroOne, eqTilde_eq_prod, r,
      Matrix.vecHead, Matrix.vecTail]

abbrev linear := BatchingStrategy.gammaPowers (ZMod 5) 2

theorem affine_success (a b γ : ZMod 5) :
    (data.derivedTarget 0 (linear.weight γ), affine a b) ∈
      data.sumcheckClaimRel 1 r (linear.weight γ) ↔ a + γ * (a + b) = 0 := by
  rw [data.sumcheckClaimRel_iff_actualSlices, actualSlices_affine]
  simp [PackingData.derivedTarget, linear, BatchingStrategy.gammaPowers,
    Fin.sum_univ_two, eq_comm]

theorem affine_incorrect_of_sum_one (a b : ZMod 5) (hab : a + b = 1) :
    ((0, r), data.unpack (affine a b)) ∉ data.openingClaimRel 1 := by
  intro h
  have he := (data.openingClaimRel_iff_transpose_actualSlices r 0 (affine a b)).mp h
  rw [map_zero, actualSlices_affine] at he
  have hz := congrFun he 1
  change (0 : ZMod 5) = a + b at hz
  rw [hab] at hz
  exact zero_ne_one hz

abbrev q1 := affine (-1) 2
abbrev q2 := affine (-2) 3

theorem q1_incorrect : ((0, r), data.unpack q1) ∉ data.openingClaimRel 1 :=
  affine_incorrect_of_sum_one _ _ (by decide)

theorem q2_incorrect : ((0, r), data.unpack q2) ∉ data.openingClaimRel 1 :=
  affine_incorrect_of_sum_one _ _ (by decide)

theorem q1_success (γ : ZMod 5) :
    (data.derivedTarget 0 (linear.weight γ), q1) ∈ data.sumcheckClaimRel 1 r (linear.weight γ) ↔
      γ = 1 := by
  rw [affine_success]
  constructor <;> intro h <;> linear_combination h

theorem q2_success (γ : ZMod 5) :
    (data.derivedTarget 0 (linear.weight γ), q2) ∈ data.sumcheckClaimRel 1 r (linear.weight γ) ↔
      γ = 2 := by
  rw [affine_success]
  constructor <;> intro h <;> linear_combination h

/-- The nonconstant source `-1 + 2X` has nonzero honest component values `(-1,1)`. -/
def honestClaims : data.ιP → data.E := fun _ => ![-1, 1]

/-- The actual original opening relation holds for this nonzero family and packed source. -/
theorem honest_opening : ((honestClaims, r), data.unpack q1) ∈ data.openingClaimRel 1 := by
  rw [data.openingClaimRel_iff_transpose_actualSlices, actualSlices_affine]
  ext u
  rw [data.transpose_apply]
  fin_cases u <;>
    norm_num [data, honestClaims, Basis.singleton_repr, Pi.basisFun_repr] <;>
    exact Pi.basisFun_repr (R := ZMod 5) (η := Fin 2) _ _

/-- Honest preservation applies to the same nonconstant packed polynomial at every challenge. -/
theorem nonzero_honest_preserved (γ : ZMod 5) :
    (data.derivedTarget honestClaims (linear.weight γ), q1) ∈
      data.sumcheckClaimRel 1 r (linear.weight γ) :=
  data.sumcheckClaimRel_derivedTarget_of_openingClaimRel _ _ _ _ honest_opening

theorem fixed_two_event (γ : ZMod 5) :
    (∃ p ∈ ({q1, q2} : Finset data.P⦃≤ 1⦄[X Fin 1]),
      ((0, r), data.unpack p) ∉ data.openingClaimRel 1 ∧
      (data.derivedTarget 0 (linear.weight γ), p) ∈ data.sumcheckClaimRel 1 r (linear.weight γ)) ↔
      γ = 1 ∨ γ = 2 := by
  classical
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨p, rfl | rfl, _, h⟩
    · exact Or.inl ((q1_success γ).mp h)
    · exact Or.inr ((q2_success γ).mp h)
  · rintro (h | h)
    · exact ⟨q1, Or.inl rfl, q1_incorrect, (q1_success γ).mpr h⟩
    · exact ⟨q2, Or.inr rfl, q2_incorrect, (q2_success γ).mpr h⟩

theorem fixed_two_probability :
    Pr{let γ ← $ᵗ (ZMod 5)}[
      ∃ p ∈ ({q1, q2} : Finset data.P⦃≤ 1⦄[X Fin 1]),
        ((0, r), data.unpack p) ∉ data.openingClaimRel 1 ∧
        (data.derivedTarget 0 (linear.weight γ), p) ∈ data.sumcheckClaimRel 1 r (linear.weight γ)] =
      2 / 5 := by
  rw [prEvent_congr _ _ _ fixed_two_event]
  rw [SampleableType.prEvent_uniformSample]
  have hc : (Finset.univ.filter fun γ : ZMod 5 => γ = 1 ∨ γ = 2).card = 2 := by decide
  rw [hc]
  norm_num

theorem fixed_two_bound :
    Pr{let γ ← $ᵗ (ZMod 5)}[
      ∃ p ∈ ({q1, q2} : Finset data.P⦃≤ 1⦄[X Fin 1]),
        ((0, r), data.unpack p) ∉ data.openingClaimRel 1 ∧
        (data.derivedTarget 0 (linear.weight γ), p) ∈ data.sumcheckClaimRel 1 r (linear.weight γ)] ≤
      2 * (linear.error : ℝ≥0∞) := by
  classical
  exact data.pr_exists_derivedTarget_not_openingClaimRel_le linear (fun _ _ h => h) r 0
    {q1, q2} ((Finset.card_insert_le _ _).trans (by simp))

theorem fixed_two_tight :
    Pr{let γ ← $ᵗ (ZMod 5)}[
      ∃ p ∈ ({q1, q2} : Finset data.P⦃≤ 1⦄[X Fin 1]),
        ((0, r), data.unpack p) ∉ data.openingClaimRel 1 ∧
        (data.derivedTarget 0 (linear.weight γ), p) ∈ data.sumcheckClaimRel 1 r (linear.weight γ)] =
      2 * (linear.error : ℝ≥0∞) := by
  rw [fixed_two_probability]
  norm_num [linear, BatchingStrategy.gammaPowers, div_eq_mul_inv]

theorem zero_correct :
    ((0, r), data.unpack (0 : data.P⦃≤ 1⦄[X Fin 1])) ∈ data.openingClaimRel 1 := by
  intro i
  simp [PackingData.unpack]

theorem zero_success (γ : ZMod 5) :
    (data.derivedTarget 0 (linear.weight γ), (0 : data.P⦃≤ 1⦄[X Fin 1])) ∈
      data.sumcheckClaimRel 1 r (linear.weight γ) :=
  data.sumcheckClaimRel_derivedTarget_of_openingClaimRel _ _ _ _ zero_correct

theorem fixed_three_event (γ : ZMod 5) :
    (∃ p ∈ ({0, q1, q2} : Finset data.P⦃≤ 1⦄[X Fin 1]),
      ((0, r), data.unpack p) ∉ data.openingClaimRel 1 ∧
      (data.derivedTarget 0 (linear.weight γ), p) ∈ data.sumcheckClaimRel 1 r (linear.weight γ)) ↔
      γ = 1 ∨ γ = 2 := by
  classical
  constructor
  · rintro ⟨p, hp, hbad, hc⟩
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact False.elim (hbad zero_correct)
    · exact (fixed_two_event γ).mp ⟨p, hp, hbad, hc⟩
  · intro h
    obtain ⟨p, hp, hbad, hc⟩ := (fixed_two_event γ).mpr h
    exact ⟨p, Finset.mem_insert_of_mem hp, hbad, hc⟩

theorem correct_candidate_excluded_probability :
    Pr{let γ ← $ᵗ (ZMod 5)}[
      ∃ p ∈ ({0, q1, q2} : Finset data.P⦃≤ 1⦄[X Fin 1]),
        ((0, r), data.unpack p) ∉ data.openingClaimRel 1 ∧
        (data.derivedTarget 0 (linear.weight γ), p) ∈ data.sumcheckClaimRel 1 r (linear.weight γ)] =
      2 / 5 := by
  rw [prEvent_congr _ _ _ fixed_three_event]
  rw [SampleableType.prEvent_uniformSample]
  have hc : (Finset.univ.filter fun γ : ZMod 5 => γ = 1 ∨ γ = 2).card = 2 := by decide
  rw [hc]
  norm_num

theorem including_correct_candidate_probability :
    Pr{let γ ← $ᵗ (ZMod 5)}[
      ∃ p ∈ ({0, q1, q2} : Finset data.P⦃≤ 1⦄[X Fin 1]),
        (data.derivedTarget 0 (linear.weight γ), p) ∈ data.sumcheckClaimRel 1 r (linear.weight γ)] =
      1 := by
  classical
  apply (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr
  intro γ
  exact ⟨0, Finset.mem_insert_self _ _, zero_success γ⟩

def adaptive (γ : ZMod 5) := affine (-γ) (1 + γ)

theorem adaptive_incorrect (γ : ZMod 5) :
    ((0, r), data.unpack (adaptive γ)) ∉ data.openingClaimRel 1 := by
  apply affine_incorrect_of_sum_one
  ring

theorem adaptive_success (γ : ZMod 5) :
    (data.derivedTarget 0 (linear.weight γ), adaptive γ) ∈
      data.sumcheckClaimRel 1 r (linear.weight γ) := by
  rw [adaptive, affine_success]
  ring

theorem adaptive_probability :
    Pr{let γ ← $ᵗ (ZMod 5)}[
      ((0, r), data.unpack (adaptive γ)) ∉ data.openingClaimRel 1 ∧
        (data.derivedTarget 0 (linear.weight γ), adaptive γ) ∈
          data.sumcheckClaimRel 1 r (linear.weight γ)] =
      1 :=
  (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun γ =>
    ⟨adaptive_incorrect γ, adaptive_success γ⟩

end RingSwitching.Packing.Tests.DerivedBatching

namespace RingSwitching.Packing.Tests.DerivedBatchingNoninjective

open RingSwitching.Packing Module MvPolynomial ProbabilityTheory
open scoped NNReal ENNReal

abbrev data : PackingData (ZMod 5) where
  P := Fin 2 → ZMod 5
  E := ZMod 5
  ιP := Fin 2
  ιE := Unit
  packBasis := Pi.basisFun _ _
  openBasis := Basis.singleton Unit _

local instance : Algebra data.P (ZMod 5) :=
  (Pi.evalRingHom (fun _ : Fin 2 => ZMod 5) 0).toAlgebra

local instance : IsScalarTower (ZMod 5) data.P (ZMod 5) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def α : data.ιP → data.E := ![0, 1]
def r : Fin 1 → data.E := 0

theorem coefficient_transport_not_injective :
    ¬ Function.Injective (algebraMap data.P (ZMod 5)) := by
  intro h
  have he := h (a₁ := ![0, 0]) (a₂ := ![0, 1]) rfl
  have h1 : (0 : ZMod 5) = 1 := congrFun he 1
  exact (by decide : (0 : ZMod 5) ≠ 1) h1

theorem incorrect :
    ((α, r), data.unpack (0 : data.P⦃≤ 1⦄[X Fin 1])) ∉ data.openingClaimRel 1 := by
  intro h
  have h1 := h 1
  have hz : (1 : ZMod 5) = 0 := by simpa [α, PackingData.unpack] using h1
  exact (by decide : (1 : ZMod 5) ≠ 0) hz

theorem derivedTarget_zero (weight : data.ιE → ZMod 5) :
    data.derivedTarget α weight = 0 := by
  have hT : data.transpose α () = ![0, 1] := by
    rw [data.transpose_apply]
    ext j
    fin_cases j <;>
      simp [data, α, Basis.singleton_repr, Pi.single_apply]
  unfold PackingData.derivedTarget
  rw [Fintype.sum_unique, hT]
  change weight () * (0 : ZMod 5) = 0
  exact mul_zero _

theorem passes (weight : data.ιE → ZMod 5) :
    (data.derivedTarget α weight, (0 : data.P⦃≤ 1⦄[X Fin 1])) ∈
      data.sumcheckClaimRel 1 r weight := by
  rw [derivedTarget_zero]
  simp [PackingData.sumcheckClaimRel]

abbrev bat := BatchingStrategy.singleton (ZMod 5) Unit

theorem zero_error : bat.error = 0 := rfl

theorem collision_certain :
    Pr{let c ← $ᵗ bat.Challenge}[
      ((α, r), data.unpack (0 : data.P⦃≤ 1⦄[X Fin 1])) ∉ data.openingClaimRel 1 ∧
        (data.derivedTarget α (bat.weight c), (0 : data.P⦃≤ 1⦄[X Fin 1])) ∈
          data.sumcheckClaimRel 1 r (bat.weight c)] = 1 :=
  (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun _ => ⟨incorrect, passes _⟩

end RingSwitching.Packing.Tests.DerivedBatchingNoninjective

/--
info: 'RingSwitching.Packing.PackingData.openingClaimRel_iff_transpose_actualSlices'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.PackingData.openingClaimRel_iff_transpose_actualSlices

/--
info: 'RingSwitching.Packing.PackingData.sumcheckClaimRel_derivedTarget_of_openingClaimRel'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.PackingData.sumcheckClaimRel_derivedTarget_of_openingClaimRel

/--
info: 'RingSwitching.Packing.PackingData.pr_derivedTarget_of_not_openingClaimRel_le'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.PackingData.pr_derivedTarget_of_not_openingClaimRel_le

/--
info: 'RingSwitching.Packing.PackingData.pr_exists_derivedTarget_not_openingClaimRel_le'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.PackingData.pr_exists_derivedTarget_not_openingClaimRel_le

/--
info: 'RingSwitching.Packing.Tests.DerivedBatching.fixed_two_tight'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.Tests.DerivedBatching.fixed_two_tight

/--
info: 'RingSwitching.Packing.Tests.DerivedBatching.correct_candidate_excluded_probability'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.Tests.DerivedBatching.correct_candidate_excluded_probability

/--
info: 'RingSwitching.Packing.Tests.DerivedBatching.including_correct_candidate_probability'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.Tests.DerivedBatching.including_correct_candidate_probability

/--
info: 'RingSwitching.Packing.Tests.DerivedBatching.adaptive_probability'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.Tests.DerivedBatching.adaptive_probability

/--
info: 'RingSwitching.Packing.Tests.DerivedBatchingNoninjective.collision_certain'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.Tests.DerivedBatchingNoninjective.collision_certain

end
