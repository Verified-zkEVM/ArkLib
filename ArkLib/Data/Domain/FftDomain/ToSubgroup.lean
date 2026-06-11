/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.Domain.FftDomain.Mem

/-!
# FFT domains as subgroups

This file associates a multiplicative subgroup of `Fˣ` to an FFT domain.

## Main definitions

- `FftDomainClass.toSubgroup`: The subgroup represented by an FFT domain.
- `FftDomain.toSubgroup`: Concrete version of the construction.

## Main results

- `mem_subgroup_iff_mem_finset`:
  Membership in the subgroup is equivalent to membership in the finset of elements.
- `mem_subgroup_iff_mem_domain`:
  Membership in the subgroup is equivalent to membership in the FFT domain.

-/

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace FftDomainClass

variable {D : Type} [FunLike D ι F] [FftDomainClass D ι F]
variable {ω : D} {i j : ι}

/-- The multiplicative subgroup of `Fˣ` represented by an FFT domain.
  This subgroup consists exactly of the normalized subgroup units
  arising from the domain parametrization.
  Since FFT domains satisfy `ω 0 = 1`, these units coincide with the values of the domain itself. -/
def toSubgroup (ω : D) : Subgroup Fˣ where
  carrier := Finset.image (CosetFftDomainClass.mkSubgroupUnit ω) Finset.univ
  mul_mem' {a b} ha hb := by {
    simp_all only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    rcases ha, hb with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
    exists (x + y)
    ext
    simp [CosetFftDomainClass.mkSubgroupUnit,
          CosetFftDomainClass.map_add,
          FftDomainClass.generator_eq_one]
  }
  one_mem' := by {
    simp only [Finset.coe_image, CosetFftDomainClass.mkSubgroupUnit]
    exists 0
    aesop
  }
  inv_mem' {x} hx := by {
    simp_all only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    obtain ⟨a, rfl⟩ := hx
    exists (-a)
    aesop (add simp [CosetFftDomainClass.mkSubgroupUnit,
                      CosetFftDomainClass.map_neg, generator_eq_one])
  }

/-- A unit belongs to the subgroup associated to an FFT domain iff
  its value belongs to the finset of elements of the domain. -/
lemma mem_subgroup_iff_mem_finset {x : Fˣ} :
  x ∈ toSubgroup ω ↔ x.val ∈ CosetFftDomainClass.toFinset ω := by
  aesop
    (add simp [toSubgroup, CosetFftDomainClass.toFinset,
                CosetFftDomainClass.mkSubgroupUnit, generator_eq_one])

/-- A unit belongs to the subgroup associated to an FFT domain iff
  its value belongs to the FFT domain. -/
@[simp]
lemma mem_subgroup_iff_mem_domain {ω : D} {x : Fˣ} :
  x ∈ toSubgroup ω ↔ x.val ∈ ω := by simp [mem_subgroup_iff_mem_finset]

end FftDomainClass

namespace FftDomain

variable {ι : Type} [Fintype ι] [AddCommGroup ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- The subgroup of units associated to a concrete FFT domain. -/
abbrev toSubgroup (ω : FftDomain ι F) : Subgroup Fˣ := FftDomainClass.toSubgroup ω

end FftDomain

end Domain
