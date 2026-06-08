/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.Domain.CosetFftDomain.Mem
import ArkLib.Data.Domain.FftDomain.Defs
import ArkLib.ToMathlib.Finset.ToListWithProof

/-!
# Membership in FFT domains

This file develops membership lemmas for FFT domains and relates them to the
corresponding coset FFT domain constructions.

## Main results

- `FftDomainClass.one_mem`: The element `1` belongs to every FFT domain.
- `FftDomain.mem_iff_exists`: Membership via the subgroup parametrization.
- `FftDomain.mem_iff_mem_toCosetFftDomain`:
  Membership agrees with the associated coset FFT domain.
- `FftDomain.mem_toFinset_iff_mem`:
  Membership agrees with membership in the finset of elements.
-/

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace FftDomainClass

variable {D : Type} [FunLike D ι F] [FftDomainClass D ι F]
variable {ω : D}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The element `1` belongs to every FFT domain. -/
@[simp]
lemma one_mem : 1 ∈ ω := ⟨0, FftDomainClass.generator_eq_one ω⟩

end FftDomainClass

namespace FftDomain

open CosetFftDomain

variable {ω : FftDomain ι F} {x : F}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Membership in a concrete FFT domain means
  being one of the values of its subgroup parametrization. -/
lemma mem_iff_exists :
  x ∈ ω ↔ ∃ i, x = ω.subgroupDomain i := by
  aesop (add simp [Membership.mem])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Membership in an FFT domain is the same as
  membership in the same domain viewed as a coset FFT domain. -/
lemma mem_iff_mem_toCosetFftDomain :
  x ∈ ω ↔ x ∈ ω.toCosetFftDomain := by
  simp [mem_iff_exists, mem_iff_exists_mul, ω.cosetGenerator_one]

omit [DecidableEq ι] in
/-- Membership in the image finset of an FFT domain means
  being one of the values of its subgroup parametrization. -/
lemma mem_toFinset_iff_exists :
  x ∈ ω.toFinset ↔ ∃ i, x = ω.subgroupDomain i := by
  aesop
    (add simp
      [CosetFftDomainClass.mem_toFinset_iff_mem,
       CosetFftDomainClass.mem_def])

omit [DecidableEq ι] in
/-- Membership in the finset of elements is the same as membership in the FFT domain. -/
@[simp]
lemma mem_toFinset_iff_mem :
  x ∈ ω.toFinset ↔ x ∈ ω := by
  rw [CosetFftDomainClass.mem_toFinset_iff_mem,
      mem_iff_mem_toCosetFftDomain]

end FftDomain

/-- Membership in a concrete FFT domain is decidable
  via membership in the finset of its elements. -/
instance {x : F} {ω : FftDomain ι F} : Decidable (x ∈ ω) :=
  decidable_of_iff _ FftDomain.mem_toFinset_iff_mem

end Domain
