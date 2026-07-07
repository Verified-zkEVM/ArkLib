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

import ArkLib.Data.Domain.CosetFftDomain.Defs
import ArkLib.ToMathlib.Finset.ToListWithProof

/-!
# Membership in coset FFT domains

This file develops membership and `toFinset` constructions for coset FFT
domains.

## Main definitions

- `Membership F D`: Membership in a domain via evaluation.
- `CosetFftDomainClass.toFinset`: The finset of elements of a domain.
- `CosetFftDomain.toFinset`: The finset of elements of a concrete coset FFT domain.

## Main results

- `CosetFftDomainClass.mem_def`: Characterization of membership.
- `CosetFftDomainClass.not_zero_mem`: Zero does not belong to a coset FFT domain.
- `CosetFftDomain.mem_iff_exists_mul`: Membership as a coset-generator multiple.
- `CosetFftDomainClass.card_toFinset`: Cardinality of the image finset.

-/

namespace Domain

open Function

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- Membership in a class-level coset FFT domain means
  being equal to one of the values of its indexing function. -/
instance {D : Type}
  [FunLike D ι F] [CosetFftDomainClass D ι F] : Membership F D where
  mem ω x := ∃ i, ω i = x

/-- A class-level coset FFT domain coerces to the type associated to its finset of elements. -/
instance
    {ι : Type} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F] :
  CoeSort D Type where
    coe d := CosetFftDomainClass.toFinset d

namespace CosetFftDomainClass

variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F] {ω : D}
variable {x : F}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Unfold membership in a class-level coset FFT domain. -/
lemma mem_def : x ∈ ω ↔ ∃ i, ω i = x := by rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Every value of a coset FFT domain belongs to that domain. -/
@[simp high]
lemma mem_self {i : ι} :
  ω i ∈ ω := by simp [mem_def]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Membership is preserved by converting a class-level coset FFT domain
  to the concrete `CosetFftDomain` structure. -/
@[simp]
lemma mem_toCosetFftDomain_iff_mem :
  x ∈ toCosetFftDomain ω ↔ x ∈ ω := by
  aesop (add simp
          [mkSubgroupUnit,
            mem_def,
            toCosetFftDomain,
            CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])

omit [DecidableEq ι] in
/-- Membership in the finset of elements is the same as membership in the coset FFT domain. -/
@[simp]
lemma mem_toFinset_iff_mem :
  x ∈ toFinset ω ↔ x ∈ ω := by aesop (add simp [toFinset, mem_def])

omit [DecidableEq ι] in
/-- Every value of a coset FFT domain belongs to the set of its elements. -/
@[simp high]
lemma mem_toFinset_self {i : ι} :
  ω i ∈ toFinset ω := by simp

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Zero is not a member of a coset FFT domain. -/
@[simp]
lemma not_zero_mem :
  0 ∉ ω := fun contra ↦ by
  rw [mem_def] at contra
  obtain ⟨i, contra⟩ := contra
  exact CosetFftDomainClass.ne_zero ω i (by simp_all)

end CosetFftDomainClass

/-- The finset of elements of a concrete coset FFT domain is inhabited.

  There always exists `ω 0`.
-/
instance {ω : CosetFftDomain ι F} : Inhabited ω.toFinset where
  default := ⟨ω 0, by simp [CosetFftDomainClass.toFinset]⟩

/-- A concrete coset FFT domain coerced to `Type` is inhabited. -/
instance {ω : CosetFftDomain ι F} : Inhabited ω where
  default := ⟨ω 0, by simp [CosetFftDomainClass.toFinset]⟩

namespace CosetFftDomain

variable {ω : CosetFftDomain ι F} {x : F}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Membership in a concrete coset FFT domain means
  being a coset generator times some subgroup element. -/
lemma mem_iff_exists_mul :
  x ∈ ω ↔ ∃ i, x = ω.cosetGenerator * ω.subgroupDomain i := by
  aesop (add simp [Membership.mem])

omit [DecidableEq ι] in
/-- Membership in the finset of elements of a concrete coset FFT domain means
  being a coset generator times some subgroup element. -/
lemma mem_toFinset_iff_exists_mul :
  x ∈ ω.toFinset ↔ ∃ i, x = ω.cosetGenerator * ω.subgroupDomain i := by
  simp [mem_iff_exists_mul]

omit [DecidableEq ι] in
/-- Membership in the finset of elements is
  the same as membership in the concrete coset FFT domain. -/
@[simp]
lemma mem_toFinset_iff_mem :
  x ∈ ω.toFinset ↔ x ∈ ω := CosetFftDomainClass.mem_toFinset_iff_mem

omit [DecidableEq ι] in
/-- Every value of a concrete coset FFT domain belongs to its finset of elements. -/
@[simp high]
lemma mem_toFinset_self {i : ι} :
  ω i ∈ ω.toFinset := CosetFftDomainClass.mem_toFinset_self

end CosetFftDomain

/-- Membership in a concrete coset FFT domain is decidable
  via membership in its finset of elements. -/
instance {x : F} {ω : CosetFftDomain ι F} : Decidable (x ∈ ω) :=
  decidable_of_iff _ CosetFftDomain.mem_toFinset_iff_mem

end Domain
