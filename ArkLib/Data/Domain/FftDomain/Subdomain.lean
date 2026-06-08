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

import ArkLib.Data.Domain.CosetFftDomain.Subdomain
import ArkLib.Data.Domain.FftDomain.Ops
import ArkLib.Data.Domain.FftDomain.ToSubgroup

/-!
# Subdomains of smooth FFT domains

This file develops the subdomain tower for smooth FFT domains and relates it to
the corresponding construction for coset FFT domains.

## Main definitions

- `FftDomainClass.subdomain`: The `i`th FFT subdomain.
- `FftDomain.subdomain`: Concrete notation for FFT subdomains.

## Main results

- `mem_fft_subdomain_iff_mem_coset_subdomain`:
  FFT and coset subdomains have the same underlying elements.
- `mem_subdomain_of_mem_subdomain_of_le`:
  Membership descends along the subdomain tower.
- `subdomain_toFinset_subset_subdomain_toFinset_of_le`:
  Inclusion of image finsets.
- `subdomain_toSubgroup_subset_subdomain_toSubgroup_of_le`:
  Inclusion of associated subgroups.
- `subdomain_toFftDomain_comm`:
  Taking subdomains commutes with normalization.

-/

namespace Domain

variable {F : Type} [Field F]

namespace FftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [FftDomainClass D (Fin (2 ^ n)) F]
variable {ω : D} {x : F}

open CosetFftDomainClass

/-- The `i`th subdomain of a smooth FFT domain,
  obtained by taking the corresponding coset subdomain and normalizing it back to an FFT domain. -/
def subdomain (ω : D) (i : ℕ) : SmoothFftDomain (n - i) F :=
  (CosetFftDomainClass.subdomain ω i).toFftDomain

/-- Membership in an FFT subdomain is the same as membership in
  the corresponding coset subdomain. -/
lemma mem_fft_subdomain_iff_mem_coset_subdomain {i : ℕ} :
  x ∈ subdomain ω i ↔ x ∈ CosetFftDomainClass.subdomain ω i := by
  simp [subdomain, mem_toFftDomain_iff_mul_mem, CosetFftDomain.map_0_eq_coset_generator]

/-- If `x` is a member of `subdomain ω i` it is a member of
  any `subdomain ω j` with `j ≤ i`. -/
lemma mem_subdomain_of_mem_subdomain_of_le {i j : ℕ} (h : x ∈ subdomain ω i) (hji : j ≤ i) :
  x ∈ subdomain ω j := by
  aesop
    (add simp [mem_fft_subdomain_iff_mem_coset_subdomain])
    (add unsafe forward [mem_subdomain_of_le_of_mem_subdomain])

/-- If `j ≤ i`, then the finset of elements of the `i`th FFT subdomain is
  contained in the finset of elements of the `j`th FFT subdomain. -/
lemma subdomain_toFinset_subset_subdomain_toFinset_of_le [DecidableEq F]
  {i j : ℕ} (hji : j ≤ i) :
  (subdomain ω i).toFinset ⊆ (subdomain ω j).toFinset := fun x hx ↦ by
  aesop (add unsafe [mem_subdomain_of_mem_subdomain_of_le])

/-- If `j ≤ i`, then the subgroup associated to the `i`th FFT subdomain is
  contained in the subgroup associated to the `j`th FFT subdomain. -/
lemma subdomain_toSubgroup_subset_subdomain_toSubgroup_of_le [DecidableEq F]
  {i j : ℕ} (hji : j ≤ i) :
  (subdomain ω i).toSubgroup ≤ (subdomain ω j).toSubgroup := fun x hx ↦ by
  aesop (add unsafe [mem_subdomain_of_mem_subdomain_of_le])

end FftDomainClass

namespace CosetFftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [CosetFftDomainClass D (Fin (2 ^ n)) F]
variable {ω : D}

/-- Normalizing the `i`th coset subdomain agrees with
  taking the `i`th FFT subdomain of the normalized domain. -/
lemma subdomain_toFftDomain_comm {i : ℕ} :
  (subdomain ω i).toFftDomain = FftDomainClass.subdomain (toFftDomain ω) i := by
  ext u
  rw [eval_toFftDomain]
  conv_rhs =>
    simp [FftDomainClass.subdomain]
  rw [eval_toFftDomain]
  conv_rhs =>
    rw [CosetFftDomain.map_0_eq_coset_generator]
  rw [subdomain_generator_pow_generator]
  simp only [FftDomainClass.apply_zero_eq_one, one_pow, inv_one, one_mul]
  conv_rhs =>
    simp [subdomain]
    rw [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain]
    simp [CosetFftDomainClass.subdomain_embed, mkSubgroupUnit]
  by_cases h : n ≤ i
  · obtain ⟨u, hu⟩ := u
    have : n - i = 0 := by omega
    simp [this] at hu
    aesop
  · simp only [h, ↓reduceDIte]
    rw [CosetFftDomainClass.eval_toFftDomain]
    conv_lhs =>
      rhs
      simp only [
        subdomain, mkSubgroupUnit,
        CosetFftDomainClass.subdomain_embed,
        ge_iff_le, inv_pow,
        CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
        h, ↓reduceDIte, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [CosetFftDomain.map_0_eq_coset_generator,
        CosetFftDomainClass.subdomain_generator_pow_generator]
    simp

/-- Multiplying an element of a coset subdomain by an element of
  a deeper FFT subdomain of the normalized domain stays in the original coset subdomain. -/
lemma mem_subdomain_of_mem_subdomain_of_mem_fft_subdomain
  {i j : ℕ} (hji : j ≤ i)
  {a b : F}
  (ha : a ∈ subdomain ω j)
  (hb : b ∈ FftDomainClass.subdomain (toFftDomain ω) i) :
  a * b ∈ subdomain ω j := by
  aesop
    (add simp [subdomain_toFftDomain_comm])
    (add unsafe [FftDomainClass.mem_subdomain_of_mem_subdomain_of_le,
                  mul_mem_of_mem_of_mem_toFftDomain])

/-- Multiplying an element of a deeper FFT subdomain of the normalized domain by
  an element of a coset subdomain stays in the coset subdomain. -/
lemma mem_subdomain_of_mem_fft_subdomain_of_mem_subdomain
  {i j : ℕ} (hji : j ≤ i)
  {a b : F}
  (ha : a ∈ FftDomainClass.subdomain (toFftDomain ω) i)
  (hb : b ∈ subdomain ω j) :
  a * b ∈ subdomain ω j := by
  rw [mul_comm]
  exact mem_subdomain_of_mem_subdomain_of_mem_fft_subdomain hji hb ha

end CosetFftDomainClass

namespace FftDomain

/-- Concrete notation for the `i`th subdomain of a smooth FFT domain. -/
abbrev subdomain {n : ℕ} (ω : SmoothFftDomain n F) (i : ℕ) : SmoothFftDomain (n - i) F :=
  FftDomainClass.subdomain ω i

end FftDomain

end Domain
