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

import ArkLib.Data.Domain.CosetFftDomain.Mem
import ArkLib.Data.Domain.FftDomain.Mem

/-!
# Normalization of coset FFT domains

This file constructs an FFT domain from a coset FFT domain by dividing out the
coset generator.

## Main definitions

- `CosetFftDomainClass.toFftDomain`: Normalization of a coset FFT domain.
- `CosetFftDomain.toFftDomain`: Concrete version of the construction.

## Main results

- `CosetFftDomainClass.eval_toFftDomain`:
  Explicit evaluation formula for the normalized domain.
- `CosetFftDomainClass.mem_toFftDomain_iff_mul_mem`:
  Membership correspondence between a domain and its normalization.
- `FftDomain.toFftDomain_eq_self`:
  Normalization is the identity on FFT domains.

-/

namespace Domain

variable {ι : Type} [AddCommGroup ι]
variable {F : Type} [Field F]

namespace CosetFftDomainClass

variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]

/-- Normalize a class-level coset FFT domain to an FFT domain by dividing out its value at `0`.
  The resulting domain has trivial coset generator and
  parametrizes the subgroup underlying the original coset. -/
def toFftDomain (ω : D) : FftDomain ι F where
  subgroupDomain := (CosetFftDomainClass.toCosetFftDomain ω).subgroupDomain
  subgroupDomain_inj := (CosetFftDomainClass.toCosetFftDomain ω).subgroupDomain_inj
  cosetGenerator := 1
  cosetGenerator_one := by rfl

/-- Evaluation in the normalized FFT domain is `(ω 0)⁻¹ * ω i`. -/
lemma eval_toFftDomain {ω : D} {i : ι} :
  toFftDomain ω i = (ω 0)⁻¹ * ω i := by
  aesop (add
    simp [
      toFftDomain,
      FftDomain.eval_fft_domain_eq_eval_coset_fft_domain,
      CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
      toCosetFftDomain, mkSubgroupUnit])

/-- An element lies in the normalized FFT domain iff multiplying it by
  the original coset representative gives an element of the original coset domain. -/
lemma mem_toFftDomain_iff_mul_mem {ω : D} {x : F} :
  x ∈ toFftDomain ω ↔ ω 0 * x ∈ ω := by
  unfold toFftDomain
  rw [FftDomain.mem_iff_mem_toCosetFftDomain,
      CosetFftDomain.mem_iff_exists_mul]
  aesop
    (add simp
      [CosetFftDomainClass.mem_def,
       CosetFftDomainClass.toCosetFftDomain,
       CosetFftDomainClass.mkSubgroupUnit])
    (add unsafe [Eq.symm])
    (add safe (by field_simp))

/-- Multiplying an element of the normalized FFT domain by
  an element of the original coset domain gives another element of the original coset domain. -/
lemma mul_mem_of_mem_toFftDomain_of_mem {ω : D} {x y : F}
  (hx : x ∈ toFftDomain ω)
  (hy : y ∈ ω) :
  x * y ∈ ω := by
  simp_all only
    [FftDomain.mem_iff_exists, Multiplicative.exists, toFftDomain, Multiplicative.ofAdd]
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hx
  simp only [Equiv.coe_fn_mk, toCosetFftDomain, mkSubgroupUnit,
              MonoidHom.coe_mk, OneHom.coe_mk]
  exists (a + b)
  have : a + b = Multiplicative.ofAdd a * Multiplicative.ofAdd b := by rfl
  rw [map_add]
  field_simp
  rfl

/-- Multiplying an element of the original coset domain by
  an element of the normalized FFT domain gives another element of the original coset domain. -/
lemma mul_mem_of_mem_of_mem_toFftDomain {ω : D} {x y : F}
  (hx : x ∈ ω)
  (hy : y ∈ toFftDomain ω) :
  x * y ∈ ω := by
  rw [mul_comm]
  exact mul_mem_of_mem_toFftDomain_of_mem hy hx

/-- Scaling the normalized FFT-domain image by `ω 0` recovers
  the original coset FFT-domain image. -/
@[simp]
lemma toFinset_image_toFftDomain_eq_toFinset [Fintype ι] [DecidableEq F] {ω : D} :
  Finset.image (fun (w : F) ↦ ω 0 * w) (toFftDomain ω).toFinset =
    CosetFftDomainClass.toFinset ω := by
  ext x
  constructor <;> rintro h
  · simp_all only [Finset.mem_image, mem_toFinset_iff_mem]
    obtain ⟨a, h₁, h₂⟩ := h
    rw [←h₂, mul_comm]
    exact mul_mem_of_mem_toFftDomain_of_mem h₁ (by simp)
  · simp_all only [mem_toFinset_iff_mem, Finset.mem_image]
    obtain ⟨a, h⟩ := h
    have : (ω 0)⁻¹ * x ∈ toFftDomain ω := by
      rw [mem_toFftDomain_iff_mul_mem]
      aesop
    exists _, this
    field_simp

/-- The original coset FFT domain and its normalized FFT domain have
  the same number of elements. -/
lemma card_toFinset_eq_card_toFftDomain_toFinset [Fintype ι] [DecidableEq F] {ω : D} :
  Finset.card (toFinset ω) = Finset.card (toFftDomain ω).toFinset := by
  aesop (add simp [toFinset_image_toFftDomain_eq_toFinset])

end CosetFftDomainClass

namespace CosetFftDomain

variable {ω : CosetFftDomain ι F} {x : F}

abbrev toFftDomain (ω : CosetFftDomain ι F) : FftDomain ι F :=
  CosetFftDomainClass.toFftDomain ω

lemma mem_toFftDomain_iff_mul_mem :
  x ∈ ω.toFftDomain ↔ ω.cosetGenerator * x ∈ ω := by
  have : ω 0 = ω.cosetGenerator := by
    have : (0 : ι) = (1 : Multiplicative ι) := by rfl
    aesop (add simp [eval_coset_fft_domain_eq_eval_generator_mul_domain])
  aesop (add simp [CosetFftDomainClass.mem_toFftDomain_iff_mul_mem])

lemma mul_mem_of_mem_toFftDomain_of_mem {y : F}
  (hx : x ∈ ω.toFftDomain)
  (hy : y ∈ ω) :
  x * y ∈ ω := CosetFftDomainClass.mul_mem_of_mem_toFftDomain_of_mem hx hy

end CosetFftDomain

namespace FftDomain

lemma toFftDomain_eq_self {ω : FftDomain ι F} :
  ω.toFftDomain = ω := by
  ext i
  simp only [CosetFftDomainClass.toFftDomain,
    CosetFftDomainClass.toCosetFftDomain_of_CosetFftDomain,
    eval_fft_domain_eq_eval_coset_fft_domain,
    CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain, Units.val_one, one_mul,
    ne_eq, Units.ne_zero, not_false_eq_true, right_eq_mul₀, Units.val_eq_one]
  exact ω.cosetGenerator_one

end FftDomain

end Domain
