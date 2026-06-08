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
import ArkLib.Data.Domain.CosetFftDomain.ToFftDomain
import ArkLib.Data.Domain.FftDomain.Ops

/-!
# Algebraic operations on coset FFT domains

This file proves the multiplicative identities satisfied by coset FFT domains
and establishes closure properties of smooth coset FFT domains.

## Main results

- `CosetFftDomain.apply_add_eq_inv_mul_mul`
- `CosetFftDomain.apply_neg_eq_sq_mul_inv`
- `CosetFftDomain.apply_sub_eq_mul_div`

For smooth domains:

- `CosetFftDomainClass.neg_mem_domain_of_mem`:
  Membership is closed under negation.
- `CosetFftDomainClass.neg_mem_domain_iff_mem`:
  Membership is invariant under negation.
- `CosetFftDomainClass.domain_implies_char_ne_2`:
  Smooth coset FFT domains of size `≠ 1` cannot exist in characteristic `2`.

-/

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomain

variable {ω : CosetFftDomain ι F} {i j : ι}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The value of a concrete coset FFT domain at `0` is its coset generator. -/
lemma apply_zero : ω 0 = ω.cosetGenerator := by
  have : (0 : ι) = (1 : Multiplicative ι) := by rfl
  aesop (add simp
     [eval_coset_fft_domain_eq_eval_generator_mul_domain])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Evaluation at a sum of indices in a coset FFT domain multiplies
  the two values and removes one copy of the coset generator. -/
lemma apply_add_eq_inv_mul_mul :
  ω (i + j) = ω.cosetGenerator⁻¹ * ω i * ω j := by cases ω with
  | mk x ω =>
    have : i + j = Multiplicative.ofAdd i * Multiplicative.ofAdd j := by rfl
    aesop
      (add simp
        [eval_coset_fft_domain_eq_eval_generator_mul_domain, ]) (add safe (by ring_nf))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Evaluation at the negated index gives the inverse value,
  scaled by the square of the coset generator. -/
lemma apply_neg_eq_sq_mul_inv :
  ω (-i) = ω.cosetGenerator ^ 2 * (ω i)⁻¹ := by cases ω with
  | mk x ω =>
  have : -i = (Multiplicative.ofAdd i)⁻¹ := by rfl
  aesop
    (add simp [eval_coset_fft_domain_eq_eval_generator_mul_domain])
    (add safe (by field_simp))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Evaluation at a difference of indices gives
  the quotient of the corresponding values, scaled by the coset generator. -/
lemma apply_sub_eq_mul_div :
  ω (i - j) = ω.cosetGenerator * ω i / ω j := by cases ω with
  | mk x ω =>
  have : (i - j) = Multiplicative.ofAdd i / Multiplicative.ofAdd j := by rfl
  aesop
    (add simp [eval_coset_fft_domain_eq_eval_generator_mul_domain, Multiplicative.ofAdd])
    (add safe (by field_simp))

end CosetFftDomain

namespace CosetFftDomainClass

section Smooth

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [CosetFftDomainClass D (Fin (2 ^ n)) F]
variable {ω : D} {x : F}

omit [DecidableEq F] in
/-- In a smooth coset FFT domain of nonzero logarithmic size,
  membership is closed under negation. -/
theorem neg_mem_domain_of_mem [nz : NeZero n] (h : x ∈ ω) :
  -x ∈ ω := by
  rw [show -x = (-1) * x by simp]
  exact mul_mem_of_mem_toFftDomain_of_mem (by simp) h

omit [DecidableEq F] in
/-- In a smooth coset FFT domain of nonzero logarithmic size,
  negation preserves and reflects membership. -/
@[simp]
lemma neg_mem_domain_iff_mem [nz : NeZero n] :
  -x ∈ ω ↔ x ∈ ω := by
  constructor <;> intro h
  · rw [show x = -(-x) by simp]
    exact neg_mem_domain_of_mem h
  · exact neg_mem_domain_of_mem h

omit [DecidableEq F] in
/-- The existence of a nontrivial smooth coset FFT domain rules out characteristic `2`. -/
lemma domain_implies_char_ne_2 [NeZero n] (ω : D) :
  ¬CharP F 2 := FftDomainClass.domain_implies_char_ne_2 (toFftDomain ω)

end Smooth

end CosetFftDomainClass

end Domain
