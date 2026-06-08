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
# Algebraic operations on FFT domains

This file proves the basic multiplicative identities satisfied by FFT domains.

## Main results

- `FftDomainClass.apply_add_eq_mul`: Addition of indices corresponds to multiplication.
- `FftDomainClass.apply_neg_eq_inv`: Negation corresponds to inversion.
- `FftDomainClass.domain_sub_eq_div_domain`: Subtraction corresponds to division.
- `FftDomainClass.apply_nsmul`: Repeated addition corresponds to exponentiation.

For smooth FFT domains:

- `FftDomainClass.neg_one_mem_domain`:
  `-1` is a member of a non-trivial FFT domain.
- `FftDomainClass.apply_eq_pow_of_generator`:
  Every element is a power of the value at `1`.
- `FftDomainClass.eq_iff_generators_eq`:
  Smooth FFT domains are determined by their generator.
- `FftDomainClass.domain_implies_char_ne_2`:
  Smooth FFT domains of positive size cannot exist in characteristic `2`.

-/

namespace Domain

variable {ι : Type} [AddCommGroup ι]
variable {F : Type} [Field F]

namespace FftDomainClass

variable {D : Type} [FunLike D ι F] [FftDomainClass D ι F]
variable {ω : D} {i j : ι}

/-- The value of an FFT domain at `0` is `1`. -/
@[simp]
lemma apply_zero_eq_one :
  ω 0 = 1 := generator_eq_one _

/-- Evaluation of an FFT domain turns addition in the index type
  into multiplication in the field. -/
lemma apply_add_eq_mul :
  ω (i + j) = ω i * ω j := by
  simp [CosetFftDomainClass.map_add]

/-- The product of two elements of an FFT domain is again in the domain. -/
lemma mul_mem_of_mem
  {x₁ x₂ : F} (hx₁ : x₁ ∈ ω) (hx₂ : x₂ ∈ ω) :
  x₁ * x₂ ∈ ω := by
  rw [CosetFftDomainClass.mem_def] at *
  obtain ⟨⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩⟩ := hx₁, hx₂
  exists (i₁ + i₂)
  aesop (add simp [apply_add_eq_mul])

/-- Evaluation at the negated index gives the inverse field element. -/
@[simp]
lemma apply_neg_eq_inv :
  ω (-i) = (ω i)⁻¹ := by
  have h_def : ω (-i) * ω i = 1 := by
    rw [←apply_add_eq_mul]
    aesop
  exact eq_inv_of_mul_eq_one_left h_def

/-- Evaluation at a difference of indices gives the quotient of the corresponding evaluations. -/
lemma domain_sub_eq_div_domain :
  ω (i - j) = ω i / ω j := by
  rw
    [sub_eq_add_neg,
      div_eq_mul_inv,
      apply_add_eq_mul,
      apply_neg_eq_inv]

/-- Evaluation at a natural multiple of an index gives the corresponding power of the evaluation. -/
lemma apply_nsmul {k : ℕ} :
  ω (k • i) = (ω i) ^ k := by
  induction k with
  | zero => simp [pow_zero]
  | succ k ih => rw [succ_nsmul, apply_add_eq_mul, ih, pow_succ]

section Smooth

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [FftDomainClass D (Fin (2 ^ n)) F]
variable {ω : D}

/-- In a smooth FFT domain of nonzero logarithmic size, `-1` belongs to the domain. -/
@[simp]
lemma neg_one_mem_domain [nz : NeZero n] :
  -1 ∈ ω := by
  have hn : n ≠ 0 := NeZero.ne _
  -- Let's denote this element as `k = 2^(i-1) : Fin (2^i)`.
  set k : Fin (2 ^ n) := ⟨2 ^ (n - 1), pow_lt_pow_right₀ (by decide) (by omega)⟩
  generalize_proofs at *
  have h_order : (ω k) ^ 2 = 1 := by
    have hk_order : (ω k) ^ 2 = (ω (k + k)) := by aesop (add simp [sq, apply_add_eq_mul])
    convert hk_order using 1
    rw [show k + k = 0 by {
      rcases n with ⟨_ | n, hn⟩
        <;> norm_num [Fin.ext_iff, Fin.val_add, Fin.val_mul] at *
      ring_nf at *
      aesop
    }]
    aesop
  generalize_proofs at *
  (
  -- Since $k$ has additive order 2 in $\text{Fin}(2^i)$, we have $(ω.subdomain i k) \neq 1$.
  have h_ne_one : (ω k) ≠ 1 := by
    have h_ne_one : (ω k) ≠ ω 0 := by
      exact fun h ↦
        absurd
          (CosetFftDomainClass.injective _ h)
          (ne_of_gt <| Nat.lt_of_le_of_lt (Nat.zero_le _) <| pow_pos (by omega) _)
    generalize_proofs at *
    (
    exact fun h ↦ h_ne_one <| h.trans <| by simp )
  generalize_proofs at *
  (exact ⟨k, Or.resolve_left (sq_eq_one_iff.mp h_order) h_ne_one⟩))

private lemma val_eq_nsmul_one {n : ℕ} (i : Fin (2 ^ n)) :
  i = i.val • (1 : Fin (2 ^ n)) := by
  simp only [Fin.ext_iff]
  convert Nat.mod_eq_of_lt i.2 using 1
  · rw [Nat.mod_eq_of_lt i.2]
  · convert Nat.mod_eq_of_lt i.2 using 1
    erw [Fin.val_mk]
    induction i.val <;> simp_all +decide [nsmulRec]
    simp_all +decide [Fin.val_add]

/-- In a smooth FFT domain, every value is a power of the value at `1`. -/
lemma apply_eq_pow_of_generator (i : Fin (2 ^ n)) :
  ω i = (ω 1) ^ i.val := by
  conv_lhs => rw [val_eq_nsmul_one i]
  simp [FftDomainClass.apply_nsmul]

/-- Two smooth FFT domains are equal iff their values at `1` are equal. -/
theorem eq_iff_generators_eq {ω₁ ω₂ : D} :
  ω₁ = ω₂ ↔ ω₁ 1 = ω₂ 1 := by
  constructor <;> (intro h; try rw [h])
  ext i
  aesop (add safe [(by rw [apply_eq_pow_of_generator i])])

/-- The existence of a nontrivial smooth FFT domain rules out characteristic `2`. -/
lemma domain_implies_char_ne_2 [NeZero n] (ω : D) :
  ¬CharP F 2 := fun hchar ↦ by
  have hn : n ≠ 0 := NeZero.ne _
  set k : Fin (2 ^ n) := ⟨2 ^ (n - 1), pow_lt_pow_right₀ (by decide) (by omega)⟩
  have hk_ne_zero : k ≠ 0 := by simp [Fin.ext_iff, k]
  have h_ne_val : ω k ≠ ω 0 := fun h => hk_ne_zero (CosetFftDomainClass.injective ω h)
  have h_ne_one : ω k ≠ 1 := by rwa [apply_zero_eq_one] at h_ne_val
  have h_kk : k + k = 0 := by
    ext
    simp only [Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.zero_mod, k]
    rcases n with _ | n <;> simp_all
    ring_nf
    simp
  have h_sq : (ω k) ^ 2 = 1 := by
    rw [sq, ←apply_add_eq_mul, h_kk, apply_zero_eq_one]
  have h_eq : ω k = 1 ∨ ω k = -1 := sq_eq_one_iff.mp h_sq
  have h_neg_eq_pos : (-1 : F) = 1 := by
    have : (2 : F) = 0 := CharP.cast_eq_zero F 2
    conv_rhs =>
      rw [show (1 : F) = 2 - 1 by norm_num, this]
    simp
  rcases h_eq with h | h
  · exact h_ne_one h
  · exact h_ne_one (by rwa [h_neg_eq_pos] at h)

end Smooth

end FftDomainClass

end Domain
