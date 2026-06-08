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

/-!
# FFT domains

This file defines FFT domains and their abstract interface.

An FFT domain is a coset FFT domain whose coset generator is `1`. Equivalently,
it is a finite multiplicative subgroup of a field equipped with an additive
indexing.

## Main definitions

- `FftDomain`: A concrete FFT domain.
- `FftDomainClass`: Typeclass for objects behaving like FFT domains.
- `SmoothFftDomain`: FFT domains indexed by `Fin (2 ^ n)`.

## Main results

- `FftDomain.injective`: FFT domains are injective.

-/

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- An FFT domain is a coset FFT domain whose coset generator is `1`.
  Equivalently, an FFT domain is exactly
  a finite multiplicative subgroup of `Fˣ` indexed additively by `ι`. -/
structure FftDomain (ι : Type) [AddCommGroup ι]
  (F : Type) [Field F] extends CosetFftDomain ι F where
  cosetGenerator_one : cosetGenerator = 1

namespace FftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Two FFT domains are equal iff their underlying subgroup parametrizations are equal. -/
private lemma eq_iff_domains_eq {ω₁ ω₂ : FftDomain ι F} :
  ω₁ = ω₂ ↔ ω₁.subgroupDomain = ω₂.subgroupDomain := by
  rcases ω₁ with ⟨⟨f₁, _, x₁⟩, h₁⟩
  rcases ω₂ with ⟨⟨f₂, _, x₂⟩, h₂⟩
  aesop

end FftDomain

instance : FunLike (FftDomain ι F) ι F where
  coe fftDomain i :=
    fftDomain.subgroupDomain i
  coe_injective' ω₁ ω₂ h := by
    simp only [FftDomain.eq_iff_domains_eq]
    ext i
    have h := congrFun h i
    simpa [Multiplicative.ofAdd] using h

namespace FftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Evaluation of an FFT domain is evaluation of its underlying subgroup parametrization. -/
lemma eval_fft_domain_eq_eval_domain
  {fftDomain : FftDomain ι F} {i : ι} :
  fftDomain i = fftDomain.subgroupDomain i := rfl

end FftDomain

/-- `FftDomain` is a `CosetFftDomainClass`. -/
instance : CosetFftDomainClass (FftDomain ι F) ι F where
  map_zero_unit ω := by
    have : (0 : ι) = (1 : Multiplicative ι) := by rfl
    aesop (add simp [FftDomain.eval_fft_domain_eq_eval_domain])
  map_add ω i j := by
    have : (0 : ι) = (1 : Multiplicative ι) := by rfl
    have : (i + j : ι) = (Multiplicative.ofAdd i) * (Multiplicative.ofAdd j) := by rfl
    aesop
      (add simp [FftDomain.eval_fft_domain_eq_eval_domain])
  map_neg ω i := by
    have : (0 : ι) = (1 : Multiplicative ι) := by rfl
    have : (-i) = (Multiplicative.ofAdd i)⁻¹ := by rfl
    aesop
      (add simp [FftDomain.eval_fft_domain_eq_eval_domain,
                 Multiplicative.ofAdd])
      (add safe (by field_simp))
  injective ω x y h := ω.subgroupDomain_inj <| by aesop

/-- Typeclass for types behaving like FFT domains.
  This extends `CosetFftDomainClass` by requiring the distinguished value at `0` to be `1`,
  corresponding to the fact that the coset representative is trivial. -/
class FftDomainClass.{u, v}
  (D : Type u) (ι : outParam (Type v)) [AddCommGroup ι]
  (F : outParam (Type v)) [Field F] [FunLike D ι F] extends
  CosetFftDomainClass D ι F where
  generator_eq_one (ω : D) : ω 0 = 1

/-- `FftDomain` is indeed an `FftDomainClass`. -/
instance : FftDomainClass (FftDomain ι F) ι F where
  generator_eq_one ω := by
    have : (0 : ι) = (1 : Multiplicative ι) := by rfl
    aesop
      (add simp [FftDomain.eval_fft_domain_eq_eval_domain])

namespace FftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Viewing an FFT domain as a coset FFT domain does not change its values. -/
lemma eval_fft_domain_eq_eval_coset_fft_domain
  {ω : FftDomain ι F} {i : ι} :
  ω i = ω.toCosetFftDomain i := by
  simp [eval_fft_domain_eq_eval_domain,
      CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
      ω.cosetGenerator_one]

end FftDomain

namespace FftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- An FFT domain is injective as a function. -/
lemma injective {ω : FftDomain ι F} :
  Function.Injective ω := CosetFftDomainClass.injective _

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- An FFT domain is injective on every set. -/
lemma injOn {ω : FftDomain ι F} {s : Set ι} :
  Set.InjOn ω s := fun _ _ _ _ h ↦ ω.injective h

end FftDomain

/-- A smooth FFT domain is an FFT domain indexed by `Fin (2 ^ n)`. -/
abbrev SmoothFftDomain (n : ℕ) (F : Type) [Field F] : Type :=
  FftDomain (Fin (2 ^ n)) F

namespace FftDomain

/-- The finite set of field elements contained in an FFT domain. -/
abbrev toFinset (ω : FftDomain ι F) : Finset F :=
  CosetFftDomainClass.toFinset ω

end FftDomain

end Domain
