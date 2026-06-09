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

/-!
# Coset FFT domains

This file defines coset FFT domains and their abstract interface.

A coset FFT domain is a multiplicative coset of a finite subgroup of a field,
indexed additively. The typeclass `CosetFftDomainClass` provides an abstract
axiomatization of such domains, while `CosetFftDomain` gives a concrete
representation.

## Main definitions

- `CosetFftDomain`: A concrete coset FFT domain.
- `CosetFftDomainClass`: Typeclass for objects behaving like coset FFT domains.
- `CosetFftDomainClass.mkSubgroupUnit`: Recovers the underlying subgroup element.
- `CosetFftDomainClass.toCosetFftDomain`: Constructs a concrete domain from a class instance.
- `SmoothCosetFftDomain`: Coset FFT domains indexed by `Fin (2 ^ n)`.

## Main results

- `CosetFftDomainClass.ne_zero`: Elements of a coset FFT domain are nonzero.
- `CosetFftDomainClass.toCosetFftDomain_of_CosetFftDomain`:
  Reconstruction is the identity on concrete domains.
- `CosetFftDomain.map_0_eq_coset_generator`:
  The value at zero is the coset generator.
- `CosetFftDomain.injective`: Coset FFT domains are injective.

-/

namespace Domain

open Function

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- A coset FFT domain is a domain of the form `x · G` for
  an FFT domain `G`. -/
structure CosetFftDomain (ι : Type) [AddCommGroup ι]
  (F : Type) [Field F] where
  subgroupDomain : Multiplicative ι →* Fˣ
  subgroupDomain_inj : Injective subgroupDomain
  cosetGenerator : Fˣ

/-- Typeclass for objects behaving like coset FFT domains as functions `ι → F`.
  The axioms say that the image is a shifted multiplicative subgroup:
  `ω 0` is the coset representative, multiplication in
  the subgroup corresponds to addition in `ι`,
  negation gives inverses up to the coset factor, and the map is injective. -/
class CosetFftDomainClass.{u, v}
  (D : Type u) (ι : outParam (Type v)) [AddCommGroup ι]
  (F : outParam (Type v)) [Field F] [FunLike D ι F] where
  map_zero_unit (ω : D) : IsUnit (ω 0)
  map_add (ω : D) (i j : ι) : ω (i + j) = (ω 0)⁻¹ * ω i * ω j
  map_neg (ω : D) (i : ι) : ω (-i) = (ω 0) ^ 2 * (ω i)⁻¹
  injective (ω : D) : Injective ω

namespace CosetFftDomainClass

variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Every point of a coset FFT domain is nonzero. -/
@[simp]
lemma ne_zero (ω : D) (i : ι) : ω i ≠ 0 := fun h ↦ by
  have h0 : IsUnit (ω 0) := map_zero_unit ω
  have h_add := map_add ω i (-i)
  rw [add_neg_cancel, h] at h_add
  simp only [mul_zero, zero_mul] at h_add
  exact h0.ne_zero h_add

end CosetFftDomainClass

namespace CosetFftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Two concrete coset FFT domains are equal iff
  their coset generators and subgroup parametrizations are equal. -/
private lemma eq_iff_gen_and_domains_eq {ω₁ ω₂ : CosetFftDomain ι F} :
  ω₁ = ω₂ ↔ ω₁.cosetGenerator = ω₂.cosetGenerator ∧
    ω₁.subgroupDomain = ω₂.subgroupDomain := by
  rcases ω₁ with ⟨f₁, h₁⟩
  aesop

end CosetFftDomain

instance : FunLike (CosetFftDomain ι F) ι F where
  coe cosetDomain i :=
    cosetDomain.cosetGenerator * cosetDomain.subgroupDomain i
  coe_injective' ω₁ ω₂ h := by
    simp only at h
    have h₀ := congrFun h 0
    have h := congrFun h
    have key₀ : (ω₁.subgroupDomain (0 : ι) : F) = 1 := by
      simp [show (0 : ι) = (1 : Multiplicative ι) from rfl]
    have key₁ : (ω₂.subgroupDomain (0 : ι) : F) = 1 := by
      simp [show (0 : ι) = (1 : Multiplicative ι) from rfl]
    rw [key₀, mul_one, key₁, mul_one] at h₀
    have h_coset : ω₁.cosetGenerator = ω₂.cosetGenerator := Units.ext h₀
    have h_eq : ∀ a : ι, (ω₁.subgroupDomain a : F) = (ω₂.subgroupDomain a : F) := fun a ↦ by
      have ha := h a
      simp only [h_coset, mul_eq_mul_left_iff, Units.ne_zero, or_false] at ha
      exact ha
    exact CosetFftDomain.eq_iff_gen_and_domains_eq.mpr
      ⟨h_coset, MonoidHom.ext fun x => Units.ext (h_eq x)⟩

namespace CosetFftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Evaluation of a concrete coset FFT domain is multiplication of
  the coset generator by the subgroup element indexed by `i`. -/
lemma eval_coset_fft_domain_eq_eval_generator_mul_domain
  {cosetDomain : CosetFftDomain ι F} {i : ι} :
  cosetDomain i = cosetDomain.cosetGenerator * cosetDomain.subgroupDomain i := rfl

end CosetFftDomain

/-- `CosetFftDomain` is indeed an instance of `CosetFftDomainClass`. -/
instance : CosetFftDomainClass (CosetFftDomain ι F) ι F where
  map_zero_unit ω := by
    aesop (add simp [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])
  map_add ω i j := by
    have :
      (i + j) = ((Multiplicative.ofAdd i) * (Multiplicative.ofAdd j) : Multiplicative ι) := by rfl
    have : ω.subgroupDomain (0 : ι) = 1 := by
      simp [show (0 : ι) = (1 : Multiplicative ι) from rfl]
    aesop
      (add simp
        [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
          Multiplicative.ofAdd])
      (add safe (by field_simp))
  map_neg ω i := by
    have h₁ : (-i : ι) = (Multiplicative.ofAdd i)⁻¹ := by rfl
    have h₂ : (0 : ι) = (Multiplicative.ofAdd 0 : Multiplicative ι) := by rfl
    aesop
      (add simp [sq, CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])
      (add safe (by field_simp))
  injective ω x y h := ω.subgroupDomain_inj <| by
    aesop
      (add simp [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])

namespace CosetFftDomainClass

/-- The normalized value `(ω 0)⁻¹ * ω i`, packaged as a unit of `F`.

  This removes the coset shift and recovers the underlying subgroup element. -/
def mkSubgroupUnit {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
    (ω : D) (i : ι) : Fˣ where
  val := (ω 0)⁻¹ * ω i
  inv := ω 0 * (ω i)⁻¹
  val_inv := by
    have h0 := CosetFftDomainClass.ne_zero ω 0
    have hi := CosetFftDomainClass.ne_zero ω i
    field_simp
  inv_val := by
    have h0 := CosetFftDomainClass.ne_zero ω 0
    have hi := CosetFftDomainClass.ne_zero ω i
    field_simp

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The normalized subgroup unit map sends addition in the index type to multiplication. -/
private lemma mkSubgroupUnit_mul {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
    (ω : D) (a b : ι) :
    mkSubgroupUnit ω (a + b) = mkSubgroupUnit ω a * mkSubgroupUnit ω b := by
  unfold mkSubgroupUnit
  have := (‹CosetFftDomainClass D ι F›.map_add ω a b)
  aesop (add safe (by grind))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The normalized subgroup unit map is injective. -/
private lemma mkSubgroupUnit_injective {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
    (ω : D) : Injective (mkSubgroupUnit ω) := by
  intro a b hab
  apply (‹CosetFftDomainClass D ι F›.injective ω)
  have h_eq : (ω 0)⁻¹ * ω a = (ω 0)⁻¹ * ω b := by
    convert congr_arg Units.val hab using 1
  exact mul_left_cancel₀
    (inv_ne_zero (show ω 0 ≠ 0 from by have :=
      (‹CosetFftDomainClass D ι F›.ne_zero ω 0) ; aesop)) h_eq

/-- Reconstruct a concrete `CosetFftDomain` from any object
  of a type satisfying `CosetFftDomainClass`. -/
def toCosetFftDomain {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
  (ω : D) :
  CosetFftDomain ι F where
  subgroupDomain := {
    toFun := fun i ↦ mkSubgroupUnit ω (Multiplicative.toAdd i)
    map_one' := by
      ext
      simp [mkSubgroupUnit, CosetFftDomainClass.ne_zero ω 0]
    map_mul' := mkSubgroupUnit_mul ω
  }
  subgroupDomain_inj := fun x y h ↦ by
    have hinj := mkSubgroupUnit_injective ω
    have h' : mkSubgroupUnit ω (Multiplicative.toAdd x) =
              mkSubgroupUnit ω (Multiplicative.toAdd y) := h
    exact Multiplicative.toAdd.injective (hinj h')
  cosetGenerator := ⟨ω 0, (ω 0)⁻¹,
    mul_inv_cancel₀ (CosetFftDomainClass.ne_zero ω (0 : ι)),
    inv_mul_cancel₀ (CosetFftDomainClass.ne_zero ω (0 : ι))⟩

omit [DecidableEq ι] [DecidableEq F] [Fintype ι] in
/-- Reconstructing a concrete coset FFT domain from its class instance
  gives back the original domain. -/
lemma toCosetFftDomain_of_CosetFftDomain {ω : CosetFftDomain ι F} :
  toCosetFftDomain ω = ω := by
  simp only [toCosetFftDomain, CosetFftDomain.eq_iff_gen_and_domains_eq]
  constructor
  · have h : (0 : ι) = (Multiplicative.ofAdd 0 : Multiplicative ι) := by rfl
    aesop (add simp [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])
  · have h : (0 : ι) = (Multiplicative.ofAdd 0 : Multiplicative ι) := by rfl
    ext i
    aesop
      (add simp [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain, mkSubgroupUnit])

omit [DecidableEq ι] [DecidableEq F] [Fintype ι] in
/-- Reconstructing a concrete coset FFT domain preserves evaluation. -/
lemma toCosetFftDomain_apply_self {ω : CosetFftDomain ι F} {i : ι} :
  toCosetFftDomain ω i = ω i := by
  rw [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain]
  aesop
    (add simp [toCosetFftDomain, mkSubgroupUnit])

end CosetFftDomainClass

/-- Any class-level coset FFT domain coerces to an embedding into `F`. -/
instance {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F] :
  CoeOut D (ι ↪ F) where
  coe ω := ⟨ω, fun _ _ h ↦ CosetFftDomainClass.injective ω h⟩

namespace CosetFftDomainClass

variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]

set_option linter.unusedSectionVars false in
omit [DecidableEq ι] [DecidableEq F] [Fintype ι] in
/-- Extensionality for class-level coset FFT domains.
  Domains are equal if their evaluations are equal. -/
@[ext]
theorem ext {ω₁ ω₂ : D} (h : ∀ i, ω₁ i = ω₂ i) : ω₁ = ω₂ := DFunLike.ext _ _ h

end CosetFftDomainClass

namespace CosetFftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The value at zero is the coset generator. -/
lemma map_0_eq_coset_generator {ω : CosetFftDomain ι F} :
  ω 0 = ω.cosetGenerator := by
  simp [eval_coset_fft_domain_eq_eval_generator_mul_domain,
        show (0 : ι) = (1 : Multiplicative ι) by rfl]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- A concrete coset FFT domain is injective as a function. -/
@[simp]
lemma injective {ω : CosetFftDomain ι F} :
  Injective ω := CosetFftDomainClass.injective _

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- A concrete coset FFT domain is injective on every set. -/
@[simp]
lemma injOn {ω : CosetFftDomain ι F} {s : Set ι} :
  Set.InjOn ω s := fun _ _ _ _ h ↦ injective h

end CosetFftDomain

/-- A smooth coset FFT domain is a coset domain indexed by `Fin (2 ^ n)`. -/
abbrev SmoothCosetFftDomain (n : ℕ) (F : Type) [Field F] : Type :=
  CosetFftDomain (Fin (2 ^ n)) F

namespace CosetFftDomainClass
/-- The elements of a domain as a finset. -/
def toFinset {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
  (ω : D) : Finset F := Finset.image ω Finset.univ

omit [DecidableEq ι] in
/-- The cardinality of the finset of elements of a domain is
  the cardinality of the indexing type. -/
@[simp]
lemma card_toFinset {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
  {ω : D} :
  Finset.card (CosetFftDomainClass.toFinset ω) = Fintype.card ι := by
  simp [CosetFftDomainClass.toFinset,
        Finset.card_image_of_injective,
        CosetFftDomainClass.injective]

end CosetFftDomainClass

namespace CosetFftDomain

/-- The finset of elements of a concrete coset FFT domain. -/
abbrev toFinset (ω : CosetFftDomain ι F) : Finset F :=
  CosetFftDomainClass.toFinset ω

end CosetFftDomain

end Domain
