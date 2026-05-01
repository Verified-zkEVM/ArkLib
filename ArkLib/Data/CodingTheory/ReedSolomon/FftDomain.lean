/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Field

/-!
# FFT domains

This module develops a unified interface for finite evaluation domains used in
multiplicative number-theoretic transforms (NTTs), Reed-Solomon encodings, and
FRI-style protocols.

The guiding idea is that an FFT evaluation domain should be viewed as a finite
additive indexing group `ι` together with an injective homomorphism into the
multiplicative group of a field. This lets us treat:

* ordinary multiplicative subgroups,
* smooth radix-2 domains indexed by `Fin (2^n)`,

within one common framework. Coset FFT domains can be treated similarly.

## Mathematical picture

An `FftDomain ι F` is an injective homomorphism

`ι → Fˣ`

where `ι` is written additively and `Fˣ` multiplicatively.

So if `ω : FftDomain ι F`, then morally one should think of `ω i` as the
`i`-th point of a multiplicative evaluation domain.

A `CosetFftDomain ι F` is a coset `x · ω`, where `x : Fˣ` is a multiplicative
shift and `ω` is an underlying FFT domain.

## Main definitions

* `FftDomain`
  : an injective additive-to-multiplicative group embedding
* `SmoothFftDomain n F`
  : an FFT domain indexed by `Fin (2^n)`
* `CosetFftDomain`
  : a multiplicative coset of an FFT domain
* `SmoothCosetFftDomain n F`
  : a coset of a radix-2 smooth FFT domain

For convenience, domains are coerced to:

* functions `ι → F`,
* finite sets of evaluation points,
* subgroups of `Fˣ` in the non-coset case.

## Subdomains

A major theme of the module is the construction of canonical radix-2 subdomains.

For `ω : SmoothFftDomain n F`, the definition

* `FftDomain.subdomain`

produces the unique subdomain of log-size `i ≤ n`, compatible with the standard
tower of radix-2 subgroups. This is developed further through:

* monotonicity:
  `FftDomain.subdomain_le`,
  `FftDomain.subdomain_le_mem`
* extremal cases:
  `FftDomain.subdomain_0`,
  `FftDomain.subdomain_last`
* power maps:
  `FftDomain.subdomain_pow_property`,
  `FftDomain.subdomain_pow_property'`
* "maps" between subdomains:
  `FftDomain.subdomain_roots_card`,
  `FftDomain.subdomain_root_exists`

There are also natural-number indexed wrappers:

* `FftDomain.subdomainNat`
* `FftDomain.subdomainNatReversed`

which are often more convenient in applications.

## Cosets

For `ω : SmoothCosetFftDomain n F`, the definition

* `CosetFftDomain.subdomain`

gives the corresponding tower of cosets, with the multiplicative shift
adjusted by the appropriate power.

Important lemmas include:

* `CosetFftDomain.subdomain_pow_property`
* `CosetFftDomain.subdomain_roots_card`
* `CosetFftDomain.subdomain_root_exists`
* `CosetFftDomain.neg_mem_dom_of_mem_dom`
* `CosetFftDomain.mul_property`

as well as the `subdomainNat` and `subdomainNatReversed` API for cosets.

## Implementation notes

The development is designed to support downstream formalizations of
Reed-Solomon style protocols, especially settings where one repeatedly moves
between:

* a large radix-2 domain,
* its smaller subdomains,
* multiplicative cosets,
* and power maps between these domains.

The emphasis is on a reusable algebraic API rather than on any single FFT
algorithm.

-/

set_option linter.style.induction false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longFile 1700

namespace ReedSolomon

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- An FFT domain is an injective group homomorphism
  whose codomain is the multiplicative group of a field.
-/
structure FftDomain (ι : Type) [AddCommGroup ι]
  (F : Type) [Field F] where
    domain : MonoidHom (Multiplicative ι) Fˣ
    inj : Function.Injective domain

namespace FftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma eq_iff_domains_eq {φ₁ φ₂ : FftDomain ι F} :
  φ₁ = φ₂ ↔ φ₁.domain = φ₂.domain := by
  rcases φ₁ with ⟨f₁, h₁⟩
  aesop

end FftDomain

instance : FunLike (FftDomain ι F) ι F where
  coe fftDomain i := fftDomain.domain i
  coe_injective' φ₁ φ₂ h := by
    have h := congrFun h
    aesop (add simp [FftDomain.eq_iff_domains_eq])

namespace FftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma eval_fft_domain_eq_eval_domain
  {fftDomain : FftDomain ι F} {i : ι} :
  fftDomain i = fftDomain.domain i := rfl

end FftDomain

instance : Coe (FftDomain ι F) (ι ↪ F) where
  coe fftDomain := ⟨fftDomain, fun i₁ i₂ h ↦
    match fftDomain with
    | ⟨domain, hinj⟩ => by aesop (add simp [FftDomain.eval_fft_domain_eq_eval_domain])
 ⟩

set_option synthInstance.checkSynthOrder false in
instance : Membership F (FftDomain ι F) where
  mem φ x := ∃ i, φ i = x

namespace FftDomain

def toFinset (ω : FftDomain ι F) : Finset F := Finset.image ω Finset.univ

instance
    {ι : Type} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F] :
  CoeSort (FftDomain ι F) Type where
    coe d := toFinset d

end FftDomain

instance {ω : FftDomain ι F} : Inhabited ω.toFinset where
  default := ⟨ω 0, by simp [FftDomain.toFinset]⟩

instance {ω : FftDomain ι F} : Inhabited ω where
  default := ⟨ω 0, by simp [FftDomain.toFinset]⟩

namespace FftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_domain_iff_exists {ω : FftDomain ι F} {x : F} :
  x ∈ ω ↔ ∃ i, ω i = x := by rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma mem_domain_self {ω : FftDomain ι F} {i : ι} :
  ω i ∈ ω := by simp [mem_domain_iff_exists]

omit [DecidableEq ι] in
lemma mem_finset_iff_exists {ω : FftDomain ι F} {x : F} :
  x ∈ ω.toFinset ↔ ∃ i, ω i = x := by simp [toFinset]

omit [DecidableEq ι] in
lemma mem_finset_iff_mem_domain {ω : FftDomain ι F} {x : F} :
  x ∈ ω.toFinset ↔ x ∈ ω := by simp [toFinset, mem_domain_iff_exists]

end FftDomain

instance {x : F} {ω : FftDomain ι F} : Decidable (x ∈ ω) :=
  decidable_of_iff _ FftDomain.mem_finset_iff_mem_domain

namespace Finset

/-- A helper to convert a finset into
  a list whose elements are the members of the finset,
  i.e. come with a proof that they belong to the finset.
-/
noncomputable def toListWithProof.{u} {α : Type u} [DecidableEq α] (s : Finset α) :
  List s :=
  let list := s.toList
  List.reduceOption <|
    list.map (fun x ↦ if h : x ∈ s then some ⟨x, h⟩ else none)

@[simp]
lemma toListWithProof_empty.{u} {α : Type u} [DecidableEq α] :
  toListWithProof (∅ : Finset α) = [] := by
  simp [toListWithProof, List.reduceOption]

lemma toListWithProof_mem.{u} {α : Type u} [DecidableEq α]
  {x : α}
  {s : Finset α}
  (hx : x ∈ s) :
  ⟨x, hx⟩ ∈ toListWithProof s := by
  simp [toListWithProof, List.reduceOption, hx]

private lemma list_reduceOption_helper
  {α : Type*} [DecidableEq α] {s : Finset α}
  {l : List α} (h : ∀ x ∈ l, x ∈ s) :
    List.map Subtype.val
      (List.reduceOption (l.map (fun x ↦ if hx : x ∈ s then some ⟨x, hx⟩ else none)))
        = l := by
  induction l with
  | nil => simp [List.reduceOption]
  | cons a t ih =>
    have ha := h a (by simp)
    simp only [List.map_cons, ha, dite_true, List.reduceOption, List.filterMap_cons, id]
    change a :: List.map Subtype.val _ = a :: t
    congr 1
    exact ih (fun x hx ↦ h x (List.mem_cons_of_mem a hx))

@[simp]
lemma toListWithProof_eq_toList.{u} {α : Type u} [DecidableEq α]
  {s : Finset α} :
  (toListWithProof s).map (fun x ↦ x.1) =
    s.toList := by
  simp only [toListWithProof]
  exact list_reduceOption_helper (fun x hx ↦ Finset.mem_toList.mp hx)

end Finset

namespace FftDomain

/-- Convert an FFT domain into a list of all its members
  with proofs the members belong to the FFT domain. -/
noncomputable def toList (ω : FftDomain ι F) : List (ω.toFinset) :=
  Finset.toListWithProof <| ω.toFinset

set_option linter.unusedSimpArgs false in -- false alert
omit [DecidableEq ι] in
lemma toList_eq_finset_toList {ω : FftDomain ι F} :
  ω.toList.map (fun x ↦ x.1) = ω.toFinset.toList := by
  simp [mem_finset_iff_exists, toList]

def toSubgroup (ω : FftDomain ι F) : Subgroup Fˣ where
  carrier := Finset.image ω.domain Finset.univ
  mul_mem' {a b} ha hb := by {
    simp_all only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      Multiplicative.exists]
    rcases ha with ⟨x, ha⟩
    rcases hb with ⟨y, hb⟩
    exists (x + y)
    simp [ha, hb]
  }
  one_mem' := by {
    rw [show (1 : Fˣ) = ω.domain (Multiplicative.ofAdd 0) by simp]
    aesop (add simp [Multiplicative.ofAdd])
  }
  inv_mem' {x} hx := by {
    simp_all only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      Multiplicative.exists]
    rcases hx with ⟨a, ha⟩
    exists (-a)
    aesop
  }

omit [DecidableEq ι] in
@[simp]
lemma mem_subgroup_iff_mem_finset {ω : FftDomain ι F} {x : Fˣ} :
  x ∈ ω.toSubgroup ↔ x.val ∈ ω.toFinset := by
  aesop (add simp [toSubgroup, toFinset])

end FftDomain

instance : CoeOut (FftDomain ι F) (Finset F) where
  coe ω := ω.toFinset

instance : CoeOut (FftDomain ι F) (Subgroup Fˣ) where
  coe ω := ω.toSubgroup

namespace FftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F]
lemma injective {ω : FftDomain ι F} :
  Function.Injective ω := fun i₁ i₂ h ↦ by cases ω with
  | mk ω hinj => aesop (add simp [eval_fft_domain_eq_eval_domain])

lemma domain_elem_invertible {ω : FftDomain ι F} {i : ι} :
  IsUnit (ω i) := by aesop (add simp [eval_fft_domain_eq_eval_domain])

@[simp]
lemma zero_is_not_in_domain {ω : FftDomain ι F} :
  0 ∉ ω := by
  simp only [mem_domain_iff_exists, not_exists]
  intro x
  have h := domain_elem_invertible (ω := ω) (i := x)
  aesop

@[simp]
lemma domain_zero_eq_one {ω : FftDomain ι F} :
  ω 0 = 1 := by
  change ↑(ω.domain (Multiplicative.ofAdd (0 : ι))) = (1 : F)
  rw [show Multiplicative.ofAdd (0 : ι) = (1 : Multiplicative ι) from rfl, map_one]
  simp

@[simp]
lemma domain_add_eq_mul_domain {ω : FftDomain ι F}
  {i₁ i₂ : ι} :
  ω (i₁ + i₂) = ω i₁ * ω i₂ := by
  convert congr_arg
    (fun x : Fˣ ↦ (x : F))
    (ω.domain.map_mul (Multiplicative.ofAdd i₁) (Multiplicative.ofAdd i₂)) using 1

@[simp]
lemma domain_neg_eq_inv_domain {ω : FftDomain ι F}
  {i₁ : ι} :
  ω (-i₁) = (ω i₁)⁻¹ := by
  have h_def : ω (-i₁) * ω i₁ = 1 := by
    rw [←FftDomain.domain_add_eq_mul_domain]
    aesop
  exact eq_inv_of_mul_eq_one_left h_def


@[simp]
lemma domain_sub_eq_div_domain {ω : FftDomain ι F}
  {i₁ i₂ : ι} :
  ω (i₁ - i₂) = ω i₁ / ω i₂ := by
  rw
    [sub_eq_add_neg,
      div_eq_mul_inv,
      FftDomain.domain_add_eq_mul_domain,
      FftDomain.domain_neg_eq_inv_domain ]

@[ext]
theorem ext {ω₁ ω₂ : FftDomain ι F} (h : ∀ i, ω₁ i = ω₂ i) :
  ω₁ = ω₂ := by aesop (add simp [eq_iff_domains_eq, Multiplicative.ofAdd])

end FftDomain

/-- A smooth FFT domain is an FFT domain whose
  domain (i.e. LHS) is a finite additive cyclic group,
  which up to isomorphis is `Fin n`. -/
abbrev SmoothFftDomain (n : ℕ) (F : Type) [Field F] : Type := FftDomain (Fin (2 ^ n)) F

namespace FftDomain

@[simp]
lemma size_of_smooth_fft_domain_eq_pow_of_2 {n : ℕ} {ω : SmoothFftDomain n F} :
  Finset.card (ω : Finset F) = 2 ^ n := by
  aesop (add simp [FftDomain.toFinset, Finset.card_image_of_injective, FftDomain.injective])

omit [DecidableEq F] in
private lemma domain_nsmul {n : ℕ} {ω : SmoothFftDomain n F} (k : ℕ) (i : Fin (2 ^ n)) :
  ω (k • i) = (ω i) ^ k := by
  induction k with
  | zero => simp [FftDomain.domain_zero_eq_one, pow_zero]
  | succ k ih =>
    rw [succ_nsmul, FftDomain.domain_add_eq_mul_domain, ih, pow_succ]

private lemma val_eq_nsmul_one {n : ℕ} (i : Fin (2 ^ n)) : i = i.val • (1 : Fin (2 ^ n)) := by
  simp only [Fin.ext_iff]
  convert Nat.mod_eq_of_lt i.2 using 1
  · rw [Nat.mod_eq_of_lt i.2]
  · convert Nat.mod_eq_of_lt i.2 using 1
    erw [Fin.val_mk]
    induction i.val <;> simp_all +decide [nsmulRec]
    simp_all +decide [Fin.val_add]

omit [DecidableEq F] in
lemma domain_eq_pow_of_generator {n : ℕ} {ω : SmoothFftDomain n F} (i : Fin (2 ^ n)) :
  ω i = (ω 1) ^ i.val := by
  conv_lhs => rw [val_eq_nsmul_one i]
  simp [domain_nsmul]

omit [DecidableEq F] in
theorem eq_iff_generators_eq {n : ℕ} {ω₁ ω₂ : SmoothFftDomain n F} :
  ω₁ = ω₂ ↔ ω₁ 1 = ω₂ 1 := by
  constructor <;> (intro h; try rw [h])
  ext i
  aesop (add safe [(by rw [domain_eq_pow_of_generator i])])

end FftDomain

/-- A coset FFT domain is a domain of the form `x · G` for
  an FFT domain `G`. -/
structure CosetFftDomain (ι : Type) [AddCommGroup ι]
  (F : Type) [Field F] where
  x : Fˣ
  fftDomain : FftDomain ι F

namespace CosetFftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma eq_iff_domains_and_gen_eq {φ₁ φ₂ : CosetFftDomain ι F} :
  φ₁ = φ₂ ↔ φ₁.x = φ₂.x ∧ φ₁.fftDomain = φ₂.fftDomain := by
  rcases φ₁ with ⟨f₁, h₁⟩
  aesop

end CosetFftDomain

instance : FunLike (CosetFftDomain ι F) ι F where
  coe cosetDomain i := cosetDomain.x * cosetDomain.fftDomain i
  coe_injective' φ₁ φ₂ h := by
    simp only at h
    have h₀ := congrFun h 0
    have h := congrFun h
    aesop (add simp [CosetFftDomain.eq_iff_domains_and_gen_eq])

namespace CosetFftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma eval_coset_fft_domain_eq_eval_x_mul_domain
  {cosetDomain : CosetFftDomain ι F} {i : ι} :
  cosetDomain i = cosetDomain.x * cosetDomain.fftDomain i := rfl

end CosetFftDomain

instance : Coe (CosetFftDomain ι F) (ι ↪ F) where
  coe cosetDomain := ⟨cosetDomain, fun i₁ i₂ h ↦ match cosetDomain with
    | ⟨x, f⟩ => FftDomain.injective (ω := f) <| by
      aesop (add simp
        [CosetFftDomain.eval_coset_fft_domain_eq_eval_x_mul_domain,
         FftDomain.injective])
 ⟩

instance : Membership F (CosetFftDomain ι F) where
  mem φ x := ∃ i, φ i = x

namespace CosetFftDomain

def toFinset (ω : CosetFftDomain ι F) : Finset F :=
  Finset.image ω Finset.univ

instance
    {ι : Type} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F] :
  CoeSort (CosetFftDomain ι F) Type where
    coe d := toFinset d

end CosetFftDomain

instance {ω : CosetFftDomain ι F} : Inhabited ω.toFinset where
  default := ⟨ω 0, by simp [CosetFftDomain.toFinset]⟩

instance {ω : CosetFftDomain ι F} : Inhabited ω where
  default := ⟨ω 0, by simp [CosetFftDomain.toFinset]⟩

namespace CosetFftDomain

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_coset_def {ω : CosetFftDomain ι F}
  {x : F} :
  x ∈ ω ↔ ∃ i, x = ω i := by aesop (add simp [Membership.mem])

omit [DecidableEq ι] in
@[simp]
lemma mem_coset {ω : CosetFftDomain ι F}
  {x : F} :
  x ∈ ω.toFinset ↔ ∃ y ∈ ω.fftDomain, x = ω.x * y := by
  aesop (add simp [toFinset, FftDomain.mem_domain_iff_exists])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_coset_domain {ω : CosetFftDomain ι F}
  {x : F} :
  x ∈ ω ↔ ∃ y ∈ ω.fftDomain, x = ω.x * y := by
  aesop (add simp
    [Membership.mem, eval_coset_fft_domain_eq_eval_x_mul_domain])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma mem_coset_domain_self {ω : CosetFftDomain ι F} {i : ι} :
  ω i ∈ ω := by simp [mem_coset_def]

omit [DecidableEq ι] in
lemma mem_coset_finset_iff_mem_coset_domain {ω : CosetFftDomain ι F}
  {x : F} :
  x ∈ ω.toFinset ↔ x ∈ ω := by simp [mem_coset_domain]

end CosetFftDomain

instance {x : F} {ω : CosetFftDomain ι F} : Decidable (x ∈ ω) :=
  decidable_of_iff _ CosetFftDomain.mem_coset_finset_iff_mem_coset_domain

namespace CosetFftDomain

noncomputable def toList (ω : CosetFftDomain ι F) : List (ω.toFinset) :=
  Finset.toListWithProof <| ω.toFinset

omit [DecidableEq ι] in
set_option linter.unusedSimpArgs false in -- false alert
lemma toList_eq_finset_toList {ω : CosetFftDomain ι F} :
  ω.toList.map (fun x ↦ x.1) = ω.toFinset.toList := by
    simp [toList, FftDomain.mem_domain_iff_exists]

omit [DecidableEq ι] in
@[simp]
lemma coset_domain_eq_image {ω : CosetFftDomain ι F} :
  Finset.image (fun (w : F) ↦ ω.x * w) ω.fftDomain.toFinset = ω.toFinset := by
  aesop (add simp [FftDomain.mem_domain_iff_exists,
                         FftDomain.mem_finset_iff_exists])

omit [DecidableEq ι] in
lemma card_eq_fft_domain_card {ω : CosetFftDomain ι F} :
  Finset.card ω.toFinset = Finset.card ω.fftDomain.toFinset := by
  rw [←coset_domain_eq_image,
      Finset.card_image_of_injective _
        (mul_right_injective₀ (Units.ne_zero _))]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma injective {ω : CosetFftDomain ι F} :
  Function.Injective ω := fun _ _ h ↦
  FftDomain.injective (ω := ω.fftDomain) <| by
    aesop (add simp [eval_coset_fft_domain_eq_eval_x_mul_domain])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma zero_is_not_in_domain {ω : CosetFftDomain ι F} :
  0 ∉ ω := by
  simp only [mem_coset_domain, FftDomain.mem_domain_iff_exists, zero_eq_mul, Units.ne_zero,
    false_or, exists_eq_right, not_exists]
  intro x contra
  have h : 0 ∈ ω.fftDomain := by aesop (add simp [FftDomain.mem_domain_iff_exists])
  exact FftDomain.zero_is_not_in_domain h

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma coset_domain_zero_eq_x {ω : CosetFftDomain ι F} :
  ω 0 = ω.x := by cases ω with
  | mk x _ =>
    simp [eval_coset_fft_domain_eq_eval_x_mul_domain]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma coset_domain_add_eq_mul_domain {ω : CosetFftDomain ι F}
  {i₁ i₂ : ι} :
  ω (i₁ + i₂) = (ω.x)⁻¹ * ω i₁ * ω i₂ := by cases ω with
  | mk x ω =>
    aesop
      (add simp [eval_coset_fft_domain_eq_eval_x_mul_domain])
      (add safe (by ring_nf))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma coset_domain_neg_eq_inv_domain {ω : CosetFftDomain ι F}
  {i₁ : ι} :
  ω (-i₁) = ω.x ^ 2 * (ω i₁)⁻¹ := by cases ω with
  | mk x ω =>
  simp [eval_coset_fft_domain_eq_eval_x_mul_domain]
  field_simp

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma coset_domain_sub_eq_div_domain {ω : CosetFftDomain ι F}
  {i₁ i₂ : ι} :
  ω (i₁ - i₂) = ω.x * ω i₁ / ω i₂ := by cases ω with
  | mk x ω =>
  simp [eval_coset_fft_domain_eq_eval_x_mul_domain]
  field_simp

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
theorem ext {ω₁ ω₂ : CosetFftDomain ι F} (h : ∀ i, ω₁ i = ω₂ i) :
  ω₁ = ω₂ := by
  have hx : ω₁.x = ω₂.x := by
    specialize h 0
    aesop
  have hext : ω₁.fftDomain = ω₂.fftDomain := FftDomain.ext <| fun i ↦ by
    aesop (add simp [eval_coset_fft_domain_eq_eval_x_mul_domain])
  exact
    eq_iff_domains_and_gen_eq.2 <| And.intro hx hext

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma x_mul_mem_coset_iff {φ : CosetFftDomain ι F}
  {y : F} :
  φ.x * y ∈ φ ↔ y ∈ φ.fftDomain := by simp [mem_coset_domain]

end CosetFftDomain

/-- A smooth coset FFT domain is a coset FFT domain
  whose underlying FFT domain is smooth. -/
abbrev SmoothCosetFftDomain (n : ℕ) (F : Type) [Field F] : Type :=
  CosetFftDomain (Fin (2 ^ n)) F

namespace FftDomain

private def subdomain_embed {n : ℕ} (i : Fin n.succ) (k : Fin (2 ^ (i : ℕ))) :
  Fin (2 ^ n) :=
  ⟨2 ^ (n - i) * k.val, match i, k with
    | ⟨i, hi⟩, ⟨k, hk⟩ => by
      simp only at hk ⊢
      by_cases hk_zero : k = 0 <;> try (subst hk_zero; simp)
      calc 2 ^ (n - i) * k < 2 ^ (n - i) * 2 ^ i :=
              Nat.mul_lt_mul_of_pos_left hk (by positivity)
          _ = 2 ^ n := by rw [←pow_add, Nat.sub_add_cancel (by omega)]⟩

private lemma subdomain_embed_add {n : ℕ} (i : Fin n.succ) (a b : Fin (2 ^ (i : ℕ))) :
  subdomain_embed i (a + b) = subdomain_embed i a + subdomain_embed i b := by
  unfold subdomain_embed
  simp +decide [Fin.val_add]
  ring_nf
  norm_num [Fin.ext_iff, Fin.val_add, Fin.val_mul]
  rw [←add_mul, ←Nat.mul_mod_mul_right, ←pow_add,
    Nat.add_sub_of_le (Nat.le_of_lt_succ i.2)]

private lemma subdomain_embed_zero {n : ℕ} (i : Fin n.succ) : subdomain_embed i (0 :
  Fin (2 ^ (i : ℕ))) = (0 : Fin (2 ^ n)) := by
  unfold subdomain_embed
  aesop

private lemma subdomain_embed_injective {n : ℕ} (i : Fin n.succ) :
  Function.Injective (subdomain_embed (n := n) i) := by
  intro a b h
  simp_all [Fin.ext_iff, subdomain_embed]

/-- Given a smooth FFT domain `ω` of log-order `n`
  this function returns its subdomain of log-order `i`.
-/
def subdomain {n : ℕ} (ω : SmoothFftDomain n F) (i : Fin n.succ) :
  SmoothFftDomain i F :=
  ⟨{ toFun := fun k ↦ ω.domain (Multiplicative.ofAdd (subdomain_embed i (Multiplicative.toAdd k)))
     map_one' := by simp [subdomain_embed_zero]
     map_mul' := by aesop (add simp [subdomain_embed_add, toAdd_mul]) },
   by
     intro a b h
     have h2 := ω.inj h
     have h3 := Multiplicative.ofAdd.injective h2
     exact Multiplicative.ofAdd.injective (subdomain_embed_injective i h3)⟩

omit [DecidableEq F] in
lemma mem_subdomain_of_eq_vals {n : ℕ} {ω : SmoothFftDomain n F}
  {x : F}
  {i j : Fin n.succ}
  (hij : i.val = j.val) :
  x ∈ ω.subdomain i ↔ x ∈ ω.subdomain j := by rw [Fin.ext hij]

@[simp]
lemma subdomain_0 {n} {ω : SmoothFftDomain n F} :
  (ω.subdomain 0 : Subgroup Fˣ) = ⊥ := by
  simp only [toSubgroup, Nat.succ_eq_add_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.pow_zero,
    Finset.univ_unique, Finset.image_singleton, Finset.coe_singleton, Subgroup.eq_bot_iff_forall,
    Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_singleton_iff, forall_eq]
  exact map_one _

omit [DecidableEq F] in
@[simp]
lemma subdomain_0' {n} {ω : SmoothFftDomain n F}
  {x : F} :
  x ∈ ω.subdomain 0 ↔ x = 1 := by
  simp only [mem_domain_iff_exists]; constructor
  · rintro ⟨i, rfl⟩; simp [subdomain, subdomain_embed]; norm_cast
  · intro h; subst h; exact ⟨0, by simp [subdomain, subdomain_embed]; norm_cast⟩


private lemma subdomain_embed_last {n : ℕ} (k : Fin (2 ^ (Fin.last n : ℕ))) :
  subdomain_embed (Fin.last n) k = Fin.cast (by simp [Fin.last]) k := by
  unfold subdomain_embed
  aesop

@[simp]
lemma subdomain_last {n} {ω : SmoothFftDomain n F} :
  (ω.subdomain (Fin.last n) : Subgroup Fˣ) = (ω : Subgroup Fˣ) := by
  ext x
  simp only [toSubgroup, Nat.succ_eq_add_one, Fin.val_last, subdomain,
    Finset.coe_image, Finset.coe_univ, Set.image_univ, Subgroup.mem_mk,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_range, Multiplicative.exists]
  constructor
    <;> intro h
    <;> rcases h with ⟨a, rfl⟩
    <;> use Fin.cast (by simp) a
    <;> simp +decide [subdomain_embed_last]
    <;> rfl

omit [DecidableEq F] in
lemma subdomain_last' {n : ℕ} {ω : SmoothFftDomain n F}
  {v : F} :
  v ∈ (ω.subdomain (@Nat.cast (Fin (n + 1)) (Fin.NatCast.instNatCast (n + 1)) n)) ↔ v ∈ ω := by
  simp only [Nat.succ_eq_add_one, Fin.val_natCast, subdomain, mem_domain_iff_exists]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    use Fin.cast (by simp) a
    unfold subdomain_embed
    aesop

private lemma subdomain_embed_of_le {n : ℕ} (i j : Fin n.succ) (h : i ≤ j)
    (k : Fin (2 ^ (i : ℕ))) :
    ∃ (l : Fin (2 ^ (j : ℕ))), subdomain_embed i k = subdomain_embed j l := by
  refine ⟨⟨2 ^ ((j : ℕ) - (i : ℕ)) * k.val, ?_⟩, ?_⟩
  · calc 2 ^ ((j : ℕ) - (i : ℕ)) * k.val < 2 ^ ((j : ℕ) - (i : ℕ)) * 2 ^ (i : ℕ) := by
          apply Nat.mul_lt_mul_of_pos_left k.isLt (by positivity)
        _ = 2 ^ (j : ℕ) := by rw [←pow_add, Nat.sub_add_cancel (by omega)]
  · simp only [subdomain_embed, Fin.ext_iff]
    rw [←mul_assoc, ←pow_add]
    have : n - ↑j + (↑j - ↑i) = n - ↑i := Nat.sub_add_sub_cancel (by omega) (by omega)
    rw [this]

lemma subdomain_le {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (h : i ≤ j) :
  (ω.subdomain i : Subgroup _) ≤ (ω.subdomain j : Subgroup Fˣ) := by
  simp only [toSubgroup, Nat.succ_eq_add_one, Finset.coe_image, Finset.coe_univ,
    Set.image_univ, SetLike.le_def, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_range, Multiplicative.exists, forall_exists_index, forall_apply_eq_imp_iff]
  intro a
  obtain ⟨l, hl⟩ := subdomain_embed_of_le i j h a
  unfold subdomain
  aesop

lemma subdomain_le_finset {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hij : i ≤ j) :
  (ω.subdomain i : Finset _) ≤ (ω.subdomain j : Finset F) := by
  unfold FftDomain.toFinset
  intro x hx
  have h_subgroup_le : (ω.subdomain i : Subgroup Fˣ) ≤ (ω.subdomain j : Subgroup Fˣ) := by
    exact subdomain_le hij
  simp_all +decide [mem_finset_iff_exists, SetLike.le_def]
  rcases hx with ⟨a, rfl⟩
  specialize h_subgroup_le a rfl
  aesop

lemma subdomain_le_mem {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hij : i ≤ j)
  {x : F}
  (hx : x ∈ ω.subdomain i) :
  x ∈ ω.subdomain j := by
  rw [←mem_finset_iff_mem_domain] at hx
  have hx := subdomain_le_finset hij hx
  aesop (add simp [mem_domain_iff_exists, mem_finset_iff_exists])

private lemma subdomain_embed_pow_eq {n : ℕ} (i j : Fin n.succ) (hji : j.val ≤ i.val)
    (k : Fin (2 ^ i.val)) :
  (2 ^ j.val) • (subdomain_embed i k) =
      subdomain_embed ⟨i.val - j.val, by omega⟩
        ⟨k.val % 2 ^ (i.val - j.val), Nat.mod_lt _ (by positivity)⟩ := by
          simp +zetaDelta only [Nat.succ_eq_add_one] at *
          unfold subdomain_embed
          norm_num [Fin.ext_iff]
          erw [Fin.val_mk]
          -- By definition of nsmulRec, we have:
          have h_nsmulRec :
            ∀ (p : ℕ) (x : Fin (2 ^ n)),
              (nsmulRec p x : Fin (2 ^ n)).val
                = (p * x.val) % 2 ^ n := by
            intro p x
            induction' p with p ih generalizing x <;> simp +decide [*, nsmulRec]
            simp +decide [add_mul, Fin.val_add, Nat.add_mod, ih]
          rw [h_nsmulRec, ←Nat.mul_mod_mul_left]
          rw [←pow_add, tsub_tsub_assoc] <;> norm_num [hji]
          · rw [
              show n - i + i = n
                by rw [tsub_add_cancel_of_le (by linarith [Fin.is_lt i])]
            ]
            ring_nf
          · exact Fin.is_le i

omit [DecidableEq F] in
private lemma subdomain_eval {n : ℕ} {ω : SmoothFftDomain n F}
  (i : Fin n.succ) (k : Fin (2 ^ i.val)) :
  (ω.subdomain i k : F) = ω (subdomain_embed i k) := by
  simp
    [Multiplicative.ofAdd, Multiplicative.toAdd,
     subdomain, FftDomain.eval_fft_domain_eq_eval_domain, subdomain_embed]

omit [DecidableEq F] in
private lemma subdomain_pow_property_aux {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i) {k : Fin (2 ^ i.val)} :
  (ω.subdomain i k) ^ (2 ^ j.val)
    = (ω.subdomain ⟨i.val - j.val, by omega⟩ (⟨k.val % 2 ^ (i.val - j.val),
        Nat.mod_lt _ (by positivity)⟩)) := by
  rw [subdomain_eval, ←domain_nsmul, subdomain_eval, subdomain_embed_pow_eq i j hji]

omit [DecidableEq F] in
lemma subdomain_pow_property {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i) {k : Fin (2 ^ i.val)} :
  (ω.subdomain i k) ^ (2 ^ j.val)
    = (ω.subdomain (i - j) (⟨k.val % 2 ^ (i.val - j.val),
        by {
          convert Nat.mod_lt _ (pow_pos (by decide : 0 < 2) _) using 1
          simp only [Nat.succ_eq_add_one, Fin.val_sub]
          rw [Nat.mod_eq_sub_mod (by {
            norm_num [hji]
            omega
          })]
          norm_num [hji]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        }
       ⟩)) := by
  rw [subdomain_pow_property_aux hji]
  convert rfl
  · exact Fin.sub_val_of_le hji
  · exact Fin.sub_val_of_le hji
  · exact Fin.sub_val_of_le hji
  · exact Fin.sub_val_of_le hji
  · exact Fin.sub_val_of_le hji

omit [DecidableEq F] in
lemma subdomain_pow_property' {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i) {x : F}
  (h : x ∈ (ω.subdomain i)) :
  x ^ (2 ^ j.val) ∈ (ω.subdomain (i - j)) := by
  aesop (add simp [subdomain_pow_property, mem_domain_iff_exists])

lemma subdomain_roots_card {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i)
  {x : F}
  (h : x ∈ (ω.subdomain (i - j))) :
  Finset.card {y ∈ (ω.subdomain i) | y ^ (2 ^ j.val) = x}
    = 2 ^ j.val := by
  have h_bijection : Finset.card (Finset.filter (fun y ↦ y.val % 2 ^ (i.val - j.val)
    = (Classical.choose
        (FftDomain.mem_domain_iff_exists.mp h)).val)
          (Finset.univ : Finset (Fin (2 ^ i.val)))) = 2 ^ j.val := by
    rw [Finset.card_eq_of_bijective]
    · use fun k hk ↦
      ⟨(Classical.choose
          (FftDomain.mem_domain_iff_exists.mp h)).val
            + k * 2 ^ (i.val - j.val), by
      have h_card :
        (Classical.choose (FftDomain.mem_domain_iff_exists.mp h)).val < 2 ^ (i.val - j.val) := by
        convert Fin.is_lt _ using 1
        simp +decide only [Nat.succ_eq_add_one, Fin.val_sub, Nat.ofNat_pos, ne_eq, pow_right_inj₀]
        rw [Nat.mod_eq_sub_mod] <;> norm_num [Nat.sub_add_comm (show (j : ℕ) ≤ i from hji)]
        · rw [Nat.mod_eq_of_lt] <;> omega
        · omega
      rw [show (2 : ℕ) ^ (i : ℕ)
        = 2 ^ (i.val - j.val) * 2 ^ (j.val)
        by rw [←pow_add,
                Nat.sub_add_cancel (show (j : ℕ) ≤ i from hji)]]
      nlinarith [pow_pos (zero_lt_two' ℕ) (i.val - j.val)
                , pow_pos (zero_lt_two' ℕ) (j.val)]⟩
    · intro a ha
      obtain ⟨k, hk⟩ : ∃ k : ℕ, a.val
        = (Classical.choose
            (FftDomain.mem_domain_iff_exists.mp h)).val
              + k * 2 ^ (i.val - j.val) ∧ k < 2 ^ j.val := by
        norm_num +zetaDelta at *
        refine ⟨a / 2 ^ (i - j : ℕ), by {
          rw [←ha, Nat.mod_add_div']
        }, by {
          exact Nat.div_lt_of_lt_mul
            <| by {
                rw
                  [←pow_add, Nat.sub_add_cancel (show (j : ℕ) ≤ i from hji)]
                exact a.2
               }
        }⟩
      exact ⟨k, hk.2, Fin.ext hk.1.symm⟩
    · simp only [Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ, Nat.add_mod,
      Nat.mul_mod_left, add_zero, dvd_refl, Nat.mod_mod_of_dvd, true_and]
      intro k hk
      rw [Nat.mod_eq_of_lt]
      exact (by
      convert Classical.choose_spec (FftDomain.mem_domain_iff_exists.mp h)
        |> fun h ↦ Fin.is_lt _
      rw [Fin.val_sub]
      rw [Nat.mod_eq_sub_mod] <;> norm_num [Nat.sub_add_comm (show (j : ℕ) ≤ i from hji)]
      · rw [Nat.mod_eq_of_lt] <;> omega
      · omega)
    · aesop
  have h_image :
    Finset.image (fun k : Fin (2 ^ i.val) ↦ ω.subdomain i k)
      (Finset.filter
        (fun y : Fin (2 ^ i.val) ↦ y.val % 2 ^ (i.val - j.val)
          = (Classical.choose (FftDomain.mem_domain_iff_exists.mp h)).val)
        (Finset.univ : Finset (Fin (2 ^ i.val))))
          = Finset.filter
            (fun y ↦ y ^ (2 ^ j.val) = x) (ω.subdomain i).toFinset := by
    ext y
    simp only [Nat.succ_eq_add_one, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_finset_iff_exists]
    constructor <;> intro hy
    · obtain ⟨a, ha₁, ha₂⟩ := hy
      use ⟨a, ha₂⟩
      have := Classical.choose_spec
        (FftDomain.mem_domain_iff_exists.mp h)
      simp_all only [Nat.succ_eq_add_one]
      rw [←ha₂, ←this, subdomain_pow_property hji]
      exact congr_arg _ (Fin.ext ha₁)
    · obtain ⟨⟨k, rfl⟩, hk⟩ := hy
      have := Classical.choose_spec (FftDomain.mem_domain_iff_exists.mp h)
      simp_all only [Nat.succ_eq_add_one, subdomain_pow_property]
      have := ω.subdomain (i - j) |>.injective (this.trans hk.symm)
      aesop
  rw [←h_image, Finset.card_image_of_injective _ FftDomain.injective, h_bijection]

lemma subdomain_root_exists {n} {ω : SmoothFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i)
  {x : F}
  (h : x ∈ (ω.subdomain (i - j))) :
  ∃ y ∈ ω.subdomain i, y ^ (2 ^ j.val) = x := by
  have h' := subdomain_roots_card hji h
  have h' : Finset.Nonempty {y ∈ toFinset (subdomain ω i) | y ^ 2 ^ j.1 = x} := by
    rw [←Finset.card_ne_zero, h']
    simp
  simp only [Finset.Nonempty, Nat.succ_eq_add_one, Finset.mem_filter] at h'
  rcases h' with ⟨y, h'⟩
  rw [mem_finset_iff_mem_domain] at h'
  aesop

omit [DecidableEq F] in
lemma subdomain_subdomain_eq_subdomain {n} {ω : SmoothFftDomain n F}
  {i : Fin n.succ} {j : Fin i.val.succ} :
  (ω.subdomain i).subdomain j = ω.subdomain (Fin.castLE (by omega) j) := by
    ext x
    rw [subdomain_eval]
    rw [subdomain_eval]
    trans (ω (subdomain_embed (Fin.castLE (by omega) j) x))
    · simp only [subdomain_embed]
      apply congrArg
      simp only [Nat.succ_eq_add_one, Fin.val_castLE, Fin.mk.injEq]
      rw [←mul_assoc]
      rw [←pow_add]
      simp only [mul_eq_mul_right_iff, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
        pow_right_inj₀, Fin.val_eq_zero_iff]
      left
      omega
    · rfl

/-- Same as `subdomain` but takes a natural number. -/
def subdomainNat {n} (ω : SmoothFftDomain n F) (i : ℕ) :
  SmoothFftDomain (Fin.ofNat n.succ i) F :=
  ω.subdomain (Fin.ofNat n.succ i)

omit [DecidableEq F] in
@[simp]
lemma subdomainNat_zero {n} {ω : SmoothFftDomain n F}
  {x : F} :
  x ∈ ω.subdomainNat 0 ↔ x = 1 := by
    simp only [subdomainNat, mem_domain_iff_exists]; constructor
    · rintro ⟨i, rfl⟩; simp [subdomain, subdomain_embed]; norm_cast
    · intro h; subst h; exact ⟨0, by simp [subdomain, subdomain_embed]; norm_cast⟩

omit [DecidableEq F] in
@[simp]
lemma subdomainNat_n {n} {ω : SmoothFftDomain n F}
  {x : F} :
  x ∈ ω.subdomainNat n ↔ x ∈ ω := by
  simp only [subdomainNat]
  rw [←subdomain_last' (ω := ω)]
  simp

/-- Same as `subdomain` but takes a natural number and reverses the order
  of subdomains. -/
def subdomainNatReversed {n : ℕ} (ω : SmoothFftDomain n F) (i : ℕ) :
  SmoothFftDomain (n - i) F :=
  ω.subdomain ⟨n - i, by omega⟩

omit [DecidableEq F] in
@[simp]
lemma subdomainNatReversed_zero {n : ℕ} {ω : SmoothFftDomain n F}
  {x : F} :
  x ∈ ω.subdomainNatReversed 0 ↔ x ∈ ω := by
  unfold subdomainNatReversed
  rw [mem_subdomain_of_eq_vals (j := Fin.last n) (by rfl)]
  rw [←subdomain_last' (ω := ω)]
  exact mem_subdomain_of_eq_vals (by simp)

omit [DecidableEq F] in
@[simp]
lemma subdomainNatReversed_n {n : ℕ} {ω : SmoothFftDomain n F}
  {x : F} :
  x ∈ ω.subdomainNatReversed n ↔ x = 1 := by
  unfold subdomainNatReversed
  rw [mem_subdomain_of_eq_vals (j := 0) (by simp), subdomain_0']

omit [DecidableEq F] in
lemma subdomainNatReversed_sub {n : ℕ} {ω : SmoothFftDomain n F}
  {i : ℕ}
  {x : F}
  (hi : i ≤ n) :
  x ∈ ω.subdomainNatReversed (n - i) ↔ x ∈ ω.subdomainNat i := by
  unfold subdomainNatReversed subdomainNat
  rw [mem_subdomain_of_eq_vals (j := ⟨i, Nat.lt_succ_of_le hi⟩) (by {
    simp
    omega
  })]
  exact mem_subdomain_of_eq_vals (by {
    simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Fin.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega)]
  })

lemma subdomainNatReversed_root_exists {n} {ω : SmoothFftDomain n F}
  {i j : ℕ} (hij : i + j ≤ n)
  {x : F}
  (h : x ∈ (ω.subdomainNatReversed (i + j))) :
  ∃ y ∈ ω.subdomainNatReversed i, y ^ (2 ^ j) = x := by
  unfold subdomainNatReversed at *
  rw [mem_subdomain_of_eq_vals
    (j := Fin.ofNat _ (n - i) - Fin.ofNat _ j)
    (by {
      norm_num
      rw [Fin.val_sub]
      simp only [Nat.succ_eq_add_one, Fin.val_natCast, Nat.add_mod_mod]
      rw [Nat.mod_eq_of_lt (a := j) (by omega)]
      have : n + 1 - j + (n - i) = n + 1 + (n - i) - j := by omega
      rw [this, Nat.add_sub_assoc (by omega)]
      norm_num
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    })] at h
  have hh := subdomain_root_exists (by {
    simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast]
    rw [Fin.natCast_le_natCast (by omega) (by omega)]
    omega
  }) h
  rw [show (Fin.ofNat _ j) = j by { simp; omega }] at hh
  rcases hh with ⟨y, hh⟩
  exists y
  rw [mem_subdomain_of_eq_vals (j := (Fin.ofNat n.succ (n - i))) (by {
    simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Fin.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega)]
  })]
  exact hh

omit [DecidableEq F] in
lemma subdomainNatReversed_mem_of_eq {n m k} {ω : SmoothFftDomain n F}
  {x : F}
  (h : m = k) :
  x ∈ ω.subdomainNatReversed m ↔ x ∈ ω.subdomainNatReversed k := by
  aesop (add simp [subdomainNatReversed, subdomainNat])

end FftDomain

namespace CosetFftDomain

section

open FftDomain

/-- Given a smooth coset FFT domain `ω` of log-order `n` returns
  a subdomain of log-order `i`. -/
def subdomain {n : ℕ} (ω : SmoothCosetFftDomain n F) (i : Fin n.succ) :
  SmoothCosetFftDomain i F :=
  ⟨ω.x ^ 2 ^ (n - i.val), ω.fftDomain.subdomain i⟩

omit [DecidableEq F] in
lemma mem_subdomain_of_eq_vals {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {x : F}
  {i j : Fin n.succ}
  (hij : i.val = j.val) :
  x ∈ ω.subdomain i ↔ x ∈ ω.subdomain j := by rw [Fin.ext hij]

omit [DecidableEq F] in
@[simp]
lemma subdomain_x {n : ℕ} {ω : SmoothCosetFftDomain n F} (i : Fin n.succ) :
  (ω.subdomain i).x = ω.x ^ 2 ^ (n - i.val) := rfl

omit [DecidableEq F] in
@[simp]
lemma subdomain_fftDomain {n} {ω : SmoothCosetFftDomain n F}
  {i : Fin n.succ} :
  (ω.subdomain i).fftDomain = ω.fftDomain.subdomain i := by rfl

lemma subdomain_0 {n : ℕ} {ω : SmoothCosetFftDomain n F} :
  (ω.subdomain 0).toFinset = {ω.x.val ^ 2 ^ n} := by
  simp only [toFinset, Nat.succ_eq_add_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.pow_zero,
    subdomain, tsub_zero, FftDomain.subdomain, subdomain_embed, Fin.val_eq_zero, mul_zero,
    Fin.mk_zero', ofAdd_zero, map_one, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.image_singleton, Finset.singleton_inj]
  exact mul_one _

omit [DecidableEq F] in
lemma subdomain_n {n : ℕ} {ω : SmoothCosetFftDomain n F} :
  (ω.subdomain (Fin.last n)) = ω := by
  aesop
    (add simp [subdomain
    , FftDomain.subdomain
    , subdomain_embed
    , eval_coset_fft_domain_eq_eval_x_mul_domain])

omit [DecidableEq F] in
lemma subdomain_n' {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {v : F} :
  v ∈ (ω.subdomain (@Nat.cast (Fin (n + 1)) (Fin.NatCast.instNatCast (n + 1)) n)) ↔ v ∈ ω :=
  Iff.intro
    (by rintro ⟨a, rfl⟩; simp only [Nat.succ_eq_add_one, Fin.val_natCast, subdomain,
      Fin.natCast_eq_last, Fin.val_last, tsub_self, pow_zero, pow_one, mem_coset_domain,
      mem_domain_iff_exists, exists_exists_eq_and]; exact ⟨_, rfl⟩)
    (by {
      have : @Nat.cast (Fin (n + 1)) (Fin.NatCast.instNatCast (n + 1)) n = Fin.last n := by
        ext; simp [Fin.last]
      rw [this, subdomain_n]; exact id
    })

omit [DecidableEq F] in
lemma subdomain_pow_property {n} {ω : SmoothCosetFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i) {k : Fin (2 ^ i.val)} :
  (ω.subdomain i k) ^ (2 ^ j.val)
    = (ω.subdomain (i - j) (⟨k.val % 2 ^ (i.val - j.val),
        by {
          convert Nat.mod_lt _ (pow_pos (by decide : 0 < 2) _) using 1
          aesop
            (add simp [Fin.val_sub])
            (add unsafe
              [(by rw [Nat.mod_eq_of_lt]),
               (by rw [Nat.mod_eq_sub_mod])])
            (add safe (by omega))
        }
       ⟩)) := by
  simp only [Nat.succ_eq_add_one, subdomain]
  rw [eval_coset_fft_domain_eq_eval_x_mul_domain,
      eval_coset_fft_domain_eq_eval_x_mul_domain,
      Units.val_pow_eq_pow_val,
      mul_pow,
      FftDomain.subdomain_pow_property hji,
      ←pow_mul,
      ←pow_add]
  congr
  have key : n.succ - j.val + i.val = (i.val - j.val) + n.succ := by omega
  aesop
    (add simp [Fin.val_sub])
    (add safe (by omega))
    (add unsafe
      [(by rw [Nat.mod_eq_of_lt]),])

omit [DecidableEq F] in
lemma subdomain_pow_property' {n} {ω : SmoothCosetFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i) {x : F}
  (h : x ∈ (ω.subdomain i)) :
  x ^ (2 ^ j.val) ∈ (ω.subdomain (i - j)) := by
  rcases h with ⟨u, hu⟩
  aesop (add simp [subdomain_pow_property,
                   mem_domain_iff_exists,
                   mem_coset_domain])

private lemma card_filter_mod_eq' (m b : ℕ) (hbm : b ≤ m) (r : ℕ) (hr : r < 2 ^ b) :
  (Finset.filter (fun k : Fin (2 ^ m) ↦ k.val % 2 ^ b = r) Finset.univ).card = 2 ^ (m - b) := by
  rw [Finset.card_eq_of_bijective (fun i (hi : i < 2 ^ (m - b)) ↦ ⟨r + i * 2 ^ b,
    by {
      rw [show 2 ^ m = 2 ^ (m - b) * 2 ^ b by rw [←pow_add, Nat.sub_add_cancel hbm]]
      nlinarith [pow_pos (zero_lt_two' ℕ) b]
  }⟩)]
  all_goals norm_num [Fin.ext_iff, Nat.add_mod, Nat.mul_mod]
  · intro a ha
    use a / 2 ^ b
    rw [←ha]
    exact ⟨Nat.div_lt_of_lt_mul
      <| by rw [←pow_add, Nat.add_sub_of_le hbm]
            exact a.2, by rw [Nat.mod_add_div']⟩
  · exact fun i hi ↦ Nat.mod_eq_of_lt hr

lemma subdomain_roots_card {n} {ω : SmoothCosetFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i)
  {x : F}
  (h : x ∈ (ω.subdomain (i - j))) :
  Finset.card {y ∈ (ω.subdomain i).toFinset | y ^ (2 ^ j.val) = x}
    = 2 ^ j.val := by
  have hmem := mem_coset_def.mp h
  let k₀_idx := Classical.choose hmem
  have hk₀ : x = (ω.subdomain (i - j)) k₀_idx := Classical.choose_spec hmem
  -- The filter on indices whose residue matches
  have h_val_sub : (i - j : Fin n.succ).val = i.val - j.val := Fin.sub_val_of_le hji
  -- Show the image equality
  have h_image :
    Finset.image (fun k : Fin (2 ^ i.val) ↦ (ω.subdomain i) k)
      (Finset.filter
        (fun y : Fin (2 ^ i.val) ↦ y.val % 2 ^ (i.val - j.val) = k₀_idx.val)
        Finset.univ)
      = Finset.filter (fun y ↦ y ^ (2 ^ j.val) = x) (ω.subdomain i).toFinset := by
    ext y
    simp only [Nat.succ_eq_add_one, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, mem_coset_finset_iff_mem_coset_domain, mem_coset_def]
    constructor
    · rintro ⟨a, ha_mod, rfl⟩
      refine ⟨⟨a, rfl⟩, ?_⟩
      rw [subdomain_pow_property hji, hk₀]
      congr 1
      exact Fin.ext ha_mod
    · rintro ⟨⟨k, rfl⟩, hpow⟩
      refine ⟨k, ?_, rfl⟩
      have hpow' := subdomain_pow_property hji (k := k) (ω := ω)
      rw [hk₀] at hpow
      have hinj := CosetFftDomain.injective (ω := ω.subdomain (i - j))
        (hpow'.symm.trans hpow)
      simp only [Fin.ext_iff] at hinj
      exact hinj
  -- Count using the bijection
  rw [←h_image]
  rw [Finset.card_image_of_injective _ (CosetFftDomain.injective (ω := ω.subdomain i))]
  -- Now use card_filter_mod_eq'
  have hk₀_lt : k₀_idx.val < 2 ^ (i.val - j.val) := by
    have := k₀_idx.isLt
    simp only [Nat.succ_eq_add_one, h_val_sub] at this
    exact this
  rw [card_filter_mod_eq' i.val (i.val - j.val) (Nat.sub_le i.val j.val) k₀_idx.val hk₀_lt]
  congr 1
  omega

lemma subdomain_root_exists {n} {ω : SmoothCosetFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i)
  {x : F}
  (h : x ∈ (ω.subdomain (i - j))) :
  ∃ y ∈ ω.subdomain i, y ^ (2 ^ j.val) = x := by
  have h' := subdomain_roots_card hji h
  have h' : Finset.Nonempty { y ∈ (subdomain ω i).toFinset | y ^ 2 ^ j.1 = x} := by
    rw [←Finset.card_ne_zero, h']
    simp
  simp only [Finset.Nonempty, Nat.succ_eq_add_one, Finset.mem_filter] at h'
  rcases h' with ⟨y, h'⟩
  exists y
  rw [mem_coset_finset_iff_mem_coset_domain] at h'
  exact h'

omit [DecidableEq F] in
private lemma fft_neg_one_in_subgroup {n} {ω : SmoothFftDomain n F}
  {i : Fin n.succ} (hi : 0 < i) :
  ∃ k : Fin (2 ^ i.val), (ω.subdomain i k : F) = -1 := by
  -- Let's denote this element as `k = 2^(i-1) : Fin (2^i)`.
  set k : Fin (2 ^ i.val) := ⟨2 ^ (i.val - 1), by
    exact pow_lt_pow_right₀ (by decide) (Nat.pred_lt (ne_bot_of_gt hi))⟩
  generalize_proofs at *
  have h_order : (ω.subdomain i k) ^ 2 = 1 := by
    have hk_order : (ω.subdomain i k) ^ 2 = (ω.subdomain i (k + k)) := by
      rw [sq, FftDomain.subdomain]
      aesop
    convert hk_order using 1
    rw [show k + k = 0 by {
      rcases i with ⟨_ | i, hi⟩
        <;> norm_num [Fin.ext_iff, Fin.val_add, Fin.val_mul] at *
      ring_nf at *
      aesop
    }]
    aesop
  generalize_proofs at *
  (
  -- Since $k$ has additive order 2 in $\text{Fin}(2^i)$, we have $(ω.subdomain i k) \neq 1$.
  have h_ne_one : (ω.subdomain i k) ≠ 1 := by
    have h_ne_one : (ω.subdomain i k) ≠ ω.subdomain i 0 := by
      exact fun h ↦
        absurd
          (ω.subdomain i |>.injective h)
          (ne_of_gt <| Nat.lt_of_le_of_lt (Nat.zero_le _) <| pow_pos (by decide) _)
    generalize_proofs at *
    (
    exact fun h ↦ h_ne_one <| h.trans <| by simp +decide [FftDomain.subdomain] )
  generalize_proofs at *
  (exact ⟨k, Or.resolve_left (sq_eq_one_iff.mp h_order) h_ne_one⟩))

omit [DecidableEq F] in
lemma neg_mem_dom_of_mem_dom {n} {ω : SmoothCosetFftDomain n F}
  {i : Fin n.succ}
  {x : F}
  (hi : 0 < i)
  (h : x ∈ (ω.subdomain i)) :
  -x ∈ (ω.subdomain i) := by
  simp only [mem_coset_domain, FftDomain.mem_domain_iff_exists] at h ⊢
  obtain ⟨y, ⟨k, rfl⟩, rfl⟩ := h
  -- Get the element mapping to -1 in ω.fftDomain.subdomain i
  obtain ⟨k₀, hk₀⟩ := fft_neg_one_in_subgroup (F := F) (ω := ω.fftDomain) (i := i) hi
  -- -x = coset_shift * (fft(-1) * fft(k)) = coset_shift * fft(k₀ + k)
  refine ⟨(ω.subdomain i).fftDomain (k₀ + k), ⟨k₀ + k, rfl⟩, ?_⟩
  simp only [subdomain_fftDomain, FftDomain.domain_add_eq_mul_domain]
  rw [hk₀]
  ring

lemma mul_property {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {i j : Fin n.succ} (hji : j ≤ i)
  {a b : F}
  (ha : a ∈ (ω.subdomain i))
  (hb : b ∈ (ω.fftDomain.subdomain j)) :
  a * b ∈ (ω.subdomain i) := by
    rw [CosetFftDomain.mem_coset_domain] at *
    obtain ⟨y, hy, rfl⟩ := ha
    refine ⟨y * b, by {
      have h_mul : ∀ (a b : F), a ∈ (ω.fftDomain.subdomain i)
        → b ∈ (ω.fftDomain.subdomain i)
        → a * b ∈ (ω.fftDomain.subdomain i) := by
        simp only [Nat.succ_eq_add_one, mem_domain_iff_exists, forall_exists_index]
        rintro a b x rfl y rfl
        use x + y
        simp +decide [FftDomain.domain_add_eq_mul_domain]
      exact h_mul _ _ hy (by simpa using FftDomain.subdomain_le_mem hji hb)
    }, by ring⟩

/-- Same as `subdomain` but takes a natural number. -/
def subdomainNat {n : ℕ} (ω : SmoothCosetFftDomain n F) (i : ℕ) :
  SmoothCosetFftDomain (Fin.ofNat n.succ i) F :=
  ω.subdomain (Fin.ofNat n.succ i)

omit [DecidableEq F] in
@[simp]
lemma subdomainNat_zero {n} {ω : SmoothCosetFftDomain n F}
  {x : F} :
  x ∈ ω.subdomainNat 0 ↔ x = ω.x ^ 2 ^ n := by
    simp only [subdomainNat]
    rw [show Fin.ofNat n.succ 0 = (0 : Fin n.succ) from rfl]
    simp only [subdomain, Fin.val_zero, Nat.sub_zero]
    constructor
    · rintro ⟨i, rfl⟩
      simp only [eval_coset_fft_domain_eq_eval_x_mul_domain, Units.val_pow_eq_pow_val]
      have : (ω.fftDomain.subdomain 0) i = 1 :=
        FftDomain.subdomain_0'.mp ⟨i, rfl⟩
      rw [this, mul_one]
    · intro h; subst h
      exact ⟨0, by
        simp only [eval_coset_fft_domain_eq_eval_x_mul_domain, Units.val_pow_eq_pow_val]
        have : (ω.fftDomain.subdomain 0) (0 : Fin _) = 1 :=
          FftDomain.subdomain_0'.mp ⟨0, rfl⟩
        rw [this, mul_one]⟩

omit [DecidableEq F] in
@[simp]
lemma subdomainNat_n {n} {ω : SmoothCosetFftDomain n F}
  {x : F} :
  x ∈ ω.subdomainNat n ↔ x ∈ ω := by
  simp only [subdomainNat]
  rw [←subdomain_n' (ω := ω)]
  simp

/-- Same as `subdomain` but takes a natural number and reverses the order
  of subdomains. -/
def subdomainNatReversed {n : ℕ} (ω : SmoothCosetFftDomain n F) (i : ℕ) :
  SmoothCosetFftDomain (n - i) F :=
  ω.subdomain ⟨n - i, by omega⟩

omit [DecidableEq F] in
lemma subdomainNatReversed_x {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {i : ℕ}
  (hi : i ≤ n) :
  (ω.subdomainNatReversed i).x = ω.x ^ 2 ^ i := by
  simp only [Nat.succ_eq_add_one, subdomainNatReversed,
    subdomain_x]
  congr
  omega

omit [DecidableEq F] in
@[simp high]
lemma subdomainNatReversed_zero {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {x : F} :
  x ∈ ω.subdomainNatReversed 0 ↔ x ∈ ω := by
  unfold subdomainNatReversed
  rw [mem_subdomain_of_eq_vals (j := Fin.last n) (by rfl)]
  rw [←subdomain_n' (ω := ω)]
  exact mem_subdomain_of_eq_vals (by simp)

@[simp high]
lemma subdomainNatReversed_n {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {x : F} :
  x ∈ ω.subdomainNatReversed n ↔ x = ω.x ^ 2 ^ n := by
  unfold subdomainNatReversed
  rw [mem_subdomain_of_eq_vals (j := 0) (by simp)
      , ←mem_coset_finset_iff_mem_coset_domain
      , subdomain_0]
  simp

omit [DecidableEq F] in
lemma subdomainNatReversed_sub {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {i : ℕ}
  {x : F}
  (hi : i ≤ n) :
  x ∈ ω.subdomainNatReversed (n - i) ↔ x ∈ ω.subdomainNat i := by
  unfold subdomainNatReversed
  rw [mem_subdomain_of_eq_vals (j := ⟨i, Nat.lt_succ_of_le hi⟩) (by {
    simp
    omega
  })]
  exact mem_subdomain_of_eq_vals (by {
    simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Fin.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega)]
  })

omit [DecidableEq F] in
lemma subdomainNatReversed_pow_property' {n} {ω : SmoothCosetFftDomain n F}
  {i j : ℕ} (hsum : j + i ≤ n) {x : F}
  (h : x ∈ (ω.subdomainNatReversed j)) :
  x ^ (2 ^ i) ∈ (ω.subdomainNatReversed (j + i)) := by
  unfold subdomainNatReversed at *
  set i_fin : Fin n.succ := Fin.ofNat n.succ (n - j) with hi_fin_def
  set j_fin : Fin n.succ := ⟨i, by omega⟩ with hj_fin_def
  have hji : j_fin ≤ i_fin := by
    simp only [j_fin, i_fin, Fin.le_def, Fin.ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have h_eq : i_fin - j_fin = Fin.ofNat n.succ (n - (j + i)) := by
    ext
    simp only [i_fin, j_fin, Fin.val_sub, Fin.ofNat, Fin.val_mk]
    conv_lhs => rw [show (n - j) % n.succ = n - j from Nat.mod_eq_of_lt (by omega)]
    conv_lhs => rw [show n.succ - i + (n - j) = (n - (j + i)) + n.succ * 1 from by omega]
    rw [Nat.add_mul_mod_self_left]
  rw [mem_subdomain_of_eq_vals (j := i_fin) (by {
    simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Fin.val_natCast, i_fin]
    rw [Nat.mod_eq_of_lt (by omega)]
  })] at h
  have key := CosetFftDomain.subdomain_pow_property' hji h
  rw [h_eq] at key
  exact (mem_subdomain_of_eq_vals (by simp)).1 key

omit [DecidableEq F] in
lemma subdomainNatReversed_pow_property_main_domain {n} {ω : SmoothCosetFftDomain n F}
  {i : ℕ} {x : F}
  (hi : i ≤ n)
  (h : x ∈ (ω.subdomainNatReversed 0)) :
  x ^ (2 ^ i) ∈ (ω.subdomainNatReversed i) := by
  unfold subdomainNatReversed at h ⊢
  have hJ : (⟨i, by omega⟩ : Fin (n + 1)) ≤ Fin.ofNat (n + 1) (n - 0) := by
    simp [Fin.le_def, Fin.ofNat]
    omega
  have hsub : Fin.ofNat (n + 1) (n - 0) - ⟨i, by omega⟩ = Fin.ofNat (n + 1) (n - i) := by
    ext
    simp only [Fin.ofNat, Fin.sub_def, Fin.val_mk]
    rw [Nat.mod_eq_of_lt (show n - 0 < n + 1 by omega)]
    have h1 : n + 1 - i + (n - 0) = (n - 0 - i) + 1 * (n + 1) := by omega
    rw [h1, Nat.add_mul_mod_self_right]
    rw [Nat.mod_eq_of_lt (show n - 0 - i < n + 1 by omega)]
    rw [Nat.mod_eq_of_lt (show n - i < n + 1 by omega)]
    omega
  have hval : (⟨i, by omega⟩ : Fin (n + 1)).val = i := rfl
  rw [mem_subdomain_of_eq_vals (j := (Fin.ofNat (n + 1) (n - 0))) (by simp)] at h
  have key := subdomain_pow_property' hJ h
  rw [hval] at key
  exact (mem_subdomain_of_eq_vals (by {
    rw [hsub]
    simp
  })).1 key

lemma subdomainNatReversed_pow_property_main_domain_toFinset {n} {ω : SmoothCosetFftDomain n F}
  {i : ℕ} {x : F}
  (hi : i ≤ n)
  (h : x ∈ (ω.subdomainNatReversed 0).toFinset) :
  x ^ (2 ^ i) ∈ (ω.subdomainNatReversed i).toFinset := by
  rw [mem_coset_finset_iff_mem_coset_domain] at *
  exact subdomainNatReversed_pow_property_main_domain hi h

lemma subdomainNat_mul_property {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {i j : ℕ} (hji : j ≤ i) (hn : i ≤ n)
  {a b : F}
  (ha : a ∈ (ω.subdomainNat i))
  (hb : b ∈ (ω.fftDomain.subdomainNat j)) :
  a * b ∈ (ω.subdomainNat i) := by
  simp only [subdomainNat, FftDomain.subdomainNat] at *
  apply mul_property
    (j := (Fin.ofNat n.succ j))
    (by {
      simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast]
      rw [Fin.natCast_le_natCast] <;> omega
    }) <;> try tauto

lemma subdomainNatReversed_mul_property {n : ℕ} {ω : SmoothCosetFftDomain n F}
  {i j : ℕ} (hji : j ≤ i) (hn : i ≤ n)
  {a b : F}
  (ha : a ∈ (ω.subdomainNatReversed j))
  (hb : b ∈ (ω.fftDomain.subdomainNatReversed i)) :
  a * b ∈ (ω.subdomainNatReversed j) := by
  simp only [subdomainNatReversed, FftDomain.subdomainNatReversed] at *
  have h := subdomainNat_mul_property (ω := ω) (i := n - j) (j := n - i) (by omega) (by omega) (by {
    simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Fin.val_natCast, subdomainNat]
    exact (mem_subdomain_of_eq_vals (by {
      simp only [Nat.succ_eq_add_one, Fin.val_natCast]
      rw [Nat.mod_eq_of_lt (by omega)]
    })).1 ha
  }) (by {
    simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Fin.val_natCast, FftDomain.subdomainNat]
    exact (FftDomain.mem_subdomain_of_eq_vals (by {
      simp only [Nat.succ_eq_add_one, Fin.val_natCast]
      rw [Nat.mod_eq_of_lt (by omega)]
    })).1 hb
  })
  exact (mem_subdomain_of_eq_vals (by simp)).1 h


lemma subdomainNatReversed_root_exists {n} {ω : SmoothCosetFftDomain n F}
  {i j : ℕ} (hij : i + j ≤ n)
  {x : F}
  (h : x ∈ (ω.subdomainNatReversed (i + j))) :
  ∃ y ∈ ω.subdomainNatReversed i, y ^ (2 ^ j) = x := by
  unfold subdomainNatReversed  at *
  rw [mem_subdomain_of_eq_vals
    (j := Fin.ofNat _ (n - i) - Fin.ofNat _ j)
    (by {
      norm_num
      rw [Fin.val_sub]
      simp only [Nat.succ_eq_add_one, Fin.val_natCast, Nat.add_mod_mod]
      rw [Nat.mod_eq_of_lt (a := j) (by omega)]
      have : n + 1 - j + (n - i) = n + 1 + (n - i) - j := by omega
      rw [this, Nat.add_sub_assoc (by omega)]
      norm_num
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    })] at h
  have hh := subdomain_root_exists (by {
    simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast]
    rw [Fin.natCast_le_natCast (by omega) (by omega)]
    omega
  }) h
  rw [show (Fin.ofNat _ j) = j by { simp; omega }] at hh
  rcases hh with ⟨y, hh⟩
  exists y
  rw [mem_subdomain_of_eq_vals (j := (Fin.ofNat n.succ (n - i))) (by {
    simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Fin.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega)]
  })]
  exact hh

omit [DecidableEq F] in
lemma subdomainNatReversed_mem_of_eq {n m k} {ω : SmoothCosetFftDomain n F}
  {x : F}
  (h : m = k) :
  x ∈ ω.subdomainNatReversed m ↔ x ∈ ω.subdomainNatReversed k := by
  aesop (add simp [subdomainNatReversed, subdomainNat])

end

end CosetFftDomain

end ReedSolomon
