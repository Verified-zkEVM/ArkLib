/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Normed.Field.Lemmas
import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
/-!
# List Decodability

The *point list* of a code `C` around a word `f` at radius `δ` is the set of codewords within
relative Hamming distance `δ` of `f`. This file defines it and the two shapes of bound on its
size: the `∀`-form predicate `listDecodable`, and the `sup`-form quantity `Lambda`.

## Main definitions

* `ListDecodable.closeCodewords`, `ListDecodable.closeCodewordsRel` — the codewords of `C`
  inside a Hamming ball, at absolute and relative radius. Both are defined under
  `open Classical in`, so they expose no decidability data.
* `ListDecodable.listDecodable`, `ListDecodable.uniqueDecodable` — `(r, ℓ)`-list
  decodability at a real list size `ℓ`, and its `ℓ = 1` special case.
* `ListDecodable.Lambda` — the maximised list size `⨆ f, |closeCodewordsRel C f δ| : ℕ∞`.

## Main statements

* `ListDecodable.Lambda_le_iff_listDecodable` — the two shapes agree, at a natural list size.
* `ListDecodable.Lambda_le_floor_iff_listDecodable`,
  `ListDecodable.Lambda_le_floor_iff_listDecodable_nnreal`,
  `ListDecodable.listDecodable_of_toENNReal_le_ofReal` — the same bridge at a real, an `ℝ≥0`,
  and an `ENNReal` list size.
* `ListDecodable.listDecodable_of_forall_finset_card_le` — the primitive constructor: a
  uniform bound on the *finite subsets* of a point list establishes `listDecodable` outright,
  finiteness included, over an arbitrary alphabet.
* `ListDecodable.Lambda_mono`, `Lambda_le_ncard`, `Lambda_le_card`, `Lambda_ne_top` — basic
  algebra of `Lambda`.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed–Solomon Proximity Testing
    with Fewer Queries*][ACFY24stir]
-/


namespace ListDecodable

open scoped NNReal

section

variable {ι : Type*} [Fintype ι]
         {F : Type*}

abbrev Code.{u, v} (ι : Type u) (S : Type v) : Type (max u v) := Set (ι → S)

open Classical in
/-- The set of `r`-close codewords to a given word `y` with respect to the Hamming distance. -/
def closeCodewords (C : Code ι F) (y : ι → F) (r : ℕ) : Set (ι → F) :=
  {c | c ∈ C ∧ c ∈ Code.hammingBall y r}

open Classical in
/-- The set of `r`-close codewords to a given word `y` with respect to the relative Hamming
distance.
Note that this is exactly `Λ (C, y, r)` from [ACFY24] and ` List (C, y, r)` from [ACFY24stir]. -/
def closeCodewordsRel (C : Code ι F) (y : ι → F) (r : ℝ) : Set (ι → F) :=
  {c | c ∈ C ∧ c ∈ Code.relHammingBall y r}

/-- A code `C` is `(r, ℓ)`-**list decodable** if every point list at relative radius `r` is
finite and has cardinality at most the real bound `ℓ`.

The finiteness conjunct is necessary because `Set.ncard` assigns cardinality zero to infinite
sets, which would make the bound vacuous over an infinite alphabet. The bound is kept real
rather than natural to accommodate the Johnson bounds; flooring it is lossless
(`Lambda_le_floor_iff_listDecodable`). -/
def listDecodable (C : Code ι F) (r : ℝ) (ℓ : ℝ) : Prop :=
  ∀ y : ι → F,
    (closeCodewordsRel C y r).Finite ∧ (closeCodewordsRel C y r).ncard ≤ ℓ

/-- A code `C` is uniquely decodable up to a relative distance `r` if for any word `y : ι → F`,
there is at most one codeword in `C` within a relative Hamming distance of `r`.
This is a special case of list decodability where the list size `ℓ` is `1`. -/
def uniqueDecodable (C : Code ι F) (r : ℝ) : Prop :=
  listDecodable C r 1

end

/-! ## The maximised list size -/

section Lambda

variable {ι : Type*} [Fintype ι] {F : Type*}

/-- The maximised list size of `C` at radius `δ`: the supremum over words `f` of the
cardinality of the point list `closeCodewordsRel C f δ`.

Membership in `closeCodewordsRel C f δ` is `δᵣ(f, ·) ≤ δ`, and relative Hamming distance is
`1/n`-quantised for `n = |ι|` (`relHammingDistRange`), so `Lambda C` is a step function of
`δ`, constant on each cell `[k/n, (k+1)/n)`. An extremal "largest `δ`" is therefore only
meaningful as an integer boundary index `k/n`, not as a real number.

`Set.encard` is used rather than `Set.ncard`, so an infinite point list contributes `⊤`
rather than silently collapsing to `0`. -/
noncomputable def Lambda (C : Code ι F) (δ : ℝ) : ℕ∞ :=
  ⨆ f : ι → F, (closeCodewordsRel C f δ).encard

/-- `Lambda` and `listDecodable` are two shapes of the same notion: at a natural list-size
bound `ℓ`, the maximised list size is at most `ℓ` iff `C` is `(δ, ℓ)`-list-decodable.

Since `listDecodable` takes a real list size, this equivalence alone does not transfer bounds
stated at other numeric types; see `Lambda_le_floor_iff_listDecodable`,
`Lambda_le_floor_iff_listDecodable_nnreal` and `listDecodable_of_toENNReal_le_ofReal`. -/
lemma Lambda_le_iff_listDecodable {C : Code ι F} {δ : ℝ} {ℓ : ℕ} :
    Lambda C δ ≤ (ℓ : ℕ∞) ↔ listDecodable C δ (ℓ : ℝ) := by
  simp only [Lambda, iSup_le_iff, listDecodable]
  constructor
  · intro h f
    have hfin : (closeCodewordsRel C f δ).Finite := Set.finite_of_encard_le_coe (h f)
    exact ⟨hfin, by exact_mod_cast (hfin.cast_ncard_eq ▸ h f)⟩
  · intro h f
    rw [← (h f).1.cast_ncard_eq]
    exact_mod_cast (h f).2

/-- At a nonnegative real list size `ℓ`, the maximised list size is at most `⌊ℓ⌋₊` iff `C` is
`(δ, ℓ)`-list-decodable.

The floor is the correct rounding in both directions, which is what makes this an `↔`: since
`Lambda` is integer-valued, `(Lambda C δ : ℝ) ≤ ℓ` is equivalent to `Lambda C δ ≤ ⌊ℓ⌋₊`. A
ceiling would give only `←`. The hypothesis `0 ≤ ℓ` is needed only for `→`; see
`Lambda_le_floor_of_listDecodable` for the hypothesis-free converse. -/
lemma Lambda_le_floor_iff_listDecodable {C : Code ι F} {δ : ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) :
    Lambda C δ ≤ (⌊ℓ⌋₊ : ℕ∞) ↔ listDecodable C δ ℓ := by
  rw [Lambda_le_iff_listDecodable]
  constructor
  · intro h y
    exact ⟨(h y).1, (h y).2.trans (Nat.floor_le hℓ)⟩
  · intro h y
    exact ⟨(h y).1, by exact_mod_cast Nat.le_floor (h y).2⟩

/-- The hypothesis-free direction of `Lambda_le_floor_iff_listDecodable`: a real-valued
list-decodability bound always floors down to a `Lambda` bound. -/
lemma Lambda_le_floor_of_listDecodable {C : Code ι F} {δ : ℝ} {ℓ : ℝ}
    (h : listDecodable C δ ℓ) : Lambda C δ ≤ (⌊ℓ⌋₊ : ℕ∞) :=
  Lambda_le_iff_listDecodable.2 fun y =>
    ⟨(h y).1, by exact_mod_cast Nat.le_floor (h y).2⟩

/-- `Lambda_le_floor_iff_listDecodable` at an `ℝ≥0` list size, where the nonnegativity side
condition is automatic. -/
lemma Lambda_le_floor_iff_listDecodable_nnreal {C : Code ι F} {δ : ℝ} {ℓ : ℝ≥0} :
    Lambda C δ ≤ (⌊(ℓ : ℝ)⌋₊ : ℕ∞) ↔ listDecodable C δ (ℓ : ℝ) :=
  Lambda_le_floor_iff_listDecodable ℓ.coe_nonneg

/-- The primitive constructor for `listDecodable`: if every *finite* set of codewords inside
the radius-`r` ball around `y` has at most `ℓ` elements, uniformly in `y`, then `C` is
`(r, ℓ)`-list decodable, finiteness of the point list included.

This is the shape a list-decoding counting argument naturally produces: it fixes a finite
family of close codewords and bounds its cardinality. Both conjuncts of `listDecodable` follow
at once, since an infinite set has finite subsets of every cardinality
(`Set.Infinite.exists_subset_card_eq`).

No finiteness of the alphabet is required, so this delivers genuine finiteness of the point
list rather than an ambient one. -/
lemma listDecodable_of_forall_finset_card_le {C : Code ι F} {r ℓ : ℝ}
    (h : ∀ (y : ι → F) (T : Finset (ι → F)), (∀ c ∈ T, c ∈ closeCodewordsRel C y r) →
      (T.card : ℝ) ≤ ℓ) :
    listDecodable C r ℓ := by
  intro y
  have hfin : (closeCodewordsRel C y r).Finite := by
    by_contra hinf
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊ℓ⌋₊ + 1)
    have hle := h y T fun c hc => hTsub hc
    rw [hTcard] at hle
    have hlt : ℓ < ((⌊ℓ⌋₊ : ℝ) + 1) := Nat.lt_floor_add_one ℓ
    push_cast at hle
    linarith
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact h y hfin.toFinset fun c hc => hfin.mem_toFinset.mp hc

/-- A natural-number bound on `Lambda` gives `(δ, r)`-list decodability at every real `r`
above it. No finiteness of the alphabet is needed: the `Lambda` bound itself forces every
point list finite. -/
lemma listDecodable_of_Lambda_le_natCast {C : Code ι F} {δ : ℝ} {ℓ : ℕ} {r : ℝ}
    (h : Lambda C δ ≤ (ℓ : ℕ∞)) (hr : (ℓ : ℝ) ≤ r) : listDecodable C δ r := by
  intro y
  have hy : (closeCodewordsRel C y δ).encard ≤ (ℓ : ℕ∞) :=
    (le_iSup (fun g : ι → F => (closeCodewordsRel C g δ).encard) y).trans h
  have hfin : (closeCodewordsRel C y δ).Finite := Set.finite_of_encard_le_coe hy
  have hn : (closeCodewordsRel C y δ).ncard ≤ ℓ := by
    exact_mod_cast hfin.cast_ncard_eq ▸ hy
  exact ⟨hfin, le_trans (by exact_mod_cast hn) hr⟩

/-- An `ENNReal.ofReal` bound on `Lambda` floors down to a `Lambda` bound at `⌊ℓ⌋₊`.

`0 ≤ ℓ` is required, `ENNReal.ofReal` clamping negative reals to `0`. No finiteness of the
alphabet is needed: the hypothesis bounds every point list by `ENNReal.ofReal ℓ ≠ ⊤`. -/
lemma Lambda_le_floor_of_toENNReal_le_ofReal {C : Code ι F} {δ : ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ)
    (h : (Lambda C δ : ENNReal) ≤ ENNReal.ofReal ℓ) : Lambda C δ ≤ (⌊ℓ⌋₊ : ℕ∞) := by
  refine iSup_le fun f => ?_
  have hpoint : (closeCodewordsRel C f δ).encard ≤ Lambda C δ :=
    le_iSup (fun g : ι → F => (closeCodewordsRel C g δ).encard) f
  have hpoint' : ((closeCodewordsRel C f δ).encard : ENNReal) ≤ (Lambda C δ : ENNReal) := by
    exact_mod_cast hpoint
  have hfin : (closeCodewordsRel C f δ).Finite := by
    refine Set.encard_ne_top_iff.mp fun htop => ?_
    have hle := hpoint'.trans h
    rw [htop] at hle
    simp at hle
  have hnatcast (n : ℕ) : ((n : ℕ∞) : ENNReal) = ENNReal.ofReal (n : ℝ) := by
    rw [ENNReal.ofReal_natCast]
    rfl
  have hcast : ((closeCodewordsRel C f δ).encard : ENNReal) =
      ENNReal.ofReal (((closeCodewordsRel C f δ).ncard : ℕ) : ℝ) := by
    calc
      ((closeCodewordsRel C f δ).encard : ENNReal) =
          ((((closeCodewordsRel C f δ).ncard : ℕ) : ℕ∞) : ENNReal) :=
        congrArg (fun x : ℕ∞ => (x : ENNReal)) hfin.cast_ncard_eq.symm
      _ = ENNReal.ofReal (((closeCodewordsRel C f δ).ncard : ℕ) : ℝ) :=
        hnatcast (closeCodewordsRel C f δ).ncard
  have h1 : ENNReal.ofReal (((closeCodewordsRel C f δ).ncard : ℕ) : ℝ) ≤
      ENNReal.ofReal ℓ := by
    rw [← hcast]
    exact hpoint'.trans h
  have h2 : (((closeCodewordsRel C f δ).ncard : ℕ) : ℝ) ≤ ℓ := by
    exact (ENNReal.ofReal_le_ofReal_iff hℓ).mp h1
  calc
    (closeCodewordsRel C f δ).encard =
        ((closeCodewordsRel C f δ).ncard : ℕ∞) := hfin.cast_ncard_eq.symm
    _ ≤ (⌊ℓ⌋₊ : ℕ∞) := by exact_mod_cast Nat.le_floor h2

/-- An `ENNReal.ofReal` bound on `Lambda` yields `listDecodable` at the same radius and list
size, by composing `Lambda_le_floor_of_toENNReal_le_ofReal` with
`listDecodable_of_Lambda_le_natCast`. -/
lemma listDecodable_of_toENNReal_le_ofReal {C : Code ι F} {δ : ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ)
    (h : (Lambda C δ : ENNReal) ≤ ENNReal.ofReal ℓ) : listDecodable C δ ℓ :=
  listDecodable_of_Lambda_le_natCast (Lambda_le_floor_of_toENNReal_le_ofReal hℓ h)
    (Nat.floor_le hℓ)

/-- The point list is monotone in the radius. -/
lemma closeCodewordsRel_subset_of_le {C : Code ι F} {δ₁ δ₂ : ℝ}
    (h : δ₁ ≤ δ₂) (f : ι → F) :
    closeCodewordsRel C f δ₁ ⊆ closeCodewordsRel C f δ₂ := by
  intro c hc
  exact ⟨hc.1, le_trans hc.2 h⟩

/-- `Lambda` is monotone in the radius. -/
lemma Lambda_mono {C : Code ι F} {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) :
    Lambda C δ₁ ≤ Lambda C δ₂ := by
  refine iSup_mono fun f => ?_
  exact Set.encard_mono (closeCodewordsRel_subset_of_le h f)

/-- Every element of a point list is a codeword. -/
lemma closeCodewordsRel_subset_code {C : Code ι F} (δ : ℝ) (f : ι → F) :
    closeCodewordsRel C f δ ⊆ C := fun _ hc => hc.1

/-- A point list of a finite code is no larger than the code. -/
lemma ncard_closeCodewordsRel_le_ncard {C : Code ι F} (δ : ℝ) (f : ι → F) (hC : C.Finite) :
    (closeCodewordsRel C f δ).ncard ≤ C.ncard :=
  Set.ncard_le_ncard (closeCodewordsRel_subset_code δ f) hC

/-- The maximised list size of a finite code is no larger than the code. -/
lemma Lambda_le_ncard {C : Code ι F} (δ : ℝ) (hC : C.Finite) :
    Lambda C δ ≤ (C.ncard : ℕ∞) := by
  refine iSup_le fun f => ?_
  calc
    (closeCodewordsRel C f δ).encard ≤ C.encard :=
      Set.encard_mono (closeCodewordsRel_subset_code δ f)
    _ = (C.ncard : ℕ∞) := hC.cast_ncard_eq.symm

/-- The maximised list size is bounded by the total number of words, each point list being a
set of words. Stated with `Nat.card`, so no `Fintype (ι → F)` instance is needed. -/
lemma Lambda_le_card {C : Code ι F} [Finite F] (δ : ℝ) :
    Lambda C δ ≤ (Nat.card (ι → F) : ℕ∞) := by
  refine iSup_le fun f => ?_
  calc
    (closeCodewordsRel C f δ).encard ≤ (Set.univ : Set (ι → F)).encard :=
      Set.encard_mono (Set.subset_univ _)
    _ = ((Set.univ : Set (ι → F)).ncard : ℕ∞) := Set.finite_univ.cast_ncard_eq.symm
    _ = (Nat.card (ι → F) : ℕ∞) := by rw [Set.ncard_univ]

/-- Over a finite alphabet the maximised list size never reaches `⊤`, being bounded by the
total number of words. Useful before moving `Lambda` into `ℕ` via `ENat.toNat`, which
collapses `⊤` to `0`. -/
lemma Lambda_ne_top {C : Code ι F} [Finite F] (δ : ℝ) :
    Lambda C δ ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (Lambda_le_card δ)

end Lambda

end ListDecodable
