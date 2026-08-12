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

Hamming balls, the list of close codewords around a word, and the two shapes of list-size
bound used in ArkLib: the `∀`-form `listDecodable` (consumed by the STIR development) and
the `sup`-form `Lambda` (ABF26 Definition 2.8's `|Λ(C, δ)|`).

## Main definitions

* `ListDecodable.closeCodewords` / `ListDecodable.closeCodewordsRel` — the codewords of `C`
  inside a Hamming ball (`Code.hammingBall` / `Code.relHammingBall`, from
  `Basic/Distance.lean` and `Basic/RelativeDistance.lean`); `closeCodewordsRel` is the
  paper's point list `Λ(C, δ, f)`. Both are defined under `open Classical in`, so they
  expose no decidability data.
* `ListDecodable.listDecodable` / `ListDecodable.uniqueDecodable` — `(r, ℓ)`-list
  decodability with a *real* list size `ℓ`, and its `ℓ = 1` special case.
* `ListDecodable.Lambda` — ABF26 Definition 2.8's maximised list size `|Λ(C, δ)| : ℕ∞`.

## Main statements

* `ListDecodable.Lambda_le_iff_listDecodable` — the two shapes agree, at a *natural* list
  size.
* `ListDecodable.Lambda_le_floor_iff_listDecodable`,
  `ListDecodable.Lambda_le_floor_iff_listDecodable_nnreal`,
  `ListDecodable.listDecodable_of_toENNReal_le_ofReal` — the same bridge at the *real* and
  `ℝ≥0` list sizes that the in-tree consumers and the Johnson-family bounds actually use.
* `ListDecodable.listDecodable_of_forall_finset_card_le` — the primitive constructor: a uniform
  bound on the *finite subsets* of a point list establishes `listDecodable` outright, finiteness
  included, over an arbitrary alphabet.
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

/-- A code `C` is `(r,ℓ)`-list decodable: every relative-radius-`r` point list is finite and
has cardinality at most the real bound `ℓ`.

The explicit finiteness conjunct is necessary because `Set.ncard` alone assigns cardinality
zero to infinite sets. Keeping the bound real-valued accommodates Johnson-bound consumers,
while recording finiteness makes the predicate meaningful over arbitrary alphabets and allows
lossless flooring to a natural list bound. -/
def listDecodable (C : Code ι F) (r : ℝ) (ℓ : ℝ) : Prop :=
  ∀ y : ι → F,
    (closeCodewordsRel C y r).Finite ∧ (closeCodewordsRel C y r).ncard ≤ ℓ

/-- A code `C` is uniquely decodable up to a relative distance `r` if for any word `y : ι → F`,
there is at most one codeword in `C` within a relative Hamming distance of `r`.
This is a special case of list decodability where the list size `ℓ` is `1`. -/
def uniqueDecodable (C : Code ι F) (r : ℝ) : Prop :=
  listDecodable C r 1

end

/-! ## ABF26 Definition 2.8 — list around a word `Λ(C, δ, f)` and `|Λ(C, δ)|`

The paper writes `Λ(C, δ, f)` for the set of codewords of `C` whose relative Hamming distance
from `f` is at most `δ`, and `|Λ(C, δ)| = max_f |Λ(C, δ, f)|` for the maximised list size.
The point list `Λ(C, δ, f)` is already provided by `closeCodewordsRel C f δ` (see above); we
do *not* introduce a paper-named alias for it. The new content here is `Lambda`, the maximised
form used by Section 4's `ε_mca` (ABF26 Definition 4.3) and Section 3's list-decoding bounds.

The basic algebra here (monotonicity, codeword-set bound) covers what is needed to state
`ε_mca` (ABF26 Definition 4.3) in the forthcoming proximity-gap layer. The full theory of
`Lambda` — Johnson bound restatement, the interleaved-code list-size bound (ABF26
Lemma 2.10), generalized Singleton, volume-based lower bounds — is the subject of ABF26 §3;
the Johnson family bounds land in `JohnsonBound/Family.lean` in this layer, the rest with
the proximity-gap development.
-/

section Lambda

variable {ι : Type*} [Fintype ι] {F : Type*}

/-- **ABF26 Definition 2.8 (maximised list size).** The supremum over words `f` of
`|Λ(C, δ, f)| = |closeCodewordsRel C f δ|` (a maximum in the paper's finite-alphabet setting).
Named to match the paper's `|Λ(C, δ)|`.

Membership in `closeCodewordsRel C f δ` is `δᵣ(f, ·) ≤ δ`, and relative Hamming distance is
`1/n`-quantised (`n := |ι|`, `relHammingDistRange`), so `Λ(C, ·)` is a step function of `δ`,
constant on each cell `[k/n, (k+1)/n)`. Read `δ`-indexed list-decoding statements modulo
this quantisation: an extremal "largest `δ*`" is only meaningful as an integer boundary
index `k*/n`, not as a real number (the ABF26 grand-challenge layer, arriving in a later
split, pins its list challenge that way).

`Set.encard` is used rather than `Set.ncard`, so an infinite point list contributes `⊤`
rather than silently collapsing to `0`. The real-valued `listDecodable` predicate records
point-list finiteness explicitly, so its bridges with finite `Lambda` bounds are instance-free
in both directions, even over an infinite alphabet. -/
noncomputable def Lambda (C : Code ι F) (δ : ℝ) : ℕ∞ :=
  ⨆ f : ι → F, (closeCodewordsRel C f δ).encard

/-- **Bridge to `listDecodable`, at a natural list size.** `Lambda` is the sup-form of the
same notion as the ∀-form `listDecodable` above (consumed by the STIR development): for a
*natural* list-size bound `ℓ`, the maximised list size `Λ(C, δ)` is at most `ℓ` iff `C` is
`(δ, ℓ)`-list-decodable.

`listDecodable`'s list size is a *real* number, and every in-tree consumer instantiates it at
`ℝ≥0` (`ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean`, `ArkLib/ProofSystem/Stir/MainThm.lean`),
while the Johnson-family bounds of `JohnsonBound/Family.lean` produce an `ENNReal.ofReal`
bound. This `ℕ`-shaped equivalence alone therefore does **not** carry those bounds across; the
real-, `ℝ≥0`- and `ENNReal`-shaped transfers are `Lambda_le_floor_iff_listDecodable`,
`Lambda_le_floor_iff_listDecodable_nnreal` and `listDecodable_of_toENNReal_le_ofReal`
below. -/
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

/-- **Bridge to `listDecodable` at a real list size.** For `0 ≤ ℓ` the maximised list size is
at most `⌊ℓ⌋₊` iff `C` is `(δ, ℓ)`-list-decodable.

The **floor** is the correct rounding in both directions, and this is what makes the statement
an `↔` rather than a pair of one-way implications: `Lambda` is integer-valued, so
`(|Λ| : ℝ) ≤ ℓ` is equivalent to `|Λ| ≤ ⌊ℓ⌋₊` (`Nat.le_floor` / `Nat.floor_le`). A ceiling
would give only the `←` direction. The hypothesis `0 ≤ ℓ` is needed for `→` only (at `ℓ < 0`,
`⌊ℓ⌋₊ = 0` and the conclusion `(0 : ℝ) ≤ ℓ` fails); the `←` direction is hypothesis-free and
is available separately as `Lambda_le_floor_of_listDecodable`. -/
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

/-- **Bridge to `listDecodable` at an `ℝ≥0` list size** — the shape the in-tree consumers use
(`ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean`, `ArkLib/ProofSystem/Stir/MainThm.lean` both take
`ℓ : ℝ≥0`). No side condition, since `ℝ≥0` is nonnegative by construction. -/
lemma Lambda_le_floor_iff_listDecodable_nnreal {C : Code ι F} {δ : ℝ} {ℓ : ℝ≥0} :
    Lambda C δ ≤ (⌊(ℓ : ℝ)⌋₊ : ℕ∞) ↔ listDecodable C δ (ℓ : ℝ) :=
  Lambda_le_floor_iff_listDecodable ℓ.coe_nonneg

/-- **The primitive way to establish `listDecodable`: bound the *finite subsets* of the point
list.** If every finite set of codewords inside the radius-`r` ball around `y` has at most `ℓ`
elements — uniformly in `y` — then `C` is `(r, ℓ)`-list decodable, finiteness of the point list
included.

This is the constructor that the four `Lambda`-to-`listDecodable` bridges above do *not* cover:
they transfer a bound already established for `Lambda`, whereas a list-decoding counting
argument (Johnson, Plotkin, the Guruswami–Sudan-style interpolation counts) naturally produces
exactly this shape — it fixes a finite family of close codewords and bounds its cardinality.
Both hypotheses of `listDecodable` come out at once: a uniform bound on finite subsets forces
the whole point list finite, since an infinite set has finite subsets of every cardinality
(`Set.Infinite.exists_subset_card_eq`).

**No finiteness on the alphabet is required, and that is the point.** `listDecodable` used to be
`∀ y, (closeCodewordsRel C y r).ncard ≤ ℓ`, which an *infinite* point list satisfies vacuously
because `Set.ncard` returns `0` there; the `Finite` conjunct closes that hole. Over a finite
alphabet the conjunct is free (`Set.toFinite _`), so it would be tempting to offer an
`[Finite F]` escape hatch instead — but that would hand back the very move the conjunct exists
to prevent, and it would push a proof into assuming a finite alphabet it does not otherwise
need. This lemma asks for the finite-subset bound the counting argument already has, and
delivers the real finiteness rather than an ambient one. -/
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

/-- **Monotone cast corollary.** A natural-number `Lambda` bound gives `(δ, r)`-list
decodability for every real `r` above it. This is the form in which a `ℕ`-valued bound such as
`JohnsonBound.johnson_bound_lambda_le_ell` reaches a real- or `ℝ≥0`-valued consumer.

No `[Finite F]`: the `Lambda` bound itself forces every point list finite
(`Set.finite_of_encard_le_coe`), which is all this direction of the bridge needs. -/
lemma listDecodable_of_Lambda_le_natCast {C : Code ι F} {δ : ℝ} {ℓ : ℕ} {r : ℝ}
    (h : Lambda C δ ≤ (ℓ : ℕ∞)) (hr : (ℓ : ℝ) ≤ r) : listDecodable C δ r := by
  intro y
  have hy : (closeCodewordsRel C y δ).encard ≤ (ℓ : ℕ∞) :=
    (le_iSup (fun g : ι → F => (closeCodewordsRel C g δ).encard) y).trans h
  have hfin : (closeCodewordsRel C y δ).Finite := Set.finite_of_encard_le_coe hy
  have hn : (closeCodewordsRel C y δ).ncard ≤ ℓ := by
    exact_mod_cast hfin.cast_ncard_eq ▸ hy
  exact ⟨hfin, le_trans (by exact_mod_cast hn) hr⟩

/-- **Bridge from an `ENNReal` bound on `Lambda`** — the shape produced by the Johnson-family
bounds (e.g. `JohnsonBound.mds_johnson_lambda_le`, which concludes
`(Lambda C δ : ENNReal) ≤ ENNReal.ofReal b`). Floors the real bound down to a `Lambda` bound.

`0 ≤ ℓ` is required: `ENNReal.ofReal` clamps negative reals to `0`. No `[Finite F]`: the
hypothesis bounds every point list by `ENNReal.ofReal ℓ ≠ ⊤`, which forces it finite. -/
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

/-- **The `ENNReal`-to-`listDecodable` transfer.** Composes
`Lambda_le_floor_of_toENNReal_le_ofReal` with `listDecodable_of_Lambda_le_natCast`, so an
`ENNReal.ofReal` Johnson-style bound on `Lambda` directly yields `listDecodable` at the same
real radius and list size. Like both ingredients, instance-free: this is the
*`Lambda`-bound → `listDecodable`* direction, where the bound forces finiteness. -/
lemma listDecodable_of_toENNReal_le_ofReal {C : Code ι F} {δ : ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ)
    (h : (Lambda C δ : ENNReal) ≤ ENNReal.ofReal ℓ) : listDecodable C δ ℓ :=
  listDecodable_of_Lambda_le_natCast (Lambda_le_floor_of_toENNReal_le_ofReal hℓ h)
    (Nat.floor_le hℓ)

/-- The point list `Λ(C, δ, f) = closeCodewordsRel C f δ` is monotone in the radius. -/
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

/-- Any element of `Λ(C, δ, f) = closeCodewordsRel C f δ` is a codeword of `C`. -/
lemma closeCodewordsRel_subset_code {C : Code ι F} (δ : ℝ) (f : ι → F) :
    closeCodewordsRel C f δ ⊆ C := fun _ hc => hc.1

/-- `|Λ(C, δ, f)| ≤ |C|` for finite `C`. -/
lemma ncard_closeCodewordsRel_le_ncard {C : Code ι F} (δ : ℝ) (f : ι → F) (hC : C.Finite) :
    (closeCodewordsRel C f δ).ncard ≤ C.ncard :=
  Set.ncard_le_ncard (closeCodewordsRel_subset_code δ f) hC

/-- `|Λ(C, δ)| ≤ |C|` for finite `C`. -/
lemma Lambda_le_ncard {C : Code ι F} (δ : ℝ) (hC : C.Finite) :
    Lambda C δ ≤ (C.ncard : ℕ∞) := by
  refine iSup_le fun f => ?_
  calc
    (closeCodewordsRel C f δ).encard ≤ C.encard :=
      Set.encard_mono (closeCodewordsRel_subset_code δ f)
    _ = (C.ncard : ℕ∞) := hC.cast_ncard_eq.symm

/-- `|Λ(C, δ)| ≤ |F^ι|`: each point list is a set of words, so the maximised
list size is bounded by the total number of words. Stated with `Nat.card`
under `[Finite F]` (no `Fintype (ι → F)` instance needed). -/
lemma Lambda_le_card {C : Code ι F} [Finite F] (δ : ℝ) :
    Lambda C δ ≤ (Nat.card (ι → F) : ℕ∞) := by
  refine iSup_le fun f => ?_
  calc
    (closeCodewordsRel C f δ).encard ≤ (Set.univ : Set (ι → F)).encard :=
      Set.encard_mono (Set.subset_univ _)
    _ = ((Set.univ : Set (ι → F)).ncard : ℕ∞) := Set.finite_univ.cast_ncard_eq.symm
    _ = (Nat.card (ι → F) : ℕ∞) := by rw [Set.ncard_univ]

/-- `|Λ(C, δ)|` is **finite** over a finite alphabet: it is bounded by `|F^ι|`, so it never
reaches `⊤`. Intended for consumers that need to move `Lambda` into `ℕ` via `ENat.toNat`,
which collapses `⊤` to `0`; there are no such consumers in the tree yet. -/
lemma Lambda_ne_top {C : Code ι F} [Finite F] (δ : ℝ) :
    Lambda C δ ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (Lambda_le_card δ)

end Lambda

end ListDecodable
