/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Alexander Hicks, Ilia Vlasov
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Normed.Field.Lemmas
import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.ToMathlib.Set.Finite
/-!
# List Decodability

The *point list* of a code `C` around a word `f` at radius `δ` is the set of codewords within
relative Hamming distance `δ` of `f`. This file defines it, its size, and list decodability.

The size is the primitive: `Lambda C δ : ℕ∞` is the maximised point-list size, and
`IsListDecodable` is a `def` whose body is the inequality `Lambda C r ≤ ⌊ℓ⌋₊`. The pointwise
readings are lemmas rather than competing definitions. Design rationale for the carriers and for
this arrangement is recorded in `docs/wiki/coding-theory-conventions.md`.

## Main definitions

* `Code.closeCodewords`, `Code.closeCodewordsRel` — the codewords of `C` inside a Hamming ball, at
  absolute and relative radius. The absolute form is the relative one at a rescaled radius
  (`closeCodewords_eq_closeCodewordsRel`).
* `Code.Lambda` — the maximised point-list size, `⨆ f, (closeCodewordsRel C f δ).encard`.
* `Code.IsListDecodable`, `Code.IsUniquelyDecodable` — `(r, ℓ)`-list decodability, and its `ℓ = 1`
  special case.

## Main statements

* `Code.Lambda_le_of_forall_finset_card_le`, `Code.Lambda_lt_of_forall_finset_card_lt` — bounding
  the size by a uniform bound on the finite subsets of the point lists, loosely and strictly.
* `Code.isListDecodable_iff_forall_finset_card_le`, `Code.isListDecodable_iff_forall_ncard_le`,
  `Code.Lambda_le_iff_forall_encard_le`, `Code.Lambda_le_iff_forall_ncard_le` — the pointwise
  characterisations.
* `Code.finite_closeCodewordsRel_of_Lambda_le` — a finite bound implies the point lists are finite.
* `Code.exists_encard_eq_Lambda`, `Code.exists_encard_eq_Lambda_of_finite` — the supremum is
  attained, so a proof may choose a maximising word.
* `Code.encard_closeCodewordsRel_le_Lambda`,
  `Code.encard_le_Lambda_of_subset_closeCodewordsRel` — bounding a point list, or any subset of
  one, by the maximised size.
* `Code.isUniquelyDecodable_iff_subsingleton`,
  `Code.isUniquelyDecodable_relativeUniqueDecodingRadius` — unique decodability as "at most one
  close codeword", and its agreement with `Code.uniqueDecodingRadius`.
* `Code.isListDecodable_iff_toENNReal_le_ofReal` — transfer between a real-valued bound and the
  integral `Lambda`.
* `Code.IsListDecodable.mono`, `Code.IsListDecodable.anti_radius`, `Code.Lambda_mono`,
  `Code.Lambda_mono_code` — monotone in the list-size bound, antitone in the radius, monotone in the
  code.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed–Solomon Proximity Testing
    with Fewer Queries*][ACFY24stir]
-/


namespace Code

open scoped NNReal

section

variable {ι : Type*} [Fintype ι]
         {F : Type*}

open Classical in
/-- The set of `r`-close codewords to a given word `y` with respect to the Hamming distance. -/
def closeCodewords (C : Set (ι → F)) (y : ι → F) (r : ℕ) : Set (ι → F) :=
  {c | c ∈ C ∧ c ∈ Code.hammingBall y r}

open Classical in
/-- The set of `r`-close codewords to a given word `y` with respect to the relative Hamming
distance.
Note that this is exactly `Λ (C, y, r)` from [ACFY24] and ` List (C, y, r)` from [ACFY24stir]. -/
def closeCodewordsRel (C : Set (ι → F)) (y : ι → F) (r : ℝ) : Set (ι → F) :=
  {c | c ∈ C ∧ c ∈ Code.relHammingBall y r}

/-- Membership in the point list, stated at an ambient `[DecidableEq F]`.

`closeCodewordsRel` is defined under `open Classical in`, so its unfolding mentions
`Classical.propDecidable`; that instance and an ambient one are definitionally but not syntactically
equal, so neither `simp` nor a rewrite with `Code.mem_relHammingBall_iff` crosses between them. Use
this lemma rather than unfolding the definition. -/
lemma mem_closeCodewordsRel_iff [DecidableEq F] {C : Set (ι → F)} {y c : ι → F} {r : ℝ} :
    c ∈ closeCodewordsRel C y r ↔ c ∈ C ∧ (δᵣ(y, c) : ℝ) ≤ r := by
  constructor
  · rintro ⟨hc, hball⟩
    simp only [Code.mem_relHammingBall_iff] at hball
    exact ⟨hc, by convert hball using 2; congr⟩
  · rintro ⟨hc, hd⟩
    refine ⟨hc, ?_⟩
    simp only [Code.mem_relHammingBall_iff]
    convert hd using 2
    congr

/-- The absolute-radius point list is the relative one at the rescaled radius `r / n`, for
`n = |ι|`. So a bound on `closeCodewords` is a `Lambda` bound after rewriting with this lemma.

No hypothesis on `ι`: when it is empty both sides are all of `C`, the radius on the right being
`r / 0 = 0` and every distance being `0`. -/
lemma closeCodewords_eq_closeCodewordsRel (C : Set (ι → F)) (y : ι → F) (r : ℕ) :
    closeCodewords C y r = closeCodewordsRel C y ((r : ℝ) / Fintype.card ι) := by
  classical
  ext c
  simp only [closeCodewords, closeCodewordsRel, Set.mem_ofPred_eq, Code.mem_hammingBall_iff,
    Code.mem_relHammingBall_iff, Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast,
    and_congr_right_iff]
  intro _
  rcases isEmpty_or_nonempty ι with _ | _
  · simp [hammingDist]
  · have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [div_le_div_iff_of_pos_right hn]
    exact Nat.cast_le.symm

/-! ## The maximised list size -/

/-- The maximised point-list size of `C` at radius `δ`: the supremum over words `f` of the
cardinality of `closeCodewordsRel C f δ`.

Note that this is the *size*; the point list itself is `closeCodewordsRel`.

Being `ℕ∞`-valued, an infinite point list contributes `⊤` rather than the `0` that `Set.ncard`
would give, so a finite bound implies finiteness rather than assuming it
(`finite_closeCodewordsRel_of_Lambda_le`).

The radius is an unrestricted `ℝ`: `Lambda` is total in it, taking value `0` below `0` where the
ball is empty. Since relative Hamming distance is `1/|ι|`-quantised (`relHammingDistRange`),
`Lambda C` is a step function of `δ`, constant on each `[k/n, (k+1)/n)`. -/
noncomputable def Lambda (C : Set (ι → F)) (δ : ℝ) : ℕ∞ :=
  ⨆ f : ι → F, (closeCodewordsRel C f δ).encard

/-- Each individual point list is bounded by the maximised one. -/
lemma encard_closeCodewordsRel_le_Lambda (C : Set (ι → F)) (δ : ℝ) (f : ι → F) :
    (closeCodewordsRel C f δ).encard ≤ Lambda C δ :=
  le_iSup (fun g : ι → F => (closeCodewordsRel C g δ).encard) f

/-- Any set contained in a point list is bounded by the maximised list size. This is what a list
derived from a point list needs, so such a list requires no `Lambda` of its own. -/
lemma encard_le_Lambda_of_subset_closeCodewordsRel {C : Set (ι → F)} {δ : ℝ} {f : ι → F}
    {S : Set (ι → F)} (hS : S ⊆ closeCodewordsRel C f δ) : S.encard ≤ Lambda C δ :=
  (Set.encard_mono hS).trans (encard_closeCodewordsRel_le_Lambda C δ f)

/-- A `Lambda` bound is exactly a uniform bound on the point lists. -/
lemma Lambda_le_iff_forall_encard_le {C : Set (ι → F)} {δ : ℝ} {b : ℕ∞} :
    Lambda C δ ≤ b ↔ ∀ f : ι → F, (closeCodewordsRel C f δ).encard ≤ b :=
  iSup_le_iff

/-- A finite `Lambda` is attained: some word's point list has exactly that size. So a proof may
choose a maximising word without assuming one exists.

`Nonempty (ι → F)` is necessary, not merely convenient: over an empty word space there is no `f` to
choose while `Lambda` is still `0`. -/
theorem exists_encard_eq_Lambda [Nonempty (ι → F)] {C : Set (ι → F)} {δ : ℝ}
    (h : Lambda C δ ≠ ⊤) : ∃ f : ι → F, (closeCodewordsRel C f δ).encard = Lambda C δ := by
  by_contra hcontra
  have hcon : ∀ f : ι → F, (closeCodewordsRel C f δ).encard ≠ Lambda C δ :=
    fun f hf => hcontra ⟨f, hf⟩
  obtain ⟨m⟩ := ‹Nonempty (ι → F)›
  set n : ℕ := (Lambda C δ).toNat with hn_def
  have hLn : Lambda C δ = (n : ℕ∞) := (ENat.natCast_toNat h).symm
  -- no point list reaches `n`, so all of them are at most `n - 1`, so `Lambda ≤ n - 1`
  have hstep : ∀ f : ι → F, (closeCodewordsRel C f δ).encard ≤ ((n - 1 : ℕ) : ℕ∞) := by
    intro f
    have hlt : (closeCodewordsRel C f δ).encard < (n : ℕ∞) :=
      hLn ▸ lt_of_le_of_ne (encard_closeCodewordsRel_le_Lambda C δ f) (hcon f)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    rw [← hk] at hlt ⊢
    exact_mod_cast Nat.le_sub_one_of_lt (by exact_mod_cast hlt)
  have hnat : n ≤ n - 1 := by
    exact_mod_cast (hLn ▸ Lambda_le_iff_forall_encard_le.mpr hstep : (n : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞))
  -- and `n = 0` is impossible: the point list at `m` would then equal `Lambda`
  have hn0 : n ≠ 0 := by
    rintro hzero
    refine hcon m ?_
    have hle0 := encard_closeCodewordsRel_le_Lambda C δ m
    rw [hLn, hzero] at hle0 ⊢
    simpa using hle0
  omega

/-- Finiteness of the point lists is a *consequence* of a finite `Lambda` bound, not an extra
hypothesis. This is what a `Set.ncard`-based formulation has to assert separately. -/
lemma finite_closeCodewordsRel_of_Lambda_le {C : Set (ι → F)} {δ : ℝ} {n : ℕ}
    (h : Lambda C δ ≤ (n : ℕ∞)) (f : ι → F) : (closeCodewordsRel C f δ).Finite :=
  Set.finite_of_encard_le_coe ((encard_closeCodewordsRel_le_Lambda C δ f).trans h)

/-- The `∀`/`ncard` characterisation of a `Lambda` bound, at a natural bound. Use it to recover
the pointwise view inside a proof; being a lemma rather than a second definition, it cannot drift
from `Lambda` and needs no synchronisation. -/
lemma Lambda_le_iff_forall_ncard_le {C : Set (ι → F)} {δ : ℝ} {n : ℕ} :
    Lambda C δ ≤ (n : ℕ∞) ↔
      ∀ f : ι → F, (closeCodewordsRel C f δ).Finite ∧ (closeCodewordsRel C f δ).ncard ≤ n := by
  rw [Lambda_le_iff_forall_encard_le]
  refine ⟨fun h f => ?_, fun h f => ?_⟩
  · have hfin := Set.finite_of_encard_le_coe (h f)
    exact ⟨hfin, by exact_mod_cast hfin.cast_ncard_eq ▸ h f⟩
  · rw [← (h f).1.cast_ncard_eq]
    exact_mod_cast (h f).2

/-- If every finite set of codewords inside the radius-`δ` ball around `f` has at most `n`
elements, uniformly in `f`, then `Lambda C δ ≤ n`. This is the shape a counting argument produces.

Point-list finiteness follows from the same hypothesis by
`Set.finite_of_forall_finset_card_le`, so no finiteness of the alphabet is required. -/
lemma Lambda_le_of_forall_finset_card_le {C : Set (ι → F)} {δ : ℝ} {n : ℕ}
    (h : ∀ (f : ι → F) (T : Finset (ι → F)), (∀ c ∈ T, c ∈ closeCodewordsRel C f δ) →
      T.card ≤ n) :
    Lambda C δ ≤ (n : ℕ∞) := by
  rw [Lambda_le_iff_forall_encard_le]
  intro f
  have hfin : (closeCodewordsRel C f δ).Finite :=
    Set.finite_of_forall_finset_card_le (R := ℕ) fun T hT => h f T fun _ hc => hT hc
  rw [← hfin.cast_ncard_eq]
  exact_mod_cast (Set.ncard_eq_toFinset_card _ hfin) ▸
    h f hfin.toFinset fun c hc => hfin.mem_toFinset.mp hc

/-- The strict companion to `Lambda_le_of_forall_finset_card_le`.

`0 < n` is necessary: at `n = 0` the hypothesis is unsatisfiable (`T = ∅` gives `0 < 0`) while the
conclusion `Lambda C δ < 0` is false. -/
lemma Lambda_lt_of_forall_finset_card_lt {C : Set (ι → F)} {δ : ℝ} {n : ℕ} (hn : 0 < n)
    (h : ∀ (f : ι → F) (T : Finset (ι → F)), (∀ c ∈ T, c ∈ closeCodewordsRel C f δ) →
      T.card < n) :
    Lambda C δ < (n : ℕ∞) :=
  lt_of_le_of_lt
    (Lambda_le_of_forall_finset_card_le fun f T hT => Nat.le_sub_one_of_lt (h f T hT))
    (by exact_mod_cast Nat.sub_lt hn Nat.one_pos)

/-- The point list is monotone in the radius. -/
lemma closeCodewordsRel_subset_of_le {C : Set (ι → F)} {δ₁ δ₂ : ℝ}
    (h : δ₁ ≤ δ₂) (f : ι → F) :
    closeCodewordsRel C f δ₁ ⊆ closeCodewordsRel C f δ₂ := by
  intro c hc
  exact ⟨hc.1, le_trans hc.2 h⟩

/-- `Lambda` is monotone in the radius. -/
lemma Lambda_mono {C : Set (ι → F)} {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) :
    Lambda C δ₁ ≤ Lambda C δ₂ := by
  refine iSup_mono fun f => ?_
  exact Set.encard_mono (closeCodewordsRel_subset_of_le h f)

/-- `Lambda` is monotone in the code. -/
lemma Lambda_mono_code {C D : Set (ι → F)} (hDC : D ⊆ C) (δ : ℝ) :
    Lambda D δ ≤ Lambda C δ := by
  unfold Lambda
  refine iSup_mono fun f => ?_
  exact Set.encard_mono fun c hc => ⟨hDC hc.1, hc.2⟩

/-! ## List decodability -/

/-- A code `C` is `(r, ℓ)`-**list decodable** if every point list at relative radius `r` has at
most `ℓ` codewords, that is, `Lambda C r ≤ ⌊ℓ⌋₊`.

Flooring loses nothing, `Lambda` being integer-valued (`isListDecodable_iff_forall_ncard_le`), and
point-list finiteness is implied rather than asserted.

This is a `def`, not an `abbrev`, and so is semireducible: `exact`, `refine` and `apply` see through
it to the `Lambda` inequality, while `simp` and `rw` need `isListDecodable_iff_Lambda_le`. -/
def IsListDecodable (C : Set (ι → F)) (r : ℝ) (ℓ : ℝ≥0) : Prop :=
  Lambda C r ≤ (⌊ℓ⌋₊ : ℕ∞)

/-- A code `C` is uniquely decodable up to a relative distance `r` if there is at most one
codeword within relative Hamming distance `r` of any word. The `ℓ = 1` case of `IsListDecodable`. -/
def IsUniquelyDecodable (C : Set (ι → F)) (r : ℝ) : Prop :=
  IsListDecodable C r 1

/-- `IsListDecodable` *is* the inequality `Lambda C r ≤ ⌊ℓ⌋₊`, by definition. The entry point
for rewriting into the `Lambda` form, which `rw` and `simp only` need but `exact` and `refine`
do not. -/
lemma isListDecodable_iff_Lambda_le {C : Set (ι → F)} {r : ℝ} {ℓ : ℝ≥0} :
    IsListDecodable C r ℓ ↔ Lambda C r ≤ (⌊ℓ⌋₊ : ℕ∞) := Iff.rfl

/-- At a *natural* list-size bound the floor disappears, so list decodability is exactly a
`Lambda` bound in `ℕ∞`. This is the shape every combinatorial list-size theorem arrives at
(`JohnsonBound`'s in particular), which is why it is worth naming. -/
lemma isListDecodable_natCast_iff {C : Set (ι → F)} {r : ℝ} {n : ℕ} :
    IsListDecodable C r (n : ℝ≥0) ↔ Lambda C r ≤ (n : ℕ∞) := by
  rw [isListDecodable_iff_Lambda_le, Nat.floor_natCast]

/-- The `∀`/`ncard` reading of `IsListDecodable`, and the proof that flooring at the definition
loses nothing: `Lambda C r ≤ ⌊ℓ⌋₊` iff every point list is finite with at most `ℓ` elements as a
real bound. -/
lemma isListDecodable_iff_forall_ncard_le {C : Set (ι → F)} {r : ℝ} {ℓ : ℝ≥0} :
    IsListDecodable C r ℓ ↔
      ∀ f : ι → F, (closeCodewordsRel C f r).Finite ∧
        ((closeCodewordsRel C f r).ncard : ℝ) ≤ ℓ := by
  rw [show IsListDecodable C r ℓ ↔ Lambda C r ≤ ((⌊ℓ⌋₊ : ℕ) : ℕ∞) from Iff.rfl,
    Lambda_le_iff_forall_ncard_le]
  refine ⟨fun h f => ⟨(h f).1, ?_⟩, fun h f => ⟨(h f).1, ?_⟩⟩
  · calc (((closeCodewordsRel C f r).ncard : ℕ) : ℝ) ≤ ((⌊ℓ⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast (h f).2
      _ ≤ (ℓ : ℝ) := Nat.floor_le ℓ.coe_nonneg
  · exact_mod_cast Nat.le_floor (h f).2

/-- **Unfolding lemma for `IsUniquelyDecodable`.** Unique decodability is the `Lambda` bound `≤ 1`.

Needed because `IsUniquelyDecodable` is a semireducible `def` wrapping another one, so neither
`rw` nor `simp` reaches the inequality, and the `⌊(1 : ℝ≥0)⌋₊ = 1` step is `Nat.floor_one` rather
than `rfl`. -/
lemma isUniquelyDecodable_iff_Lambda_le {C : Set (ι → F)} {r : ℝ} :
    IsUniquelyDecodable C r ↔ Lambda C r ≤ 1 := by
  rw [show IsUniquelyDecodable C r ↔ IsListDecodable C r 1 from Iff.rfl,
    isListDecodable_iff_Lambda_le, Nat.floor_one, Nat.cast_one]

/-- `IsUniquelyDecodable` really is "at most one close codeword": the point list at radius `r` is a
subsingleton for every word. This is the lemma that pins the definition to its stated meaning. -/
lemma isUniquelyDecodable_iff_subsingleton {C : Set (ι → F)} {r : ℝ} :
    IsUniquelyDecodable C r ↔ ∀ y : ι → F, (closeCodewordsRel C y r).Subsingleton := by
  rw [isUniquelyDecodable_iff_Lambda_le, Lambda_le_iff_forall_encard_le]
  simp only [Set.encard_le_one_iff_subsingleton]

/-- Every code is uniquely decodable at its relative unique-decoding radius. This is
`Code.eq_of_le_uniqueDecodingRadius` phrased in the list-decoding layer, identifying
`Code.uniqueDecodingRadius` with the `ℓ = 1` case of list decodability.

No hypothesis on `ι`: when it is empty the word space `ι → F` is a singleton, so every point list
is a subsingleton outright. -/
theorem isUniquelyDecodable_relativeUniqueDecodingRadius [DecidableEq F]
    (C : Set (ι → F)) : IsUniquelyDecodable C (Code.relativeUniqueDecodingRadius C : ℝ) := by
  refine isUniquelyDecodable_iff_subsingleton.mpr fun y c hc c' hc' => ?_
  rcases isEmpty_or_nonempty ι with _ | _
  · exact Subsingleton.elim c c'
  · have key : ∀ z : ι → F, z ∈ closeCodewordsRel C y (Code.relativeUniqueDecodingRadius C : ℝ) →
        Δ₀(y, z) ≤ Code.uniqueDecodingRadius C := by
      intro z hz
      have h2 : ((Δ₀(y, z) : ℝ≥0) / (Fintype.card ι : ℝ≥0))
          ≤ Code.relativeUniqueDecodingRadius C := by
        have hmem := (mem_closeCodewordsRel_iff.mp hz).2
        simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast] at hmem
        rw [← NNReal.coe_le_coe]
        push_cast
        exact hmem
      rw [Code.relativeUniqueDecodingRadius, div_le_div_iff_of_pos_right
        (by simp [Fintype.card_pos (α := ι)])] at h2
      rw [Code.uniqueDecodingRadius_eq_floor_div_2]
      exact Nat.le_floor (by exact_mod_cast h2)
    exact Code.eq_of_le_uniqueDecodingRadius C y hc.1 hc'.1 (key c hc) (key c' hc')

/-- Monotone in the list-size bound, by monotonicity of `Nat.floor`. This is the lemma that ad-hoc
`…_of_le` variants of individual list-size theorems would otherwise each re-derive. -/
lemma IsListDecodable.mono {C : Set (ι → F)} {r : ℝ} {ℓ₁ ℓ₂ : ℝ≥0}
    (h : IsListDecodable C r ℓ₁) (hℓ : ℓ₁ ≤ ℓ₂) : IsListDecodable C r ℓ₂ :=
  h.trans (by exact_mod_cast Nat.floor_le_floor (show (ℓ₁ : ℝ) ≤ (ℓ₂ : ℝ) from hℓ))

/-- Shrinking the radius preserves list decodability at the same bound, by `Lambda_mono`: the
point lists only get smaller. The companion to `IsListDecodable.mono`, which weakens the bound.

Named `anti_radius`, not `mono_radius`: `Lambda` is monotone in the radius, so the *predicate* is
antitone in it. -/
lemma IsListDecodable.anti_radius {C : Set (ι → F)} {r₁ r₂ : ℝ} {ℓ : ℝ≥0}
    (h : IsListDecodable C r₂ ℓ) (hr : r₁ ≤ r₂) : IsListDecodable C r₁ ℓ :=
  (Lambda_mono hr).trans h

/-- `IsListDecodable` from a bound on the finite subsets of the point lists: the
`IsListDecodable`-shaped form of `Lambda_le_of_forall_finset_card_le`, at a real bound. -/
lemma isListDecodable_of_forall_finset_card_le {C : Set (ι → F)} {r : ℝ} {ℓ : ℝ≥0}
    (h : ∀ (f : ι → F) (T : Finset (ι → F)), (∀ c ∈ T, c ∈ closeCodewordsRel C f r) →
      (T.card : ℝ) ≤ ℓ) :
    IsListDecodable C r ℓ :=
  Lambda_le_of_forall_finset_card_le fun f T hT => Nat.le_floor (h f T hT)

/-- Any `Finset` of codewords inside the radius-`r` ball around `y` has at most `ℓ` elements. The
converse of `isListDecodable_of_forall_finset_card_le`, for use when list decodability is a
hypothesis rather than the goal. -/
lemma IsListDecodable.finset_card_le {C : Set (ι → F)} {r : ℝ} {ℓ : ℝ≥0}
    (h : IsListDecodable C r ℓ) (y : ι → F) (T : Finset (ι → F))
    (hT : ∀ c ∈ T, c ∈ closeCodewordsRel C y r) : (T.card : ℝ) ≤ ℓ := by
  obtain ⟨hfin, hcard⟩ := isListDecodable_iff_forall_ncard_le.mp h y
  refine le_trans ?_ hcard
  exact_mod_cast Set.ncard_le_ncard (fun c hc => hT c hc) hfin

/-- `C` is `(r, ℓ)`-list decodable exactly when every finite family of codewords inside a
radius-`r` ball has at most `ℓ` elements.

For the subset spelling `↑T ⊆ closeCodewordsRel C y r`, cross with
`simp only [Set.subset_def, Finset.mem_coe]`. -/
lemma isListDecodable_iff_forall_finset_card_le {C : Set (ι → F)} {r : ℝ} {ℓ : ℝ≥0} :
    IsListDecodable C r ℓ ↔
      ∀ (y : ι → F) (T : Finset (ι → F)), (∀ c ∈ T, c ∈ closeCodewordsRel C y r) →
        (T.card : ℝ) ≤ ℓ :=
  ⟨fun h => h.finset_card_le, isListDecodable_of_forall_finset_card_le⟩

/-- Transfer from an `ENNReal` bound on `Lambda`, which is the shape real-valued list-size bounds
arrive in. See `isListDecodable_iff_toENNReal_le_ofReal` for the equivalence.

No finiteness of the alphabet is needed: the hypothesis bounds every point list by
`ENNReal.ofReal ℓ ≠ ⊤`, which forces it finite. -/
lemma isListDecodable_of_toENNReal_le_ofReal {C : Set (ι → F)} {δ : ℝ} {ℓ : ℝ≥0}
    (h : (Lambda C δ : ENNReal) ≤ ENNReal.ofReal ℓ) : IsListDecodable C δ ℓ := by
  refine Lambda_le_iff_forall_encard_le.mpr fun f => ?_
  have hpoint : ((closeCodewordsRel C f δ).encard : ENNReal) ≤ (Lambda C δ : ENNReal) := by
    exact_mod_cast encard_closeCodewordsRel_le_Lambda C δ f
  have hle := hpoint.trans h
  have hfin : (closeCodewordsRel C f δ).Finite := by
    refine Set.encard_ne_top_iff.mp fun htop => ?_
    rw [htop] at hle
    simp at hle
  have hcast : ((closeCodewordsRel C f δ).encard : ENNReal) =
      ENNReal.ofReal (((closeCodewordsRel C f δ).ncard : ℕ) : ℝ) := by
    rw [← hfin.cast_ncard_eq, ENNReal.ofReal_natCast]
    rfl
  rw [hcast] at hle
  have h2 : (((closeCodewordsRel C f δ).ncard : ℕ) : ℝ) ≤ ℓ :=
    (ENNReal.ofReal_le_ofReal_iff ℓ.coe_nonneg).mp hle
  rw [← hfin.cast_ncard_eq]
  exact_mod_cast Nat.le_floor h2

/-- The converse of `isListDecodable_of_toENNReal_le_ofReal`: a `IsListDecodable` hypothesis pushes
forward to the `ENNReal` shape, `Lambda` being integer-valued and `⌊ℓ⌋₊ ≤ ℓ`. -/
lemma toENNReal_le_ofReal_of_isListDecodable {C : Set (ι → F)} {δ : ℝ} {ℓ : ℝ≥0}
    (h : IsListDecodable C δ ℓ) : (Lambda C δ : ENNReal) ≤ ENNReal.ofReal ℓ := by
  have h' : (Lambda C δ : ENNReal) ≤ ((⌊ℓ⌋₊ : ℕ) : ENNReal) := by
    exact_mod_cast isListDecodable_iff_Lambda_le.mp h
  refine h'.trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (Nat.floor_le ℓ.coe_nonneg)

/-- **The `ENNReal` boundary, as an equivalence.** Real-valued list-size bounds and the integral
`Lambda` bound are interchangeable, so neither side is privileged: the Johnson family arrives on
the left, the `ε`-error layer consumes on the left, and STIR/WHIR hypotheses live on the right. -/
lemma isListDecodable_iff_toENNReal_le_ofReal {C : Set (ι → F)} {δ : ℝ} {ℓ : ℝ≥0} :
    IsListDecodable C δ ℓ ↔ (Lambda C δ : ENNReal) ≤ ENNReal.ofReal ℓ :=
  ⟨toENNReal_le_ofReal_of_isListDecodable, isListDecodable_of_toENNReal_le_ofReal⟩

/-! ## Algebra of `Lambda` -/

/-- Every element of a point list is a codeword. -/
lemma closeCodewordsRel_subset_code {C : Set (ι → F)} (δ : ℝ) (f : ι → F) :
    closeCodewordsRel C f δ ⊆ C := fun _ hc => hc.1

/-- A point list of a finite code is no larger than the code. -/
lemma ncard_closeCodewordsRel_le_ncard {C : Set (ι → F)} (δ : ℝ) (f : ι → F) (hC : C.Finite) :
    (closeCodewordsRel C f δ).ncard ≤ C.ncard :=
  Set.ncard_le_ncard (closeCodewordsRel_subset_code δ f) hC

/-- The maximised list size of a finite code is no larger than the code. -/
lemma Lambda_le_ncard {C : Set (ι → F)} (δ : ℝ) (hC : C.Finite) :
    Lambda C δ ≤ (C.ncard : ℕ∞) := by
  refine iSup_le fun f => ?_
  calc
    (closeCodewordsRel C f δ).encard ≤ C.encard :=
      Set.encard_mono (closeCodewordsRel_subset_code δ f)
    _ = (C.ncard : ℕ∞) := hC.cast_ncard_eq.symm

/-- The maximised list size is bounded by the total number of words, each point list being a
set of words. Stated with `Nat.card`, so no `Fintype (ι → F)` instance is needed. -/
lemma Lambda_le_card {C : Set (ι → F)} [Finite F] (δ : ℝ) :
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
lemma Lambda_ne_top {C : Set (ι → F)} [Finite F] (δ : ℝ) :
    Lambda C δ ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (Lambda_le_card δ)

/-- `exists_encard_eq_Lambda` over a finite alphabet, where the finiteness hypothesis discharges
itself. This is the form the soundness analyses want, since they fix a maximising word. -/
theorem exists_encard_eq_Lambda_of_finite {C : Set (ι → F)} [Finite F] [Nonempty (ι → F)] (δ : ℝ) :
    ∃ f : ι → F, (closeCodewordsRel C f δ).encard = Lambda C δ :=
  exists_encard_eq_Lambda (Lambda_ne_top δ)

end

end Code
