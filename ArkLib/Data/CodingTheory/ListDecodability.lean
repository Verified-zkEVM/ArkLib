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
relative Hamming distance `δ` of `f`. This file defines it and its size.

The **size is the primitive**: `Lambda C δ : ℕ∞` is the maximised list size, and every statement
about how large a point list is — an upper bound, a lower bound, or an equality between two codes'
list sizes — is an (in)equality on it. `IsListDecodable` is a `def` whose body *is* one such
inequality, not a parallel definition; keeping the two separate is what once let them disagree, a
`Set.ncard`-based body being satisfied by an *infinite* point list. With `Set.encard` and `ℕ∞`,
point-list finiteness is a consequence of a finite bound rather than a conjunct to be remembered.

## Main definitions

* `Code.closeCodewords`, `Code.closeCodewordsRel` — the codewords of `C`
  inside a Hamming ball, at absolute and relative radius. Both are defined under
  `open Classical in`, so they expose no decidability data; `mem_closeCodewordsRel_iff` is the
  membership lemma that crosses to an ambient `[DecidableEq F]`, so no consumer needs to open the
  definition. The absolute form is the relative one at a rescaled radius
  (`closeCodewords_eq_closeCodewordsRel`), not a second notion.
* `Code.Lambda` — the maximised list size `⨆ f, |closeCodewordsRel C f δ| : ℕ∞`.
* `Code.IsListDecodable`, `Code.IsUniquelyDecodable` — `(r, ℓ)`-list decodability as
  the `def` `Lambda C r ≤ ⌊ℓ⌋₊` at `ℓ : ℝ≥0`, and its `ℓ = 1` special case. Semireducible, and
  that is load-bearing; see the `IsListDecodable` docstring.

## Main statements

* `Code.Lambda_le_of_forall_finset_card_le` — the primitive way to bound the size: a
  uniform bound on the *finite subsets* of the point lists, which is the shape a counting
  argument produces. `isListDecodable_of_forall_finset_card_le` is its real-bound form, and
  `Lambda_lt_of_forall_finset_card_lt` its strict one, for the `|Λ(C, δ)| < |F|` statements.
* `Code.isListDecodable_iff_forall_finset_card_le` — the same finite-subset reading as an
  *equivalence*, so list decodability can be consumed in that shape as well as established in it;
  `Code.IsListDecodable.finset_card_le` is its forward half, available as dot notation.
* `Code.finite_closeCodewordsRel_of_Lambda_le` — finiteness as a consequence.
* `Code.exists_encard_eq_Lambda`, `exists_encard_eq_Lambda_of_finite` — the supremum is
  attained, so a proof may *choose* a maximising word, as [ABF26] Lemma 6.12 does.
* `Code.Lambda_le_iff_forall_encard_le`, `Lambda_le_iff_forall_ncard_le`,
  `isListDecodable_iff_forall_ncard_le` — the pointwise characterisations, as lemmas rather than a
  competing definition, so they cannot drift.
* `Code.encard_closeCodewordsRel_le_Lambda`,
  `Code.encard_le_Lambda_of_subset_closeCodewordsRel` — the two handles for *lower*
  bounds on the list size, and for bounding any list contained in a point list (a derived list,
  such as a block-relative one, therefore needs no `Lambda` of its own).
* `Code.isListDecodable_iff_Lambda_le`, `isListDecodable_natCast_iff`,
  `isUniquelyDecodable_iff_Lambda_le` — the definitional unfoldings, and the shape at a natural
  bound, which is what combinatorial list-size theorems produce.
* `Code.isUniquelyDecodable_iff_subsingleton` — unique decodability really is "at most one
  close codeword".
* `Code.isUniquelyDecodable_relativeUniqueDecodingRadius` — the `ℓ = 1` anchor, identifying
  this layer's unique decodability with `Code.uniqueDecodingRadius` and
  `Code.eq_of_le_uniqueDecodingRadius`, so the two accounts of unique decoding are one.
* `Code.isListDecodable_iff_toENNReal_le_ofReal` — the one boundary at which real-valued
  bounds, such as the Johnson family's `ENNReal.ofReal` shape, meet the integral `Lambda`.
* `Code.IsListDecodable.mono`, `Code.IsListDecodable.anti_radius` — monotone in the
  list-size bound, antitone in the radius.
* `Code.Lambda_mono`, `Lambda_le_ncard`, `Lambda_le_card`, `Lambda_ne_top` — basic
  algebra of `Lambda`.

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

/-- **Membership in the point list, at whatever `DecidableEq F` is ambient.**

`closeCodewordsRel` is defined under `open Classical in`, so its unfolding mentions
`Classical.propDecidable`. A consumer working under an ambient `[DecidableEq F]` — which is the
normal situation for this layer — therefore has two instances that are definitionally but not
syntactically equal, and neither `simp` nor a direct rewrite with `Code.mem_relHammingBall_iff`
crosses between them. `hammingDist` does not depend on the choice, so the crossing is sound; this
lemma performs it once so that no consumer has to open the definition to do it again. -/
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

/-- The absolute-radius point list is the relative one at the rescaled radius `r / n`, relative
Hamming distance being `Δ₀ / n` for `n = |ι|`.

So `closeCodewords` is a spelling of `closeCodewordsRel`, not a parallel notion: it needs no list
size of its own, and a bound on it is a `Lambda` bound after rewriting with this lemma. [ABF26]
Definition 2.8 parameterises the point list by a relative radius, which is why `Lambda` is defined
there.

No hypothesis on `ι`: when it is empty both sides are all of `C`, the radius on the right being
`r / 0 = 0` and every distance being `0`. -/
lemma closeCodewords_eq_closeCodewordsRel (C : Set (ι → F)) (y : ι → F) (r : ℕ) :
    closeCodewords C y r = closeCodewordsRel C y ((r : ℝ) / Fintype.card ι) := by
  classical
  ext c
  simp only [closeCodewords, closeCodewordsRel, Set.mem_setOf_eq, Code.mem_hammingBall_iff,
    Code.mem_relHammingBall_iff, Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast,
    and_congr_right_iff]
  intro _
  rcases isEmpty_or_nonempty ι with _ | _
  · simp [hammingDist]
  · have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [div_le_div_iff_of_pos_right hn]
    exact Nat.cast_le.symm

/-! ## The maximised list size -/

/-- The maximised list size of `C` at radius `δ`: the supremum over words `f` of the
cardinality of the point list `closeCodewordsRel C f δ`.

This is `[ABF26]`'s `|Λ(C, δ)|` — the *size*, not the list. The list itself is `closeCodewordsRel`,
which Definition 2.8 writes `Λ(C, δ, f)`; the paper's §1 uses the bare `Λ(C, δ)` for the maximised
size, as here. Worth stating, because `[ACFY24]` and `[ACFY24stir]` use `Λ` for the *list*.

**Why `ℕ∞`.** A list size is a cardinal, and the carrier is load-bearing twice over. Integrality
makes flooring a real bound an *equivalence*, so a real-valued Johnson bound is recorded without
loss. And `⊤` records an infinite point list honestly, where `Set.ncard` would report `0` — so a
bound `Lambda C δ ≤ n` cannot be established by an infinite list, and finiteness is a
*consequence* (`finite_closeCodewordsRel_of_Lambda_le`) rather than a side condition.

**Why the radius is `ℝ`, unrestricted.** Every radius the literature names is an *arithmetic
expression* — `1 - √ρ - η`, `ℓ/(ℓ+1) · (1 - ρ - η)`, a Johnson radius — and none of them is
constrained to `[0, 1]`, or even to `ℝ≥0`, by the mathematics that produces it. Narrowing the
carrier does not make those expressions land in range; it only moves the obligation, and both ways
of discharging it are worse than the total statement:

* *Truncate.* At `δ < 0` the point list is empty, but the radius-`0` point list is `{f}` — so a
  bound established for the empty list would be asserted of a singleton. The statement changes
  meaning, silently, in a regime that is reachable rather than hypothetical. Silent wrongness under
  a total-looking statement is precisely the failure mode this file exists to remove.
* *Guard.* Carry `0 ≤ 1 - √ρ - η` as a hypothesis wherever such a radius appears. That is a
  hypothesis the mathematics does not need — the bound holds for every `η > 0`, trivially so once
  the ball is empty — and importing hypotheses a statement does not need is the anti-pattern
  recorded in `docs/wiki/coding-theory-conventions.md`.

So a negative radius is not a degenerate case to exclude but the honest value of a total function:
the ball is empty and `Lambda` is `0`. That the list-size *bound* moves the other way, to `ℝ≥0`, is
not an inconsistency between the two arguments but a difference between the two objects — a bound
is a cardinality, where negative is unsatisfiable, while a radius is a threshold on a total distance
function, where negative is attained. See `IsListDecodable` for that side.

Membership in `closeCodewordsRel C f δ` is `δᵣ(f, ·) ≤ δ`, and relative Hamming distance is
`1/n`-quantised for `n = |ι|` (`relHammingDistRange`), so `Lambda C` is a step function of
`δ`, constant on each cell `[k/n, (k+1)/n)`. An extremal "largest `δ`" is therefore only
meaningful as an integer boundary index `k/n`, not as a real number. -/
noncomputable def Lambda (C : Set (ι → F)) (δ : ℝ) : ℕ∞ :=
  ⨆ f : ι → F, (closeCodewordsRel C f δ).encard

/-- Each individual point list is bounded by the maximised one. -/
lemma encard_closeCodewordsRel_le_Lambda (C : Set (ι → F)) (δ : ℝ) (f : ι → F) :
    (closeCodewordsRel C f δ).encard ≤ Lambda C δ :=
  le_iSup (fun g : ι → F => (closeCodewordsRel C g δ).encard) f

/-- Any set contained in a point list is bounded by the maximised list size.

This is what a *derived* list needs, and the reason none of them requires a `Lambda` of its own:
`BlockRelDistance.listBlock_subset_listHamming` places WHIR's block-relative list inside a point
list, and its size bound then follows from this lemma. -/
lemma encard_le_Lambda_of_subset_closeCodewordsRel {C : Set (ι → F)} {δ : ℝ} {f : ι → F}
    {S : Set (ι → F)} (hS : S ⊆ closeCodewordsRel C f δ) : S.encard ≤ Lambda C δ :=
  (Set.encard_mono hS).trans (encard_closeCodewordsRel_le_Lambda C δ f)

/-- A `Lambda` bound is exactly a uniform bound on the point lists. -/
lemma Lambda_le_iff_forall_encard_le {C : Set (ι → F)} {δ : ℝ} {b : ℕ∞} :
    Lambda C δ ≤ b ↔ ∀ f : ι → F, (closeCodewordsRel C f δ).encard ≤ b :=
  iSup_le_iff

/-- **The supremum is attained.** `Lambda` is defined as a `⨆`, and a supremum is in general not a
maximum — but `[ABF26]` uses it as one: the proof of Lemma 6.12 begins by *choosing* a word at
which the point list has size `|Λ(C, δ)|`. That step is available here whenever `Lambda` is finite,
a bounded set of naturals having a greatest element, and this lemma is what makes it available
without a hypothesis. Without it the choice would have to be re-derived inline, or — the real risk
— imported as an assumption.

`Nonempty (ι → F)` is genuinely needed and not merely convenient: over an empty word space there is
no `f` to choose, while `Lambda` is still `0`. It is implied by `Nonempty F`, and also holds
whenever `ι` is empty. -/
theorem exists_encard_eq_Lambda [Nonempty (ι → F)] {C : Set (ι → F)} {δ : ℝ}
    (h : Lambda C δ ≠ ⊤) : ∃ f : ι → F, (closeCodewordsRel C f δ).encard = Lambda C δ := by
  by_contra hcontra
  have hcon : ∀ f : ι → F, (closeCodewordsRel C f δ).encard ≠ Lambda C δ :=
    fun f hf => hcontra ⟨f, hf⟩
  obtain ⟨m⟩ := ‹Nonempty (ι → F)›
  set n : ℕ := (Lambda C δ).toNat with hn_def
  have hLn : Lambda C δ = (n : ℕ∞) := (ENat.coe_toNat h).symm
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

/-- **The primitive way to bound `Lambda`: bound the finite subsets of the point lists.** If every
finite set of codewords inside the radius-`δ` ball around `f` has at most `n` elements, uniformly
in `f`, then `Lambda C δ ≤ n`.

This is the shape a list-decoding counting argument naturally produces: it fixes a finite family
of close codewords and bounds its cardinality. Finiteness of the whole point list follows from the
same hypothesis, by `Set.Finite.of_forall_finset_card_le`, so no finiteness of the alphabet is
required.

Prefer this over an `[Finite F]` variant taking a bare `ncard` bound. Such a variant would be
*sound* — under a finite alphabet `ncard` cannot lie, so there is no vacuity to exploit — but it
imports a hypothesis the statement does not need, and it lets a proof reach the conclusion without
ever exhibiting the finiteness that list decoding is about. This lemma asks for the bound a
counting argument already has. -/
lemma Lambda_le_of_forall_finset_card_le {C : Set (ι → F)} {δ : ℝ} {n : ℕ}
    (h : ∀ (f : ι → F) (T : Finset (ι → F)), (∀ c ∈ T, c ∈ closeCodewordsRel C f δ) →
      T.card ≤ n) :
    Lambda C δ ≤ (n : ℕ∞) := by
  rw [Lambda_le_iff_forall_encard_le]
  intro f
  have hfin : (closeCodewordsRel C f δ).Finite :=
    Set.Finite.of_forall_finset_card_le (ℓ := (n : ℝ))
      fun T hT => by exact_mod_cast h f T fun c hc => hT hc
  rw [← hfin.cast_ncard_eq]
  exact_mod_cast (Set.ncard_eq_toFinset_card _ hfin) ▸
    h f hfin.toFinset fun c hc => hfin.mem_toFinset.mp hc

/-- The **strict** companion to `Lambda_le_of_forall_finset_card_le`.

`[ABF26]` states list-size bounds strictly as well as loosely — `|Λ(C, δ)| < |F|` is the shape of
[BCHKS25] Theorem 1.9 and the hypothesis of Lemma 6.12 — and a counting argument that produces a
strict bound on finite subsets should not have to weaken it to reach `Lambda`. `0 < n` is forced:
`T = ∅` already gives `0 ≤ n`, so `T.card < 0` is unsatisfiable and the hypothesis would be vacuous
at `n = 0` while the conclusion `Lambda C δ < 0` is false. -/
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

/-! ## List decodability

`IsListDecodable` is notation, not a second notion: its content is the inequality
`Lambda C r ≤ ⌊ℓ⌋₊`, and `isListDecodable_iff_Lambda_le` is `Iff.rfl`. One definition to keep
correct, no two notions to keep in sync — while the literature-shaped name still reads better in
a hypothesis list than the unfolded inequality.

**Why keep a named predicate at all.** The maximally unified option is to have none: delete it and
spell its consumers' hypotheses `Lambda (C i) (δ i) ≤ ⌊l i⌋₊` directly. That was weighed and not
taken — not because the existing hypotheses read that way, but because a bare inequality has no
namespace: `h.mono` on `Lambda C r ≤ n` resolves to `LE.le.mono` and means something else. The name
buys `IsListDecodable.mono` and `IsListDecodable.anti_radius` at zero mathematical cost, the
predicate being *definitionally* the inequality, so nothing rests on the choice and it stays
revisitable —
the cost is editing its six hypotheses, three in `ProofSystem/Stir` here and three in
`ProofSystem/Whir` on the branches where that development lives. The naming question for this
layer, including why the *namespace* is the part that should eventually change and when, is
recorded once in `docs/wiki/coding-theory-conventions.md` rather than restated here.
-/

/-- A code `C` is `(r, ℓ)`-**list decodable**: every point list at relative radius `r` has at most
`ℓ` codewords, that is `Lambda C r ≤ ℓ`.

**Why the bound is real-valued at all, rather than `ℕ∞`.** Because a list-decoding hypothesis is
never used alone. The theorems that consume it put the *same* bound into the hypothesis and into
the conclusion's arithmetic: `|Λ(C, δ)| ≤ L` gives `ε_mca(C, 1 - √(1-δ+η)) ≤ (L²·δn + 1/η)/|F|`
([GCXK25] Theorem 3, via [ABF26]), and STIR's out-of-domain sampling pays `L(L-1)/2`. Stating the
hypothesis at `ℕ∞` would force every such theorem to carry two variables and a coupling between
them — reintroducing, one level up, exactly the two-objects-to-keep-in-sync problem this file
removes. The bound has to be usable as a number.

**And `ℝ≥0` rather than `ℝ`,** because a negative bound is not a weaker statement but an
unsatisfiable one: `(ncard : ℝ) ≤ ℓ < 0` has no models, so the narrower carrier loses no statement
worth making, while it drops the `0 ≤ ℓ` side condition from every transfer lemma. Admitting `ℝ`
also splits the two readings, `⌊ℓ⌋₊ = 0` saying every point list is empty where `(ncard : ℝ) ≤ ℓ`
says nothing is possible. That the existing call sites already pass `ℝ≥0` is a consequence of this,
not the reason for it.

**Proving a `IsListDecodable` goal.** `exact`, `refine` and `apply` unify at default transparency,
so they see straight through to the underlying `Lambda … ≤ …` — no bridge lemma is needed. `simp`
and `rw` match at *reducible* transparency and so leave it folded, which is what keeps goals
readable; start from `refine Lambda_le_iff_forall_encard_le.mpr ?_` rather than
`rw [Lambda_le_iff_forall_encard_le]` when you want the pointwise form.

**`def`, not `abbrev`, and the difference is not cosmetic.** As an `abbrev` this is *reducible*,
and then Mathlib's `@[simp] ge_iff_le` — an `Iff.rfl` whose left-hand side is a bare `GE.ge`
application — unifies with the whole folded term and `simp` silently unfolds it, all the way to
`WithBot.LE` on `ℕ∞`. Two costs: goals become unreadable, and `IsListDecodable.mono` becomes
unreachable, since dot notation then looks for `WithBot.LE.mono`. Note this is specific to a
`≤`-shaped body: an `abbrev` whose body is a `∀` is not affected. Downstream STIR/WHIR proofs are
`simp`-heavy, so semireducibility is load-bearing here.

**The floor has two spellings.** `ℝ≥0` carries its own (noncomputable) `FloorSemiring`, inherited
from the subtype, so `⌊ℓ⌋₊` and `⌊(ℓ : ℝ)⌋₊` both elaborate and are definitionally equal — but not
syntactically, so `rw` does not cross between them. This definition uses `⌊ℓ⌋₊`, the spelling
natural to the type; a caller arriving with the coerced form crosses with `norm_cast`, Mathlib's
`Nonneg.nat_floor_coe` being tagged `@[norm_cast]`.

**Flooring at the definition is lossless**, `Lambda` being integer-valued: see
`isListDecodable_iff_forall_ncard_le`. Point-list finiteness is likewise implied rather than
asserted. -/
def IsListDecodable (C : Set (ι → F)) (r : ℝ) (ℓ : ℝ≥0) : Prop :=
  Lambda C r ≤ (⌊ℓ⌋₊ : ℕ∞)

/-- A code `C` is uniquely decodable up to a relative distance `r` if there is at most one
codeword within relative Hamming distance `r` of any word. The `ℓ = 1` case of `IsListDecodable`. -/
def IsUniquelyDecodable (C : Set (ι → F)) (r : ℝ) : Prop :=
  IsListDecodable C r 1

/-- **Unfolding lemma.** `IsListDecodable` *is* the inequality `Lambda C r ≤ ⌊ℓ⌋₊`, by definition.

This is not a bridge between two notions — the five lemmas of that kind are gone, along with the
second definition they connected. It is the entry point for rewriting into the `Lambda` form, which
`exact` and `refine` do not need (they unify at default transparency) but `rw` and `simp only` do,
`IsListDecodable` being semireducible. -/
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

/-- **Unique decoding is the `ℓ = 1` case, and this connects the two notions of it.** Every code is
uniquely decodable at its relative unique-decoding radius — which is exactly what
`Code.eq_of_le_uniqueDecodingRadius` says, phrased in the list-decoding layer.

Without this, `Code.uniqueDecodingRadius` (used by the `ProximityGap` developments) and
`IsUniquelyDecodable` would be two unconnected accounts of the same notion — the situation this file
exists to avoid. [ABF26] introduces the list explicitly as the extension of unique decoding from
`δ_min/2` to an arbitrary radius, so the two belong to one framework.

No hypothesis on `ι`: when it is empty the whole word space `ι → F` is the singleton containing the
empty function, so every point list is a subsingleton outright. -/
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

/-- **Using a list-decodability hypothesis on a concrete finite family.** The converse of
`isListDecodable_of_forall_finset_card_le`: any `Finset` of codewords inside the radius-`r` ball
around `y` has at most `ℓ` elements.

This is the direction a proof needs when list decodability is a *hypothesis* rather than the goal,
and it is stated in the namespace so that dot notation works — `h.finset_card_le y T hT`. Without
it, a consumer has to route through `isListDecodable_iff_forall_ncard_le` and carry the finiteness
witness by hand, which is friction with no mathematical content. -/
lemma IsListDecodable.finset_card_le {C : Set (ι → F)} {r : ℝ} {ℓ : ℝ≥0}
    (h : IsListDecodable C r ℓ) (y : ι → F) (T : Finset (ι → F))
    (hT : ∀ c ∈ T, c ∈ closeCodewordsRel C y r) : (T.card : ℝ) ≤ ℓ := by
  obtain ⟨hfin, hcard⟩ := isListDecodable_iff_forall_ncard_le.mp h y
  refine le_trans ?_ hcard
  exact_mod_cast Set.ncard_le_ncard (fun c hc => hT c hc) hfin

/-- **The finite-subset characterisation of list decodability.** `C` is `(r, ℓ)`-list decodable
exactly when every finite family of codewords inside a radius-`r` ball has at most `ℓ` elements.

This is the reading a counting argument produces *and* consumes, so it is worth having as an
equivalence rather than only the constructor direction: `.mpr` is
`isListDecodable_of_forall_finset_card_le` and `.mp` is `IsListDecodable.finset_card_le`.

Note that this is a *characterisation*, not a second definition — the point-list finiteness that a
`Set.ncard`-based formulation has to carry as a conjunct is a consequence here, so there is nothing
to keep in sync. A caller preferring the subset spelling `↑T ⊆ closeCodewordsRel C y r` crosses to
this one with `simp only [Set.subset_def, Finset.mem_coe]`. -/
lemma isListDecodable_iff_forall_finset_card_le {C : Set (ι → F)} {r : ℝ} {ℓ : ℝ≥0} :
    IsListDecodable C r ℓ ↔
      ∀ (y : ι → F) (T : Finset (ι → F)), (∀ c ∈ T, c ∈ closeCodewordsRel C y r) →
        (T.card : ℝ) ≤ ℓ :=
  ⟨fun h => h.finset_card_le, isListDecodable_of_forall_finset_card_le⟩

/-- **The `ENNReal` transfer** — the one boundary at which real-valued bounds meet the integral
`Lambda`. This is the shape the Johnson-family bounds produce, and the shape the `ε`-error layer
(`ProximityGap`, and the Grand Challenge parameter carriers) states its list-size side conditions
in, so both directions get used; see `isListDecodable_iff_toENNReal_le_ofReal`.

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
