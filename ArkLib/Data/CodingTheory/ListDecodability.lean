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
relative Hamming distance `δ` of `f`. This file defines it and its size.

The **size is the primitive**: `Lambda C δ : ℕ∞` is the maximised list size, and every statement
about how large a point list is — an upper bound, a lower bound, or an equality between two codes'
list sizes — is an (in)equality on it. `listDecodable` is a `def` whose body *is* one such
inequality, not a parallel definition; keeping the two separate is what once let them disagree, a
`Set.ncard`-based body being satisfied by an *infinite* point list. With `Set.encard` and `ℕ∞`,
point-list finiteness is a consequence of a finite bound rather than a conjunct to be remembered.

## Main definitions

* `ListDecodable.closeCodewords`, `ListDecodable.closeCodewordsRel` — the codewords of `C`
  inside a Hamming ball, at absolute and relative radius. Both are defined under
  `open Classical in`, so they expose no decidability data.
* `ListDecodable.Lambda` — the maximised list size `⨆ f, |closeCodewordsRel C f δ| : ℕ∞`.
* `ListDecodable.listDecodable`, `ListDecodable.uniqueDecodable` — `(r, ℓ)`-list decodability as
  the `abbrev` `Lambda C r ≤ ⌊ℓ⌋₊` at `ℓ : ℝ≥0`, and its `ℓ = 1` special case.

## Main statements

* `ListDecodable.Lambda_le_of_forall_finset_card_le` — the primitive way to bound the size: a
  uniform bound on the *finite subsets* of the point lists, which is the shape a counting
  argument produces. `listDecodable_of_forall_finset_card_le` is its real-bound form.
* `ListDecodable.finite_closeCodewordsRel_of_Lambda_le` — finiteness as a consequence.
* `ListDecodable.Lambda_le_iff_forall_encard_le`, `Lambda_le_iff_forall_ncard_le`,
  `listDecodable_iff_forall_ncard_le` — the pointwise characterisations, as lemmas rather than a
  competing definition, so they cannot drift.
* `ListDecodable.listDecodable_iff_Lambda_le`, `listDecodable_natCast_iff` — the definitional
  unfolding, and its shape at a natural bound, which is what combinatorial list-size theorems
  produce.
* `ListDecodable.listDecodable_of_toENNReal_le_ofReal` — the one boundary at which real-valued
  bounds, such as the Johnson family's `ENNReal.ofReal` shape, meet the integral `Lambda`.
* `ListDecodable.listDecodable.mono` — monotonicity in the list-size bound.
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

/-! ## The maximised list size -/

/-- The maximised list size of `C` at radius `δ`: the supremum over words `f` of the
cardinality of the point list `closeCodewordsRel C f δ`.

**Why `ℕ∞`.** A list size is a cardinal, and the carrier is load-bearing twice over. Integrality
makes flooring a real bound an *equivalence*, so a real-valued Johnson bound is recorded without
loss. And `⊤` records an infinite point list honestly, where `Set.ncard` would report `0` — so a
bound `Lambda C δ ≤ n` cannot be established by an infinite list, and finiteness is a
*consequence* (`finite_closeCodewordsRel_of_Lambda_le`) rather than a side condition.

Membership in `closeCodewordsRel C f δ` is `δᵣ(f, ·) ≤ δ`, and relative Hamming distance is
`1/n`-quantised for `n = |ι|` (`relHammingDistRange`), so `Lambda C` is a step function of
`δ`, constant on each cell `[k/n, (k+1)/n)`. An extremal "largest `δ`" is therefore only
meaningful as an integer boundary index `k/n`, not as a real number. -/
noncomputable def Lambda (C : Code ι F) (δ : ℝ) : ℕ∞ :=
  ⨆ f : ι → F, (closeCodewordsRel C f δ).encard

/-- Each individual point list is bounded by the maximised one. -/
lemma encard_closeCodewordsRel_le_Lambda (C : Code ι F) (δ : ℝ) (f : ι → F) :
    (closeCodewordsRel C f δ).encard ≤ Lambda C δ :=
  le_iSup (fun g : ι → F => (closeCodewordsRel C g δ).encard) f

/-- A `Lambda` bound is exactly a uniform bound on the point lists. -/
lemma Lambda_le_iff_forall_encard_le {C : Code ι F} {δ : ℝ} {b : ℕ∞} :
    Lambda C δ ≤ b ↔ ∀ f : ι → F, (closeCodewordsRel C f δ).encard ≤ b :=
  iSup_le_iff

/-- Finiteness of the point lists is a *consequence* of a finite `Lambda` bound, not an extra
hypothesis. This is what a `Set.ncard`-based formulation has to assert separately. -/
lemma finite_closeCodewordsRel_of_Lambda_le {C : Code ι F} {δ : ℝ} {n : ℕ}
    (h : Lambda C δ ≤ (n : ℕ∞)) (f : ι → F) : (closeCodewordsRel C f δ).Finite :=
  Set.finite_of_encard_le_coe ((encard_closeCodewordsRel_le_Lambda C δ f).trans h)

/-- The `∀`/`ncard` characterisation of a `Lambda` bound, at a natural bound. Use it to recover
the pointwise view inside a proof; being a lemma rather than a second definition, it cannot drift
from `Lambda` and needs no synchronisation. -/
lemma Lambda_le_iff_forall_ncard_le {C : Code ι F} {δ : ℝ} {n : ℕ} :
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
same hypothesis, an infinite set having finite subsets of every cardinality
(`Set.Infinite.exists_subset_card_eq`), so no finiteness of the alphabet is required.

Prefer this over an `[Finite F]` variant taking a bare `ncard` bound. Such a variant would be
*sound* — under a finite alphabet `ncard` cannot lie, so there is no vacuity to exploit — but it
imports a hypothesis the statement does not need, and it lets a proof reach the conclusion without
ever exhibiting the finiteness that list decoding is about. This lemma asks for the bound a
counting argument already has. -/
lemma Lambda_le_of_forall_finset_card_le {C : Code ι F} {δ : ℝ} {n : ℕ}
    (h : ∀ (f : ι → F) (T : Finset (ι → F)), (∀ c ∈ T, c ∈ closeCodewordsRel C f δ) →
      T.card ≤ n) :
    Lambda C δ ≤ (n : ℕ∞) := by
  rw [Lambda_le_iff_forall_encard_le]
  intro f
  have hfin : (closeCodewordsRel C f δ).Finite := by
    by_contra hinf
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf (n + 1)
    have hle := h f T fun c hc => hTsub hc
    omega
  rw [← hfin.cast_ncard_eq]
  exact_mod_cast (Set.ncard_eq_toFinset_card _ hfin) ▸
    h f hfin.toFinset fun c hc => hfin.mem_toFinset.mp hc

/-! ## List decodability

`listDecodable` is notation, not a second notion: its content is the inequality
`Lambda C r ≤ ℓ`. It is an `abbrev`, so it is transparent to the elaborator — one definition to
keep correct, and no bridge lemmas to keep in sync — while the literature-shaped name still reads
better in a hypothesis list than the unfolded inequality.
-/

/-- A code `C` is `(r, ℓ)`-**list decodable**: every point list at relative radius `r` has at most
`ℓ` codewords, that is `Lambda C r ≤ ℓ`.

**The bound is `ℝ≥0`, not `ℝ`.** Johnson bounds are real-valued, so a real bound is wanted; but a
negative list-size bound is meaningless, and admitting one splits the two readings — `⌊ℓ⌋₊ = 0`
says every point list is empty, whereas `(ncard : ℝ) ≤ ℓ < 0` is unsatisfiable. Taking `ℓ : ℝ≥0`
removes the disagreement and with it the `0 ≤ ℓ` side conditions a real bound forces onto every
transfer lemma. Every call site in the tree already uses `ℝ≥0`.

**Proving a `listDecodable` goal.** `exact`, `refine` and `apply` unify at default transparency,
so they see straight through to the underlying `Lambda … ≤ …` — no bridge lemma is needed. `simp`
and `rw` match at *reducible* transparency and so leave it folded, which is what keeps goals
readable; start from `refine Lambda_le_iff_forall_encard_le.mpr ?_` rather than
`rw [Lambda_le_iff_forall_encard_le]` when you want the pointwise form.

**`def`, not `abbrev`, and the difference is not cosmetic.** As an `abbrev` this is *reducible*,
and then Mathlib's `@[simp] ge_iff_le` — an `Iff.rfl` whose left-hand side is a bare `GE.ge`
application — unifies with the whole folded term and `simp` silently unfolds it, all the way to
`WithBot.LE` on `ℕ∞`. Two costs: goals become unreadable, and `listDecodable.mono` becomes
unreachable, since dot notation then looks for `WithBot.LE.mono`. Note this is specific to a
`≤`-shaped body: an `abbrev` whose body is a `∀` is not affected. Downstream STIR/WHIR proofs are
`simp`-heavy, so semireducibility is load-bearing here.

**The floor has two spellings.** `ℝ≥0` carries its own (noncomputable) `FloorSemiring`, inherited
from the subtype, so `⌊ℓ⌋₊` and `⌊(ℓ : ℝ)⌋₊` both elaborate and are definitionally equal — but not
syntactically, so `rw` does not cross between them. This definition uses `⌊ℓ⌋₊`, the spelling
natural to the type; a caller arriving with the coerced form crosses with `norm_cast`, Mathlib's
`Nonneg.nat_floor_coe` being tagged `@[norm_cast]`.

**Flooring at the definition is lossless**, `Lambda` being integer-valued: see
`listDecodable_iff_forall_ncard_le`. Point-list finiteness is likewise implied rather than
asserted. -/
def listDecodable (C : Code ι F) (r : ℝ) (ℓ : ℝ≥0) : Prop :=
  Lambda C r ≤ (⌊ℓ⌋₊ : ℕ∞)

/-- A code `C` is uniquely decodable up to a relative distance `r` if there is at most one
codeword within relative Hamming distance `r` of any word. The `ℓ = 1` case of `listDecodable`. -/
def uniqueDecodable (C : Code ι F) (r : ℝ) : Prop :=
  listDecodable C r 1

/-- **Unfolding lemma.** `listDecodable` *is* the inequality `Lambda C r ≤ ⌊ℓ⌋₊`, by definition.

This is not a bridge between two notions — the five lemmas of that kind are gone, along with the
second definition they connected. It is the entry point for rewriting into the `Lambda` form, which
`exact` and `refine` do not need (they unify at default transparency) but `rw` and `simp only` do,
`listDecodable` being semireducible. -/
lemma listDecodable_iff_Lambda_le {C : Code ι F} {r : ℝ} {ℓ : ℝ≥0} :
    listDecodable C r ℓ ↔ Lambda C r ≤ (⌊ℓ⌋₊ : ℕ∞) := Iff.rfl

/-- At a *natural* list-size bound the floor disappears, so list decodability is exactly a
`Lambda` bound in `ℕ∞`. This is the shape every combinatorial list-size theorem arrives at
(`JohnsonBound`'s in particular), which is why it is worth naming. -/
lemma listDecodable_natCast_iff {C : Code ι F} {r : ℝ} {n : ℕ} :
    listDecodable C r (n : ℝ≥0) ↔ Lambda C r ≤ (n : ℕ∞) := by
  rw [listDecodable_iff_Lambda_le, Nat.floor_natCast]

/-- The `∀`/`ncard` reading of `listDecodable`, and the proof that flooring at the definition loses
nothing: `Lambda C r ≤ ⌊ℓ⌋₊` iff every point list is finite with at most `ℓ` elements as a real
bound. -/
lemma listDecodable_iff_forall_ncard_le {C : Code ι F} {r : ℝ} {ℓ : ℝ≥0} :
    listDecodable C r ℓ ↔
      ∀ f : ι → F, (closeCodewordsRel C f r).Finite ∧
        ((closeCodewordsRel C f r).ncard : ℝ) ≤ ℓ := by
  rw [show listDecodable C r ℓ ↔ Lambda C r ≤ ((⌊ℓ⌋₊ : ℕ) : ℕ∞) from Iff.rfl,
    Lambda_le_iff_forall_ncard_le]
  refine ⟨fun h f => ⟨(h f).1, ?_⟩, fun h f => ⟨(h f).1, ?_⟩⟩
  · calc (((closeCodewordsRel C f r).ncard : ℕ) : ℝ) ≤ ((⌊ℓ⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast (h f).2
      _ ≤ (ℓ : ℝ) := Nat.floor_le ℓ.coe_nonneg
  · exact_mod_cast Nat.le_floor (h f).2

/-- Monotone in the list-size bound, by monotonicity of `Nat.floor`. This is the lemma that ad-hoc
`…_of_le` variants of individual list-size theorems would otherwise each re-derive. -/
lemma listDecodable.mono {C : Code ι F} {r : ℝ} {ℓ₁ ℓ₂ : ℝ≥0}
    (h : listDecodable C r ℓ₁) (hℓ : ℓ₁ ≤ ℓ₂) : listDecodable C r ℓ₂ :=
  h.trans (by exact_mod_cast Nat.floor_le_floor (show (ℓ₁ : ℝ) ≤ (ℓ₂ : ℝ) from hℓ))

/-- `listDecodable` from a bound on the finite subsets of the point lists: the
`listDecodable`-shaped form of `Lambda_le_of_forall_finset_card_le`, at a real bound. -/
lemma listDecodable_of_forall_finset_card_le {C : Code ι F} {r : ℝ} {ℓ : ℝ≥0}
    (h : ∀ (f : ι → F) (T : Finset (ι → F)), (∀ c ∈ T, c ∈ closeCodewordsRel C f r) →
      (T.card : ℝ) ≤ ℓ) :
    listDecodable C r ℓ :=
  Lambda_le_of_forall_finset_card_le fun f T hT => Nat.le_floor (h f T hT)

/-- **The `ENNReal` transfer** — the one boundary at which real-valued bounds meet the integral
`Lambda`. This is the shape the Johnson-family bounds produce.

No finiteness of the alphabet is needed: the hypothesis bounds every point list by
`ENNReal.ofReal ℓ ≠ ⊤`, which forces it finite. -/
lemma listDecodable_of_toENNReal_le_ofReal {C : Code ι F} {δ : ℝ} {ℓ : ℝ≥0}
    (h : (Lambda C δ : ENNReal) ≤ ENNReal.ofReal ℓ) : listDecodable C δ ℓ := by
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

/-! ## Algebra of `Lambda` -/

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

end

end ListDecodable
