/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.Basic.Distance

/-!
# Erasure correction for codes over a finite alphabet

A generic erasure-correction predicate `SupportsErasureCorrection C`
asserting that a deterministic algorithm exists that recovers any codeword
`u ∈ C` from a partial observation `f : ι → Option F` with strictly fewer
than `δ_min(C) · |ι|` erasures, and returns `⊥` otherwise.

**What this file delivers, and what it does not.** `SupportsErasureCorrection` is a
*tautology*: `exists_erasure_corrector` proves it for an arbitrary code, with no hypotheses
whatsoever (including at `∅` and at `Set.univ`). The reason is that ABF26 Definition 6.4's
content lives entirely in the corrector's *correction time* `ecor_C` — Lemma 6.5's claim is
`ecor_C = O((s · n)³)` — and ArkLib's extractors are uniformly cost-free, so no cost parameter
is carried and `∃ E` ranges over arbitrary mathematical functions. The predicate must
therefore **not** be used as a hypothesis in the expectation that it constrains `C`.

The substantive, reusable content of this file is the uniqueness lemma
`eq_of_consistent_with_erased`: below `minDist C` erasures at most one codeword is consistent
with the partial observation (a Hamming-distance pigeonhole). That is what makes the classical
corrector exist. See the Definition 6.4 and Lemma 6.5 rows, and Roadmap Phase 6.2, of
`docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md` for the full ledger
entry.

Lives in `Data/CodingTheory/` rather than at the protocol layer (where the
ABF26 toy problem originally introduced it) because the predicate is generic
across proof systems — any reduction whose extractor erasure-decodes its
oracles consumes the same shape.

## Main definitions

* `CodingTheory.SupportsErasureCorrection` — ABF26 Definition 6.4 with the correction-time
  parameter dropped (and hence, as explained above, a tautology).

## Main statements

* `CodingTheory.eq_of_consistent_with_erased` — uniqueness of the codeword consistent with a
  lightly-erased word.
* `CodingTheory.exists_erasure_corrector` — a corrector exists, for every code.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26] (§6.2: Definition 6.4, Lemma 6.5)
* [Guruswami, V., Rudra, A., and Sudan, M., *Essential Coding Theory*][codingtheory]
    (Proposition 1.4.2(4): a code of minimum distance `d` corrects exactly `d − 1` erasures;
    Exercise 5.3 for the Gaussian-elimination running time, which is out of scope here)
* [Bordage, S., Chiesa, A., Guan, Z., and Manzur, I., *All Polynomial Generators Preserve
    Distance with Mutual Correlated Agreement*][BCGM25] (Definition 3.7,
    `LinearCode.projectedWord` — see the generalization note on
    `eq_of_consistent_with_erased`)
-/

namespace CodingTheory

open Code

variable {ι F : Type*} [Fintype ι]

/-- **ABF26 Definition 6.4** (erasure-correction predicate).

A code `C ⊆ (ι → F)` supports **erasure correction** if there exists a
deterministic algorithm `E_C` that, on any input `f : ι → Option F`:

  (i)  if `f` has strictly fewer than `δ_min(C) · |ι|` erasures and
       there exists a (necessarily unique) codeword `u ∈ C` agreeing
       with `f` off the erasures, then `E_C(f) = some u`;
  (ii) otherwise `E_C(f) = none`.

Clause (ii) — easy to miss in a quick port from the paper — pins down the *witness*: without
it, `E := fun _ ↦ some <arbitrary>` satisfies the recovery clause for any `f` whose
preconditions fail. With it, the corrector is essentially unique.

**Warning: this predicate is a tautology; it says nothing about `C`.** Clause (ii) constrains
`E`, not `C`, so it does not make the predicate informative. The paper additionally tracks the
corrector's running time (`ecor_C`), and that cost bound is the entire content of ABF26 D6.4
and L6.5 (`ecor_C = O((s · n)³)`). ArkLib's extractors are uniformly cost-free (unclocked), so
no cost parameter is carried here, and `∃ E` consequently ranges over arbitrary mathematical
functions: `exists_erasure_corrector` discharges `SupportsErasureCorrection C` for *every*
`C : Set (ι → F)` with no hypotheses. Do **not** use `SupportsErasureCorrection` as a
hypothesis expecting it to constrain `C`; a statement that needs the erasure-decoding fact
should use the uniqueness lemma `eq_of_consistent_with_erased` instead, which is the
substantive reusable content here. (Ledger: the Definition 6.4 / Lemma 6.5 rows and Roadmap
Phase 6.2 of `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`.)

Degenerate boundary, as a consequence of the same reading: for `|C| ≤ 1` there are no distinct
pairs of codewords, so `Code.minDist C = sInf ∅ = 0`. The recovery guard
`#erasures < Code.minDist C` is then unsatisfiable, and clause (ii) forces `E f = none` even on
a fully unerased exact codeword — so the predicate is satisfied only by the trivial corrector
`fun _ ↦ none`. Consumers wanting actual recovery need a nontrivial code. -/
def SupportsErasureCorrection [DecidableEq F]
    (C : Set (ι → F)) : Prop :=
  ∃ E : (ι → Option F) → Option (ι → F),
    ∀ (f : ι → Option F),
      -- (i) recovery clause
      (∀ u ∈ C, (∀ i, f i = some (u i) ∨ f i = none) →
        ((Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C →
          E f = some u)) ∧
      -- (ii) failure clause: ⊥ unless both small-erasures AND a witness exist
      (¬ (∃ u ∈ C, (∀ i, f i = some (u i) ∨ f i = none) ∧
            (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C) →
        E f = none)

/-- **Uniqueness pigeonhole for erasure decoding (ABF26 L6.5 core).** Two
codewords consistent with the same partially-erased word `f`, with strictly
fewer than `minDist C` erasures, are equal: they can disagree only on erased
coordinates, so their Hamming distance is below the code's minimum distance.

**Generalization note (for whoever needs this next).** This is the `Option`-clothed special
case of the injectivity of `LinearCode.projectedWord`
(`ArkLib/Data/CodingTheory/Basic/LinearCode.lean`, Definition 3.7 of [BCGM25]): the general
statement is that two codewords of `C` which agree outside a set `T` with
`T.card < Code.minDist C` are equal, i.e. `projectedWord · Tᶜ` is injective on `C`. Here `T`
is the erasure set `{i | f i = none}`. That general form belongs next to `projectedWord`, and a
future author should put it there and derive this lemma from it rather than re-deriving the
pigeonhole. It is stated here only because `Basic/Distance.lean` (this file's sole ArkLib
import) sits *below* `Basic/LinearCode.lean`, and no `projectedWord` injectivity lemma exists
yet to route through. -/
theorem eq_of_consistent_with_erased [DecidableEq F] {C : Set (ι → F)}
    {f : ι → Option F} {u v : ι → F} (hu : u ∈ C) (hv : v ∈ C)
    (hfu : ∀ i, f i = some (u i) ∨ f i = none)
    (hfv : ∀ i, f i = some (v i) ∨ f i = none)
    (hcard : (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C) :
    u = v := by
  by_contra hne
  -- `u` and `v` agree wherever `f` is not erased.
  have hsub : disagreementCols u v ⊆ Finset.univ.filter (fun i ↦ f i = none) := by
    intro i hi
    rw [mem_disagreementCols] at hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hfu i with h1 | h1
    · rcases hfv i with h2 | h2
      · exact absurd (Option.some.inj (h1.symm.trans h2)) hi
      · exact h2
    · exact h1
  have hdist : Δ₀(u, v) ≤ (Finset.univ.filter (fun i ↦ f i = none)).card := by
    rw [hammingDist_eq_disagreementCols_card]
    exact Finset.card_le_card hsub
  -- but distinct codewords are at distance ≥ `minDist C`.
  have hmin : Code.minDist C ≤ Δ₀(u, v) :=
    Nat.sInf_le ⟨u, hu, v, hv, hne, rfl⟩
  omega

/-- **An erasure corrector exists, for every code.** A witness for
`CodingTheory.SupportsErasureCorrection C` exists for an arbitrary `C : Set (ι → F)`, with no
hypotheses at all.

The corrector is defined classically: if a codeword of `C` consistent with the
non-erased positions exists (necessarily unique below `minDist C` erasures, by
`eq_of_consistent_with_erased`), return it; otherwise return `none`.

This is the *existence half* of ABF26 Lemma 6.5 (`lemma:efficient-erasure-correction`), and
the reason `SupportsErasureCorrection` is a tautology — see that definition's docstring.

**Scope caveat — this theorem captures nothing from the paper's cited source.** The substance
of ABF26 L6.5 and of its [codingtheory] citation is the *algorithmic* claim that an
`F`-additive code is erasure-corrected in `O((s · n)^3)` field operations (Gaussian elimination
on the parity-check matrix). That polynomial-time bound is out of ArkLib's cost-free model —
extractors are uniformly unclocked across the library — so it is deliberately not formalized.
Accordingly this theorem has **no additivity hypothesis** and uses nothing from
[codingtheory]; the name deliberately no longer claims otherwise. -/
theorem exists_erasure_corrector [DecidableEq F]
    (C : Set (ι → F)) : SupportsErasureCorrection C := by
  classical
  refine ⟨fun f ↦
    if h : ∃ u ∈ C, (∀ i, f i = some (u i) ∨ f i = none) ∧
        (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C
    then some h.choose else none, fun f ↦ ⟨?_, ?_⟩⟩
  · -- (i) recovery: the classical witness coincides with `u` by uniqueness.
    intro u hu hfu hcard
    have h : ∃ u ∈ C, (∀ i, f i = some (u i) ∨ f i = none) ∧
        (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C :=
      ⟨u, hu, hfu, hcard⟩
    dsimp only
    rw [dif_pos h]
    obtain ⟨hmem, hagree, _⟩ := h.choose_spec
    exact congrArg some (eq_of_consistent_with_erased hmem hu hagree hfu hcard)
  · -- (ii) failure clause: the guard is exactly the negated hypothesis.
    intro hno
    dsimp only
    rw [dif_neg hno]

end CodingTheory
