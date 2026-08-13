# CodingTheory notation and conventions

What you need in order to read and write statements in `ArkLib/Data/CodingTheory/`: which
notation is in scope, which numeric type each quantity lives in, and the local naming and
layout choices that are specific to this subtree.

General Lean style — naming, docstrings, formatting, citations — is
[`CONTRIBUTING.md`](../../CONTRIBUTING.md). This page does not repeat it; where the two
overlap, `CONTRIBUTING.md` wins.

## Notation

The notation declared in `Basic/Distance.lean`, `Basic/RelativeDistance.lean`,
`Basic/LinearCode.lean` and `InterleavedCode.lean` is global once imported. Most of the
declarations live in `namespace Code` for name resolution, but the notation itself is not
namespaced.

### Distance and norm

- `Δ₀(u, v)` — `hammingDist u v` (absolute Hamming distance, `ℕ`).
- `Δ₀(u, C)` — `distFromCode u C` (absolute distance to a code, `ℕ∞`).
- `Δ₀'(u, C)` — `distFromCode' C u` (computable variant, `ℕ∞`, needs `[Fintype C]`).
- `‖u‖₀` — `hammingNorm u` (Hamming norm of a word, `ℕ`).
- `‖C‖₀` — `Code.dist C` (minimum distance of a code, **`ℕ`**).
- `‖C‖₀'` — `dist' C` (computable variant of `Code.dist`, but **`ℕ∞`**, needs `[Fintype C]`;
  it is a `Finset.min`, so the empty case is `⊤` rather than `0`).

`Code.dist` and `Code.minDist` are both `ℕ`-valued infima over existentially-described sets,
differing only in the comparison:

- `Code.dist C = sInf {d | ∃ u v ∈ C, u ≠ v ∧ Δ₀(u,v) ≤ d}` — bounded-by form;
- `Code.minDist C = sInf {d | ∃ u v ∈ C, u ≠ v ∧ Δ₀(u,v) = d}` — attained form.

Both are `0` for a code with fewer than two elements, since `sInf ∅ = 0`. Watch for this in any
statement that would otherwise be read as "the distance is at least …".

### Relative distance

- `δᵣ(u, v)` — `relHammingDist u v` (relative Hamming distance, `ℚ≥0`).
- `δᵣ(u, C)` — `relDistFromCode u C` (relative distance to a code, `ENNReal`).
- `δᵣ'(w, C)` — `relDistFromCode' w C` (computable variant, `ℚ≥0`).
- `δᵣ C` — `minRelHammingDistCode C` (minimum relative Hamming distance of a code; the absence
  of parentheses is what distinguishes it from `δᵣ(u, C)`).

### Interleaved codes

- `C ^⋈ κ` — `CodeInterleavable.interleaveCode C κ` (instances for both `Set`-based codes and
  `ModuleCode`).
- `⋈| u` — `Interleavable.interleave u` (interleave of a `WordStack`).
- `u ⋈₂ v` — `Interleavable₂.interleave₂ u v` (pairwise interleave).
- `⋈⁻¹| u` — `Stackifiable.stackify u` (the reverse).
- `Λᵢ(u, C, δ)` — `relHammingBallInterleavedCode C u δ`.

### Scoped notation

- `LinearCode.ρ C` — `LinearCode.rate C`. Declared as `scoped syntax &"ρ" term`, so `ρ` remains
  available as a local variable name elsewhere.

### Written in docstrings, but not notation

- `Λ(C, δ, f)` and `Λ(C, δ)` — write `Code.closeCodewordsRel C f δ` and `Code.Lambda C δ` in Lean. A PR
  adding real notation for these should mirror the `Δ₀(...)` style declared at top level in
  `ListDecodability.lean`.
- `δ_min(C)` — write `Code.minDist C / Fintype.card ι`, or `δᵣ C` for the relative form.

The literature's `RS[F, L, k]`, `IRS[F, L, k, s]`, `FRS[F, L, k, s, ω]` and `UM[F, L, k, s]`
shortcuts are deliberately not introduced: `ReedSolomon.code`, `ReedSolomon.Folded.frsCode` and
friends are preferred for navigability. Revisit if a proof becomes hard to read because of it.

## Type conventions

Most friction in this subtree comes from picking the wrong numeric type, so check here first.

| Quantity | Type | Where it shows up |
|---|---|---|
| Hamming distance (pairwise, absolute) | `ℕ` | `hammingDist`, `Δ₀(u, v)`, `hammingNorm`, `‖u‖₀` |
| Min distance of a code (absolute) | `ℕ` | **both** `Code.dist` (`‖C‖₀`) and `Code.minDist` — see above for how they differ |
| Min distance, computable variant | `ℕ∞` | `Code.dist'` (`‖C‖₀'`) |
| Distance to a code (absolute, may be `⊤`) | `ℕ∞` | `distFromCode` (`Δ₀(u, C)`), `distFromCode'` (`Δ₀'(u, C)`) |
| Relative Hamming distance | `ℚ≥0` | `relHammingDist`, `δᵣ(u, v)` |
| Relative distance to a code | `ENNReal` | `relDistFromCode`, `δᵣ(u, C)` |
| Relative distance to a code, computable | `ℚ≥0` | `relDistFromCode'`, `δᵣ'(w, C)` |
| Min relative distance of a code | `ℚ≥0` | `minRelHammingDistCode`, `δᵣ C` |
| Code rate | `ℚ≥0` | `LinearCode.rate`, `ρ C` — see the rate caveat below |
| Alphabet-normalized rate | `ℚ≥0` | `LinearCode.alphabetRate`; `alphabetRate_cast_eq` gives the `ℝ`-cast form |
| Proximity radius `δ` argument | `ℝ`, deliberately unrestricted | `Code.Lambda` — see below; do **not** narrow it |
| Real-valued bounds | `ℝ`, then wrapped | right-hand sides of capacity bounds, `JohnsonBound.Jqℓ`, `Jcap` |
| ε-errors (`ε_pg`, `ε_ca`, `ε_mca`) | `ENNReal` | — |
| Probabilities | `ENNReal` | the `Pr_{...}[...]` notation |
| List sizes | `ℕ∞`, cast to `ENNReal` for real-valued bounds | `Lambda`, built from `closeCodewordsRel`'s `.encard` |
| List-size *bounds* in a predicate | `ℝ≥0` | `Code.IsListDecodable`'s `ℓ` — see below for why, and why it is not `ℕ∞` |
| Polynomial degree bound | `Polynomial.degreeLT F k : Submodule F F[X]` | `ReedSolomon.code`, `Folded.frsCode` |
| Linear code carrier | `Submodule F (ι → A) = ModuleCode ι F A` | `ReedSolomon.code`, `Interleaved.irsCode`, `Folded.frsCode`, `extensionCodeSubmodule` |
| Non-linear code carrier | `Set (ι → A)` | `extensionCode`, the list-decodability layer, and theorems over arbitrary alphabets |

**The two rates are different, and the difference is load-bearing.** `LinearCode.rate` is the
base-field-dimension rate `dim/n`. Over a module alphabet `F^s` the alphabet-normalized rate is
`dim/(s·n)`, which is `LinearCode.alphabetRate`. They agree only at `s = 1`
(`alphabetRate_one_eq_rate`). The subspace-design and MDS statements use the alphabet-normalized
one; substituting `rate` there gives false statements. Both formulas are total and yield `0` in
the zero-denominator cases.

**`Lambda` is built from `Set.encard`,** so an infinite point list contributes `⊤` rather than
collapsing to `0`, and a finite bound therefore *implies* point-list finiteness
(`finite_closeCodewordsRel_of_Lambda_le`) instead of asserting it. `Lambda_ne_top` is the separate
finite-alphabet consequence.

**The list size is the primitive; list-decodability is notation for a bound on it.**
`IsListDecodable` is a `def` whose body *is* `Lambda C r ≤ ⌊ℓ⌋₊` at `ℓ : ℝ≥0` — not a second
definition, so there is nothing to bridge, and the pointwise `∀`/`ncard` readings are lemmas
(`Lambda_le_iff_forall_ncard_le`, `isListDecodable_iff_forall_ncard_le`) that cannot drift from it.

The value has to be primitive; this was not a free choice. `[ABF26]` states, on this one quantity,
bounds that no predicate can carry: **ceilings** (for the constrained code,
`|Λ(C⁺,δ)| ≤ ⌈|F|/(1-η)·ε_ca⌉`), **strict**
bounds (`|Λ(C,δ)| < |F|`), **lower** bounds (Lemma 3.7 / Corollary 3.8), **inequalities and
equalities between two codes' list sizes** (`|Λ(C,δ)| ≤ |Λ(C^⋈m,δ)| ≤ |Λ(C,δ)|^m`, and the
extension-code equality), and **arithmetic** on them (`binom(b+r,r)·|Λ|^r`). A `∀`/`ncard`
predicate expresses only the first two rows of that list.

Consequences worth knowing before touching this layer:

- **Do not add a second predicate for "the list is small."** Keeping one alongside the value is
  how the two came to disagree once already: a `Set.ncard`-based body is satisfied by an
  *infinite* point list, since `ncard` reports `0` there.
- **Do not offer an ambient-finiteness escape hatch** (a `[Finite F]` lemma turning a bare `ncard`
  bound into `IsListDecodable`). Such a lemma is *sound* — under a finite alphabet `ncard` cannot lie
  — but it imports a hypothesis the statement does not need, and it lets a proof reach the
  conclusion without ever exhibiting the finiteness that list decoding is about. Bound the *finite
  subsets* instead: `Lambda_le_of_forall_finset_card_le` is the shape a counting argument produces
  anyway, and it needs nothing of the alphabet.
- **The value is needed regardless of the predicate:** a *lower* bound on a list size, or an
  equality between two codes' list sizes, has no predicate form at all.
- **Unique decoding is the `ℓ = 1` case, not a separate notion.** `Code.uniqueDecodingRadius` and
  `Code.eq_of_le_uniqueDecodingRadius` in `Basic/DecodingRadius.lean` are what the `ProximityGap`
  developments use; `isUniquelyDecodable_relativeUniqueDecodingRadius` identifies them with
  `IsUniquelyDecodable`. Do not grow a third account: [ABF26] introduces the list precisely as the
  extension of unique decoding from `δ_min/2` to an arbitrary radius.
- **Do not give a derived list its own `Lambda`.** A list contained in a point list — WHIR's
  block-relative `Λ𞁒` reaching it through `listBlock_subset_listHamming`, say — is bounded by
  `encard_le_Lambda_of_subset_closeCodewordsRel`. Likewise the absolute-radius point list is the
  relative one at radius `r/n` (`closeCodewords_eq_closeCodewordsRel`), so it needs no size notion.
  One outlier remains, in another owner's file and left for a follow-up:
  `ProximityGap/BCIKS20/AffineSpaces.lean`'s `rs_listDecoding_card_lt_field` inlines point-list
  membership instead of using `closeCodewordsRel`, and is really `Lambda (code domain deg) δ < |F|`
  — the `[ABF26]` statement, whose unified form already exists on the ABF26 branch.
  `Lambda_lt_of_forall_finset_card_lt` is the lemma it would go through: its hypothesis is already
  that theorem's, verbatim.
- **Do not open `closeCodewordsRel` to reason about membership.** It is defined `open Classical in`,
  so under an ambient `[DecidableEq F]` the two instances are definitionally but not syntactically
  equal and neither `simp` nor a direct `Code.mem_relHammingBall_iff` rewrite crosses them.
  `mem_closeCodewordsRel_iff` does the crossing once; use it rather than repeating the
  `convert … using 2; congr` by hand.
- **`Lambda` is a `⨆` but may be used as a `max`.** `exists_encard_eq_Lambda` (and its finite-
  alphabet corollary) supplies the maximising word, which is what [ABF26] Lemma 6.12's proof
  chooses. Do not add a hypothesis asserting the maximum exists.

`exact`/`refine`/`apply` unify at default transparency and so see through `IsListDecodable` to the
`Lambda` inequality; `simp` and `rw` match at reducible transparency and leave it folded. Keep it a
`def`: as an `abbrev` it is reducible, and then Mathlib's `@[simp] ge_iff_le` unifies with the whole
`≤`-shaped body and `simp` unfolds it to `WithBot.LE`, which both mangles goals and makes
`IsListDecodable.mono` unreachable via dot notation. (`omega` is no help either way — it has no `ℕ∞`
support; a bare `by omega` on such a goal only ever succeeds through its assumption fallback.)

**Why the radius is `ℝ` while the bound is `ℝ≥0`.** These are two different objects, and each
argument is about the object rather than about what the tree happens to contain.

The *radius* is a threshold on a total distance function, so `Lambda` is total in it, and every
radius the literature names is an arithmetic expression (`1 - √ρ - η`, `ℓ/(ℓ+1)·(1 - ρ - η)`, a
Johnson radius) that nothing constrains to `[0, 1]` or even to `ℝ≥0`. Narrowing the carrier only
moves the obligation, and both discharges are worse: *truncating* replaces a negative radius by
`0`, where the point list is `{f}` rather than `∅`, so a bound proved of the empty list gets
asserted of a singleton — a silent meaning change in a reachable regime; *guarding* adds
`0 ≤ 1 - √ρ - η` to statements whose mathematics does not need it, which is the anti-pattern two
bullets up. A negative radius is not a degenerate case but the honest value: empty ball,
`Lambda = 0`.

The *bound* is a cardinality, where negative is unsatisfiable rather than weak — so `ℝ≥0` loses no
statement worth making and drops `0 ≤ ℓ` from every transfer. It is real-valued rather than `ℕ∞`
because the theorems that consume a list-decoding hypothesis reuse the same bound as a *number* in
their conclusions — `|Λ(C, δ)| ≤ L` gives `ε_mca ≤ (L²δn + 1/η)/|F|` ([GCXK25] Theorem 3), STIR's
out-of-domain sampling pays `L(L-1)/2` — so an `ℕ∞` hypothesis would force two variables and a
coupling, reintroducing one level up the very problem this layer removes.

That all six predicate call sites already pass `ℝ≥0` for *both* arguments — three in
`ProofSystem/Stir` here, three in `ProofSystem/Whir` on the branches where that development lives —
is a consequence of these being the right carriers, not the reason for choosing them. It does mean
the change costs no call-site edits.

**Where this layer deliberately differs from the `ε`-error layer.** The proximity-error functions
take `δ : I` (the closed unit interval), because their sources define them only there. `Lambda`
takes `δ : ℝ` and is total. That is not drift: `I` carries no `Sub`, so a radius written as
`1 - √ρ - η` cannot be *formed* in it without a membership proof at every call site, and `Lambda`
has meaning outside `[0, 1]` (below, the empty ball; at and above `1`, all of `C`) where an error
probability does not. The coercion at the boundary — `GrandChallenges` writes
`Lambda (C^⋈ m) (gridPt k : ℝ)` — is the honest record of that difference, not a defect to unify
away.

**Several readings, one definition — the alternatives are `iff` lemmas, not parallel `def`s.**
This came up as a design objection worth recording (Ilia Vlasov, ArkLib #731): in a general-purpose
library, should we not carry *several* definitions of list decodability and prove them equivalent,
rather than privileging one? The answer here is that we do carry several readings, as
characterisation lemmas — `Lambda_le_iff_forall_encard_le`, `Lambda_le_iff_forall_ncard_le`,
`isListDecodable_iff_forall_ncard_le`, `isListDecodable_iff_forall_finset_card_le`,
`isListDecodable_iff_toENNReal_le_ofReal`, `isUniquelyDecodable_iff_subsingleton` — which is
Mathlib's own practice and gives the same freedom at the call site. Parallel *definitions* cost
what lemmas do not: `n` of them need `n²` bridges, consumers fragment across them, and each is a
place to drift. This file is the cautionary case — the two notions it replaced *had* drifted, and
the `Set.ncard`-based one turned out to be satisfiable by an **infinite** point list at bound `0`,
which is why a finiteness conjunct had been bolted onto it.

The distinction that makes the question look sharper than it is: `Lambda` is not a rival
*predicate*, it is a different kind of object — a value in `ℕ∞`. It has to be primitive because the
sources do arithmetic on it (see the shapes above); the propositions are what get derived. So the
choice is not between two `Prop`s.

**Whether to keep the predicate at all is an open question, deliberately answered "yes."**
The maximally unified option is to delete `IsListDecodable` and spell its six hypotheses
`Lambda (C i) (δ i) ≤ ⌊l i⌋₊`. It was weighed and not taken, and the reason is not that the
existing hypotheses read that way. A bare inequality has no namespace: `h.mono` on
`Lambda C r ≤ n` resolves to `LE.le.mono` and means something else, so every weakening step would
have to be written out. The named predicate buys `IsListDecodable.mono` and `IsListDecodable.anti_radius`
— the two moves every consumer makes — at zero mathematical cost, the predicate being
*definitionally* the inequality. Nothing rests on the choice, so it stays revisitable; the cost of
revisiting is editing those six hypotheses.

**This layer lives in `namespace Code`, and that was a correction** (2026-08-13). It used to be
`namespace ListDecodable` — a namespace naming a *property* while holding the objects: the point
list, the list size, and one predicate about them. Everything it operates on was already next door
in `Code` (`minDist`, `relHammingDist`, `relHammingBall`, `uniqueDecodingRadius`), and this layer
is now formally tied to that one through `isUniquelyDecodable_relativeUniqueDecodingRadius`, so
keeping the two halves of a single notion in two namespaces was the same fragmentation the layer
exists to remove. A local `abbrev Code ι S := Set (ι → S)` went with it: it shadowed the `Code`
namespace, was used only inside its own file, and `Set (ι → F)` is what the rest of the subtree
writes anyway.

`Lambda` stays capitalised: a term named for a capital Greek letter is capitalised, which is
Mathlib's own treatment (`Real.Gamma`, `Complex.Gamma`) rather than a local exception. The
predicates gained the `Is` prefix Mathlib uses and this subtree already used for `IsMDS` —
`Code.IsListDecodable`, `Code.IsUniquelyDecodable` — which only reads well once the namespace is
right, and lemma names follow in lowerCamel (`isListDecodable_iff_Lambda_le`).

> **Trap, and the reason the move was not free.** `open scoped NNReal` *inside* `namespace Code`
> silently fails to bring in the `ℝ≥0` notation if any `Code.NNReal.*` declaration exists, because
> the `open` resolves to that sub-namespace instead of the real one; `ℝ≥0` then reparses as
> `ℝ ≥ 0` and every signature using it fails with `failed to synthesize LE Type`. Two lemmas in
> `Basic/RelativeDistance.lean` were written `lemma NNReal.foo` inside `namespace Code` and so
> created exactly that — which is why `Basic/DecodingRadius.lean` spells its `NNReal`s longhand.
> They now carry `_root_.` prefixes. **Never declare `Foo.bar` inside `namespace Code` when `Foo`
> is a namespace you also want to `open`; use `_root_.Foo.bar`.**

**Declarations removed when the list size became primitive** (2026-08-12). No `@[deprecated]`
aliases were left. Five of the six cannot be restated at all: they mention `IsListDecodable` at a real
bound, which no longer type-checks. The sixth, `Lambda_le_floor_of_toENNReal_le_ofReal`, mentions
only `Lambda` and so could be kept, but it has no successor to alias *to* — its replacement is a
different statement at `ℝ≥0`. An audit of every local and remote branch, plus both
proximity-prize repositories, found no consumer of any of them. Each replacement below is
compile-checked against the row it replaces:

| Removed | Use instead |
|---|---|
| `Lambda_le_iff_listDecodable` | `isListDecodable_natCast_iff` |
| `Lambda_le_floor_iff_listDecodable` | `isListDecodable_iff_Lambda_le` |
| `Lambda_le_floor_iff_listDecodable_nnreal` | `isListDecodable_iff_Lambda_le` |
| `Lambda_le_floor_of_listDecodable` | `isListDecodable_iff_Lambda_le` (`.mp`) |
| `listDecodable_of_Lambda_le_natCast` | `isListDecodable_natCast_iff` then `IsListDecodable.mono` |
| `Lambda_le_floor_of_toENNReal_le_ofReal` | `isListDecodable_iff_toENNReal_le_ofReal` |

### Coercions

- `ENNReal.ofReal x` when `x : ℝ` may be negative — it truncates to `0`. Used on the right-hand
  side of capacity bounds.
- A direct cast `(x : ENNReal)` when the source is `ℝ≥0` or `ℕ`, hence non-negative.
- `x.toNNReal` for `ℝ → ℝ≥0`. Each call site should be provably non-negative under its
  hypotheses, or deliberately aligned with a stated regime so that truncation lands on a vacuous
  case.
- `Real.rpow x y` for non-integer real exponents; `^` desugars to this when base and exponent are
  both `ℝ`.

## Local naming choices

These supplement [`CONTRIBUTING.md`](../../CONTRIBUTING.md#naming-conventions); they do not
replace it.

- **Code families** are namespaced with a `Code` suffix: `ReedSolomon.code`,
  `ReedSolomon.Folded.frsCode`, `ReedSolomon.Interleaved.irsCode`,
  `ReedSolomon.Multiplicity.umCode`.
- **Functions with established notation** may take a Lean identifier close to it — `qEntropy`,
  `Jqℓ`, `Jcap`, `Lambda` — where a descriptive name would be less recognisable than the symbol.
  This is a narrow exception; prefer descriptive names otherwise (the point list `Λ(C,δ,f)` is
  `closeCodewordsRel`, not `Lam`).
- **A bound on an ε-error or a list size for a specific code family** reads
  `<codeFamily>_<quantity>_<regime>`:
  - `<codeFamily>` — `linear`, `rs`, `frs`, `irs`, `mds`, `subspaceDesign`; omit when the
    statement is alphabet-generic.
  - `<quantity>` — `lambda` (list size), `dim`, `johnson_bound`, `epsCA`, `epsMCA`, `epsPG`.
  - `<regime>` — `unique_decoding`, `johnson_range`, `capacity`, `breakdown`,
    `lower_capacity`, …; omit when there is no regime distinction.

  So `mds_johnson_lambda_le` and `frs_lambda_le_johnson_mds`, while
  `johnson_bound_lambda_le_ell` drops the family because it holds over any alphabet. A statement
  that is not a bound keeps its ordinary Mathlib shape: `isSubspaceDesign_frsCode` leads with the
  predicate, `irs_rate_distance` and `frs_rate_distance_of_dvd` are equations, and
  `lambda_extensionCode_eq_lambda_interleaved` is a descriptive equality.

## Namespace layout

- `CodingTheory.*` — definitions and predicates that are not Reed-Solomon specific: `qEntropy`,
  `IsSubspaceDesign`, `ExtensionFieldPresentation`, `extensionCode`, `hammingBallVolume`,
  `eq_of_consistent_with_erased`.
- `ReedSolomon.*` — the Reed-Solomon variants and their sub-namespaces `Interleaved`, `Folded`,
  `Multiplicity`.
- `ProximityGap.*` — ε-errors and predicate-style proximity material.

A theorem follows its subject: `CodingTheory.*` for general codes, `ReedSolomon.*` when
Reed-Solomon specific, `ProximityGap.*` when it bounds an ε-error.

`CodingTheory` is not a tree-wide convention, and several primitives predate it and live
elsewhere on purpose: MDS-ness is `LinearCode.IsMDS` in `Basic/LinearCode.lean`, the distance and
list primitives are in `Code.*` and `Code.*`, and the Johnson functions are in
`JohnsonBound.*`. Do not relocate them into `CodingTheory` without a separate discussion.

ArkLib deliberately does not expose a cost-free "supports erasure correction" predicate: without
a cost model it would be satisfied by every code. The erasure content is the metric uniqueness
theorem `CodingTheory.eq_of_consistent_with_erased`.

## Sorry comments for external results

A `sorry` standing in for a result taken from a paper rather than proved in-tree names its
source:

```
sorry -- <classification> [Citation].
```

- `<classification>` ∈ `{external admit, bridge, derived, in-tree admit}`.
- `[Citation]` is a bibliography key with a statement locator (`[GG25 Cor 4.9]`), and that key
  must have an entry in [`blueprint/src/references.bib`](../../blueprint/src/references.bib). For
  a derived item, name the results it follows from instead.

Each such `sorry` should correspond to a row in
[`../kb/audits/open-problems-list-decoding-and-correlated-agreement.md`](../kb/audits/open-problems-list-decoding-and-correlated-agreement.md);
if an admit decomposes into sub-goals, record the decomposition there.

`ArkLib/Data/CodingTheory/` currently contains no `sorry`.
