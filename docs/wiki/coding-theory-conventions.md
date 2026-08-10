# CodingTheory naming and convention guide

Local conventions used in `ArkLib/Data/CodingTheory/` and its subdirectories.
These are not enforced by tooling but they are followed consistently across the
ABF26 statement layer. In the current tree that layer is `JohnsonBound/Family.lean`,
`SubspaceDesign.lean`, and the `ReedSolomon/` code families; the next split of the
ABF26 development (`ProximityGap/Errors.lean`, `ProximityGap/CapacityBounds.lean`,
`ListDecoding/Bounds.lean`, `Connections/ListDecodingAndCA.lean`) follows the same
conventions and several examples below are drawn from it. Reviewers should look
for these patterns in both.

## Theorem naming

**Status: target convention, not yet the tree's state.** The pattern below is the
one the ABF26 ε-error and list-size layer is being written to. At the time of
writing **no declaration in the tree conforms to it in full** — the examples in
the table are all forthcoming names from the proximity-gap and toy-problem
splits, not current ones. Treat this section as the rule for *new* ε-error and
list-size bounds; do not expect to find it in existing code, and do not rename
existing declarations to match it without a separate discussion.

Statement-level theorems that bound an ε-error or list-size for a specific code
family should follow the pattern:

```
<codeFamily>_<quantity>_<regime>_<authors><year>
```

Illustrative (all **forthcoming**, none present today):

| Lean name | Reads as |
|---|---|
| `linear_epsCA_1_5_johnson_bgks20` | linear-code `ε_ca` bound in the 1.5-Johnson regime, from BGKS20 |
| `rs_epsMCA_johnson_range_bchks25` | Reed-Solomon `ε_mca` bound in the Johnson range, from BCHKS25 |
| `rs_epsCA_breakdown_cs25` | Reed-Solomon `ε_ca` breakdown bound, from CS25 |
| `linear_lambda_ge_elias_volume_eli57` | linear-code list-size lower bound from Elias volume bound |
| `rs_lambda_high_rate_jh01` | Reed-Solomon list-size bound in the high-rate regime, from JH01 |

Where current names diverge, and why:

| Current name | Divergence |
|---|---|
| `frs_is_subspaceDesign_gk16` | states a *property*, not a bound, so `<quantity>` is the property name |
| `subspaceDesign_tau_lower` | no `<authors><year>` slot; the source is [GG25] |
| `johnson_bound_lambda_le_ell` | `<codeFamily>` is absent (the bound is alphabet-generic) |
| `mds_johnson_lambda_le` | no `<authors><year>` slot; the source is ABF26 Cor 3.3 |
| `lambda_extensionCode_eq_lambda_interleaved` | descriptive equality, not a bound |

Slots:

- **`<codeFamily>`** — `linear`, `rs`, `frs`, `irs`, `subspaceDesign`, `mds`, etc.
- **`<quantity>`** — `lambda` (list size), `dim`, `johnson_bound`; and, from the
  next split, `epsCA`, `epsMCA`, `epsPG`.
- **`<regime>`** — e.g. `unique_decoding`, `johnson_range`, `capacity`,
  `breakdown`, `lower_capacity`. Skip when there's no regime distinction.
- **`<authors><year>`** — lowercase author initials + 2-digit year (`bchks25`,
  `gg25`, `eli57`). For two-paper joint citations: `bchks25_kk25`.

The pattern keeps names searchable, indicates the source paper at a glance, and
disambiguates the same quantity bounded under different regimes (e.g.
`rs_epsCA_breakdown_cs25` vs `rs_epsCA_bchks25_item2`).

## Definition naming

| Kind | Convention | Examples |
|---|---|---|
| Paper-named function | Lean-id close to paper notation | `qEntropy`, `Jqℓ`, `Jcap`, `Lambda` (the point list `Λ(C,δ,f)` is the descriptive `closeCodewordsRel`); next split `epsCA`, `epsMCA` |
| Descriptive function | snake_case describing the math | `hammingBallVolume`, `frsEvalOnPoints`, `restrictedRelHammingDist` (next split) |
| Predicate / property | `IsX` style | `LinearCode.IsMDS`, `IsSubspaceDesign`; (next split) `IsFAdditive`, `LineDecodable` |
| Structure / `abbrev` | PascalCase | `ExtensionFieldPresentation` (a `structure`); `WordStack`, `InterleavedWord` (`abbrev`s for `Matrix`) |
| Code family | namespaced + `Code` suffix | `ReedSolomon.code`, `ReedSolomon.Folded.frsCode`, `ReedSolomon.Interleaved.irsCode` |

## Notation

The notation declared inside `Basic/Distance.lean`, `Basic/RelativeDistance.lean`,
`Basic/LinearCode.lean`, and `InterleavedCode.lean` becomes globally available
once imported (most declarations live inside `namespace Code` for name-resolution
purposes but the notation itself is global).

### Distance and norm

- `Δ₀(u, v)` — `hammingDist u v` (absolute Hamming distance, `ℕ`).
- `Δ₀(u, C)` — `distFromCode u C` (absolute distance to a code, `ℕ∞`).
- `Δ₀'(u, C)` — `distFromCode' C u` (computable variant, `ℕ∞`, needs `[Fintype C]`).
- `‖u‖₀` — `hammingNorm u` (Hamming norm of a word, `ℕ`).
- `‖C‖₀` — `Code.dist C` (minimum distance of a code, **`ℕ`**). Both `Code.dist`
  and `Code.minDist` are `ℕ`-valued infima (`sInf`) over existentially-described
  sets; they differ only in the comparison used:
  `Code.dist C = sInf {d | ∃ u v ∈ C, u ≠ v ∧ Δ₀(u,v) ≤ d}` (bounded-by form) versus
  `Code.minDist C = sInf {d | ∃ u v ∈ C, u ≠ v ∧ Δ₀(u,v) = d}` (attained form).
  Both are `0` for codes with fewer than two elements (`sInf ∅ = 0`).
- `‖C‖₀'` — `dist' C` (computable variant of `Code.dist`, but **`ℕ∞`**, needs
  `[Fintype C]`; it is `Finset.min`, so the empty case is `⊤` rather than `0`).

### Relative distance

- `δᵣ(u, v)` — `relHammingDist u v` (relative Hamming distance, `ℚ≥0`).
- `δᵣ(u, C)` — `relDistFromCode u C` (relative distance to a code, `ENNReal`).
- `δᵣ'(w, C)` — `relDistFromCode' w C` (computable variant, `ℚ≥0`).
- `δᵣ C` — `minRelHammingDistCode C` (minimum relative Hamming distance of a
  code; no parens distinguishes from `δᵣ(u, C)`).

### Interleaved code operators

- `C ^⋈ κ` — `CodeInterleavable.interleaveCode C κ` (interleaved code; instances
  for both `Set`-based codes and `ModuleCode`).
- `⋈| u` — `Interleavable.interleave u` (concrete interleave of a `WordStack`).
- `u ⋈₂ v` — `Interleavable₂.interleave₂ u v` (pairwise interleave).
- `⋈⁻¹| u` — `Stackifiable.stackify u` (reverse).
- `Λᵢ(u, C, δ)` — `relHammingBallInterleavedCode C u δ` (relative Hamming ball
  for an interleaved code).

### Scoped notation (require `open` of the namespace)

- `LinearCode.ρ C` — `LinearCode.rate C` (`ℚ≥0`-valued rate; declared as
  `scoped syntax &"ρ" term`, so `ρ` can still be used as a local variable
  name in other scopes).
- (Next split.) `CodingTheory.restrictedRelHammingDist T f g` with its scoped notation
  `Δ[T]` applied as `Δ[T] (f, g)` (paper-style `Δ_T(f, g)`) ships with the proximity-gap split, next to its
  first consumers; this layer keeps only the full-domain distance notions.

### Conspicuously absent (only in docstring comments, not actual notation)

- `Λ(C, δ, f)` and `Λ(C, δ)` — appear in `ListDecodability.lean` docstrings as
  paper-aliases for `closeCodewordsRel C f δ` and `Lambda C δ` respectively, but **no
  notation declaration**. Use the function names directly. If a future PR wants
  to add the notation, it should mirror the `Δ₀(...)` style declared at top
  level in `ListDecodability.lean`.
- `δ_min(C)` — appears in many docstrings (especially ABF26 statements), but
  not as Lean notation. The raw form `Code.minDist C / Fintype.card ι` or
  the existing `δᵣ C` (relative min distance) covers the same quantity.

The paper's `RS[F, L, k]`, `IRS[F, L, k, s]`, `FRS[F, L, k, s, ω]`,
`UM[F, L, k, s]` shortcuts are *not* introduced as Lean notation. Per design
decision (polish-plan D2): descriptive names like `ReedSolomon.code`,
`ReedSolomon.Folded.frsCode` are preferred for navigability. Revisit if a
downstream proof becomes hard to read because of this choice.

## Type conventions

| Quantity | Type | Where it shows up |
|---|---|---|
| Hamming distance (pairwise, absolute) | `ℕ` | `hammingDist`, `Δ₀(u, v)`, `hammingNorm`, `‖u‖₀` |
| Min distance of a code (absolute) | `ℕ` | **both** `Code.dist` (`‖C‖₀`) and `Code.minDist`; see the notation section above for how they differ |
| Min distance, computable variant | `ℕ∞` | `Code.dist'` (`‖C‖₀'`) |
| Distance to a code (absolute, may be `⊤`) | `ℕ∞` | `distFromCode` (`Δ₀(u, C)`), `distFromCode'` (`Δ₀'(u, C)`) |
| Relative Hamming distance | `ℚ≥0` | `relHammingDist`, `δᵣ(u, v)` |
| Relative distance to a code | `ENNReal` | `relDistFromCode`, `δᵣ(u, C)` |
| Relative distance to a code, computable | `ℚ≥0` | `relDistFromCode'`, `δᵣ'(w, C)` |
| Min relative distance of a code | `ℚ≥0` | `minRelHammingDistCode`, `δᵣ C` |
| Restricted relative Hamming distance | `ℝ≥0` | `restrictedRelHammingDist` (paper `Δ_T(f,g)`; **next split**) |
| Code rate | `ℚ≥0` | `LinearCode.rate`, `ρ C` — base-field dimension over block length, `dim/n`; over a module alphabet `F^s` this is **not** ABF26 D2.5's alphabet-normalized `dim/(s·n)`, which call sites needing it spell out explicitly (`subspaceDesign_tau_lower`, `frs_is_subspaceDesign_gk16`) |
| Proximity radius `δ` argument | `ℝ` today (`ℝ≥0` preferred for new API) | `Lambda`; (next split) `epsCA`, `epsMCA` |
| Paper-style real-valued bounds | `ℝ` (then wrapped) | RHS of capacity-bound theorems, `JohnsonBound.Jqℓ`, `Jcap` |
| ε-errors (`ε_pg`, `ε_ca`, `ε_mca`) | `ENNReal` | (**next split**) `epsCA`, `epsMCA`, `epsPG` |
| Probabilities | `ENNReal` | `Pr_{...}[...]` notation |
| List sizes | `ℕ∞` (then cast to `ENNReal` for bounds) | `Lambda`, built from `closeCodewordsRel`'s `.encard` |
| Polynomial degree-bound | `Polynomial.degreeLT F k : Submodule F F[X]` | `ReedSolomon.code`, `Folded.frsCode` |
| Linear code carrier | `Submodule F (ι → A) = ModuleCode ι F A` | `ReedSolomon.code`, `Interleaved.irsCode`, `Folded.frsCode`, `extensionCodeSubmodule` |
| Non-linear code carrier | `Set (ι → A) = Code ι A` | `extensionCode` (the `Set` form; `extensionCodeSubmodule` is its `Submodule` counterpart), theorems over arbitrary alphabets |

Note on `Lambda`: it is built from `Set.encard`, so an infinite point list contributes `⊤`.
Bridges to the older `Set.ncard`-based `listDecodable` predicate and finite numeric bounds carry
the necessary finiteness hypotheses; `Lambda_ne_top` records the finite-alphabet consequence.

### Coercion conventions

- `ENNReal.ofReal x` when the source `x : ℝ` may be negative (truncates to 0).
  Used for the RHS of capacity-bound theorems.
- Direct cast `(x : ENNReal)` when the source `x : ℝ≥0` / `ℕ` is non-negative.
- `x.toNNReal` for `ℝ → ℝ≥0` conversions; each call site should be either
  provably non-negative under hypotheses or intentionally aligned with the
  paper's stated regime (so truncation matches a vacuous case).
- `Real.rpow x y` for non-integer real exponents; `^` desugars to this when
  both base and exponent are `ℝ`.

## Tagged sorry comments

**The current ABF26 coding-theory layer has no `sorry`s** — every statement in it
is proved. This section is the convention for *future* external admits, kept here
so the next split does not invent a second shape.

External-admit theorems use the canonical comment shape:

```
sorry -- ABF26-X.Y; <classification> [Citation].
```

- `<classification>` ∈ `{external admit, bridge, derived, in-tree admit}`.
- `[Citation]` matches the paper-bibliography key (`[GG25 Cor 4.9]`,
  `[BCHKS25 Thm 1.3]`, etc.), and that key **must** have an entry in
  [`blueprint/src/references.bib`](../../blueprint/src/references.bib) per
  [`CONTRIBUTING.md`](../../CONTRIBUTING.md).
  For derived items, give the antecedent IDs instead
  (`derived from R4.2 + T4.9.2`).

Every tagged sorry should map 1-to-1 to a row in
[`../kb/audits/open-problems-list-decoding-and-correlated-agreement.md`](../kb/audits/open-problems-list-decoding-and-correlated-agreement.md),
and reviewers should expect the `ABF26-X.Y` tag in the comment to match an
audit-doc row. If an admit decomposes into sub-goals, track the decomposition in
the audit row rather than in working notes, so the ledger stays complete.

## File and namespace layout

The ABF26 material follows this namespace layout:

- `CodingTheory.*` for non-RS-specific definitions and predicates
  (`qEntropy`, `IsSubspaceDesign`, `ExtensionFieldPresentation`, `extensionCode`,
  `hammingBallVolume`; next split `LineDecodable`). The substantive erasure result is the
  metric uniqueness theorem `CodingTheory.eq_of_consistent_with_erased`; ArkLib does not expose
  a cost-free “supports erasure correction” predicate because it would be vacuous.
  **Note the pre-existing exceptions**: MDS-ness is `LinearCode.IsMDS`
  (in `Basic/LinearCode.lean`), the distance and list primitives live in
  `Code.*` / `ListDecodable.*`, and the Johnson functions live in
  `JohnsonBound.*`. `CodingTheory` is a *new* namespace introduced by the ABF26
  layer, not a pre-existing tree-wide convention — do not move existing
  declarations into it without a separate discussion.
- `ReedSolomon.*` for RS variants and sub-namespaces
  (`ReedSolomon.Interleaved.irsCode`, `ReedSolomon.Folded.frsCode`,
  `ReedSolomon.Folded.Admissible`, `ReedSolomon.Multiplicity.umCode`).
- `ProximityGap.*` for ε-errors, grand challenges, and predicate-style
  proximity material.

Theorems (admitted external results) stay in `CodingTheory.*` where they
operate on general codes, `ReedSolomon.*` where RS-specific, or
`ProximityGap.*` where they bound an `ε`-error.
