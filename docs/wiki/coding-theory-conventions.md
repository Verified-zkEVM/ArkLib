# CodingTheory naming and convention guide

Local conventions used in `ArkLib/Data/CodingTheory/` and its subdirectories.
They are not enforced by tooling. Where they say nothing, follow
[`CONTRIBUTING.md`](../../CONTRIBUTING.md) and Mathlib.

## Theorem naming

Follow the Mathlib conventions in
[`CONTRIBUTING.md`](../../CONTRIBUTING.md#naming-conventions): a theorem name
describes what it says, in `snake_case`, built from the symbol dictionary and the
`_of_` / `_iff` / `_le` suffix conventions.

**Do not encode paper items in declaration names.** No `<authors><year>` suffix,
no `lemma_4_3`, no `thmA2`. Such a name drifts as soon as the source is
renumbered or a second source is cited, and it tells a reader nothing that the
statement does not. Citations belong in the module docstring's `## References`
section; a declaration docstring may name a source only where the statement
genuinely depends on which formulation is meant.

For a statement bounding an ε-error or a list size for a specific code family,
name it after the family, the quantity, and the regime:

```
<codeFamily>_<quantity>_<regime>
```

| Lean name | Reads as |
|---|---|
| `johnson_bound_lambda_le_ell` | the Johnson list-size bound `Λ ≤ ℓ`; alphabet-generic, so no `<codeFamily>` |
| `mds_johnson_lambda_le` | MDS list-size bound in the Johnson regime |
| `rs_lambda_le_johnson_mds`, `irs_lambda_le_johnson_mds`, `frs_lambda_le_johnson_mds` | the same at Reed-Solomon, interleaved RS, folded RS; `johnson_mds` is the `<regime>` |
| `isSubspaceDesign_frsCode`, `isSubspaceDesign_umCode` | a *property* rather than a bound, so the predicate name leads (Mathlib's `isCompact_Icc` shape) |
| `subspaceDesign_tau_lower` | a lower bound on the profile `τ` of a subspace design |
| `irs_rate_distance`, `frs_rate_distance_of_dvd` | an *equation* rather than a bound, so no `<regime>`; `_of_dvd` is the Mathlib hypothesis suffix |
| `lambda_extensionCode_eq_lambda_interleaved` | a descriptive equality |

Slots:

- **`<codeFamily>`** — `linear`, `rs`, `frs`, `irs`, `subspaceDesign`, `mds`, etc.
- **`<quantity>`** — `lambda` (list size), `dim`, `johnson_bound`, `epsCA`,
  `epsMCA`, `epsPG`.
- **`<regime>`** — e.g. `unique_decoding`, `johnson_range`, `capacity`,
  `breakdown`, `lower_capacity`. Skip when there is no regime distinction.

## Definition naming

| Kind | Convention | Examples |
|---|---|---|
| Function with established notation | Lean-id close to the standard notation | `qEntropy`, `Jqℓ`, `Jcap`, `Lambda` (the point list `Λ(C,δ,f)` is the descriptive `closeCodewordsRel`) |
| Descriptive function | lowerCamelCase describing the math | `hammingBallVolume`, `frsEvalOnPoints` |
| Predicate / property | `IsX` style | `LinearCode.IsMDS`, `IsSubspaceDesign` |
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

### Conspicuously absent (only in docstring comments, not actual notation)

- `Λ(C, δ, f)` and `Λ(C, δ)` — used in docstrings for `closeCodewordsRel C f δ` and
  `Lambda C δ`, but there is **no notation declaration**. Use the function names in Lean. A PR
  adding the notation should mirror the `Δ₀(...)` style declared at top level in
  `ListDecodability.lean`.
- `δ_min(C)` — used in docstrings, but not Lean notation. The raw form
  `Code.minDist C / Fintype.card ι`, or `δᵣ C` for the relative minimum distance, covers the
  same quantity.

The literature's `RS[F, L, k]`, `IRS[F, L, k, s]`, `FRS[F, L, k, s, ω]` and `UM[F, L, k, s]`
shortcuts are deliberately *not* Lean notation: descriptive names like `ReedSolomon.code` and
`ReedSolomon.Folded.frsCode` are preferred for navigability. Revisit if a proof becomes hard to
read because of it.

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
| Code rate | `ℚ≥0` | `LinearCode.rate`, `ρ C` — base-field dimension over block length, `dim/n`; over a module alphabet `F^s` this is **not** the alphabet-normalized `dim/(s·n)`, which is `LinearCode.alphabetRate` (`alphabetRate_cast_eq` gives the `ℝ`-cast form the subspace-design statements use inline). For finite nontrivial `F`, positive `s`, and positive block length this is ABF26 D2.5; the Lean formula is total and assigns `0` in the zero-denominator cases. |
| Proximity radius `δ` argument | `ℝ` in existing API; prefer `ℝ≥0` for new API | `Lambda` |
| Real-valued bounds | `ℝ`, then wrapped | RHS of capacity-bound theorems, `JohnsonBound.Jqℓ`, `Jcap` |
| ε-errors (`ε_pg`, `ε_ca`, `ε_mca`) | `ENNReal` | — |
| Probabilities | `ENNReal` | `Pr_{...}[...]` notation |
| List sizes | `ℕ∞` (then cast to `ENNReal` for bounds) | `Lambda`, built from `closeCodewordsRel`'s `.encard` |
| Polynomial degree-bound | `Polynomial.degreeLT F k : Submodule F F[X]` | `ReedSolomon.code`, `Folded.frsCode` |
| Linear code carrier | `Submodule F (ι → A) = ModuleCode ι F A` | `ReedSolomon.code`, `Interleaved.irsCode`, `Folded.frsCode`, `extensionCodeSubmodule` |
| Non-linear code carrier | `Set (ι → A) = Code ι A` | `extensionCode` (the `Set` form; `extensionCodeSubmodule` is its `Submodule` counterpart), theorems over arbitrary alphabets |

Note on `Lambda`: it is built from `Set.encard`, so an infinite point list contributes `⊤`.
The real-valued `listDecodable` predicate records point-list finiteness alongside its `Set.ncard`
bound, so all bridges between it and finite `Lambda` bounds are instance-free;
`Lambda_ne_top` records the separate finite-alphabet consequence.

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

A `sorry` standing in for a result taken from a paper rather than proved in-tree carries a
comment naming its source:

```
sorry -- <classification> [Citation].
```

- `<classification>` ∈ `{external admit, bridge, derived, in-tree admit}`.
- `[Citation]` is a bibliography key with a statement locator (`[GG25 Cor 4.9]`), and that key
  **must** have an entry in
  [`blueprint/src/references.bib`](../../blueprint/src/references.bib), per
  [`CONTRIBUTING.md`](../../CONTRIBUTING.md). For a derived item, name the results it follows
  from instead.

Each such `sorry` should correspond to a row in
[`../kb/audits/open-problems-list-decoding-and-correlated-agreement.md`](../kb/audits/open-problems-list-decoding-and-correlated-agreement.md).
If an admit decomposes into sub-goals, record the decomposition in that row.

The `ArkLib/Data/CodingTheory/` coding-theory layer described by this page currently contains no
`sorry`.

## File and namespace layout

The ABF26 material follows this namespace layout:

- `CodingTheory.*` for non-RS-specific definitions and predicates
  (`qEntropy`, `IsSubspaceDesign`, `ExtensionFieldPresentation`, `extensionCode`,
  `hammingBallVolume`). The erasure result is the metric uniqueness theorem
  `CodingTheory.eq_of_consistent_with_erased`; ArkLib does not expose a cost-free "supports
  erasure correction" predicate, because it would be vacuous.
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

A theorem lives in `CodingTheory.*` when it is about general codes, `ReedSolomon.*` when it is
Reed-Solomon specific, and `ProximityGap.*` when it bounds an `ε`-error.
