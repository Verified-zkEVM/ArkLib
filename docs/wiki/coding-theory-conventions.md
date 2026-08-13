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

- `Λ(C, δ, f)` and `Λ(C, δ)` — write `closeCodewordsRel C f δ` and `Lambda C δ` in Lean. A PR
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
| Proximity radius `δ` argument | `ℝ` in existing API; prefer `ℝ≥0` for new API | `Lambda` |
| Real-valued bounds | `ℝ`, then wrapped | right-hand sides of capacity bounds, `JohnsonBound.Jqℓ`, `Jcap` |
| ε-errors (`ε_pg`, `ε_ca`, `ε_mca`) | `ENNReal` | — |
| Probabilities | `ENNReal` | the `Pr_{...}[...]` notation |
| List sizes | `ℕ∞`, cast to `ENNReal` for bounds | `Lambda`, built from `closeCodewordsRel`'s `.encard` |
| Polynomial degree bound | `Polynomial.degreeLT F k : Submodule F F[X]` | `ReedSolomon.code`, `Folded.frsCode` |
| Linear code carrier | `Submodule F (ι → A) = ModuleCode ι F A` | `ReedSolomon.code`, `Interleaved.irsCode`, `Folded.frsCode`, `extensionCodeSubmodule` |
| Non-linear code carrier | `Set (ι → A) = Code ι A` | `extensionCode`, and theorems over arbitrary alphabets |

**The two rates are different, and the difference is load-bearing.** `LinearCode.rate` is the
base-field-dimension rate `dim/n`. Over a module alphabet `F^s` the alphabet-normalized rate is
`dim/(s·n)`, which is `LinearCode.alphabetRate`. They agree only at `s = 1`
(`alphabetRate_one_eq_rate`). The subspace-design and MDS statements use the alphabet-normalized
one; substituting `rate` there gives false statements. Both formulas are total and yield `0` in
the zero-denominator cases.

**`Lambda` is built from `Set.encard`,** so an infinite point list contributes `⊤` rather than
collapsing to `0`. The real-valued `listDecodable` predicate pairs point-list finiteness with its
`Set.ncard` bound, which is what makes every bridge between the two instance-free;
`Lambda_ne_top` is the separate finite-alphabet consequence.

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
list primitives are in `Code.*` and `ListDecodable.*`, and the Johnson functions are in
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
