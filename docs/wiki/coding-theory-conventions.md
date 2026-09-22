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
| Proximity radius `δ` for list size and generator MCA | `ℝ`, deliberately unrestricted | `Code.Lambda`, `IsMCA`, `mcaError` |
| Proximity radius `δ` for paper-facing errors | `ℝ≥0` | `epsPg`, `epsCa`, `epsMca` |
| Proximity radius `δ` as a *quantifier on an error bound* | `I` (`= [0,1]`) | `IsMCAGenerator`'s `∀ δ : I` — this is the one place the sources' `[0,1]` binds |
| Real-valued bounds | `ℝ`, then wrapped | right-hand sides of capacity bounds, `JohnsonBound.Jqℓ`, `Jcap` |
| ε-errors (`ε_pg`, `ε_ca`, `ε_mca`) — value | `ENNReal` | it is a supremum of probabilities |
| ε-errors — *bound*, compared with `↑` not `ENNReal.ofReal` | `I → ℝ≥0` | `IsMCAGenerator`'s `ε_mca` |
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

**Where the closed interval `[0,1]` does and does not bind.** It binds on the *error bound*:
BCGM25 Def 3.14 types `ϵMCA : [0,1] → [0,1]` and quantifies `γ ∈ [0,1]`, and both ABF26 Grand
Challenges quantify `δ* ∈ [0,1]`, so `IsMCAGenerator` quantifies `δ : I` and types its `ε_mca` as
`I → ℝ≥0`. Closed, not `Ioo 0 1`: BCGM25 Lemma 3.18 gives `ϵMCA(0) = ϵZE` and Remark 3.15 saturates
`ϵMCA(γ) = 1` above some `γ₀ < 1`.

It does **not** bind on the radius argument to a value. `IsMCA`, `mcaError`, and `Lambda` take
`δ : ℝ`. The abbreviation `epsMca` specializes `mcaError` to affine lines and accepts `δ : ℝ≥0`.
See [`proximity-error-conventions.md`](proximity-error-conventions.md) for the complete
proximity-error API.

**`Lambda` is built from `Set.encard`,** so an infinite point list contributes `⊤` rather than
collapsing to `0`, and a finite bound therefore *implies* point-list finiteness
(`finite_closeCodewordsRel_of_Lambda_le`) instead of asserting it. `Lambda_ne_top` is the separate
finite-alphabet consequence.

**The list size is the primitive; list-decodability is notation for a bound on it.**
`IsListDecodable` is a `def` whose body *is* `Lambda C r ≤ ⌊ℓ⌋₊` at `ℓ : ℝ≥0`, so there is nothing to
bridge, and the pointwise readings are lemmas that cannot drift from it.

`[ABF26]` puts shapes on this one quantity that no predicate can carry:
ceilings (`|Λ(C⁺,δ)| ≤ ⌈|F|/(1-η)·ε_ca⌉`), strict bounds (`|Λ(C,δ)| < |F|`), *lower* bounds,
equalities between two codes' list sizes (`|Λ(C,δ)| ≤ |Λ(C^⋈m,δ)| ≤ |Λ(C,δ)|^m`, and the
extension-code equality), and arithmetic (`binom(b+r,r)·|Λ|^r`). A predicate expresses only the
upper bounds. The value is therefore primitive and the propositions about it are derived; `Lambda` is
not a rival predicate but a different kind of object.

**Several readings, one definition.** The alternative formulations are characterisation lemmas, not
parallel `def`s: `Lambda_le_iff_forall_encard_le`,
`Lambda_le_iff_forall_ncard_le`, `isListDecodable_iff_forall_ncard_le`,
`isListDecodable_iff_forall_finset_card_le`, `isListDecodable_iff_toENNReal_le_ofReal`,
`isUniquelyDecodable_iff_subsingleton`. That is Mathlib's practice and gives the same freedom at the
call site, where parallel definitions would need `n²` bridges, fragment consumers, and each drift.

Rules for this layer:

- **Do not add a second predicate for "the list is small."** A `Set.ncard`-based body is satisfied by an
  *infinite* point list, since `ncard` reports `0` there, so it needs a finiteness conjunct carried
  alongside it — which is the drift this layer exists to prevent.
- **Do not offer an ambient-finiteness escape hatch** (a `[Finite F]` lemma turning a bare `ncard`
  bound into `IsListDecodable`). It would be sound but imports a hypothesis the statement does not
  need. Bound the *finite subsets* instead, with `Lambda_le_of_forall_finset_card_le`, which is the
  shape a counting argument produces anyway and needs nothing of the alphabet.
- **Unique decoding is the `ℓ = 1` case, not a separate notion.** `Code.uniqueDecodingRadius` and
  `Code.eq_of_le_uniqueDecodingRadius` in `Basic/DecodingRadius.lean` are what the `ProximityGap`
  developments use; `isUniquelyDecodable_relativeUniqueDecodingRadius` identifies them with
  `IsUniquelyDecodable`. Do not grow a third account.
- **Do not give a derived list its own `Lambda`.** A list contained in a point list is bounded by
  `encard_le_Lambda_of_subset_closeCodewordsRel`, and the absolute-radius point list is the relative
  one at radius `r/n` (`closeCodewords_eq_closeCodewordsRel`). A counting argument that inlines
  point-list membership should go through `Lambda_lt_of_forall_finset_card_lt` instead.
- **Do not open `closeCodewordsRel` to reason about membership.** It is defined `open Classical in`,
  so under an ambient `[DecidableEq F]` the two instances are definitionally but not syntactically
  equal and neither `simp` nor a direct `Code.mem_relHammingBall_iff` rewrite crosses them.
  `mem_closeCodewordsRel_iff` does the crossing once.
- **`Lambda` is a `⨆` but may be used as a `max`.** `exists_encard_eq_Lambda` and its
  finite-alphabet corollary supply the maximising word. Do not add a hypothesis asserting the
  maximum exists.
- **Keep `IsListDecodable` a `def`, not an `abbrev`.** As an `abbrev` it is reducible, and Mathlib's
  `@[simp] ge_iff_le` then unifies with the `≤`-shaped body, so `simp` unfolds it to `WithBot.LE` —
  mangling goals and making `IsListDecodable.mono` unreachable via dot notation. `exact`, `refine`
  and `apply` see through it either way; `simp` and `rw` need `isListDecodable_iff_Lambda_le`.
  (`omega` is no help on such goals: it has no `ℕ∞` support.)
- **Keep the predicate.** Deleting it and spelling the hypotheses `Lambda (C i) (δ i) ≤ ⌊l i⌋₊` was
  weighed and not taken: a bare inequality has no namespace, so `h.mono` would resolve to
  `LE.le.mono`. The name buys `IsListDecodable.mono` and `IsListDecodable.anti_radius` at zero
  mathematical cost, the predicate being *definitionally* the inequality, so the choice stays
  revisitable.

**Why the radius is `ℝ` while the bound is `ℝ≥0`.** They are different objects.

The *radius* is a threshold on a total distance function, so `Lambda` is total in it, and every
radius the literature names is an arithmetic expression (`1 - √ρ - η`, `ℓ/(ℓ+1)·(1 - ρ - η)`, a
Johnson radius) that nothing constrains to `[0, 1]` or even to `ℝ≥0`. Narrowing only moves the
obligation, and both discharges are worse: *truncating* replaces a negative radius by `0`, where the
point list is `{f}` rather than `∅`, so a bound proved of the empty list gets asserted of a
singleton; *guarding* adds `0 ≤ 1 - √ρ - η` to statements whose mathematics does not need it. A
negative radius is the honest value: empty ball, `Lambda = 0`.

The *bound* is a cardinality, where negative is unsatisfiable rather than weak, so `ℝ≥0` loses no
statement worth making and drops `0 ≤ ℓ` from every transfer. It is real-valued rather than `ℕ∞`
because the theorems consuming a list-decoding hypothesis reuse the same bound as a *number* in
their conclusions, and an `ℕ∞` hypothesis would force two variables and a coupling between them.

**How this layer composes with the proximity-error layer.** `Code.Lambda` and `mcaError` both take
total real radii, while `epsPg`, `epsCa`, and the affine-line abbreviation `epsMca` take
nonnegative radii. A numeric cast is therefore sometimes needed, as in
`Lambda (C^⋈ m) (gridPt k : ℝ)`, but no interval-membership proof is.

**This layer lives in `namespace Code`,** alongside the objects it operates on (`minDist`,
`relHammingDist`, `relHammingBall`, `uniqueDecodingRadius`), to which it is tied through
`isUniquelyDecodable_relativeUniqueDecodingRadius`. Codes are spelled `Set (ι → F)` rather than
through a local abbreviation: an `abbrev Code` here would be `Code.Code`, which trips
`linter.dupNamespace`, and a non-`sorry` warning under `ArkLib/` fails `validate.sh`.

`Lambda` is capitalised because it is named for a capital Greek letter, as Mathlib does with
`Real.Gamma`. Predicates take the `Is` prefix — `Code.IsListDecodable`, `Code.IsUniquelyDecodable`,
matching `IsMDS` — and their lemmas are lowerCamel (`isListDecodable_iff_Lambda_le`).

> **Never declare `Foo.bar` inside `namespace Code` when `Foo` is a namespace you also want to
> `open` there.** Write `_root_.Foo.bar`, or put the lemma where it belongs. The declaration brings
> `Code.Foo` into existence, and an `open scoped Foo` *inside* `namespace Code` — here or in any
> importing file — then resolves to that empty sub-namespace, silently dropping the notation. For
> `NNReal` the symptom is `ℝ≥0` reparsing as `ℝ ≥ 0`, with every signature using it failing on
> `failed to synthesize LE Type`. The `open` must be lexically inside the namespace to bite:
> `open Code NNReal` in one command, or `open Code` with a separate root-level `open scoped NNReal`,
> are unaffected.

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
  - `<quantity>` — `lambda` (list size), `dim`, `johnson_bound`, `epsCa`, `epsMca`, `epsPg`.
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

`ArkLib/Data/CodingTheory/` contains a baselined set of admitted external results. New or changed
admissions must use this comment form and pass the exhaustive axiom sweep.
