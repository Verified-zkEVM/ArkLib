# Proximity Error API

This page describes ArkLib's numeric APIs for proximity gap, correlated agreement, and mutual
correlated agreement. For code carriers and distance types, see
[`coding-theory-conventions.md`](coding-theory-conventions.md). For probability notation, see
[`probability-conventions.md`](probability-conventions.md).

## Modules

| Module | Contents |
| --- | --- |
| `ProximityGenerator/Basic.lean` | Generator-parametric mutual correlated agreement: `IsMCA`, `mcaError`, and `IsMCAGenerator` |
| `ProximityGap/Errors.lean` | `epsPg`, `epsCa`, `epsMca`, their order properties, predicate bridges, and affine-line MCA comparison theorems |
| `ProximityGap/Basic.lean` | Predicate forms of proximity gap and correlated agreement |
| `ProximityGenerator/TensorGenerator.lean` | Mutual-correlated-agreement transport through tensor generators and row-wise interleaving |
| `ProximityGap/GrandChallenges.lean` | Integer-grid challenge predicates, answer types, witnesses, and Reed--Solomon prize specializations |
| `ProximityGap/CapacityBounds.lean` | Source-audited §4 upper/lower bounds on `epsCa` and canonical `mcaError` |
| `ProximityGap/LineDecoding.lean` | Natural-cardinality line decodability and its MCA consequence |
| `Connections/ListDecodingAndCA.lean` | §5 conversions between `Code.Lambda`, CA, and MCA |
| `ProximityGap/GrandChallenges/CapacityBounds.lean` | Admit-dependent capacity-bound witness extensions; imports the core carrier, never conversely |

## Mutual correlated agreement

`CoreDefinitions.mcaError` is the numeric mutual-correlated-agreement value:

```lean
noncomputable def mcaError
    (G : Generator S ℓ F) (C : ModuleCode ι F A) (δ : ℝ) : ENNReal
```

It takes a generator, a module code, and a total real radius. `IsMCAGenerator` packages a
pointwise bound on this value over radii in the unit interval:

```lean
def IsMCAGenerator
    (G : Generator S ℓ F) (ε : I → ℝ≥0) (C : ModuleCode ι F A) : Prop
```

The defining equivalence is `isMCAGenerator_iff_mcaError_le`. Use
`IsMCAGenerator.prob_le` when a proof needs the probability bound for one word family.

`epsMca` provides concise notation for the affine-line specialization at a nonnegative radius:

```lean
noncomputable abbrev epsMca (C : ModuleCode ι F A) (δ : ℝ≥0) : ENNReal :=
  mcaError (AffineLineGenerator F) C (δ : ℝ)
```

The abbreviation is transparent; use the lemmas for `mcaError` directly.

The main value lemmas are:

- `mcaError_mono`, `mcaError_le_one`, and `mcaError_ne_top`;
- `mcaError_eq_of_floor_eq` for constancy on integer-agreement cells;
- the transport lemmas in `MCAGenerator.lean` and `TensorGenerator.lean`.

## Proximity gap and correlated agreement

`Errors.lean` provides the following paper-facing values:

| Declaration | Type and meaning |
| --- | --- |
| `epsPg C δ` | proximity-gap error for `C : Set (ι → A)` and `δ : ℝ≥0` |
| `epsCa C δ_fld δ_int` | affine-line correlated-agreement error with separate fold and interleaved radii |
| `epsCa' C δ` | equal-radius specialization `epsCa C δ δ` |
| `epsCaCurves C k δ_fld δ_int` | correlated-agreement error for degree-`k` polynomial combinations |
| `epsCaAffineSpaces C k δ_fld δ_int` | correlated-agreement error for uniform samples from affine spans |

These values use `Set` code carriers because their events are also meaningful for nonlinear codes.
Use `ModuleCode` when applying the comparison theorems with mutual correlated agreement.

Their order behavior is not uniform:

| Value | Available behavior |
| --- | --- |
| `mcaError G C δ` (and hence `epsMca C δ`) | monotone in `δ` |
| `epsCa C δ_fld δ_int` | monotone in `δ_fld` and antitone in `δ_int` |
| `epsPg C δ` | zero for `1 ≤ δ`; the zero singleton code gives a positive value at `δ = 0`, so global monotonicity fails in general |
| `epsCa' C δ` | zero for `1 ≤ δ`; no global monotonicity lemma is provided |

The relevant declarations are `epsCa_mono_left`, `epsCa_antitone_right`,
`epsPg_eq_zero_of_one_le`, `epsCa_eq_zero_of_one_le_right`, and
`epsPg_singleton_zero_pos`.

## Comparisons and bridges

For a module code and a common nonnegative radius,

```text
epsPg C δ ≤ epsCa C δ δ ≤ epsMca C δ.
```

This is `epsPg_le_epsCa_le_epsMca`; its two component inequalities are
`epsPg_le_epsCa` and `epsCa_le_mcaError_affineLine`.

The unique-decoding comparison is:

- `mcaError_le_epsCa_of_pos_of_two_mul_lt_dist` for the MCA-to-CA direction;
- `mcaError_eq_epsCa_of_pos_of_two_mul_lt_dist` for the resulting equality.

For a positive row-wise interleaving width and a radius in `(0, 1)`:

- `mcaError_le_moduleInterleavedCode` gives the base-to-interleaved inequality;
- `mcaError_interleaved_le` gives the interleaved-to-base inequality;
- `mcaError_interleaved_eq` gives equality.

The numeric correlated-agreement values are connected to the predicate API by:

- `δ_ε_correlatedAgreementAffineLines_iff_epsCa_le`;
- `δ_ε_correlatedAgreementCurves_iff_epsCaCurves_le`;
- `δ_ε_correlatedAgreementAffineSpaces_iff_epsCaAffineSpaces_le`.

These equivalences allow existing predicate-based proofs to consume numeric bounds without
introducing a second predicate.

## Numeric types

| Quantity | Type |
| --- | --- |
| radius passed to `IsMCA`, `mcaError`, or `Code.Lambda` | `ℝ` |
| radius passed to `epsPg`, `epsCa`, or `epsMca` | `ℝ≥0` |
| radius quantified by `IsMCAGenerator` | `I`, the closed unit interval |
| numeric error value or probability | `ENNReal` |
| error bound | `ℝ≥0` |

Compare an `ENNReal` value with a nonnegative bound using a coercion, for example
`mcaError G C δ ≤ (ε : ENNReal)`. Use `mcaError_ne_top` before applying `ENNReal.toNNReal`.

## Grand challenges

`GrandChallenges.lean` defines `grandMcaChallenge` and `grandListDecodingChallenge`. Each accepts
either:

- an adjacent grid crossing between `k / n` and `(k + 1) / n`; or
- an `allGood` certificate covering every grid point through radius one.

Use `GrandMcaResolution` or `GrandListResolution` for adjacent boundaries and `GrandMcaAnswer` or
`GrandListAnswer` when the endpoint case must also be representable. The methods `to_challenge`
convert either form to its logical challenge.

The prize API uses `PrizeDomainAdmissible`, `prizeRate`, `prizeDimension`, and
`prizeCode_rate_eq` to select Reed--Solomon codes at exact rates. `McaPrizeResolution.to_prize`
and `ListPrizeResolution.to_prize` assemble per-rate answers.

Bounds that produce one-sided prize evidence belong in extension modules below
`ProximityGap/GrandChallenges/`. For example, `McaLowerWitness.ofJohnsonRangeBound` is in
`GrandChallenges/CapacityBounds.lean`; this keeps `GrandChallenges.lean` independent of the
catalogue's external admits.

## Naming

Names treat initialisms as words: `epsMca`, `epsCa`, `epsPg`, `GrandMcaAnswer`, and
`grandMcaChallenge`.
The canonical generator-level value retains its established name `mcaError`. The suffixes `_le`,
`_eq`, `_mono`, `_of_...`, and `_iff_...` describe the conclusion and hypotheses in the usual
mathlib style.

## Sources and axiom accounting

The file-level references and paper KB pages identify the source results represented by these
theorems. Run `./scripts/validate.sh --axioms` to verify their axiom dependencies along with the
rest of the library.
