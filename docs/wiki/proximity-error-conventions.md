# Proximity Error API

This page describes ArkLib's numeric APIs for proximity gap, correlated agreement, and mutual
correlated agreement. For code carriers and distance types, see
[`coding-theory-conventions.md`](coding-theory-conventions.md). For probability notation, see
[`probability-conventions.md`](probability-conventions.md).

## Modules

| Module | Contents |
| --- | --- |
| `ProximityGenerator/Basic.lean` | Generator-parametric mutual correlated agreement: `IsMCA`, `mcaError`, and `IsMCAGenerator` |
| `ProximityGap/Errors.lean` | `caError`, `epsPg`, `epsCa`, `epsMca`, their order properties, predicate bridges, and affine-line MCA comparison theorems |
| `ProximityGap/Basic.lean` | Predicate forms of proximity gap and correlated agreement |
| `ProximityGenerator/TensorGenerator.lean` | Mutual-correlated-agreement transport through tensor generators and row-wise interleaving |
| `ProximityGap/GrandChallenges.lean` | Integer-grid challenge predicates, answer types, witnesses, and Reed--Solomon prize specializations |
| `ProximityGap/CapacityBounds.lean` | Source-audited §4 upper/lower bounds on `epsCa` and canonical `mcaError` |
| `ProximityGap/LineDecoding.lean` | Natural-cardinality line decodability and its MCA consequence |
| `Connections/ListDecodingAndCA.lean` | §5 conversions between `Code.Lambda`, CA, and MCA |
| `ProximityGap/GrandChallenges/CapacityBounds.lean` | Proved Johnson-range capacity-bound witnesses; imports the core carrier, never conversely |

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
- `isMCA_comp_equiv` and `mcaError_comp_equiv` for invariance under coordinate equivalences;
- the transport lemmas in `MCAGenerator.lean` and `TensorGenerator.lean`.

## Proximity gap and correlated agreement

`ProximityGap.caError G C δ_fld δ_int` is the generator-indexed CA error. It takes the
supremum, over stacks that are not jointly `δ_int`-close to `C`, of the probability that
`∑ j, G x j • u j` is `δ_fld`-close when `x` is sampled uniformly. Stacks that are jointly
close contribute zero. The seed type needs `SampleableType`; this already implies that it
is finite and nonempty. The row and coordinate types have `Fintype` instances.

`Errors.lean` provides these specializations:

| Declaration | Type and meaning |
| --- | --- |
| `epsPg C δ` | proximity-gap error for `C : Set (ι → A)` and `δ : ℝ≥0` |
| `epsCa C δ_fld δ_int` | affine-line correlated-agreement error with separate fold and interleaved radii |
| `epsCa' C δ` | equal-radius specialization `epsCa C δ δ` |
| `caError (univariatePowersGenerator F k) C δ_fld δ_int` | correlated-agreement error for degree-`k` polynomial combinations |
| `caError (AffineSpaceGenerator F k) C δ_fld δ_int` | correlated-agreement error for uniform samples from affine spans |

These values use `Set` code carriers because their events are also meaningful for nonlinear codes.
Use `ModuleCode` when applying the comparison theorems with mutual correlated agreement.

`epsCa` and `epsCa'` are abbreviations. Use `epsCa_eq` to recover the affine-line
sampling formula in proofs. Curves and affine spaces use `caError` with the generators in
the table above.

`caError_affineSpace_eq` recovers uniform sampling from the generated affine subspace.
Its proof uses `uniform_affine_combination`, including dependent and zero directions.
That lemma lives in `BCIKS20/AffineCoefficients/Basic.lean`; the higher-level
`BCIKS20/AffineCoefficients.lean` gives `correlatedAgreement_affine_coefficients`.
The affine-space numeric bridge now requires a finite-field sampler, whereas the
predicate itself can sample a finite affine image without sampling the field.

Their order behavior is not uniform:

| Value | Available behavior |
| --- | --- |
| `mcaError G C δ` (and hence `epsMca C δ`) | monotone in `δ` |
| `caError G C δ_fld δ_int` (and hence `epsCa`) | monotone in `δ_fld` and antitone in `δ_int` |
| `epsPg C δ` | zero for `1 ≤ δ`; the zero singleton code gives a positive value at `δ = 0`, so global monotonicity fails in general |
| `epsCa' C δ` | zero for `1 ≤ δ`; no global monotonicity lemma is provided |

The generator-level declarations are `caError_mono_left` and `caError_antitone_right`.
The affine-line versions `epsCa_mono_left` and `epsCa_antitone_right` specialize them.
The endpoint declarations are
`epsPg_eq_zero_of_one_le`, `epsCa_eq_zero_of_one_le_right`, and
`epsPg_singleton_zero_pos`.

## Comparisons and bridges

Use `prob_le_caError` to bound one stack's fold-close probability when joint proximity
fails. For a module code, `caError_le_mcaError` gives
`caError G C δ δ ≤ mcaError G C (δ : ℝ)` for any generator and nonnegative radius.
A close combination supplies an agreement set; failure of joint proximity forces some
row to have no codeword extension on that set, which witnesses `IsMCA`.

For the affine-line instance,

```text
epsPg C δ ≤ epsCa C δ δ ≤ epsMca C δ.
```

This is `epsPg_le_epsCa_le_epsMca`; its two component inequalities are
`epsPg_le_epsCa` and `epsCa_le_mcaError_affineLine`.

The unique-decoding comparison is:

- `mcaError_le_epsCa_of_pos_of_two_mul_lt_dist` for the MCA-to-CA direction;
- `mcaError_eq_epsCa_of_pos_of_two_mul_lt_dist` for the resulting equality.

For any generator whose finite seed space has at most as many elements as the field,
`CoreDefinitions.mcaError_moduleInterleavedCode_le_of_card_le` bounds the error of a finite
row-wise interleaving by the base-code error. The reverse bound
`CoreDefinitions.mcaError_le_mcaError_moduleInterleavedCode` needs only a nonempty row type.
Both hold at every real radius; when the row type is finite and nonempty, their equality is
`CoreDefinitions.mcaError_moduleInterleavedCode_eq_of_card_le`.

The affine-line compatibility results retain their positive-width and `(0, 1)` radius
hypotheses:

- `mcaError_le_moduleInterleavedCode` gives the base-to-interleaved inequality;
- `mcaError_interleaved_le` gives the interleaved-to-base inequality;
- `mcaError_interleaved_eq` gives equality.

Jo26's field-size-weighted bound for seed spaces larger than the field remains unformalized in
ArkLib.

The numeric correlated-agreement values are connected to the predicate API by:

- `δ_ε_correlatedAgreementAffineLines_iff_epsCa_le`;
- `δ_ε_correlatedAgreementCurves_iff_caError_le`;
- `δ_ε_correlatedAgreementAffineSpaces_iff_caError_le`.

These equivalences allow existing predicate-based proofs to consume numeric bounds without
introducing a second predicate.

## Numeric types

| Quantity | Type |
| --- | --- |
| radius passed to `IsMCA`, `mcaError`, or `Code.Lambda` | `ℝ` |
| radius passed to `caError`, `epsPg`, `epsCa`, or `epsMca` | `ℝ≥0` |
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
`GrandChallenges/CapacityBounds.lean`. Its bound is proved via [DKT26], with the printed
constant from [BCHKS25] Theorem 4.6. Keeping it in an extension leaves `GrandChallenges.lean`
independent of the bound catalogue.

## Naming

Names treat initialisms as words: `epsMca`, `epsCa`, `epsPg`, `GrandMcaAnswer`, and
`grandMcaChallenge`.
The generator-level values are `caError` and `mcaError`. The suffixes `_le`,
`_eq`, `_mono`, `_of_...`, and `_iff_...` describe the conclusion and hypotheses in the usual
mathlib style.

## Sources and axiom accounting

The file-level references and paper KB pages identify the source results represented by these
theorems. Run `./scripts/validate.sh --axioms` to verify their axiom dependencies along with the
rest of the library.
