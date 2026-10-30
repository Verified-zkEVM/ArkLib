# Probability conventions

ArkLib uses VCVio's native measure semantics. Write events as `Pr{let x ← mx}[p x]`,
measures as `𝒟[mx]`, and uniform draws as `$ᵗ S`. A probabilistic computation has type
`ProbComp α`; it is not a Mathlib `PMF α`.

## Uniform sampling

State `[SampleableType S]` when a public definition samples an abstract type `S`.
This supplies an executable sampler and its uniform-distribution law. Retain `[Fintype S]`
when the statement also uses cardinalities. Do not add sampler assumptions to purely algebraic
or counting statements that never sample.

Import `ArkLib.Data.Probability.Uniform` and open `ProbabilityTheory` to use the scoped,
noncomputable samplers for nonempty finite subtypes and finsets. For a proof-local finite sample
space without an existing sampler, use `letI := SampleableType.ofFintype S`.
Do not install a global fallback instance for every finite type: concrete executable samplers
should remain canonical.

Use `SampleableType.prEvent_uniformSample` to turn a uniform event into a cardinality ratio.
Use `prEvent_uniformSample_equiv`, `prEvent_uniformSample_prod`, or
`prEvent_uniformSample_finSnoc` to transport uniform events. Two samplers with the same
native distribution need not be equal as programs.

For dependent challenges, preserve the sampling stages. Sampling `q` uniformly from a prime set
and then `α` uniformly from `Fin k → ZMod q` gives every prime equal weight. A uniform draw from
the dependent type of all pairs instead weights `q` by `q^k`. The reusable bridge and bounds live
in `ArkLib/Data/MvPolynomial/PrimeFingerprintProbability.lean`; its test distinguishes the laws
using primes `{2, 3}` and one variable. Keep the counting input in `PrimeFingerprint` independent
of sampler assumptions.

Use `ProtocolSpec.instSampleableTypeChallengeSeqCompose` and
`ProtocolSpec.instSampleableTypeChallengeAppend` when exposing challenge samplers for composed
protocol families. This keeps the sampler family definitionally equal to the one expected by
composition theorems and retains the chosen component samplers through dependent index transport.
Rebuilding the entire family's samplers with `SampleableType.ofFintype` can preserve the
probabilities while changing the sampler programs.

## Event proofs

Use VCVio's `prEvent_mono`, `prEvent_congr`, `prEvent_or_le`, `prEvent_exists_le`, and
`prEvent_bind_le_of_forall_le` for generic probability reasoning. Import their public owner
modules instead of creating ArkLib aliases or compatibility wrappers. Generic missing lemmas
belong upstream in VCVio before their ArkLib consumers are integrated.

`ArkLib/Data/Probability/Instances.lean` retains specialized mathematical facts about
Schwartz–Zippel, dot products, and coordinate membership. `Combinatorial.lean` contains the
collision-to-image-size argument for probability measures on a countable full-mass carrier.
These mathematical helpers live in `namespace Probability`. `Sequential.lean` averages the error of
a second computation over the actual output distribution of the first, charging exceptional outputs
separately and needing no losslessness assumption. `KoalaBear.lean` gives the sextic extension
`KoalaBear.Ext6` a computable `SampleableType` instance that samples six base-field limbs.

`VCVio.EvalDist.ProbabilityBounds` also supplies
`prEvent_exists_finset_le_card_mul` for a fixed finite candidate set and
`prEvent_exists_and_le_of_subsingleton` for an exact-functional candidate predicate.
Fix the set or predicate before the sampled challenge. Batching collision events
exclude candidates whose full claim is already correct; adaptive candidate lists
need a separate argument.

Losslessness is `IsProbabilityMeasure 𝒟[mx]`, or the equivalent successful-event statement
`Pr{let _ ← mx}[True] = 1`. For computations that may fail, the complement probability is
successful mass minus the event probability; replacing it with `1 - Pr{…}[…]` needs losslessness.
Operational `support` describes possible executions. A measure-zero event alone does not prove
that an execution is impossible.

## Migrating an in-flight branch

Replace `Pr_{…}[…]` and `$ᵖ` with native event notation and sampling. Replace PMF-specific
applications, sums, and support arguments with native event or measure lemmas; changing only
the notation is insufficient. Import VCVio modules directly: the former `ArkLib.ToVCVio`
compatibility tree and `ArkLib.Data.Probability.Notation` have been removed.

Run `./scripts/validate.sh --axioms` before committing. Validation runs
`lake exe retiredsweep --require-empty`: every ArkLib declaration's type and body must avoid
direct references to retired probability constants. This mode has no baseline exceptions.
The source-policy plugin also rejects active retired notation, including uses hidden inside
`#guard_msgs`; ordinary comments and strings remain allowed.

See the [conversion ledger](../design/native-measure-ledger.md) for the upstream API map and
semantic constraints. A textually clean merge of an older branch can still fail these checks.
