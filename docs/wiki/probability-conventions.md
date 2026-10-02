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

## Event proofs

Use VCVio's `prEvent_mono`, `prEvent_congr`, `prEvent_or_le`, `prEvent_exists_le`, and
`prEvent_bind_le_of_forall_le` for generic probability reasoning. Import their public owner
modules instead of creating ArkLib aliases or compatibility wrappers. Generic missing lemmas
belong upstream in VCVio before their ArkLib consumers are integrated.

`ArkLib/Data/Probability/Instances.lean` retains specialized mathematical facts about
Schwartz–Zippel, dot products, and coordinate membership. `Combinatorial.lean` contains the
collision-to-image-size argument for probability measures on a countable full-mass carrier.
These mathematical helpers live in `namespace Probability`.

An event `Pr{let x ← mx; let y ← f x}[p y]` elaborates to nested expectations of its draws,
`wp⟦mx⟧ (fun x => wp⟦f x⟧ (predInd p))`, and the `expect_norm` simp set keeps it in that form.
Three habits follow:

- A lemma stated for a variable program, such as `Pr{let y ← mx >>= f}[q y]`, becomes a nested
  event when it is applied. Bridge it with `simpa only [expect_norm] using h`.
- `rw` with an equation between whole computations does not find a `do` block inside an event.
  Rewrite the inner program, or first fold the event back with `← prEvent_bind` or
  `← prEvent_map`, then normalize.
- Comparing events of several draws goes through `gcongr` or `wp_le_of_forall_le`, since
  `prEvent_mono` is stated for one draw.

Statements about the possible outputs of one computation, such as perfect completeness, an
honest run's support, or an event of probability zero, are usually shortest with `prvcgen`. See
[`program-logic.md`](program-logic.md).

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
