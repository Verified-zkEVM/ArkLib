# Probability conventions

ArkLib uses VCVio's measure semantics. Write events as `Pr{let x ← mx}[p x]`,
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
distribution need not be equal as programs.

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
- Comparing events of several draws goes through `gcongr`, `ExpectationWP.wp_mono` or
  `wp_le_of_forall_le`, since `prEvent_mono` is stated for one draw. `ExpectationWP.wp_mono`
  compares two observations of one draw pointwise, and `wp_le_of_forall_le` bounds an expectation
  by a constant that bounds each of its values.

Statements about the outputs of one computation, such as perfect completeness, an honest run's
support, an event of probability zero, or a bound that averages over a uniform challenge, are
usually shortest with `prvcgen`. See [`program-logic.md`](program-logic.md), which also shows
bounds on nested expectations.

Losslessness is `IsProbabilityMeasure 𝒟[mx]`, or the equivalent successful-event statement
`Pr{let _ ← mx}[True] = 1`. For computations that may fail, the complement probability is the
successful mass minus the event probability. Replacing it with `1 - Pr{…}[…]` needs losslessness.
Operational `support` describes possible executions. A measure-zero event alone does not prove
that an execution is impossible.

## Migrating an in-flight branch

Replace `Pr_{…}[…]` and `$ᵖ` with the event notation `Pr{let x ← mx}[p x]` and uniform draws
`$ᵗ S`. Replace PMF-specific applications, sums, and support arguments with event or measure
lemmas: changing only the notation is insufficient. Import VCVio modules directly. ArkLib has no
`ArkLib.ToVCVio` compatibility tree and no `ArkLib.Data.Probability.Notation` module.

Code written against VCVio's removed discrete API (`Pr[… | …]`, `probEvent`, `evalSPMF`, …)
converts with VCVio's codemod: run
`python3 .lake/packages/VCVio/scripts/migrate-native-probability.py` on its source directories.
VCVio's guides, in the checkout Lake places at `.lake/packages/VCVio/`, describe the API.
`docs/agents/probability.md` covers the measure semantics, events, expectations and their laws,
and `docs/agents/probability-migration.md` maps each removed form to its replacement. The
[conversion ledger](../design/native-measure-ledger.md) records ArkLib's own conversion.

Run `./scripts/validate.sh --axioms` before committing. Validation runs
`lake exe retiredsweep --require-empty`: every ArkLib declaration's type and body must avoid
direct references to retired probability constants. This mode has no baseline exceptions.
The source-policy plugin also rejects active retired notation, including uses hidden inside
`#guard_msgs`. Ordinary comments and strings remain allowed. A textually clean merge of an older
branch can still fail these checks.
