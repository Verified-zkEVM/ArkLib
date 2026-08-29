# 01b — Type-Tree True-Sight Rename Cutover

> **Current status (2026-08-29).** The generic `Interaction.TypeTree` rename and its cursor/append
> substrate have landed in PolyFun. This document remains the naming contract for ArkLib's
> oracle-specific refinement. It no longer describes pending generic PolyFun rename work.

**Normative naming decision and operational PR map.** This document fixes the names of the
sequential interaction carrier and its oracle-reduction refinement, and specifies the complete
cross-repository cutover. It complements the semantic inventory in `01` and the landing train in
`01a`; it does not add a new mathematical abstraction.

## 1. Decision

The generic sequential carrier is a well-founded dependent type tree:

```lean
Interaction.TypeTree :=
  PFunctor.FreeM TypeTree.basePFunctor PUnit

TypeTree.basePFunctor.A := Type u
TypeTree.basePFunctor.B := id

TypeTree.Path tree := PFunctor.FreeM.Path tree
```

Each internal node chooses a move type `X`; a value `x : X` selects the continuation. `Protocol`
is not used for this bare carrier: roles, participants, local syntax, execution, and security
meaning live in later decorations and bundles.

The oracle-reduction refinement is an oracle type tree:

```lean
Interaction.Oracle.TypeTree :=
  PFunctor.FreeM Oracle.TypeTree.basePFunctor PUnit

Oracle.Position.Branch (.public X) := X
Oracle.Position.Branch (.oracle X) := PUnit
```

At an oracle node, the prover's runtime message remains a value `x : X`. Only the **branch index**
is `PUnit`: every `x` selects the same structural continuation. The runtime lens remembers this
distinction:

```lean
Oracle.TypeTree.runtimeLens :
  Oracle.TypeTree.basePFunctor ⟶ TypeTree.basePFunctor

public x ↦ x
oracle x ↦ PUnit.unit
```

This yields two canonical paths:

- `Oracle.TypeTree.BranchPath tree := PFunctor.FreeM.Path tree` records exactly the values that
  select structural continuations;
- `Oracle.TypeTree.ExecutionPath tree := PFunctor.FreeM.PathAlong runtimeLens tree` records the
  concrete values exchanged during execution, including prover oracle messages.

`BranchPath` does not mean that one party controls every move. It is the control-flow/branch path.
`ExecutionPath` is the global execution record, not the verifier's direct observation. The
projection `ExecutionPath → BranchPath` is identity at public nodes and sends every oracle payload
to `PUnit.unit`.

The higher-level name `Protocol` is reserved for a bundle containing at least an oracle type tree,
roles, and oracle-interface decorations. `Reduction` remains the executable statement/witness
transformation built over that protocol data.

## 2. Stack placement

The PolyFun rename is **PF-6R**, stacked directly after PF-6A and before PF-6B:

```text
#54 FreeP/substitution monoid
  → #55 free substitution-monoid universal property
  → PF-6A / #62 polynomial interaction normalization
  → PF-6R complete TypeTree naming cutover
  → PF-6B dependent TypeTree.Chain composition/coherence (gated)
```

PF-6A deliberately preserved the historical public names so its algebraic normalization remained
reviewable. PF-6R is the isolated mechanical/API migration promised by that boundary. PF-6B must be
written only against the new names.

## 3. PF-6R: exact PolyFun cutover

**Title:** `refactor(interaction): rename sequential specs to type trees`

**Base:** exact PF-6A head `11e02c0101933b7966123017b40cffdfed1399bf` until PF-6A is merged or
restacked.

### 3.1 Module and carrier names

| Historical API | Cutover API |
|---|---|
| `PolyFun.Interaction.Basic.Spec` | `PolyFun.Interaction.Basic.TypeTree` |
| `PolyFun/Interaction/Basic/Spec.lean` | `PolyFun/Interaction/Basic/TypeTree.lean` |
| `PolyFun.Interaction.Basic.SpecFintype` | `PolyFun.Interaction.Basic.TypeTreeFintype` |
| `PolyFun/Interaction/Basic/SpecFintype.lean` | `PolyFun/Interaction/Basic/TypeTreeFintype.lean` |
| `Interaction.Spec` | `Interaction.TypeTree` |
| sequential `namespace Spec` | `namespace TypeTree` |
| `Spec.Transcript` | `TypeTree.Path` |

All sequential namespace members move with the carrier, including `Node`, `Decoration`,
`MonadDecoration`, `Ownership`, `Sampler`, `Fintype`, `Chain`, `StateChain`, `Telescope`, `done`,
`node`, `append`, `replicate`, `stepPoly`, and `substMonoid`.

### 3.2 Names that encode the old carrier

The cutover includes exported names whose `Spec` or `Transcript` component specifically denotes the
sequential type tree:

| Historical family | Cutover family |
|---|---|
| `TypeTree`'s historical `DecoratedSpec` / `decoratedSpecEquiv` | `TypeTree.Decorated` / `TypeTree.decoratedEquiv` |
| `InteractionOver.runSpec` | `InteractionOver.runTypeTree` |
| `Chain.toSpec` and theorem family | `Chain.toTypeTree` and theorem family |
| `Telescope.toSpec`, `toSpecAlgebra` | `Telescope.toTypeTree`, `toTypeTreeAlgebra` |
| `TwoParty.perspectiveSpec` | `TwoParty.typeTreePerspective` |
| `SyntaxOver.TwoParty.pairedSpec` | `SyntaxOver.TwoParty.pairedTypeTree` |
| `ShapeOver.TwoParty.pairedSpec` | `ShapeOver.TwoParty.pairedTypeTree` |
| `InteractionOver.TwoParty.pairedSpec` | `InteractionOver.TwoParty.pairedTypeTree` |
| `pairedMonadicSpec` / `monadicSpec` specialization families | `pairedMonadicTypeTree` / `monadicTypeTree` |
| `sampleTranscript` | `samplePath` |
| sequential `Transcript.*` operations | `TypeTree.Path.*` operations |
| `Chain.splitTranscript` / `appendTranscript` | `Chain.splitPath` / `appendPath` |

The bridge into `Interaction.Concurrent` must use the same vocabulary rather than preserve a
second “transcript” facade:

| Historical concurrent bridge | Cutover bridge |
|---|---|
| `StepOver.spec` | `StepOver.tree` |
| `Observed.ofTranscript` | `Observed.ofPath` |
| `ObservedTranscript` | `ObservedPath` |
| `eventOfTranscript` / `transcriptOfEvent` | `eventOfPath` / `pathOfEvent` |
| `ProcessOver.TranscriptRel` | `ProcessOver.StepRel` |
| `Observation.Process.TranscriptRel` | `Observation.Process.StepRel` |
| `SafetyRefinement.matchTranscript` | `SafetyRefinement.matchPath` |

`StepRel` is deliberate consolidation: these relations include both the source state and selected
path and are already aliases of `PFunctor.DynSystem.StepRel`; they are not relations on bare
transcripts. Local binder names may remain `spec` when they are not exported. The acceptance gate
is about public vocabulary and documentation, not cosmetic churn in every proof binder.

The paired-specialization theorem families follow their renamed declarations (for example,
`pairedSpec_focal_sender` becomes `pairedTypeTree_focal_sender`). Likewise every theorem whose
name begins with `toSpec_`, `splitTranscript_`, or another renamed declaration follows that
declaration; PF-6R must not leave old theorem names behind merely because their statements compile.

### 3.3 Audited repository surface

The implementation sweep covers all of the following, not only `Basic/Spec.lean`:

- sequential `Basic` modules and the `TwoParty`/`Multiparty` specializations built over them;
- the `Concurrent` bridge wherever a step embeds a sequential tree or complete path;
- `PolyFunTest/Interaction`, including the PF-6A normalization canaries, dependent-chain examples,
  two-/multiparty examples, and concurrent examples;
- the generated `PolyFun.lean` umbrella import;
- root agent guidance and maintained `docs/reading` / `docs/wiki` pages.

The audit at PF-6A head found a minimum direct edit surface of 38 source files and five test files
under the narrow old-name search above. Import-only and prose-only dependents enlarge the final
diff; the acceptance search, rather than this count, is authoritative.

### 3.4 Explicit exclusions

PF-6R does **not** rename unrelated uses of “specification”:

- `Interaction.Concurrent.Spec`, a separate concurrent source syntax;
- `DynSystem.SafetySpec`, `Process.SafetySpec`, and other proposition/policy specifications;
- VCVio `OracleSpec`, the dependent query-response signature;
- Lean/Std `Do.Spec` theorem namespaces;
- domain specifications whose name does not denote `Interaction.TypeTree`.

`Interaction.Concurrent.Spec` may receive its own true-sight review later. Mixing that decision into
PF-6R would make the sequential cutover non-mechanical.

### 3.5 No compatibility facade

The final PR contains no deprecated aliases for `Interaction.Spec`, `Spec.Transcript`, old module
paths, or old specialization names. The generic `TypeTree` cutover has now landed in PolyFun;
ArkLib's oracle-specific specialization remains an implementation contract rather than a frozen
API. Keeping aliases would preserve two vocabularies throughout every downstream theorem. Git
history and the explicit rename table above provide migration history.

The PR is semantically conservative: underlying `FreeM` representations, universes, reducibility,
`@[match_pattern]` behavior, constructor equations, append, path splitting, substitution-monoid
structure, and universal-property statements do not change.

## 4. Downstream cutover train

The cross-repository migration is atomic by dependency revision, not by pretending one GitHub PR
can edit three repositories.

### 4.1 VCVio pin/cutover

Advance the PolyFun pin to PF-6R and update all sequential imports and names in one VCVio PR. The
current audit finds nine VCVio files using the sequential carrier, concentrated in the UC runtime,
scheduler, and `Std.Do` bridge. Public functions such as `specOf` that return a type tree become
`treeOf` when exported; unrelated `OracleSpec` and `Std.Do.Spec` names remain unchanged.

### 4.2 ArkLib generic interaction cutover

After the VCVio candidate is green, advance ArkLib's dependency pins and migrate its generic
interaction layer from `Interaction.Spec`/`Spec.Transcript` to `Interaction.TypeTree`/
`TypeTree.Path`. The current core-rebuild audit finds 45 ArkLib files on this surface. This is a
mechanical dependency-alignment PR; it must not also redesign reductions or security notions.

### 4.3 ArkLib oracle type-tree cutover

Land the oracle-specific names with AR-2A, or isolate them in a naming-only commit immediately
before AR-2A if the prototype is already under review:

| Prototype name | Normative name |
|---|---|
| `Interaction.Oracle.Spec` | `Interaction.Oracle.TypeTree` |
| `ArkLib.Interaction.Oracle.Spec` module / `Oracle/Spec.lean` | `ArkLib.Interaction.Oracle.TypeTree` / `Oracle/TypeTree.lean` |
| `Oracle.Spec.basePFunctor` | `Oracle.TypeTree.basePFunctor` |
| `Oracle.Spec.executionLens` | `Oracle.TypeTree.runtimeLens` |
| `Oracle.Spec.toInteractionSpec` | `Oracle.TypeTree.toTypeTree` |
| `Oracle.Spec.toSpecRoles` | `Oracle.TypeTree.toTypeTreeRoles` |
| `Oracle.Spec.PublicTranscript` | `Oracle.TypeTree.BranchPath` |
| `Oracle.Spec.FullTranscript` | `Oracle.TypeTree.ExecutionPath` |
| `FullTranscript.toInteractionTranscript` / `.ofInteractionTranscript` | `ExecutionPath.toTypeTreePath` / `.ofTypeTreePath` |
| `projectPublicFull` | `ExecutionPath.toBranchPath` |
| `projectPublic` | eliminate in favor of `ExecutionPath.ofTypeTreePath` then `.toBranchPath` |
| `PublicTranscript.*` operation families | `BranchPath.*` operation families |
| `transcriptAppend` and dependent theorem family | `ExecutionPath.append` and theorem family |
| `Oracle.Spec.Chain.toSpec` / `Telescope.toSpec` | `Oracle.TypeTree.Chain.toTypeTree` / `Telescope.toTypeTree` |
| `Spec.OracleMessagesAt` | `Oracle.TypeTree.OracleMessagesAt` |
| `Oracle.Spec.Protocol` / projection `.spec` | `Oracle.Protocol` / projection `.tree` |

The current core-rebuild prototype has 23 `ArkLib/Interaction` files on this oracle naming surface.
`OracleSpec` remains the VCVio query-response signature and must not be changed by this cutover.
Compiler-local records that are genuinely cryptographic transcripts keep that word. A path-aligned
record such as BCS's prototype `SharedTranscript`, however, becomes `SharedExecutionPath`; the
criterion is what the object is, not which layer currently defines it.

## 5. PF-6R acceptance and validation

The exact-head PR must satisfy all of the following:

1. `TypeTree.done` and `TypeTree.node` remain reducible match patterns over the same `FreeM`
   constructors.
2. `TypeTree.Path tree` is definitionally `PFunctor.FreeM.Path tree`.
3. PF-6A's `stepPoly`, substitution-monoid, chain, stopping-tree, and universal-property canaries
   compile under their new namespaces without additional transports.
4. A dependent two-branch example distinguishes both paths and confirms append/split equations.
5. `./scripts/update-lib.sh` regenerates `PolyFun.lean`; no generated file is hand-edited.
6. `lake build --wfail`, `lake test`, `lake lint`, `lake exe lint-style`, umbrella imports, and
   documentation integrity all pass on the exact head.
7. Negative searches find no historical sequential imports or public names in source, tests,
   generated imports, agent guidance, or maintained docs. Search patterns must be narrow enough to
   allow `Concurrent.Spec`, `SafetySpec`, `OracleSpec`, and `Std.Do.Spec`.
8. The diff contains no semantic changes disguised by the rename: compare normalized declarations
   or inspect `git diff --word-diff-regex` around every non-identifier change.

Before running Lean validation in the new worktree, apply the user-wide dependency-cache policy:
verify the exact Mathlib URL, revision, and `lean-toolchain`, then reuse a healthy matching cache.

## 6. Review slicing

The PR is large in changed lines but has one semantic claim: **the public names now identify the
objects already formalized**. Review it in four passes:

1. module moves and generated imports;
2. carrier/namespace/path names and definitional canaries;
3. exported specialization/projection names;
4. docs, tests, negative searches, and downstream pin evidence.

Any proof repair requiring a new cast, changed theorem hypothesis, altered universe, or weaker
equation is a blocker and must be split from PF-6R. PF-6B begins only after this cutover is green.
