# Separating RS mathematics from executable cost proofs

Historical decoder development record, preserved from commit `765ae773`. Checkpoint statements
and remaining-work lists below describe that development stage. Current mathematical owners are
`ListDecodability/Capacity.lean` and `MutualCorrelatedAgreement/Capacity.lean`; the executable endpoint
is `ListDecoding/CapacityDecoder.lean`. The September 6 no-band revision migrates that endpoint
without adding a whole-decoder bit/RAM complexity claim.


Status: checkpoints A and B implemented and validated.
Implementation worktree: `ArkLib-rs-algebraic-machine-epoch1`, based on `305e7146`.
The integration target remains `quang/all-rate-rs-capacity-formalization`, 2026-09-05.
Initial inspection: `e3567c1c`. Audience: the mathematics/MCA orchestrator, the decoder
orchestrator, and reviewers of the computational claim.

The recommendation is to separate the mathematical theorems from executable
realization, then prove the existing decoder runs in a small, explicitly defined
algebraic machine. Do not reorganize the entire branch or rebuild the decoder.
Do not make binary arithmetic or a Turing-machine backend a prerequisite.

## What is already proved, and what this revision adds

[ListDecodability/Capacity.lean](../../ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity.lean)
owns the exact-list existence theorem.
[Capacity.lean](../../ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/CapacityDecoder.lean)
owns `capacity_decoder_exact_output_and_primitive_work`, which connects the
actual coordinate decoder's output to the specification and bounds its returned
primitive-work ledger. These proofs remain useful.

The missing claim is that an execution in a restricted machine has that output
and a comparable cost. A Lean function returning `(answer, cost)` does not impose
this restriction: its body could perform uncharged computation. Adding a monad
or a cost field without restricting its operations would not fix that problem.

The new proof should connect three distinct claims:

1. The output consists exactly of the sufficiently agreeing polynomials.
2. A particular algebraic program produces the existing decoder's output.
3. Its operationally defined execution cost has the required bound.

The mathematics orchestrator can strengthen list bounds and prove mutual
correlated agreement (MCA) independently of items 2 and 3.

## Target dependency structure

Arrows below mean “provides results to,” not Lean import direction.

```text
Pure RS specifications and mathematical definitions
   ├── interpolation / lifting / list geometry / MCA ───────────────┐
   └── executable representations and correctness proofs ──────┐  │
                                                              │  │
Small algebraic machine → routine realization and cost proofs ─┤  │
                                                              ▼  ▼
                           Public decoder theorem and bridges
```

Keep the paper-facing full theorem in `Capacity.lean`. Give its purely
mathematical list theorem a lightweight owner module, `ListDecodability/Capacity.lean`.
The full capstone is deliberately allowed to import both
sides; MCA development should import the mathematical owner, not the capstone.

The existing
[ListDecoding/Specification.lean](../../ArkLib/Data/CodingTheory/ReedSolomon/ListSpecification.lean)
is already an extensional, cost-free specification. Reuse it where appropriate.
An extensional decoder certificate alone does not supply an algorithm.

## First integration patch: remove the actual import leaks

These are small extractions, not a directory migration. The cutover updates all
callers directly: no compatibility aliases or forwarding modules remain.

| Current dependency | Revision | Check |
| --- | --- | --- |
| `SymbolicReceivedInterpolation` imported `LocalColumnTranslationSemantics` for `LocalColumnTranslationMachine.sourceColumn` | Own the definition as `HiddenDerivative.sourceMonomial` in `HiddenDerivative/SourceMonomial.lean`; import it and `LocalConstraintMap` directly from symbolic interpolation | Mathematical consumers no longer import column execution; original semantics still compiles |
| `TaylorAllSolutions` and `GeometricBandParameters` import `SeparantChainRefinement` for `jetDegree_le_total` and `separant_total_le` | Put those two purely mathematical lemmas in existing `TotalJetDegreeRootCount.lean`; update consumers | Taylor, characteristic-zero Taylor, and geometric bounds no longer import sparse execution through these lemmas |
| `Capacity.lean` combined pure lists and execution | Own the pure public statement in `ReedSolomon/ListDecodability/Capacity.lean`; leave execution in `ListDecoding/CapacityDecoder.lean` | Same theorem type, lightweight mathematical import path |

Use intrinsic mathematical names in the new owner modules and update every
caller in the integration patch. The degree lemmas now live directly in
`ReedSolomon.HiddenDerivative`. Do not replace the executable separant-chain relation:
the mathematical consumers need only the two degree lemmas, not that relation.

The import boundary is checked by `python3 scripts/check-rs-math-imports.py`,
also run by repository validation. Lean parses the dependency headers; the guard
traverses local imports and rejects the current execution/cost owner names.
The mathematical entry points contain 87, 18, 74, 75, and 135 local modules,
respectively, in the guard's displayed order. Both removed execution bridges
were also checked as negative examples and rejected.

Integration owns this patch and publishes its commit hash before parallel edits
to affected files. Freeze shared signatures after that checkpoint.

## The computation model we will certify

Use a small first-order algebraic machine, not unrestricted Lean callbacks.
The syntax and composed Horner slice now implement this contract; the decoder
realization against this model remains open.

- Programs have finite syntax: literals, primitive operations, branches, loops,
  and calls to finite, defined subprograms. There is no constructor accepting an
  arbitrary Lean function or predicate to evaluate for free.
- Values have explicit representations: field cells, scalar counters, booleans,
  and list/record cells. Structural operations inspect or construct boundedly
  many cells. Append, equality of lists, lookup by traversal, and copying are
  programs, not unit-cost bulk primitives.
- Fix the primitive menu before implementing the decoder. Field arithmetic,
  field equality, scalar arithmetic/comparison, and individual structural/control
  operations have specified charges. Decide division and conversion conventions
  explicitly. No polynomial evaluation, matrix elimination, root finding, or
  enumeration is a primitive.
- Scalar arithmetic is unit-cost abstract arithmetic, not bit arithmetic. Call
  the result an algebraic machine bound; do not claim a bounded-word RAM theorem
  unless word-size invariants are separately proved. Do not permit a bulk
  scalar-to-list or encoded-answer decoding primitive.
- Count control, calls, and materialization, or prove a constant-factor bound
  absorbing them. A field-operation count can be a separate projection of a
  resource vector; it is not a substitute for the total-machine-work claim.
- Inputs are materialized coordinate/received-value rows and integer parameters.
  Outputs are materialized coefficient lists. Their mathematical interpretation
  is a specification relation, not free execution of a polynomial algorithm.
- For each fixed gap, choose integer parameters and a fixed program before
  choosing block length, dimension, prime field, or received word. The real gap
  is not a runtime oracle. Do not assume an input-specific compiled program or
  precomputed alphabet, matrix, or answer.

The machine interpreter may be written using Lean functions. That is harmless
provided the *programs* cannot invoke arbitrary functions, and the transition
semantics specifies only the fixed primitive operations. This distinction is
what reduces the human audit surface.

## Realization strategy and the cost theorem

Keep the existing executable functions as a reference implementation. For each
routine, provide a machine program, a representation relation, and a theorem
that execution produces the same represented result. Prove cost composition
from the machine semantics, not from a caller-supplied annotation.

Aim for a bound of the schematic form

```text
machine steps ≤ c(d,m) × existing primitive work + setupBound(n,k,q,d,m,A).
```

This is a target to prove, not an assumed property of a new interface. Charge
setup explicitly and prove its absorption into the final bound. In particular,
audit support-enumeration fuel, powers used to calculate fuel, scalar dispatch,
interpreter administration, field/extension-coordinate enumeration, and output
collection. Either execute and charge fuel construction, or remove proof fuel
from the machine program and prove termination from the existing traces.

Preserve the requested leading exponents `2d` and `d`: constant-factor or
sufficiently low polynomial overhead can be absorbed in the existing absolute
additive exponent; a generic polynomial simulation might multiply `d` and is
not automatically acceptable. Prove the absorption, including the order-zero
branch where the executed multiplicity depends on block length. Do not hide
block-length dependence in a supposedly gap-only constant.

The final public statement should exhibit an actual machine program and its
terminating execution, exact output, list bound, and operational cost bound.
It must not accept an uninstantiated “all routines are efficiently realizable”
hypothesis. State explicitly that this is algebraic cost, not native Lean time
or binary complexity. Align manuscript wording separately before claiming that
a differently worded paper runtime theorem is fully formalized.

## Work packages and acceptance gates

### Current machine implementation

The reusable implementation lives in `ArkLib/Data/Computation/AlgebraicMachine/`:

- `Basic.lean` defines atomic values, fixed registers, pair cells, and a closed primitive menu.
  Programs cannot carry field literals other than zero and one, arbitrary callbacks, or bulk
  list/polynomial operations. Natural literals are fixed code constants.
- `Command.lean` defines structured finite code and a charged small-step machine. The theorem
  `Executes.steps` turns each compositional certificate into an actual trace with the same cost.
  `Executes.run` connects it to the fuel-bounded observer; `run_sound` proves that successful
  observation entails a terminating trace within the observation limit.
- `Representation.lean` defines finite-heap validity, extension, and linked-list representation.
  Public materialized-input theorems require `Heap.WellFormed`; the unrestricted semantic heap
  type alone is not a finite-input guarantee. Allocation preserves this invariant and old lists.
- `Horner.lean` realizes descending-coefficient evaluation with explicit pointer traversal
  and a preserved register interface. Its exact bound is `12k + 7` steps for `k` coefficients.
- `HornerRefinement.lean` proves agreement with the existing Horner reference machine and
  computational-polynomial evaluation, using an explicit coefficient-representation premise.
- `BatchHorner.lean` calls the fixed Horner program for each of `m` supplied points and allocates
  one result cell each time. It takes exactly `(12k + 22)m + 7` steps and materializes results
  in **reversed point order**. There is no implicit output reversal or conversion.
- `Canary.lean` reduces the actual interpreter on asymmetric coefficients and a two-point batch,
  and checks insufficient observation fuel and a type-invalid branch.

The unit is an abstract algebraic-machine step, including unbounded natural arithmetic and
pointer access. It is not native execution time, a bounded-word RAM bound, or bit complexity.
Input-independent code and finite materialized data are part of the final theorem boundary.
The observer's fuel is not accessible to the program; no fuel-computation oracle is introduced.

An independent source review accepted the core and composed slice, including both exact
cost formulas, call-register preservation, output order, and the finite-input and fixed-program
conditions above. This is not a review of the full decoder realization: packages C–E remain open.
The implementation uses no new admissions, opaque routine-realization assumptions, or bit backend.

Validation on 2026-09-05, after incorporating MCA presentation commit `f18c4eff`:
`./scripts/validate.sh --axioms` passed, including the full build, source-policy and warning
gates, runtime checks, import boundary, docs/KB checks, and axiom fixtures/regression gate.
The sweep covered 30,949 declarations across 1,107 modules, with no new axiom/sorry taint
and no nonstandard axioms. Existing unrelated admission debt was not changed or allowlisted.

### Concrete realization order after the slice

1. Establish cost-preserving register renaming to embed subroutines into larger fixed banks.
   Realize shared structural routines: traversal, reversal, lookup/update, ranges, prefixes,
   Cartesian products, and coordinate-pair arithmetic. Build common matrix/elimination
   machinery once for both interpolation and coefficient recovery.
2. Interpolation: support enumeration, local translation/rewrite, matrix assembly, nonzero
   kernel extraction, sparse emission, and ambient-search failure paths. The current reference
   enumerates support `n + 2` times in a successful attempt; a cached implementation needs a
   correctness bridge, not a cost proof pretending those traversals do not happen.
3. Recovery: field/extension setup and alphabets, separant stages, center/jet enumeration,
   coefficient lifting, residual checks and matrix recovery, and canonical acceptance/filtering.
4. Assembly: scalar dispatch, small-block enumeration, both field regimes, and absorption of
   setup and control work. The `d = 0` branch uses `m = n / 2`; its dependence on block length
   cannot be hidden in a gap-only constant. Remove reference proof fuel from actual loops, or
   explicitly realize and charge its construction. Avoid a final bulk deduplication primitive.

This order reuses the existing reference outputs and semantic lemmas. It does not replace
the verified decoder with a new unconnected algorithm.

These are dependency waves, not time promises. The first substantive vertical
slice determines whether the bulk realization work is affordable as designed.

| Package | Owner | Deliverable and acceptance |
| --- | --- | --- |
| A. Interface separation | Integration | The three extractions above; unchanged public theorem types; mathematical import closure excludes execution/cost modules |
| B. Machine and vertical slice | Machine worker | Restricted syntax, semantics, representations, cost composition; realize Horner evaluation inside a list traversal with a loop and a subroutine call; prove value agreement and cost bound |
| C. Interpolation realization | Interpolation worker | Support enumeration, local-column construction, elimination, and interpolation produce the reference outputs with operational bounds, including setup |
| D. Recovery realization | Recovery worker | Coordinate alphabets, separant chain, jet enumeration/lifting, filtering and duplicate handling produce the reference outputs with operational bounds |
| E. Decoder assembly | Integration | Actual dispatcher and exceptional branches; one exact-output machine theorem with both field regimes; absorb all overhead |
| F. Independent audit and cleanup | Reviewer, then integration | Audit primitive menu, representations, uniformity and capstone; run builds/axiom checks; update paper-facing documentation without overstating the computation model |

B is a gate before large-scale realization, not a parallel excuse to invent
incompatible local machine languages. During B, C and D can inventory routines,
define representation relations, and isolate existing semantic lemmas. After B,
C and D run independently against the frozen machine API.

Use at most three algorithm workers: machine, interpolation, recovery.
Integration coordinates and owns shared files. Rotate a completed worker into
independent review of code they did not author rather than expanding concurrency.
Do not launch these workers merely because this planning document exists.

## Ownership alongside the MCA orchestrator

The MCA orchestrator owns symbolic interpolation, rational Taylor geometry,
field-independent list mathematics, and the qualitative MCA theorems in
[`MutualCorrelatedAgreement/Capacity.lean`](../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity.lean)
and [`ListDecodability/Capacity.lean`](../../ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/Capacity.lean).
The qualitative MCA argument is complete; sharper quantitative refinements remain separate.
It does not wait for the algorithmic machine.

The algorithm orchestrator owns executable routines, machine semantics, cost
bounds, and execution-specific refinement files. Shared mathematical root-finding
files are allocated by exact filename, not by a blanket directory claim.

Integration owns `Capacity.lean`, `GeometricOutputBounds.lean`, shared
specifications, and the initial extraction commit. Generic stronger list bounds
attach through exactness/cardinality bridges; MCA itself requires its own
mathematical proof and is not supplied by decoder exactness.

Each worker records its base commit, writable files, deliverable, and acceptance
check before editing. Use separate worktrees/build directories and integrate
onto the single central branch. Request interface changes through integration;
do not silently change another lane's assumptions. Report verified checkpoints
and blockers, not routine progress chatter.

## Review and completion checklist

- Check transitive imports of `SymbolicReceivedInterpolation`,
  `TaylorAllSolutions`, `TaylorCharZeroSolutions`, and `GeometricCodewordBound`.
  Enforce the boundary with an import-closure test, not just filename conventions.
- Compile changed owners, original execution consumers, and public capstones.
  Check theorem types and axiom dependencies; add no admissions or assumptions
  that replace the algorithmic proof obligation.
- Review the primitive syntax and transition semantics line by line. Check that
  bulk computation cannot enter via an opaque callback, a conversion, an input
  representation, or an unproved realization instance.
- Check every executed path, including exceptional/failed branches as specified.
  Use small executable examples as regression tests, not as complexity proofs.
- Audit the quantifier order, representation relation, output completeness,
  gap-only constants, and both final exponents independently.
- Run repository validation before commits/pushes, and the axiom gate for proof
  changes. Do not run competing builds in the same writable build directory.
- Retain useful internal lemmas, without compatibility aliases. Defer broad file moves,
  incidental renames, binary backends, and a general verified Lean compiler.

Completion means reviewers can inspect a small machine definition and a clear
public theorem, while Lean checks the intervening realization proofs. It does
not mean nobody needs to review specifications or modelling choices. It means
reviewers no longer have to trust every algorithm's handwritten cost annotation.
