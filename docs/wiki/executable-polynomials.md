# Executable polynomial programs

Use this page when an algorithm computes polynomial messages, folds evaluation tables, or claims
arithmetic costs. Module routing belongs in [repo-map.md](repo-map.md); focused build, native
runtime and axiom checks belong in [quickstart.md](quickstart.md).

## Runtime data and mathematical views

Use CompPoly evaluation tables and coefficient arrays for executable data. Keep sparse Mathlib
polynomial interpretations in the proof layer, and explain each representation-specific
`noncomputable` declaration individually. Proof erasure can remove classical proofs; an algorithm
cannot obtain its runtime values through classical choice.
A finite analysis function with executable equality may still be an ordinary computable
definition. Proof-only use alone does not require a `noncomputable` marker.

For Boolean tables, use the little-endian convention of `CMlPolynomialEval`: adjacent entries
eliminate the least significant remaining coordinate. `evalMle`, `eval₂Mle` and `evalMleLayer`
use recursive interpolation. The shared `lagrangeBasisFast` builds a basis table by reusing each
tail table. An asymmetric test should distinguish reversed coordinate order.

Check ordinary generic and concrete callers, their compiler IR, and native execution. An IR
check establishes code generation; mathematical correctness still needs kernel-checked proofs.
See the [affine-row acceptance caller](../../ArkLibTest/ToCompPoly/Multilinear/Affine.lean).

## Formal coefficients over finite fields

Prove formal polynomial or coefficient equality when constructing messages. Equality of
finite-field evaluations alone is insufficient: over `F₂`, `X³` and `X` agree at every field
element but have different coefficient arrays. Interpolating a higher-degree circuit's Boolean
table can likewise change the polynomial queried at a later challenge point.

Use ring homomorphisms for circuit substitution, canonical multilinear-table semantics for
folding, and representation refinement for the final array. Degree-limited coefficient recovery
is appropriate after its degree hypothesis is proved. The
[formal affine-row theorem](../../ArkLib/ToCompPoly/Multilinear/Affine.lean) works over a
commutative ring and does not require interpolation nodes beyond the Boolean row endpoints.

## Costs of the executed arithmetic program

Reuse `ArithmeticSpec`, certified operations and `profileArithmetic` from the
[univariate arithmetic owners](../../ArkLib/ToCompPoly/Univariate/ArithmeticCost.lean).
Tie a cost theorem to the program the runtime executes: use a shared operation-parametric driver,
explicit measured-program erasure, or a proved compiler replacement selected by the caller.
Equal outputs from two separately implemented algorithms do not establish equal work. A compiler
replacement affects newly compiled callers; it does not rewrite dependency bodies already compiled.

State whether a bound applies to one instruction coordinate or their sum. A bound for every
coordinate needs another argument before becoming a total. Keep field arithmetic, table reads,
metadata instructions and structural storage bounds distinct. The arithmetic profile does not
measure allocation, garbage collection or machine-index operations.

Padded coefficient arrays retain zero entries until explicit normalization. Streaming addition
costs depend on the actual accumulator widths and input order. Convolution order also matters to the
executed program even when the resulting polynomials commute. The
[raw fraction-fold cost owner](../../ArkLib/ToCompPoly/Univariate/ArithmeticFractionFoldCost.lean)
records these recurrences. Retain general group-width terms before specializing to a positive,
nonempty exact partition. Count final trimming and zero tests when they are actually executed.

Inspect compiled control flow as well as arithmetic profiles. Recursive certified wrappers or
repeated array pops can add work that primitive-request counts do not describe. The
[normalization program](../../ArkLib/ToCompPoly/Univariate/ArithmeticNormalization.lean)
keeps its original array and certified result type fixed throughout a backwards scan. A zero
branch returns the recursive call directly; the outer constructor extracts at most one prefix
and reuses the full array when possible. Its exact request profile excludes prefix extraction
and allocation. Scaled native probes supplement that profile without proving machine-time or
allocator bounds.

## Source openings and backend work

An input view can implement one logical answer with several underlying queries. Prove opening
bounds through the actual substitution/terminal action, and use an execution log whose erasure
law connects it to the same endpoint. Equality under deterministic handlers alone does not imply
identical traces or costs. The generic
[prior-source log law](../../ArkLib/Interaction/Oracle/SourceRouting.lean),
[terminal-bind/erasure laws](../../ArkLib/Interaction/Oracle/LoggedExecution.lean) and native
[`logged_final_query_eq_boundary`](../../ArkLib/ProofSystem/Sumcheck/Interaction/Resources.lean)
connect the actual terminal action and its ordered log to the retained boundary view. Preserve
fresh-message queries and prover-private continuation effects when routing a source; see
[interaction-naming.md](interaction-naming.md).

Count work inside a transparent dense-table handler separately from oracle openings. A source
query bound describes the oracle protocol; it does not by itself bound the complete dense runner.

Ambient sampling and source openings are separate logs. Use the actual phased execution and
party partition when attributing sampler requests; identical query indices can occur on either
party. [LogUp's endpoint consumers](../../ArkLib/ProofSystem/Logup/Interaction/SamplingResources.lean)
preserve the actual Bool and ordered ambient log, specialize actual supported draw lengths, and
use proved honest private-party count zero for default totals. An arbitrary prover can make
additional private requests. A supported complete-result equation is not a losslessness theorem
or a fixed count for a partial run that aborts before later stages.

## Logical storage and actual builders

State the inventory before claiming a storage bound: retained input/source messages, all relevant
private table levels, source/path payload roots and active workspace are separate roles. Preserve
explicit allowances for opaque getter/view, embedding/primitive and caller/raw representations.
A raw query log can retain an arbitrarily large response type; its entry count alone is not a
payload-size bound.

Inspect the selected constructor's actual builder. An increasing array-push loop keeps bounded
old/new prefixes. `List.mapTR` instead keeps a reverse accumulator. Recursive `certifiedMap` can
retain certified heads and a returned suffix before list-to-array conversion. An array-push
invariant does not justify the latter census. Distinguish completed buffers from their builder
prefixes, and count empty arrays/outer containers separately from scalar positions. The
[concrete buffer proofs](../../ArkLib/ProofSystem/Logup/Prover/StorageBuffers.lean) illustrate these
three cases; the [combined inventory](../../ArkLib/ProofSystem/Logup/Prover/StorageLedger.lean)
keeps BASE/E/Nat/Fin payload, arrays, list cells and context roots in separate categories.

Label such bounds as declared logical cells/container roles. They may conservatively count aliases
more than once and do not establish allocator peak, physical sharing, bytes, closure/stack layout,
GC liveness or a census of every historical allocation. Native scaling probes provide additional
engineering evidence; instruction profiles and output equality do not prove those machine claims.
