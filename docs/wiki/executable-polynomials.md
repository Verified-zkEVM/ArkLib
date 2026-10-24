# Executable polynomial programs

Use this page when an algorithm computes polynomial messages, folds evaluation tables, or claims
arithmetic costs. Module routing belongs in [repo-map.md](repo-map.md); focused build, native
runtime and axiom checks belong in [quickstart.md](quickstart.md).

## Runtime data and mathematical views

Use CompPoly evaluation tables and coefficient arrays for executable data. Keep sparse Mathlib
polynomial interpretations in the proof layer, and explain each representation-specific
`noncomputable` declaration individually. Proof erasure can remove classical proofs; an algorithm
cannot obtain its runtime values through classical choice.

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

Padded coefficient arrays retain zero entries until explicit normalization. Addition therefore
depends on the actual accumulator width and input order. Convolution order also matters to the
executed program even when the resulting polynomials commute. The
[raw fraction-fold cost owner](../../ArkLib/ToCompPoly/Univariate/ArithmeticFractionFoldCost.lean)
records these recurrences. Retain general group-width terms before specializing to a positive,
nonempty exact partition. Count final trimming and zero tests when they are actually executed.

## Source openings and backend work

An input view can implement one logical answer with several underlying queries. Prove opening
bounds through the actual substitution/terminal action, and use an execution log whose erasure
law connects it to the same endpoint. Equality under deterministic handlers alone does not imply
identical traces or costs; see [interaction-naming.md](interaction-naming.md).

Count work inside a transparent dense-table handler separately from oracle openings. A source
query bound describes the oracle protocol; it does not by itself bound the complete dense runner.
