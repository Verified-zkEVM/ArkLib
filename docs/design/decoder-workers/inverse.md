# Worker A: compute tower inverses and materialize coefficients

Read the shared worker instructions in [README](README.md). Start from the exact
checkpoint SHA supplied by the coordinator. Your branch is `quang/decoder-m1-inverse`.

## Owned files

Create `TowerAlgebra/Inverse.lean` and `TowerAlgebra/Materialize.lean`. You may add
corresponding tests under `ArkLibTest/Data/CodingTheory/ReedSolomon/ListDecoding/`.
Do not edit existing tower, recovery, or dispatcher modules.

## Deliverable

Implement inversion in the finite algebra F[U,V]/(G(U),H(U,V)) for a well-formed tower.
Use the actual nested polynomial representation and its reduction operations. Return
an explicit failure result for nonunits. Prove that the computed inverse succeeds for
a unit denominator, and that multiplying by the returned inverse reduces to one.
Connect unitness to nonvanishing at all geometric points, with assumptions explicit.
The inverse must be computed; a caller-supplied inverse or choice in executable code
does not satisfy this task.

The intended route is a multiplication matrix in the rectangular basis
U^i V^j, followed by determinant/adjugate inversion. If a different finite linear-algebra
algorithm is materially simpler, document the algorithm and performance implications.
Do not enumerate F or points. Reuse existing matrix and concrete polynomial tools.

Add coefficient materialization: reduce numerator times the computed denominator inverse
for each message slot; preserve the supplied width; prove specialization equals the
original rational coefficients at every retained point. Produce a well-formed tower
packet usable by `AgreementRecovery.Tower`.

## Starting points and acceptance

Read `TowerRepresentation.lean`, `TowerAlgebra/SplitZeroUnit.lean`, and
`TowerAlgebra/PreprocessFiber.lean`. The latter clears coefficient slots deliberately.
Existing univariate inversion/materialization code is useful precedent, but treating
V as a field or inverting a zero divisor is invalid.

Acceptance requires compiled success/soundness/materialization theorems and executable
examples covering a unit, a zero divisor, multiple components, and an extension-only
base modulus. Report any missing bridge theorem precisely. Do not weaken the success
statement by assuming the algorithm already returned an inverse.
