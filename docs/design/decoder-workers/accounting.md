# Worker B: prove tower partition and dimension accounting

Read [shared instructions](README.md). Use the supplied checkpoint SHA and branch
`quang/decoder-m1-accounting`.

## Owned files

Create `TowerAlgebra/PartitionAccounting.lean` and
`TowerAlgebra/PreprocessAccounting.lean`, with corresponding new test files if useful.
Do not edit the existing splitter or preprocessor.

## Deliverable

Prove that `splitZeroUnit` gives a disjoint geometric partition of a well-formed
parent, with the residual zero on zero-tagged children and nonzero on unit-tagged
children. Account for list positions or prove output uniqueness: a membership-only
existence theorem does not rule out duplicate components.

Prove that the sum of child dimensions equals the parent dimension. Dimension is
base degree times fiber degree. Include removal of zero-dimensional pieces in the
statement about the actual returned list.

For `preprocessFiber`, prove disjointness of retained components and that the sum of
output dimensions is at most the input dimension under its existing characteristic
and degree assumptions. Retained geometric points are exactly input points where the
supplied separant is nonzero; connect your accounting with that existing theorem.

## Starting points and acceptance

Read `TowerAlgebra/Normalization.lean` for `terminal_fiber_degree_sum` and degree
preservation under base reduction. Read the existing D5 `factorTower` product,
coprimality, root uniqueness, and terminal invariants. The splitter already proves
point soundness, completeness, specialization preservation, and well-formedness.
Do not reimplement those operations or count base-field roots (extension points matter).

Acceptance requires compiled theorems for the actual output lists, with no added
assumption asserting the desired partition or dimension sum. Cover constant/empty
pieces and repeated or ramified fibers where the preprocessor permits them. Return
precise statements and axiom output for the principal accounting theorems.
