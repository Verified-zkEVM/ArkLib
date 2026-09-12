# Personal 1 algebra, decomposition and norm checkpoint

This collection adopts seven reviewed worker checkpoints alongside the
[Personal 3 collection](personal-3-checkpoint.md), on the Taylor payload baseline
`21310026e27b9c13ea64999c095b7770cda22bad`. The collection branch is
`quang/decoder-worker-integration`; Personal 4 remains the core adoption owner.

## Source provenance and completion boundary

| Slice | Original commit | Established boundary |
| --- | --- | --- |
| Stored fractions | `86fe35c1f8242296a654fb15d733a3bc0690a470` | Executed arithmetic, validity, gcd cancellation and checked exact division |
| Function-field Euclid | `bef80f008b2cebe001536d678197279cd1d980ef` | Lawful executable fraction field and actual polynomial Euclid, with semantic gcd/division refinement |
| Multiplicity residues | `9384d639c04f95df3807ac770814fafab6005e18` | Actual residue initialization/loop and successful reconstruction under perfect-field hypotheses |
| Inverse Frobenius | `5efbc8d1d74ec259cd409307cfa2ecdd2a085952` | Certified coefficient contraction, reconstruction and degree descent; concrete prime-field instance |
| Tree refinement | `0f40de342312a63448313c87e78211f040556687` | Balanced weighted product, batched tagged routing, global reconstruction and destination divisibility |
| Polynomial norms | `6e43c1a11ff2b56c7865e91ba3bcd1f135947634` | Actual remainder multiplication matrix/determinant, specialization and point detection |
| Universal scan | `3e708ec8ce810b0720760747f6e672742d8a3771` | Executed three-way component scan, product/root coverage, residual classification and distinct position labels |

Production and test contents are unchanged from these commits. The three decomposition tests
are relocated from `ArkLibTest/FullSquarefreeDecomposition/` to the matching production layout
`ArkLibTest/Data/Polynomial/FullSquarefreeDecomposition/`.

The shared runtime registers `FunctionFieldAlgorithmsTests.run`, `FunctionFieldEuclidTests.run`,
`FullSquarefreeResidueTests.run`, `FullSquarefreeFrobeniusTests.run`,
`FullSquarefreeTreeTests.run`, `NormProductsTests.run`, and `UniversalAgreementTests.run`.
The umbrella is regenerated from tracked source instead of copying worker validation-only edits.

## Remaining obligations and next assignment

G01 still needs executable canonical representative extraction and denominator clearing,
multivariate gcd, normalization and all-fiber factor descent. The immediate consumer milestone
is ordinary-interpolant normalization that preserves every polynomial graph, with an actual
nonzero regular-center resultant obstruction. It must handle characteristic-divisible
multiplicities without assuming the imperfect field `E(X)` is perfect.

G02 still needs the residue/multiplicity identity, true-characteristic exhaustion argument,
recursive-only factors, weighted tagged refinement and final multiplicity grouping. Its final
driver must produce the labelled decomposition and call it from threshold selection.

G06 still needs descent through every projection fiber, the chart-derived universal-position
bound, multiplicity of the actual norm product, and candidate assembly/coverage. Generic root
coverage from a product identity is not yet this chart-dependent candidate theorem.

Personal 1 continues to own G01/G02/G06. Personal 3 owns G07/G08/G09, including the
constructed-field dependency; those groups have returned checkpoints and are not deferred. Personal 4 owns shared chart validity and
coverage, Taylor construction, zeroth-order composition and integration. The payload is already
available at `21310026e...`; full chart validity/coverage remains a separate contract.

## Acceptance

Each original checkpoint reported full validation and independent review. The collection must
also pass `./scripts/validate.sh --axioms` with all thirteen Personal 1/3 runtime suites registered,
unchanged dependency pins and unchanged axiom baseline before publication. Record the collection
commit and actual combined gate result in the coordinator handoff. A later core merge with new
Taylor work requires validation again; individual worker gates do not establish that result.
