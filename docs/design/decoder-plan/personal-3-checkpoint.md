# Personal 3 field, resultant and selection checkpoint

This collection adds six reviewed production/test pairs to the Taylor payload baseline
`21310026e27b9c13ea64999c095b7770cda22bad`, registers their six compiled runtime suites, and
regenerates the public imports. It does not complete G07, G08, G09 or the symbolic decoder.

The collection branch is `quang/decoder-worker-integration`. Personal 4 owns its eventual adoption
into the core branch. A validated collection on this branch does not certify a later merge
with Personal 4's in-progress Taylor changes; that combined state needs its own full gate.

## Source provenance

Production and test contents are preserved exactly from these worker commits. The direct-selection
test is relocated to mirror its production path under
`ArkLibTest/Data/CodingTheory/ReedSolomon/ListDecoding/HigherOrderProducer/`:

| Slice | Original commit | Established boundary |
| --- | --- | --- |
| Quotient fields | `d7a61f24ce6bb91f95d453b3ac5daef403e42e93` | Stored monic quotient arithmetic, actual Euclid inversion, field instance under certified irreducibility |
| Quadratic centers | `86e6e5fefe4ca142ea00237e2bcd746aa8fa5025` | Executed bounded Euler search, odd-prime success, distinct requested quadratic prefix within its size bound |
| Linear Rojas producer | `88ac5445416fba1c9ac5bf094eeaed70767169da` | Input-dependent degree-one perturbation and resultant identity, retaining zero-coordinate roots |
| Stored resultant | `859cfc0a2def199d170f560619ffc4a99f5727c7` | Actual padded Sylvester matrix and determinant, checked input degree bounds |
| Gabber–Galil graph | `13d569edffedc4cdd6d6f2103ae10b61b8cd3b6d` | Eight affine labels, inverse/reversal identities and dart-count regularity, preserving loops and multiplicities |
| Direct-system capture | `e0cee2d383402fe8182e01d5cd3858165d32b1af` | Executed all-subsets enumeration and common-zero capture from supplied evaluation and linear differential data |

The separate direct-selection source commit `39de784d6de87e71a6cfdfc060c15e0d9e3daf1d`
is already represented by the last row; do not collect it again.

Runtime registration is centralized in `scripts/AgreementRecoveryRuntime.lean`:
`ExplicitQuotientTests.run`, `ExplicitCenterTests.run`, `RojasLinearProducerTests.run`,
`RojasUnivariateProducerTests.run`, `GabberGalilTest.run`, and `ArkLibTest.DirectSelection.run`.
Worker validation-only umbrella edits are replaced by fresh umbrella generation here.

## Remaining obligations

- G07 must construct general extensions over the current center field, with actual irreducible
  search/certification, characteristic/cardinality/embedding data, inverse Frobenius and a
  sufficiently large prefix. The coordinator connects prime/quadratic guards and dispatch.
- G08 must construct the general multivariate perturbation and representation packets from
  the actual system, including mixed-dimensional affine isolated-root coverage. The univariate
  padded determinant does not by itself provide these guarantees.
- G09 must identify the supplied linear rows with actual chart differentials and prove tangent
  injectivity. Spectral certification, graph powering and expander selection remain separate
  from the direct all-subsets path.
- I0/I1 must compose these produced guarantees with candidate materialization and recovery.
  A common-zero capture theorem with supplied differential premises is an intermediate bridge.

## Acceptance

All three worker branches reported runtime success and full `validate.sh --axioms` success.
The collection additionally requires the same full gate on the combined source, independent
integration review, and no change to dependency pins or the axiom baseline before publication.
Record the actual exit status and collection commit in the coordinator handoff; do not infer
combined validation from the separate worker gates.

The team ledger is Personal 1 for G01/G02/G06, Personal 3 for G07/G08/G09, and Personal 4 for
I0/I1/G03/G04/G05/G10. Personal 2 is unavailable. The user explicitly confirmed these launches.
