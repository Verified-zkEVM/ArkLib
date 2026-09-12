# Verified decoder status

Source checkpoint: `3c67cb3fa669985b2add6c5d080a3060c4728789`, validated on 2026-09-11.
Use the [current task board](README.md#current-task-board) for subsequent assignments and revisions.
All source paths below are relative to `ArkLib/Data/CodingTheory/ReedSolomon/` unless stated otherwise.

## Implemented and proved

| Component | Source owners | Established boundary |
| --- | --- | --- |
| Input and dispatch | `ListDecoding/HiddenDerivativeDecoder/{Input,Run,Correctness}` | Supplied-equation and certified-support entrypoints; ordered guards; exact impossible-agreement, constant and bounded-fallback branches |
| Support interpolation | `HiddenDerivativeDecoder/Explainer`, `Explainer/Support`, `EquationChecks` under `ListDecoding` | Actual local rows and nonzero-kernel extraction; checked degree/support bounds; equation explains all wanted messages under the certificate hypotheses |
| Tower packets | `ListDecoding/TowerRepresentation` | Canonical nested coefficients, well-formedness, geometric specialization and univariate embedding |
| Zero/unit split | `ListDecoding/TowerAlgebra/{SplitZeroUnit,PartitionAccounting}` | Executed splitting, geometric coverage/disjointness, residual zero/unit properties and exact dimension accounting |
| Fiber preprocessing | `ListDecoding/TowerAlgebra/{PreprocessFiber,PreprocessAccounting}` | Exact retained separant-nonzero point set, well-formed disjoint outputs and dimension nonincrease |
| Quotient normalization | `ListDecoding/TowerAlgebra/ReductionAlgebra` | Executable reduction is additive, idempotent and compatible with multiplication |
| Inversion and materialization | `ListDecoding/TowerAlgebra/{Inverse,InverseElimination,GeometricSeparation,Materialize}` | Unit completeness, nonunit failure, geometric nonvanishing equivalence, canonical inverses, executed coefficient materialization and rational specialization |
| Batched recovery | `ListDecoding/AgreementRecovery/{BatchedTower,BatchedTowerCorrectness}` | Shared product-tree restriction, fiber-local reductions, exact represented-family recovery, stopping/interpolation, final filtering and duplicate freedom |
| Taylor specification | `HiddenDerivative/RootFinding/Taylor/Chart`, `SquareSystems/TaylorTable`, `ListDecoding/ComputedTaylorMap` | Rational chart identities, regular-solution specialization and executed numerator recurrence; a specification/reference for the missing fast constructor |
| Nonreduced arithmetic | `ArkLib/Data/MvPolynomial/{BoxTruncation,BoxAlgebra}` and `ArkLib/Data/Polynomial/NilpotentInverse` | Executable box ring, canonical arithmetic and finite inverse correction given a nilpotent residual certificate |
| Ordinary ingredients | `ListDecoding/{OrdinaryInterpolation,OrdinaryQuotientDecoder,OrdinaryInterpolatedDecoder}` | Executed interpolation, actual quotient Newton doubling, global coefficient shifting and recovery; exactness still assumes a suitable regular center |

Recovery is complete for the supplied represented family. Promoting it to the complete agreement
list requires coverage from an actual candidate constructor. This is an honest modular theorem,
not completion of the missing candidate producer.

The inverse runtime uses elimination on the full rectangular multiplication matrix and verifies
the returned quotient equations. It equals the Cramer reference under the proved hypotheses.
It does not claim the sharper cost of linear algebra over the base quotient. `Matrix.SquareSolve`
is certified here for injective square matrices, not as a general singular-system solver.

## What changed in the completed foundation integration

- Worker A's returned inverse implementation was repaired and its missing unit-to-success and
  nonvanishing-to-unit proofs were closed. Materialization now executes elimination.
- Workers B and C's accounting and batching patches were repaired, compiled, and connected to
  executed regression suites. Tests distinguish equal base moduli with different fiber moduli.
- Worker D's equation checks were repaired. Duplicate exponent-frame entries were removed before
  allocating adapter rows, preserving their kernel and making valid support construction succeed.
- Worker E's review led to an explicit `Fintype.card F = ringChar F` options requirement for the
  paper's prime-base-field contract and isolated guard tests. The generic runtime field interface
  remains broader than that public paper contract.
- Characteristic two is excluded from symbolic dispatch for valid inputs: `n ≤ 2 < N_*`.
  The future concrete Rojas call path must inherit this dispatch fact.
- Box arithmetic and finite nilpotent inverse correction were added as the next Taylor foundation.
  The whole parameter-ideal nilpotence bound and initial lifted Bézout inverse are still missing.

## Remaining algorithm obligations

| Paper procedure | Current completion boundary |
| --- | --- |
| `ExactHiddenDerivativeDecode` | Dispatch and easy branches exist; symbolic execution still returns a typed unavailable error |
| `RecoverAgreement` | Tower and batched consumers are implemented and proved for represented families |
| `FirstOrderNormCandidates` | Finite preprocessing is ready; generic component loop, actual norms, labelled decomposition and unconditional constructor coverage remain |
| `PairedCandidates` | Direct current-chart systems, concrete isolated-root producer, and both actual selection modes remain |
| `FastRegularTaylorFamily` | Mathematical chart and arithmetic foundations exist; projection, confluent lifting and global reconstruction remain |
| `SplitZeroUnit` | Tower procedure and correctness/accounting are implemented |
| `PreprocessFiber` | Tower procedure and correctness/accounting are implemented |
| `ZerothOrderDecode` | Existing ordinary ingredients are reusable; dedicated interpolation correspondence, global normalization, one-center selection and unconditional run remain |

Finite D5 over `E[U]/G` does not implement the earlier generic component loop over `E(U)[V]`.
Squarefree support and Hasse-threshold retention do not produce a full multiplicity-labelled
factorization. Existing Rojas extraction/specialization consumes supplied polynomial or
factorization data; it does not construct the system-to-resultant producer. The old conditional
square-system wrapper also uses affine shifts and tail equations absent from the new target.

The existing ordinary interpolation already uses Lee–O'Sullivan and a verified fast
Mulders–Storjohann reducer. Calling it merely dense elimination is outdated. Its relation to the
paper's specified interpolation-basis algorithm still requires proof; renaming it is insufficient.
The dedicated zeroth-order branch can reuse the existing quotient Newton implementation.

## Verification evidence

The source checkpoint passed `./scripts/validate.sh --axioms`: project build, compile-time clients,
warning budgets, source-policy fixtures, all registered compiled runtime suites, generated imports,
RS mathematical import boundaries, documentation checks and the axiom regression gate.

The scan covered 37,636 declarations across 1,571 modules. It reported 289 declarations with
pre-existing admission taint, no nonstandard-axiom taint, and no new axiom/admission regression.
The baseline was unchanged. Principal new inverse, materialization, solver and correction proofs
use only `propext`, `Classical.choice` and `Quot.sound`.

Runtime cases cover nonunits, multiple components, extension-only parameters, ramified fibers,
branch-local reductions, early stopping, final rejection, deduplication, successful support
construction, malformed bounds, and mixed nilpotent terms. Independent source review found no
mathematical defect in the repaired normalization/inverse contracts and shared input changes.
This evidence certifies the foundation checkpoint, not the unfinished full decoder.
