/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.CapacityDecoder
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PositionSubsetDecoder
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SquareSystemDecoder
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.RepresentedExact
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.CoefficientCRT
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.FiberPreprocess

/-!
# Decoder map for the Reed--Solomon capacity paper

This module is a reader index for the algorithms in [DKTZ26]. It imports retained reference
interfaces and records their integration boundary. It adds no executable wrapper or cost claim.
Current implementation coordination is maintained in `docs/design/decoder-plan/README.md`.

## Exact hidden-derivative decoding

`HiddenDerivativeDecoder.runSupplied` and `runCertified` implement the paper branch order,
checked equation/support inputs, and the impossible-agreement, constant and bounded-fallback
branches. Their successful easy outputs are exact. The symbolic branch still returns
`symbolicBackendUnavailable`; success for all supported inputs is not yet proved.

`PositionSubsetDecoder.run_exact` is the authorized fallback's exactness theorem.
`ReedSolomon.capacity_decoder_exact_output_and_primitive_work` describes the retained coordinate
executor and its observed primitive-work ledger. It is not the paper's norm/paired decoder.
Mathematical list theorems in `ReedSolomon.PaperGuide` describe finite sets; classical extraction
of those sets does not implement the missing symbolic algorithm.

## Recovering agreement from finite representations

`TowerRepresentation` stores canonical coefficients in `(E[U]/G)[V]/h` without extracting roots.
`AgreementRecovery.BatchedTower.recoverAgreement_represented_exact` proves represented-family
exactness for actual product-tree restriction, fiber-local splitting, stopping and interpolation,
final agreement filtering, and deduplication. `recoverAgreement_exact_of_coverage` promotes this
to the existing `ExactOutput` contract once an actual constructor's coverage theorem is supplied.
Coverage is proof-only, not an input to the runtime.

The univariate `FiniteRepresentation` and `AgreementRecovery.decode_represented_exact` remain
available as the special-case consumer and compatibility interfaces. Tower recovery is implemented;
the missing work is construction and coverage of the full symbolic candidate families.

## Finite-algebra split, preprocessing and materialization

`TowerAlgebra.SplitZeroUnit` implements zero/unit splitting over the finite tower.
`PartitionAccounting` proves geometric disjointness and exact dimension accounting.
`PreprocessFiber` and `PreprocessAccounting` implement and certify the retained separant-nonzero
point set, well-formedness and dimension nonincrease, using the existing D5 operations.

`ReductionAlgebra` proves quotient-normalization laws. `Inverse` and `GeometricSeparation` prove
unit completeness and the geometric nonvanishing criterion. `InverseElimination` executes a
verified elimination backend equal to the Cramer reference; `Materialize` uses it to produce
canonical message coefficients with correct rational specialization. These are complete finite
algebra foundations. They do not compute the preceding first-order norm candidate construction.

## First-order norm candidates

The full `FirstOrderNormCandidates` producer remains unfinished. Required work includes generic
component splitting over `E(U)[V]`, universal-agreement bookkeeping, actual polynomial norms,
full multiplicity-labelled squarefree decomposition, and candidate coverage. Finite D5 over
`E[U]/G` does not implement that earlier generic component loop. Existing Hasse-threshold retention
is a specification/reference; it does not replace the paper's full decomposition in execution.

## Paired candidates and isolated roots

`SquareSystemDecoder.run_exact_of_torus_cover` is conditional on a `TorusBackend` satisfying
`CoversTorusIsolatedRoots`. Its older affine-shift and tail-coordinate construction does not
implement the current direct affine system. Existing Rojas extraction and specialization begin
from supplied polynomial or factorization data. The system-to-resultant producer, its isolated-root
coverage, direct-system capture, explicit extension fields and both selection modes remain open.
The fixed-gap mode requires the executed expander and its spectral/selection certificates.

## Regular Taylor and dedicated zeroth-order decoding

`ComputedTaylorMap` and the mathematical Taylor chart provide rational numerator identities and
regular-solution specialization. The box ring and finite nilpotent inverse correction are executed
foundations. `FastRegularTaylorFamily` still needs regular projection, a good confluent sample,
local monic quotient arithmetic, algebraic/differential Newton lifting and global reconstruction.
Its runtime cannot be replaced by the existing scalar numerator recurrence.

`OrdinaryInterpolation` already executes Lee--O'Sullivan interpolation with the verified fast
Mulders--Storjohann reducer. `OrdinaryQuotientDecoder` executes quotient Newton doubling and shared
recovery. `OrdinaryInterpolatedDecoder.run_exact_of_regular_center` composes them conditionally.
The dedicated `ZerothOrderDecode` still needs the prescribed interpolation correspondence, global
normalization, a computed obstruction and one selected regular center, and unconditional exactness.
It can reuse ordinary quotient Newton without waiting for the full differential Taylor constructor.

## Verification boundary

The foundation checkpoint has passed the full build, runtime, source/import and axiom gates.
Its current public success theorems do not establish successful symbolic decoding on every valid
input. Final completion requires concrete producers, global separant/center coverage and exactness
of the actual program in both selection modes. Arithmetic, bit and RAM complexity proofs are
outside the current implementation task.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual
  Correlated Agreement: From Johnson to Capacity*][DKTZ26], decoding algorithms and appendices.
-/

@[expose] public section
