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

This module is a reader index for the algorithms in [DKTZ26]. It imports proved interfaces and
records their exact integration status. It adds no executable wrapper and no complexity claim.

## Exact hidden-derivative decoding

The paper's `ExactHiddenDerivativeDecode` algorithm does not yet have one end-to-end Lean `run`
function and exactness theorem. Two retained reference decoders establish useful, narrower
contracts:

* `ReedSolomon.ListDecoding.PositionSubsetDecoder.run_exact` is an exponential correctness
  reference that enumerates
  position subsets and does not enumerate field elements.
* `ReedSolomon.capacity_decoder_exact_output_and_primitive_work` connects the retained coordinate
  executor to
  `ReedSolomon.ListDecoding.ExactOutput` and to its observed primitive-work ledger. It is not the
  paper's norm and
  square-system decoder, and it makes no bit-complexity claim.

The mathematical list theorems imported by `ArkLib.Data.CodingTheory.ReedSolomon.PaperGuide` are
exact finite-set
specifications. Classical extraction of those sets is not an efficient decoder.

## Recovering agreement from finite representations

`ReedSolomon.ListDecoding.FiniteRepresentation` stores the paper's pair `(h,C)` without storing
parameter roots or an
extension field. `ReedSolomon.ListDecoding.AgreementRecovery.decode_represented_exact` proves that
executable gcd splitting,
base-field interpolation, and the final agreement check recover exactly the qualifying messages
inside the represented family.
`ReedSolomon.ListDecoding.AgreementRecovery.RepresentedExactOutput.toExactOutput` promotes this to
the ordinary
complete-list contract when the constructor supplies a coverage proof. Coverage is a theorem
hypothesis, never an input to the program.

This is the proved semantic endpoint behind `RecoverAgreement` for a single univariate pair
`(h,C)`. The paper's two-level tower representation and its recovery consumer still need
integration.

## First-order norm candidates

The `FirstOrderNormDecoder` subtree contains executable and semantic components for the paper's
`FirstOrderNormCandidates` routine:

* the D5 factor tower performs branchwise dynamic evaluation, radical and separant processing, and
  coefficientwise CRT reconstruction;
* `ReedSolomon.ListDecoding.FirstOrderNormDecoder.preprocess` removes repeated and separant-zero
  fiber roots below the
  characteristic and packages well-formed finite representations.

These components do not yet compose into a top-level candidate constructor with a `run` function,
coverage theorem, and `ReedSolomon.ListDecoding.ExactOutput` capstone. They must not be cited as
an integrated implementation
of `FirstOrderNormCandidates`.

## Paired candidates and square systems

`ReedSolomon.ListDecoding.SquareSystemDecoder.run_exact_of_torus_cover` corresponds to the
square-system and Taylor-chart
path behind `PairedCandidates`. It is conditional on a caller-supplied `TorusBackend` satisfying
`CoversTorusIsolatedRoots`. `Rojas.AffineSolver` supplies the affine-chart wrapper but does not
construct the missing toric resultant solver. Consequently this is a conditional semantic
composition theorem, not an unconditional implementation or bit-cost theorem. It retains the older
affine-shift and tail-coordinate construction; the paper's direct affine solve and paired selection
are not implemented by this wrapper.

## Taylor and zero/unit subroutines

`ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ComputedTaylorMap` and
`ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TaylorChartMap` connect represented initial
jets to materialized message
coefficients and prove the relevant coverage implications. The D5 coefficient-splitting and fiber
preprocessing modules prove the finite-algebra operations used by the paper's regular Taylor and
zero/unit procedures. There is currently no single executable capstone for
`FastRegularTaylorFamily`, `SplitZeroUnit`, or `PreprocessFiber` as complete paper procedures.

## Verification boundary

At the present source state, the proved executable endpoints are the retained reference decoder,
represented-family agreement recovery, and the square-system composition relative to an explicit
backend contract. The norm constructor, toric solver, their end-to-end composition, and a
whole-decoder bit/RAM bound remain separate obligations. Reader-facing claims should preserve this
boundary.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual
  Correlated Agreement: From Johnson to Capacity*][DKTZ26], decoding algorithms and appendices.
-/

@[expose] public section
