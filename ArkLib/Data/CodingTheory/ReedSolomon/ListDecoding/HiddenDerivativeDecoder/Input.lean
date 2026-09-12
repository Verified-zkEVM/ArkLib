/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Space
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.ConcreteEquation
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ExactOutput
public import ArkLib.Data.Polynomial.Differential.Basic
/-!
# Public inputs for the paper hidden-derivative decoder

This file contains the ordinary finite received word, integer options, explicit failure type, and
the supplied sparse-equation contract used by `ExactHiddenDerivativeDecode`.  Runtime branch
selection uses only natural-number comparisons.  The semantic predicates live separately and do
not supply candidate families or any other output that the decoder is meant to construct.

The bounded fallback follows the paper literally: after the impossible-agreement and constant
branches, it is selected exactly when `n < N_*`, `k <= d`, or a prescribed arithmetic guard
fails.  `N_*` and the guard bounds are data fixed by the interpolation parameters; there is no
caller-controlled fallback flag.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HiddenDerivativeDecoder

open Polynomial PolynomialDifferential

/-- Ordinary finite Reed--Solomon decoding input.

The embedding packages the promised distinct evaluation points.  The received values, message
dimension, and integral agreement threshold are the only remaining instance data.
-/
structure Input (F : Type*) (n : Nat) where
  /-- Pairwise-distinct evaluation points. -/
  domain : Fin n ↪ F
  /-- Received value at each evaluation point. -/
  received : Fin n → F
  /-- Requested coefficient-vector width. -/
  k : Nat
  /-- Minimum number of agreements. -/
  agreement : Nat
  /-- Supplied prime characteristic, used by executable arithmetic guards. -/
  characteristic : Nat

/-- Candidate-selection mode prescribed by the paper.

The fixed-gap parameters are integers so branch selection remains executable; their mathematical
interpretation is checked by `ValidOptions`.
-/
inductive SelectionMode where
  /-- Enumerate all position subsets in the higher-order candidate constructor. -/
  | allSubsets
  /-- Use the fixed-gap expander with the supplied positive rational gap. -/
  | fixedGap (numerator denominator : Nat)
  deriving DecidableEq, Repr

/-- Finite structural parameters and arithmetic guard bounds.

The paper's common `N_*` and arithmetic guards are computed below from these structural
parameters.  They are deliberately absent as fields, so the caller cannot force fallback by
choosing an inflated threshold.
-/
structure Options where
  /-- Hidden-derivative order `d`. -/
  order : Nat
  /-- Interpolation multiplicity `m`. -/
  multiplicity : Nat
  /-- Total jet-degree bound `B`. -/
  jetDegree : Nat
  /-- Linear factor `C` in the challenge-degree bound `deg_X Q <= C n`. -/
  xDegreeFactor : Nat
  /-- Higher-order agreement selection mode. -/
  selection : SelectionMode := .allSubsets
  deriving DecidableEq, Repr

/-- A conservative constant-grid bound derived solely from the Taylor jet degree.

The paper's monic projection evaluates a degree-`B` leading form, while the subsequent regular
fiber search evaluates a resultant of degree at most `2 B (B-1)`.  The uniform `2 B^2` bound
therefore supplies both finite grids.  It is structural data, rather than a caller-selected guard.
-/
def coordinateGridGuard (opts : Options) : Nat :=
  2 * opts.jetDegree ^ 2

/-- Linear specialization-degree coefficient derived from the supplied equation bounds. -/
def centerLinearGuard (opts : Options) : Nat :=
  opts.xDegreeFactor + opts.jetDegree

/-- The paper's common bounded-instance threshold, fixed by structural parameters.

The successor makes each constituent guard strictly smaller than the threshold.  The leading
`3` is the characteristic-two normalization required by the implementation plan.
-/
def boundedThreshold (opts : Options) : Nat :=
  max 3 (max (opts.jetDegree + 1)
    (max (coordinateGridGuard opts + 1) (centerLinearGuard opts + 1)))

/-- Checkable validity of the finite decoding input.

The final clause records the paper's prime-field size promise in the generic field interface:
the characteristic is at least the block length.  For `ZMod q` with prime `q`, this is `n <= q`.
-/
def ValidInput {F : Type*} [Field F] {n : Nat} (input : Input F n) : Prop :=
  1 ≤ input.k ∧ input.k ≤ n ∧ input.k ≤ input.agreement ∧
    n ≤ input.characteristic ∧ input.characteristic = ringChar F

/-- Checkable consistency conditions for paper-derived options.

Placing every fixed guard strictly below `N_*` makes all prescribed guards automatic in the large
branch from `n <= char(F)` and `n <= |F|`.  The threshold is normalized to at least three, as in
the formalization plan.
-/
def ValidOptions {F : Type*} [Field F] [Fintype F] {n : Nat} (_input : Input F n)
    (opts : Options) : Prop :=
  0 < opts.multiplicity ∧
    0 < opts.jetDegree ∧
    0 < opts.xDegreeFactor ∧
    n ≤ Fintype.card F ∧
    match opts.selection with
    | .allSubsets => True
    | .fixedGap numerator denominator =>
        0 < numerator ∧ numerator < denominator

/-- The arithmetic guards checked before entering the symbolic branch.

These are the paper's characteristic, finite-grid, and quadratic center-field size checks.
The supplied prime characteristic is also the paper base-field size; reading it does not
enumerate the field. A
failure belongs to the authorized bounded-position fallback branch.
-/
@[reducible] def prescribedGuardsPass (characteristic fieldCard n k : Nat)
    (opts : Options) : Prop :=
  max (k - 1) opts.jetDegree < characteristic ∧
    coordinateGridGuard opts < fieldCard ∧
    centerLinearGuard opts * n < fieldCard ^ 2

/-- Computed paper guard for `ExactBySubsets`.

There is deliberately no Boolean or mode field that can force this fallback.
-/
@[reducible] def fallbackRequired (F : Type*) [Field F] [Fintype F] {n : Nat}
    (input : Input F n)
    (opts : Options) : Prop :=
  n < boundedThreshold opts ∨ input.k ≤ opts.order ∨
    ¬ prescribedGuardsPass input.characteristic input.characteristic n input.k opts

/-- Decidable result of the top-level branch selector, in paper order. -/
inductive Branch where
  /-- `A > n`: no word can have enough agreements. -/
  | impossibleAgreement
  /-- `k = 1`: count sufficiently frequent received values. -/
  | constant
  /-- A bounded instance, small message degree, or failed prescribed guard. -/
  | boundedFallback
  /-- Execute separant stages, Taylor construction, candidates, and recovery. -/
  | symbolic
  deriving DecidableEq, Repr

/-- Explicit failures of the paper decoder.

The milestone-one symbolic error makes the unimplemented constructor boundary visible.  In
particular it can never be confused with the successful empty list or trigger a second fallback.
-/
inductive Error where
  /-- A support certificate failed a checked dimension or kernel condition. -/
  | certificateFailure
  /-- A supplied concrete equation is zero or violates its advertised bounds. -/
  | invalidEquation
  /-- The symbolic constructor is not yet installed at this milestone. -/
  | symbolicBackendUnavailable
  /-- An installed Taylor, candidate, or recovery operation reported a genuine failure. -/
  | symbolicFailure
  deriving DecidableEq, Repr

/-- Executable sparse differential equation supplied to the decoder.

Concrete variables `0,1,...,d+1` denote `X,Y₀,...,Y_d`, respectively.
-/
structure SuppliedEquation (F : Type*) [Zero F] (opts : Options) where
  /-- Sparse computable polynomial in `X,Y₀,...,Y_d`. -/
  polynomial : CPoly.CMvPolynomial (opts.order + 2) F

/-- Executably check that a supplied equation is nonzero and obeys its advertised support bounds.

The concrete coordinates are `X,Y₀,…,Y_d`, so coordinate zero is checked against `C n` and
the sum of all remaining coordinates is checked against `B`.  `Lawful.monomials` contains exactly
the stored nonzero terms; consequently an empty list is precisely the zero sparse polynomial.
-/
def SuppliedEquation.boundsPass {F : Type*} [Zero F] {n : Nat} {opts : Options}
    (equation : SuppliedEquation F opts) : Bool :=
  let monomials := CPoly.Lawful.monomials equation.polynomial
  !monomials.isEmpty && monomials.all fun monomial =>
    decide (monomial.degreeOf 0 ≤ opts.xDegreeFactor * n) &&
      decide ((∑ i : Fin (opts.order + 2),
        if i = 0 then 0 else monomial.degreeOf i) ≤ opts.jetDegree)

/-- The supplied equation respects the paper's finite support bounds. -/
def SuppliedEquation.WithinBounds {F : Type*} [Field F] {n : Nat} {opts : Options}
    (equation : SuppliedEquation F opts) : Prop :=
  let Q := HiddenDerivative.semanticEquation equation.polynomial
  (∀ exponent ∈ Q.support,
      exponent none ≤ opts.xDegreeFactor * n ∧
        HiddenDerivative.totalJetDegree exponent ≤ opts.jetDegree)

/-- Semantic promise of the supplied-equation entrypoint.

The bounded nonzero equation must vanish after substituting every degree-`< k` message meeting
the requested agreement threshold.  This is the one intentional proof-level premise of supplied
mode; it contains no candidate list, root representation, or decoder output.
-/
def SuppliedEquation.Explains {F : Type*} [Field F] [DecidableEq F] {n : Nat}
    (input : Input F n) {opts : Options} (equation : SuppliedEquation F opts) : Prop :=
  SuppliedEquation.WithinBounds (n := n) equation ∧
    HiddenDerivative.semanticEquation equation.polynomial ≠ 0 ∧
    ∀ P : F[X], P.degree < input.k →
      input.agreement ≤ Code.agree (evalOnPoints input.domain P) input.received →
      PolynomialDifferential.differentialSpecialization
        (HiddenDerivative.semanticEquation equation.polynomial) P = 0

end ReedSolomon.ListDecoding.HiddenDerivativeDecoder
