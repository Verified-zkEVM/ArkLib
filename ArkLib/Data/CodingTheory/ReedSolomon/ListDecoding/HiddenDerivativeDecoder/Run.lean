/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ConstantDecoder
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HiddenDerivativeDecoder.Explainer
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PositionSubsetDecoder
/-!
# Paper-derived top-level decoder dispatch

This module executes the branch order of `ExactHiddenDerivativeDecode`: impossible agreement,
constant messages, the paper-authorized position-subset fallback, then symbolic decoding from the
supplied equation.  The symbolic constructor is an explicit milestone boundary.  Until it is
installed it returns `symbolicBackendUnavailable`; failure never runs the subset decoder.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HiddenDerivativeDecoder

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F] [BEq F] [LawfulBEq F]
variable (cmp : F → F → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Compute the paper branch in its specified order. -/
def dispatch {n : Nat} (input : Input F n) (opts : Options) : Branch :=
  if n < input.agreement then .impossibleAgreement
  else if input.k = 1 then .constant
  else if fallbackRequired F input opts then .boundedFallback
  else .symbolic

/-- Milestone-one symbolic-constructor boundary.

Later milestones replace this body with the separant/Taylor/candidate/recovery composition.  This
stub returns a typed error and has no path to the exponential fallback.
-/
def symbolicDecode {n : Nat} (_input : Input F n) (_opts : Options)
    (_equation : SuppliedEquation F _opts) : Except Error (List (List F)) :=
  .error .symbolicBackendUnavailable

/-- Execute `ExactHiddenDerivativeDecode` from a supplied sparse equation.

The equation's sparse nonzero and support bounds are checked before symbolic execution; its
semantic vanishing promise is consumed by correctness.  Easy branches return exact outputs now.
A large valid symbolic instance reports the explicit milestone error until the concrete
constructor pipeline is installed.
-/
def runSupplied {n : Nat} (input : Input F n) (opts : Options)
    (equation : SuppliedEquation F opts) : Except Error (List (List F)) :=
  match dispatch (F := F) input opts with
  | .impossibleAgreement => .ok []
  | .constant => .ok (ConstantDecoder.run cmp input.agreement input.received)
  | .boundedFallback =>
      .ok (PositionSubsetDecoder.run input.domain input.received input.k input.agreement)
  | .symbolic =>
      if equation.boundsPass (n := n) then symbolicDecode input opts equation
      else .error .invalidEquation

/-- Execute `ExactHiddenDerivativeDecode` from a certified finite monomial support.

The support constructor assembles the actual local interpolation matrix and extracts a nonzero
kernel vector.  Certificate failure remains observable; on success this entrypoint invokes the
same ordered dispatcher and symbolic boundary as supplied-equation mode.
-/
def runCertified {n : Nat} (input : Input F n) (opts : Options)
    (certificate : SupportCertificate) : Except Error (List (List F)) :=
  match dispatch (F := F) input opts with
  | .impossibleAgreement => .ok []
  | .constant => .ok (ConstantDecoder.run cmp input.agreement input.received)
  | .boundedFallback =>
      .ok (PositionSubsetDecoder.run input.domain input.received input.k input.agreement)
  | .symbolic =>
      match construct input opts certificate with
      | .error error => .error error
      | .ok equation => runSupplied cmp input opts equation

end ReedSolomon.ListDecoding.HiddenDerivativeDecoder
