/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HiddenDerivativeDecoder.Explainer.Support
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HiddenDerivativeDecoder.Input

/-!
# Certified-support entrypoint for the paper decoder

The public certificate contains only a finite prescribed monomial support. Its validity predicate
checks the support shape and bounds plus a strict dimension margin for the actual matrix built
from the ordinary decoder input. The constructor executes that matrix, extracts a nonzero kernel
vector, and returns the same concrete sparse equation accepted by supplied-equation mode.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HiddenDerivativeDecoder

open Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative

/-- Finite support data for certified equation construction. Exponent vectors use the order
`[X,Y₀,...,Y_d]`. -/
structure SupportCertificate where
  vectors : List (List ℕ)
  deriving DecidableEq, Repr

/-- Internal arbitrary-support package using the multiplicity fixed by the public options. -/
def SupportCertificate.support (opts : Options) (certificate : SupportCertificate) :
    Explainer.Support :=
  ⟨certificate.vectors, opts.multiplicity⟩

/-- Execute all public support checks: local interpolation validity, actual row-count margin, and
the equation bounds consumed by later symbolic stages. -/
def SupportCertificate.check {F : Type*} [Field F] {n : ℕ} (input : Input F n)
    (opts : Options) (certificate : SupportCertificate) : Bool :=
  Explainer.check opts.order (input.k - 1) input.agreement (certificate.support opts)
      (Explainer.receivedPoints input.domain input.received) &&
    certificate.vectors.all fun v =>
      decide (v.getD 0 0 ≤ opts.xDegreeFactor * n) &&
        decide (Explainer.denseJetDegree opts.order v ≤ opts.jetDegree)

/-- A public support certificate is valid exactly when its finite runtime check accepts. -/
def SupportCertificate.Valid {F : Type*} [Field F] {n : ℕ} (input : Input F n)
    (opts : Options) (certificate : SupportCertificate) : Prop :=
  certificate.check input opts = true

/-- Logical characterization of the public executable support check. -/
theorem SupportCertificate.check_eq_true_iff {F : Type*} [Field F] {n : ℕ}
    (input : Input F n) (opts : Options) (certificate : SupportCertificate) :
    certificate.check input opts = true ↔
      Explainer.Valid (F := F) opts.order (input.k - 1) input.agreement
          (certificate.support opts) (Explainer.receivedPoints input.domain input.received) ∧
        ∀ v ∈ certificate.vectors,
          let exponent := NonzeroInterpolationMachine.exponent opts.order v
          exponent none ≤ opts.xDegreeFactor * n ∧ totalJetDegree exponent ≤ opts.jetDegree := by
  simp only [SupportCertificate.check, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hlocal, hbounds⟩
    refine ⟨hlocal, ?_⟩
    intro v hv
    simpa only [NonzeroInterpolationMachine.exponent_none,
      ← Explainer.denseJetDegree_eq] using hbounds v hv
  · rintro ⟨hlocal, hbounds⟩
    refine ⟨hlocal, ?_⟩
    intro v hv
    simpa only [NonzeroInterpolationMachine.exponent_none,
      ← Explainer.denseJetDegree_eq] using hbounds v hv

/-- Execute certified support interpolation. Failure means that a finite support or dimension
check was not justified; symbolic failures remain distinct in the top-level decoder error type. -/
def construct {F : Type*} [Field F] [DecidableEq F] {n : ℕ} (input : Input F n)
    (opts : Options) (certificate : SupportCertificate) :
    Except Error (SuppliedEquation F opts) :=
  if certificate.check input opts then
    match Explainer.construct? (F := F) opts.order (input.k - 1) input.agreement
        (certificate.support opts) (Explainer.receivedPoints input.domain input.received) with
    | none => .error .certificateFailure
    | some result => .ok ⟨result.equation⟩
  else .error .certificateFailure

section Correctness

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

omit [DecidableEq F] in
private theorem source_within_bounds (input : Input F n) (opts : Options)
    (certificate : SupportCertificate)
    (hvalid : certificate.Valid input opts)
    (coefficients : ℕ → F) :
    ∀ exponent ∈
        (InterpolationPointBlockMachine.sourceCombination opts.order certificate.vectors
          coefficients).support,
      exponent none ≤ opts.xDegreeFactor * n ∧ totalJetDegree exponent ≤ opts.jetDegree := by
  have hchecked := (SupportCertificate.check_eq_true_iff input opts certificate).mp hvalid
  have hconditions := (Explainer.check_eq_true_iff opts.order (input.k - 1)
    input.agreement (certificate.support opts)
    (Explainer.receivedPoints input.domain input.received)).mp hchecked.1
  intro exponent hexponent
  have hwidth := hconditions.2.2.1
  change exponent ∈
    (InterpolationPointBlockMachine.sourceCombination opts.order
      (certificate.support opts).vectors coefficients).support at hexponent
  rw [Explainer.sourceCombination_eq (certificate.support opts) hwidth] at hexponent
  obtain ⟨v, hv, he⟩ := List.mem_map.mp
    (NonzeroInterpolationMachine.combination_support _ coefficients exponent hexponent)
  rw [← he]
  exact hchecked.2 v hv

/-- A valid public support certificate makes equation construction succeed and yields the exact
semantic certificate of the executed local matrix and kernel solver. -/
theorem construct_success (input : Input F n) (opts : Options)
    (certificate : SupportCertificate) (hvalid : certificate.Valid input opts) :
    ∃ equation, construct input opts certificate = .ok equation ∧
      ∃ result,
        Explainer.construct? (F := F) opts.order (input.k - 1) input.agreement
            (certificate.support opts)
            (Explainer.receivedPoints input.domain input.received) = some result ∧
          equation.polynomial = result.equation ∧
          Explainer.Certified (input.k - 1) input.agreement (certificate.support opts)
            (Explainer.receivedPoints input.domain input.received) result := by
  have hchecked := (SupportCertificate.check_eq_true_iff input opts certificate).mp hvalid
  obtain ⟨result, hrun, hcertified⟩ := Explainer.construct?_success
    (certificate.support opts) (Explainer.receivedPoints input.domain input.received) hchecked.1
  have hcheck : certificate.check input opts = true := hvalid
  exact ⟨⟨result.equation⟩, by simp [construct, hcheck, hrun], result, hrun, rfl, hcertified⟩

/-- Certified-support construction is a supplied equation that explains every qualifying
message. The vanishing property is derived from the executed local constraints and dimension
margin; it is not part of the caller's certificate. -/
theorem construct_explains (input : Input F n) (opts : Options)
    (certificate : SupportCertificate) (_hinput : ValidInput input)
    (hvalid : certificate.Valid input opts) :
    ∃ equation, construct input opts certificate = .ok equation ∧ equation.Explains input := by
  obtain ⟨equation, hconstruct, result, hrun, hequation, hcertified⟩ :=
    construct_success input opts certificate hvalid
  refine ⟨equation, hconstruct, ?_, ?_, ?_⟩
  · dsimp [SuppliedEquation.WithinBounds]
    rw [hequation, hcertified.2.2.2.1]
    exact source_within_bounds input opts certificate hvalid
      (fun i => result.coefficients.getD i 0)
  · rw [hequation]
    exact hcertified.2.2.2.2.1
  · intro P hPdegree hagreement
    have hPnat : P.natDegree ≤ input.k - 1 := by
      by_cases hPzero : P = 0
      · rw [hPzero, Polynomial.natDegree_zero]
        omega
      · have hlt : P.natDegree < input.k :=
          (Polynomial.natDegree_lt_iff_degree_lt hPzero).mpr hPdegree
        omega
    have hagreement' :
        input.agreement ≤ (polynomialAgreementSet input.domain input.received P).card := by
      unfold Code.agree at hagreement
      let agreementSet : Finset (Fin n) :=
        Finset.univ.filter (fun i => P.eval (input.domain i) = input.received i)
      change input.agreement ≤ agreementSet.card at hagreement
      simpa only [polynomialAgreementSet, agreementSet] using hagreement
    rw [hequation]
    exact hcertified.vanishes_of_agreements (certificate.support opts) input.domain
      input.received result P hPnat hagreement'

end Correctness

end ReedSolomon.ListDecoding.HiddenDerivativeDecoder
