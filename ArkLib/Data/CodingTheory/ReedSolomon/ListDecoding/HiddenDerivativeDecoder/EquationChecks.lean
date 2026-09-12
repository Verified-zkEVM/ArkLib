/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HiddenDerivativeDecoder.Explainer
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Finsupp.Option

/-!
# Executable equation checks for the hidden-derivative decoder

This module certifies the sparse support check used by supplied-equation mode.  The executable
check iterates only over CompPoly's stored nonzero monomials; the main reflection theorem proves
that this is exactly the semantic support of the renamed differential polynomial, together with
the advertised X- and total-jet-degree bounds.

The same file records the arithmetic facts used by dispatch.  In particular, a finite field is
not identified with its prime subfield: `PrimeFieldSized F` is the explicit hypothesis needed to
rewrite `Fintype.card F` as `ringChar F`.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HiddenDerivativeDecoder

open PolynomialDifferential
open ReedSolomon.HiddenDerivative

private theorem finToJetVariable_eq_finSuccEquiv (r : ℕ) :
    HiddenDerivative.finToJetVariable r = ⇑(_root_.finSuccEquiv (r + 1)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem finToJetVariable_injective (r : ℕ) :
    Function.Injective (HiddenDerivative.finToJetVariable r) := by
  rw [finToJetVariable_eq_finSuccEquiv]
  exact (_root_.finSuccEquiv (r + 1)).injective

private theorem fromCMvPolynomial_support {F : Type*} [Field F] {r : ℕ}
    (Q : CPoly.CMvPolynomial (r + 2) F) :
    (CPoly.fromCMvPolynomial Q).support = CPoly.CMvPolynomial.support Q := by
  rfl

/-- Renaming the concrete coordinates neither loses nor invents a support exponent. -/
theorem semanticEquation_support {F : Type*} [Field F] {r : ℕ}
    (Q : CPoly.CMvPolynomial (r + 2) F) :
    (HiddenDerivative.semanticEquation Q).support =
      (CPoly.CMvPolynomial.support Q).image
        (Finsupp.mapDomain (HiddenDerivative.finToJetVariable r)) := by
  classical
  rw [HiddenDerivative.semanticEquation,
    MvPolynomial.support_rename_of_injective (finToJetVariable_injective r),
    fromCMvPolynomial_support]

/-- Every semantic support exponent comes from one of the finite stored nonzero monomials, and
conversely every stored monomial contributes its renamed exponent to semantic support. -/
theorem mem_semanticEquation_support_iff {F : Type*} [Field F] {r : ℕ}
    (Q : CPoly.CMvPolynomial (r + 2) F)
    (exponent : JetVariable r →₀ ℕ) :
    exponent ∈ (HiddenDerivative.semanticEquation Q).support ↔
      ∃ monomial ∈ CPoly.Lawful.monomials Q,
        monomial.toFinsupp.mapDomain (HiddenDerivative.finToJetVariable r) = exponent := by
  classical
  rw [semanticEquation_support]
  simp [CPoly.CMvPolynomial.support, Finset.mem_image]

private theorem renamed_none {r : ℕ} (monomial : CPoly.CMvMonomial (r + 2)) :
    (monomial.toFinsupp.mapDomain (HiddenDerivative.finToJetVariable r)) none =
      monomial.degreeOf 0 := by
  rw [show (none : JetVariable r) = HiddenDerivative.finToJetVariable r 0 by rfl,
    Finsupp.mapDomain_apply (finToJetVariable_injective r)]
  rfl

private theorem renamed_totalJetDegree {r : ℕ} (monomial : CPoly.CMvMonomial (r + 2)) :
    totalJetDegree
        (monomial.toFinsupp.mapDomain (HiddenDerivative.finToJetVariable r)) =
      ∑ i : Fin (r + 2), if i = 0 then 0 else monomial.degreeOf i := by
  have hcoord (j : Fin (r + 1)) :
      (monomial.toFinsupp.mapDomain (HiddenDerivative.finToJetVariable r)) (some j) =
        monomial.degreeOf j.succ := by
    rw [show (some j : JetVariable r) =
      HiddenDerivative.finToJetVariable r j.succ by rfl,
      Finsupp.mapDomain_apply (finToJetVariable_injective r)]
    rfl
  rw [totalJetDegree, Finsupp.degree_eq_sum]
  simp_rw [Finsupp.some_apply, hcoord]
  symm
  rw [Fin.sum_univ_succ]
  simp

namespace SuppliedEquation

/-- Proof-facing statement of exactly the per-stored-monomial bounds checked at runtime. -/
def StoredWithinBounds {F : Type*} [Zero F] {n : ℕ} {opts : Options}
    (equation : SuppliedEquation F opts) : Prop :=
  ∀ monomial ∈ CPoly.Lawful.monomials equation.polynomial,
    monomial.degreeOf 0 ≤ opts.xDegreeFactor * n ∧
      (∑ i : Fin (opts.order + 2),
        if i = 0 then 0 else monomial.degreeOf i) ≤ opts.jetDegree

/-- Direct reflection of the Boolean loop before translating to the semantic polynomial. -/
theorem boundsPass_eq_true_iff_stored {F : Type*} [Zero F] {n : ℕ} {opts : Options}
    (equation : SuppliedEquation F opts) :
    equation.boundsPass (n := n) = true ↔
      CPoly.Lawful.monomials equation.polynomial ≠ [] ∧
        equation.StoredWithinBounds (n := n) := by
  simp [SuppliedEquation.boundsPass, StoredWithinBounds, List.all_eq_true]

/-- The executable sparse check is exactly semantic nonzeroness plus the intended semantic
support bounds.  The proof goes through the finite stored support rather than enumerating `F`. -/
theorem boundsPass_eq_true_iff {F : Type*} [Field F] {n : ℕ}
    {opts : Options} (equation : SuppliedEquation F opts) :
    equation.boundsPass (n := n) = true ↔
      HiddenDerivative.semanticEquation equation.polynomial ≠ 0 ∧
        equation.WithinBounds (n := n) := by
  classical
  rw [boundsPass_eq_true_iff_stored]
  constructor
  · rintro ⟨hnonempty, hstored⟩
    have hsemanticNonempty :
        (HiddenDerivative.semanticEquation equation.polynomial).support.Nonempty := by
      obtain ⟨monomial, hmonomial⟩ :=
        List.exists_mem_of_ne_nil (CPoly.Lawful.monomials equation.polynomial) hnonempty
      refine ⟨monomial.toFinsupp.mapDomain
        (HiddenDerivative.finToJetVariable opts.order), ?_⟩
      exact (mem_semanticEquation_support_iff equation.polynomial _).2
        ⟨monomial, hmonomial, rfl⟩
    have hsemanticNonzero :
        HiddenDerivative.semanticEquation equation.polynomial ≠ 0 := by
      rw [Finset.nonempty_iff_ne_empty, ne_eq, MvPolynomial.support_eq_empty] at hsemanticNonempty
      exact hsemanticNonempty
    refine ⟨hsemanticNonzero, ?_⟩
    dsimp [SuppliedEquation.WithinBounds]
    intro exponent hexponent
    obtain ⟨monomial, hmonomial, rfl⟩ :=
      (mem_semanticEquation_support_iff equation.polynomial exponent).1 hexponent
    simpa only [renamed_none, renamed_totalJetDegree] using hstored monomial hmonomial
  · rintro ⟨hsemanticNonzero, hsemanticBounds⟩
    have hsemanticNonempty :
        (HiddenDerivative.semanticEquation equation.polynomial).support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, ne_eq, MvPolynomial.support_eq_empty]
      exact hsemanticNonzero
    have hstoredNonempty : CPoly.Lawful.monomials equation.polynomial ≠ [] := by
      intro hempty
      obtain ⟨exponent, hexponent⟩ := hsemanticNonempty
      obtain ⟨monomial, hmonomial, _⟩ :=
        (mem_semanticEquation_support_iff equation.polynomial exponent).1 hexponent
      simp [hempty] at hmonomial
    refine ⟨hstoredNonempty, ?_⟩
    intro monomial hmonomial
    have hexponent :
        monomial.toFinsupp.mapDomain (HiddenDerivative.finToJetVariable opts.order) ∈
          (HiddenDerivative.semanticEquation equation.polynomial).support :=
      (mem_semanticEquation_support_iff equation.polynomial _).2
        ⟨monomial, hmonomial, rfl⟩
    have hbounds := hsemanticBounds _ hexponent
    simpa only [renamed_none, renamed_totalJetDegree] using hbounds

end SuppliedEquation

/-! ### Checked public promises without field enumeration -/

/-- Executable arithmetic part of `ValidInput`.  The ring-characteristic equality remains an
explicit theorem hypothesis: computing it is not a reason to enumerate the field. -/
def inputArithmeticPass {F : Type*} {n : ℕ} (input : Input F n) : Bool :=
  decide (1 ≤ input.k) &&
    decide (input.k ≤ n) &&
    decide (input.k ≤ input.agreement) &&
    decide (n ≤ input.characteristic)

theorem inputArithmeticPass_eq_true_iff {F : Type*} {n : ℕ} (input : Input F n) :
    inputArithmeticPass input = true ↔
      1 ≤ input.k ∧ input.k ≤ n ∧ input.k ≤ input.agreement ∧
        n ≤ input.characteristic := by
  simp only [inputArithmeticPass, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem inputArithmeticPass_eq_true_iff_validInput {F : Type*} [Field F] {n : ℕ}
    (input : Input F n) (hcharacteristic : input.characteristic = ringChar F) :
    inputArithmeticPass input = true ↔ ValidInput input := by
  rw [inputArithmeticPass_eq_true_iff]
  simp [ValidInput, hcharacteristic]

/-- Executable structural part of `ValidOptions`.  The finite-field cardinality promise stays
proof-facing so this check never obtains `Fintype.card F` by enumerating field elements. -/
def optionsArithmeticPass (opts : Options) : Bool :=
  decide (0 < opts.multiplicity) &&
    decide (0 < opts.jetDegree) &&
    decide (0 < opts.xDegreeFactor) &&
    match opts.selection with
    | .allSubsets => true
    | .fixedGap numerator denominator =>
        decide (0 < numerator) && decide (numerator < denominator)

theorem optionsArithmeticPass_eq_true_iff (opts : Options) :
    optionsArithmeticPass opts = true ↔
      0 < opts.multiplicity ∧
        0 < opts.jetDegree ∧
        0 < opts.xDegreeFactor ∧
        match opts.selection with
        | .allSubsets => True
        | .fixedGap numerator denominator =>
            0 < numerator ∧ numerator < denominator := by
  cases hselection : opts.selection <;>
    simp only [optionsArithmeticPass, hselection, Bool.and_eq_true, decide_eq_true_eq]
  all_goals tauto

theorem optionsArithmeticPass_eq_true_iff_validOptions {F : Type*} [Field F] [Fintype F]
    {n : ℕ} (input : Input F n) (opts : Options) (hcard : n ≤ Fintype.card F)
    (hprime : Fintype.card F = ringChar F) :
    optionsArithmeticPass opts = true ↔ ValidOptions input opts := by
  rw [optionsArithmeticPass_eq_true_iff]
  have hcardChar : n ≤ ringChar F := hcard.trans_eq hprime
  simp only [ValidOptions, hprime, hcardChar, true_and]
  rfl

/-- Exact hypothesis under which the size of a finite field may be read as its characteristic.
It holds for prime fields such as `ZMod p`; it is intentionally not asserted for extensions. -/
def PrimeFieldSized (F : Type*) [Field F] [Fintype F] : Prop :=
  Fintype.card F = ringChar F

theorem characteristic_eq_card_of_validInput {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (input : Input F n) (hinput : ValidInput input) (hprime : PrimeFieldSized F) :
    input.characteristic = Fintype.card F :=
  hinput.2.2.2.2.trans hprime.symm

/-! ### Dispatch arithmetic -/

/-- Above the structural threshold, `ValidInput` alone supplies every arithmetic guard currently
used by `fallbackRequired`.  This theorem concerns only the numeric dispatch guard; it does not
claim correctness of the unfinished symbolic backend. -/
theorem prescribedGuardsPass_of_validInput_of_large {F : Type*} [Field F] {n : ℕ}
    (input : Input F n) (opts : Options) (hinput : ValidInput input)
    (hlarge : boundedThreshold opts ≤ n) :
    prescribedGuardsPass input.characteristic input.characteristic n input.k opts := by
  rcases hinput with ⟨hkpos, hkn, _hkagreement, hnchar, _hchar⟩
  have hjetThreshold : opts.jetDegree + 1 ≤ boundedThreshold opts := by
    unfold boundedThreshold
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hgridThreshold : coordinateGridGuard opts + 1 ≤ boundedThreshold opts := by
    unfold boundedThreshold
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcenterThreshold : centerLinearGuard opts + 1 ≤ boundedThreshold opts := by
    unfold boundedThreshold
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hjetN : opts.jetDegree < n := by omega
  have hgridN : coordinateGridGuard opts < n := by omega
  have hcenterN : centerLinearGuard opts < n := by omega
  have hnpos : 0 < n := by omega
  have hkminusN : input.k - 1 < n := by omega
  have hkminusChar : input.k - 1 < input.characteristic := hkminusN.trans_le hnchar
  have hjetChar : opts.jetDegree < input.characteristic := hjetN.trans_le hnchar
  have hgridChar : coordinateGridGuard opts < input.characteristic :=
    hgridN.trans_le hnchar
  have hcenterChar : centerLinearGuard opts < input.characteristic :=
    hcenterN.trans_le hnchar
  refine ⟨max_lt hkminusChar hjetChar, hgridChar, ?_⟩
  have hmul :
      centerLinearGuard opts * n < input.characteristic * n :=
    Nat.mul_lt_mul_of_pos_right hcenterChar hnpos
  have hmul' :
      input.characteristic * n ≤ input.characteristic * input.characteristic :=
    Nat.mul_le_mul_left input.characteristic hnchar
  simpa [pow_two] using hmul.trans_le hmul'

/-- If the structural threshold and order test both pass, the current fallback predicate is false.
This audits the arithmetic without changing the runtime branch order. -/
theorem not_fallbackRequired_of_validInput_of_large {F : Type*} [Field F] [Fintype F]
    {n : ℕ} (input : Input F n) (opts : Options) (hinput : ValidInput input)
    (hlarge : boundedThreshold opts ≤ n) (horder : opts.order < input.k) :
    ¬ fallbackRequired F input opts := by
  unfold fallbackRequired
  simp only [not_or]
  refine ⟨not_lt_of_ge hlarge, not_le_of_gt horder, ?_⟩
  intro hnot
  exact hnot (prescribedGuardsPass_of_validInput_of_large input opts hinput hlarge)

/-! ### Checked construction -/

/-- A valid finite support certificate produces an equation accepted by the executable equation
check.  No field-cardinality hypothesis is needed here: `SupportCertificate.Valid` already checks
the actual finite matrix row margin, while `construct_explains` supplies semantic nonzeroness and
support bounds from the executed kernel construction. -/
theorem construct_boundsPass {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (input : Input F n) (opts : Options) (certificate : SupportCertificate)
    (hinput : ValidInput input) (hvalid : certificate.Valid input opts) :
    ∃ equation, construct input opts certificate = .ok equation ∧
      equation.boundsPass (n := n) = true := by
  obtain ⟨equation, hconstruct, hexplains⟩ :=
    construct_explains input opts certificate hinput hvalid
  refine ⟨equation, hconstruct, ?_⟩
  exact (SuppliedEquation.boundsPass_eq_true_iff equation).2
    ⟨hexplains.2.1, hexplains.1⟩

end ReedSolomon.ListDecoding.HiddenDerivativeDecoder
