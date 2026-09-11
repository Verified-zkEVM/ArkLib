/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.FactorTower

/-!
# Euclidean invariance of the D5 factor tower

This file proves that every rooted terminal branch of `factorTower` carries the ordinary
field-polynomial gcd of the initial specialized pair, up to multiplication by a unit.  The proof
handles the zero-divisor and zero-remainder leaves explicitly.  On a recursive unit branch, it
uses the exact specialization of the computed remainder and the fact that the normalized divisor
differs from the original specialized divisor by an invertible scalar.

The result is semantic over every field extension.  It does not materialize a quotient-ring gcd,
agreement witnesses, or a complete list decoder.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance : DecidableEq F := instDecidableEqOfLawfulBEq
local instance : DecidableEq (CPolynomial F) := instDecidableEqOfLawfulBEq

/-- The Euclidean gcd of two polynomials over a field.  Decidable equality is chosen classically
inside the definition, so semantic statements over an arbitrary field extension do not carry an
irrelevant computational typeclass hypothesis. -/
noncomputable def fieldGCD {K : Type*} [Field K] (a b : K[X]) : K[X] := by
  exact @EuclideanDomain.gcd K[X] inferInstance (Classical.decEq K[X]) a b

/-- The field gcd of a polynomial and zero is the polynomial itself. -/
@[simp] theorem fieldGCD_zero_right {K : Type*} [Field K] (a : K[X]) :
    fieldGCD a 0 = a := by
  exact @EuclideanDomain.gcd_zero_right K[X] inferInstance (Classical.decEq K[X]) a

/-- Replacing the first argument by an associate replaces the field gcd by an associate. -/
theorem fieldGCD_associated_left {K : Type*} [Field K]
    {a a' b : K[X]} (h : Associated a a') :
    Associated (fieldGCD a b) (fieldGCD a' b) := by
  unfold fieldGCD
  apply associated_of_dvd_dvd
  · apply @EuclideanDomain.dvd_gcd K[X] inferInstance (Classical.decEq K[X])
    · exact (@EuclideanDomain.gcd_dvd_left K[X] inferInstance
        (Classical.decEq K[X]) a b).trans h.dvd
    · exact @EuclideanDomain.gcd_dvd_right K[X] inferInstance
        (Classical.decEq K[X]) a b
  · apply @EuclideanDomain.dvd_gcd K[X] inferInstance (Classical.decEq K[X])
    · exact (@EuclideanDomain.gcd_dvd_left K[X] inferInstance
        (Classical.decEq K[X]) a' b).trans h.symm.dvd
    · exact @EuclideanDomain.gcd_dvd_right K[X] inferInstance
        (Classical.decEq K[X]) a' b

/-- One ordinary Euclidean remainder step preserves the field gcd up to association. -/
theorem fieldGCD_mod_step {K : Type*} [Field K] (a b : K[X]) :
    Associated (fieldGCD b (a % b)) (fieldGCD a b) := by
  unfold fieldGCD
  apply associated_of_dvd_dvd
  · apply @EuclideanDomain.dvd_gcd K[X] inferInstance (Classical.decEq K[X])
    · exact (EuclideanDomain.dvd_mod_iff
          (@EuclideanDomain.gcd_dvd_left K[X] inferInstance (Classical.decEq K[X])
            b (a % b))).1
        (@EuclideanDomain.gcd_dvd_right K[X] inferInstance (Classical.decEq K[X])
          b (a % b))
    · exact @EuclideanDomain.gcd_dvd_left K[X] inferInstance (Classical.decEq K[X]) _ _
  · apply @EuclideanDomain.dvd_gcd K[X] inferInstance (Classical.decEq K[X])
    · exact @EuclideanDomain.gcd_dvd_right K[X] inferInstance (Classical.decEq K[X]) _ _
    · exact (EuclideanDomain.dvd_mod_iff
          (@EuclideanDomain.gcd_dvd_right K[X] inferInstance (Classical.decEq K[X]) a b)).2
        (@EuclideanDomain.gcd_dvd_left K[X] inferInstance (Classical.decEq K[X]) a b)

/-- At a root routed through a unit-leading branch, the recursive normalized pair has a field gcd
associated to that of the parent pair.  No boundedness or reduction hypothesis on the input
quotient representatives is required. -/
theorem unitBranch_fieldGCD_associated {K : Type*} [Field K]
    (phi : F →+* K) (x : K) (state : TowerState (F := F))
    (modulus leading inverse : CPolynomial F) (lower : List (CPolynomial F))
    (hbranch : (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) ∈
      splitLeading state.divisor.coefficients state.modulus)
    (hroot : modulus.toPoly.eval₂ phi x = 0) :
    Associated
      (fieldGCD
        ((nextUnitPair modulus inverse leading lower state.dividend).dividend.specialize phi x)
        ((nextUnitPair modulus inverse leading lower state.dividend).divisor.specialize phi x))
      (fieldGCD (state.dividend.specialize phi x) (state.divisor.specialize phi x)) := by
  let branch : LeadingBranch (F := F) :=
    ⟨modulus, leading :: lower, some inverse⟩
  have hfollow := (splitLeading_branch_root state.divisor.coefficients
    state.modulus_ne_zero state.modulus_squarefree phi x branch hbranch hroot).2
  obtain ⟨dropped, hcoefficients, hdropped, hinverse⟩ := hfollow
  change state.divisor.coefficients = dropped ++ leading :: lower at hcoefficients
  change leading.toPoly.eval₂ phi x * inverse.toPoly.eval₂ phi x = 1 at hinverse
  have hinverseNe : inverse.toPoly.eval₂ phi x ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hinverse
    exact zero_ne_one hinverse
  have hchildMonic := (splitLeading_child_invariants state branch hbranch).2.1
  have hnextDividend :
      (nextUnitPair modulus inverse leading lower state.dividend).dividend.specialize phi x =
        state.divisor.specialize phi x * C (inverse.toPoly.eval₂ phi x) := by
    rw [FiberPolynomial.specialize, nextUnitPair_dividend_toCPolynomial,
      specialize_normalizedDivisor phi x hchildMonic hroot leading inverse lower hinverse]
    rw [FiberPolynomial.specialize, FiberPolynomial.toCPolynomial, hcoefficients]
    exact congrArg (fun p => p * C (inverse.toPoly.eval₂ phi x))
      (specialize_ofDescending_eq_of_prefix_zero phi x dropped (leading :: lower) hdropped).symm
  have hnextDivisor :
      (nextUnitPair modulus inverse leading lower state.dividend).divisor.specialize phi x =
        state.dividend.specialize phi x % state.divisor.specialize phi x := by
    rw [FiberPolynomial.specialize, nextUnitPair_divisor_toCPolynomial]
    exact specialize_unitBranch_remainder_eq_mod phi x state.modulus_ne_zero
      state.modulus_monic state.modulus_squarefree state.dividend state.divisor
      modulus leading inverse lower hbranch hroot
  rw [hnextDividend, hnextDivisor]
  exact (fieldGCD_associated_left
    (associated_mul_unit_left _ _
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hinverseNe)))).trans
    (fieldGCD_mod_step _ _)

/-- Every rooted terminal factor carries, up to a unit, the field gcd of the initial specialized
dividend and divisor.  In particular, the explicit zero-divisor leaf returns the dividend, and
the explicit zero-remainder leaf returns the normalized divisor reached by the final step. -/
theorem factorTower_terminal_fieldGCD_associated (state : TowerState (F := F))
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (terminal : TerminalGCDBranch (F := F))
    (hterminal : terminal ∈ factorTower state)
    (hroot : terminal.modulus.toPoly.eval₂ phi x = 0) :
    Associated (terminal.gcdPolynomial.specialize phi x)
      (fieldGCD (state.dividend.specialize phi x) (state.divisor.specialize phi x)) := by
  induction state using factorTower.induct with
  | case1 state ih =>
      rw [factorTower.eq_def] at hterminal
      simp only [List.mem_flatMap] at hterminal
      obtain ⟨attached, _, hterminal⟩ := hterminal
      rcases attached with ⟨⟨modulus, coefficients, inverseOption⟩, hbranch⟩
      have hready := splitLeading_ready state.divisor.coefficients state.modulus
        (⟨modulus, coefficients, inverseOption⟩ : LeadingBranch (F := F)) hbranch
      cases coefficients with
      | nil =>
          cases inverseOption with
          | none =>
              simp only [List.mem_singleton] at hterminal
              subst terminal
              have hdivisorZero := zeroBranch_specialize_divisor_eq_zero phi x
                state.modulus_ne_zero state.modulus_squarefree state.divisor modulus
                hbranch hroot
              rw [hdivisorZero, fieldGCD_zero_right]
          | some inverse => simp [LeadingBranch.Ready] at hready
      | cons leading lower =>
          cases inverseOption with
          | none => simp [LeadingBranch.Ready] at hready
          | some inverse =>
              simp only at hterminal
              let attached : {branch // branch ∈
                  splitLeading state.divisor.coefficients state.modulus} :=
                ⟨⟨modulus, leading :: lower, some inverse⟩, hbranch⟩
              let next := nextUnitPair modulus inverse leading lower state.dividend
              by_cases hzero : next.divisor.toCPolynomial = 0
              · have hterminalEq : terminal =
                    (⟨modulus, next.dividend, .zeroRemainder⟩ :
                      TerminalGCDBranch (F := F)) := by
                  simpa [next, hzero] using hterminal
                subst terminal
                have hnextDivisorZero : next.divisor.specialize phi x = 0 := by
                  rw [FiberPolynomial.specialize, hzero]
                  simp [specializeFiberCPolynomial, CPolynomial.toPoly_zero]
                have hstep := unitBranch_fieldGCD_associated phi x state modulus leading inverse
                  lower hbranch hroot
                change Associated
                  (fieldGCD (next.dividend.specialize phi x) (next.divisor.specialize phi x))
                  (fieldGCD (state.dividend.specialize phi x)
                    (state.divisor.specialize phi x)) at hstep
                rw [hnextDivisorZero, fieldGCD_zero_right] at hstep
                simpa using hstep
              · have hzero' : reduceFiberCoefficients modulus
                    (state.dividend.toCPolynomial.modByMonic
                      (normalizedDivisor modulus inverse (leading :: lower))) ≠ 0 := by
                  simpa only [next, nextUnitPair_divisor_toCPolynomial] using hzero
                have hinvariants := splitLeading_child_invariants state
                  (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) hbranch
                let child : TowerState (F := F) :=
                  { modulus := modulus
                    modulus_ne_zero := hinvariants.1
                    modulus_monic := hinvariants.2.1
                    modulus_squarefree := hinvariants.2.2
                    dividend := next.dividend
                    divisor := next.divisor }
                have hterminalChild : terminal ∈ factorTower child := by
                  simpa [child, hzero'] using hterminal
                have hchildRoot : modulus.toPoly.eval₂ phi x = 0 :=
                  factorTower_root_sound child phi x terminal hterminalChild hroot
                have hterminalGCD := ih attached leading lower inverse rfl rfl hzero
                  hterminalChild
                have hstep := unitBranch_fieldGCD_associated phi x state modulus leading inverse
                  lower hbranch hchildRoot
                exact hterminalGCD.trans hstep

end ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5
