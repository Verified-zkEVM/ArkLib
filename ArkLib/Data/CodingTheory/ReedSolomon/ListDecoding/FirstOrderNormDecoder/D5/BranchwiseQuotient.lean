/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.CoefficientCRT

/-!
# Branchwise monic quotients for the D5 factor tower

Terminal gcd degrees can vary between base factors.  Consequently a single CRT reconstruction
need not be monic over the unsplit base algebra.  This file keeps the terminal factors separate:
on each factor the tower's terminal gcd is monic, so ordinary monic division is executable.

The resulting quotient specializes to the exact field-polynomial quotient at every geometric
root of its factor.  The terminal factors retain the full base-degree budget, while quotient
fiber degree never exceeds the initial dividend degree.  No exceptional-fiber branch or runtime
claim is introduced here.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance branchwiseQuotientDecidableEqF : DecidableEq F :=
  instDecidableEqOfLawfulBEq
local instance branchwiseQuotientDecidableEqCPolynomial : DecidableEq (CPolynomial F) :=
  instDecidableEqOfLawfulBEq

/-- If the initial dividend is monic, every terminal gcd representative is monic over its
terminal base factor. -/
theorem factorTower_terminal_gcd_monic (state : TowerState (F := F))
    (hdividend : state.dividend.toCPolynomial.monic)
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state) :
    terminal.gcdPolynomial.toCPolynomial.monic := by
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
              rcases hterminal with rfl
              exact hdividend
          | some inverse => simp [LeadingBranch.Ready] at hready
      | cons leading lower =>
          cases inverseOption with
          | none => simp [LeadingBranch.Ready] at hready
          | some inverse =>
              let attached : {branch // branch ∈
                  splitLeading state.divisor.coefficients state.modulus} :=
                ⟨⟨modulus, leading :: lower, some inverse⟩, hbranch⟩
              let next := nextUnitPair modulus inverse leading lower state.dividend
              have hnextDividend : next.dividend.toCPolynomial.monic := by
                rw [nextUnitPair_dividend_toCPolynomial]
                exact (CPolynomial.monic_toPoly_iff _).mpr
                  (normalizedDivisor_monic modulus inverse leading lower)
              by_cases hzero : next.divisor.toCPolynomial = 0
              · have hterminalEq : terminal =
                    (⟨modulus, next.dividend, .zeroRemainder⟩ :
                      TerminalGCDBranch (F := F)) := by
                  simpa [next, hzero] using hterminal
                rw [hterminalEq]
                exact hnextDividend
              · have hzero' : reduceFiberCoefficients modulus
                    (state.dividend.toCPolynomial.modByMonic
                      (normalizedDivisor modulus inverse (leading :: lower))) ≠ 0 := by
                  simpa only [next, nextUnitPair_divisor_toCPolynomial] using hzero
                have hinvariants := splitLeading_child_invariants state
                  (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) hbranch
                have hterminalChild : terminal ∈ factorTower
                    { modulus := modulus
                      modulus_ne_zero := hinvariants.1
                      modulus_monic := hinvariants.2.1
                      modulus_squarefree := hinvariants.2.2
                      dividend := next.dividend
                      divisor := next.divisor } := by
                  simpa [hzero'] using hterminal
                exact ih attached leading lower inverse rfl rfl hzero
                  hnextDividend hterminalChild

/-- Specialization commutes with executable division by a globally monic fiber polynomial. -/
theorem specializeFiberCPolynomial_divByMonic
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (p q : CPolynomial (CPolynomial F)) (hq : q.monic) :
    specializeFiberCPolynomial (p.divByMonic q) phi x =
      specializeFiberCPolynomial p phi x /ₘ specializeFiberCPolynomial q phi x := by
  rw [specializeFiberCPolynomial, specializeFiberCPolynomial,
    specializeFiberCPolynomial,
    CPolynomial.divByMonic_toPoly_eq_divByMonic p q hq]
  exact Polynomial.map_divByMonic _ ((CPolynomial.monic_toPoly_iff q).mp hq)

/-- Executable quotient of the initial dividend by one terminal gcd, canonically reduced modulo
that terminal base factor. -/
def terminalQuotientPolynomial (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F)) : CPolynomial (CPolynomial F) :=
  reduceFiberCoefficients terminal.modulus
    (state.dividend.toCPolynomial.divByMonic terminal.gcdPolynomial.toCPolynomial)

/-- One terminal factor together with its branch-local quotient. -/
structure TerminalQuotientBranch where
  terminal : TerminalGCDBranch (F := F)
  quotient : FiberPolynomial (F := F)

/-- Package the executable branch-local quotient in canonical descending-coefficient form. -/
def makeTerminalQuotientBranch (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F)) : TerminalQuotientBranch (F := F) :=
  ⟨terminal, FiberPolynomial.ofCPolynomial (terminalQuotientPolynomial state terminal)⟩

/-- Divide by the terminal gcd independently on every returned base factor. -/
def quotientTower (state : TowerState (F := F)) : List (TerminalQuotientBranch (F := F)) :=
  (factorTower state).map (makeTerminalQuotientBranch state)

/-- The empty factor tower has an explicitly empty quotient output. -/
@[simp]
theorem quotientTower_eq_nil_of_factorTower_eq_nil (state : TowerState (F := F))
    (h : factorTower state = []) : quotientTower state = [] := by
  simp [quotientTower, h]

/-- Every terminal factor occurs exactly once in the branchwise quotient list. -/
theorem makeTerminalQuotientBranch_mem_quotientTower (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state) :
    makeTerminalQuotientBranch state terminal ∈ quotientTower state := by
  exact List.mem_map_of_mem hterminal

/-- A branch-local quotient specializes to ordinary monic division by the terminal gcd. -/
theorem terminalQuotientPolynomial_specialize
    (state : TowerState (F := F))
    (hdividend : state.dividend.toCPolynomial.monic)
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : terminal.modulus.toPoly.eval₂ phi x = 0) :
    specializeFiberCPolynomial (terminalQuotientPolynomial state terminal) phi x =
      state.dividend.specialize phi x /ₘ terminal.gcdPolynomial.specialize phi x := by
  have hterminalMonic := factorTower_terminal_gcd_monic state hdividend terminal hterminal
  rw [terminalQuotientPolynomial,
    specialize_reduceFiberCoefficients phi x
      (factorTower_terminal_invariants state terminal hterminal).2.1 hroot,
    specializeFiberCPolynomial_divByMonic phi x _ _ hterminalMonic]
  rfl

/-- The packaged quotient has the same specialization theorem as its nested polynomial payload. -/
theorem makeTerminalQuotientBranch_specialize
    (state : TowerState (F := F))
    (hdividend : state.dividend.toCPolynomial.monic)
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : terminal.modulus.toPoly.eval₂ phi x = 0) :
    (makeTerminalQuotientBranch state terminal).quotient.specialize phi x =
      state.dividend.specialize phi x /ₘ terminal.gcdPolynomial.specialize phi x := by
  rw [makeTerminalQuotientBranch, FiberPolynomial.specialize_ofCPolynomial]
  exact terminalQuotientPolynomial_specialize state hdividend terminal hterminal phi x hroot

/-- On every rooted terminal factor, terminal gcd times branch quotient is exactly the initial
specialized dividend. -/
theorem terminal_gcd_mul_terminalQuotient_specialize
    (state : TowerState (F := F))
    (hdividend : state.dividend.toCPolynomial.monic)
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : terminal.modulus.toPoly.eval₂ phi x = 0) :
    terminal.gcdPolynomial.specialize phi x *
        (makeTerminalQuotientBranch state terminal).quotient.specialize phi x =
      state.dividend.specialize phi x := by
  have hterminalMonic : (terminal.gcdPolynomial.specialize phi x).Monic :=
    ((CPolynomial.monic_toPoly_iff _).mp
      (factorTower_terminal_gcd_monic state hdividend terminal hterminal)).map _
  have hassociated :=
    factorTower_terminal_fieldGCD_associated state phi x terminal hterminal hroot
  have hgcdDvd : fieldGCD (state.dividend.specialize phi x)
      (state.divisor.specialize phi x) ∣ state.dividend.specialize phi x :=
    @EuclideanDomain.gcd_dvd_left K[X] inferInstance (Classical.decEq K[X]) _ _
  have hterminalDvd : terminal.gcdPolynomial.specialize phi x ∣
      state.dividend.specialize phi x :=
    hassociated.dvd_iff_dvd_left.mpr hgcdDvd
  have hmod : state.dividend.specialize phi x %ₘ
      terminal.gcdPolynomial.specialize phi x = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hterminalMonic).mpr hterminalDvd
  rw [makeTerminalQuotientBranch_specialize state hdividend terminal hterminal phi x hroot]
  have hdivision := Polynomial.modByMonic_add_div
    (state.dividend.specialize phi x) (terminal.gcdPolynomial.specialize phi x)
  rw [hmod, zero_add] at hdivision
  exact hdivision

/-- Canonical reduction and monic division do not increase branch quotient fiber degree. -/
theorem terminalQuotientPolynomial_natDegree_le
    (state : TowerState (F := F))
    (hdividend : state.dividend.toCPolynomial.monic)
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state) :
    (terminalQuotientPolynomial state terminal).natDegree ≤
      state.dividend.toCPolynomial.natDegree := by
  let raw := state.dividend.toCPolynomial.divByMonic terminal.gcdPolynomial.toCPolynomial
  have hterminalMonic := factorTower_terminal_gcd_monic state hdividend terminal hterminal
  have hrawDegree : raw.natDegree ≤ state.dividend.toCPolynomial.natDegree := by
    rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly,
      CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ hterminalMonic]
    exact Polynomial.natDegree_le_natDegree (Polynomial.degree_divByMonic_le _ _)
  by_cases hquotient : terminalQuotientPolynomial state terminal = 0
  · rw [hquotient]
    rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero, Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · exact (natDegree_reduceFiberCoefficients_le terminal.modulus raw hquotient).trans hrawDegree

/-- The sum of base degree times branch quotient fiber degree stays within the initial
base-by-fiber degree budget. -/
theorem terminalQuotient_weighted_sum_le
    (state : TowerState (F := F))
    (hdividend : state.dividend.toCPolynomial.monic) :
    ((factorTower state).map fun terminal =>
      terminal.modulus.natDegree * (terminalQuotientPolynomial state terminal).natDegree).sum ≤
        state.modulus.natDegree * state.dividend.toCPolynomial.natDegree := by
  have hpointwise : ∀ terminal ∈ factorTower state,
      terminal.modulus.natDegree * (terminalQuotientPolynomial state terminal).natDegree ≤
        terminal.modulus.natDegree * state.dividend.toCPolynomial.natDegree := by
    intro terminal hterminal
    exact Nat.mul_le_mul_left terminal.modulus.natDegree
      (terminalQuotientPolynomial_natDegree_le state hdividend terminal hterminal)
  have hsum :
      ((factorTower state).map fun terminal =>
        terminal.modulus.natDegree * (terminalQuotientPolynomial state terminal).natDegree).sum ≤
      ((factorTower state).map fun terminal =>
        terminal.modulus.natDegree * state.dividend.toCPolynomial.natDegree).sum := by
    exact List.sum_le_sum hpointwise
  calc
    _ ≤ ((factorTower state).map fun terminal =>
        terminal.modulus.natDegree * state.dividend.toCPolynomial.natDegree).sum := hsum
    _ = ((factorTower state).map fun terminal => terminal.modulus.natDegree).sum *
        state.dividend.toCPolynomial.natDegree := by
      induction factorTower state with
      | nil => simp
      | cons terminal terminals ih => simp [ih, Nat.add_mul]
    _ = state.modulus.natDegree * state.dividend.toCPolynomial.natDegree := by
      rw [factorTower_natDegree_sum]

end ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5
