/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.CanonicalFiber

/-!
# Well-founded D5 factor tower

This file iterates the executable D5 pair update over the squarefree base-factor tree.  Each state
carries a nonzero monic squarefree base modulus.  Zero divisors and zero remainders become explicit
terminal branches; nonzero remainders recurse with strictly smaller outer fiber width.

The construction is only the D5 Euclidean factor tower.  It does not yet materialize the decoder's
agreement witnesses or claim complete list-decoder coverage.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance : DecidableEq F := instDecidableEqOfLawfulBEq
local instance : DecidableEq (CPolynomial F) := instDecidableEqOfLawfulBEq

/-- A recursion state whose base modulus retains the D5 factorization invariants. -/
structure TowerState where
  modulus : CPolynomial F
  modulus_ne_zero : modulus ≠ 0
  modulus_monic : modulus.monic
  modulus_squarefree : Squarefree modulus.toPoly
  dividend : FiberPolynomial (F := F)
  divisor : FiberPolynomial (F := F)

/-- Why a factor-tower branch terminates. -/
inductive TerminalReason
  | zeroDivisor
  | zeroRemainder

/-- One terminal base factor and the explicit final Euclidean polynomial on that factor. -/
structure TerminalGCDBranch where
  modulus : CPolynomial F
  gcdPolynomial : FiberPolynomial (F := F)
  reason : TerminalReason

/-- A normalized divisor has exactly the fiber degree dictated by its retained lower list. -/
theorem normalizedDivisor_natDegree (modulus inverse leading : CPolynomial F)
    (lower : List (CPolynomial F)) :
    (normalizedDivisor modulus inverse (leading :: lower)).natDegree = lower.length := by
  let normalized := normalizedDivisor modulus inverse (leading :: lower)
  have hmonic : normalized.toPoly.Monic :=
    normalizedDivisor_monic modulus inverse leading lower
  have hdegree : normalized.toPoly.degree = (lower.length : WithBot ℕ) := by
    dsimp only [normalized]
    rw [normalizedDivisor, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
      CPolynomial.X_toPoly]
    rw [Polynomial.degree_add_eq_left_of_degree_lt
      (by
        rw [Polynomial.degree_X_pow]
        simpa only [List.length_map] using
          degree_ofDescending_lt (lower.map fun coefficient =>
            (coefficient * inverse).modByMonic modulus))]
    simp
  change normalized.natDegree = lower.length
  rw [CPolynomial.natDegree_toPoly]
  rw [Polynomial.degree_eq_natDegree hmonic.ne_zero] at hdegree
  exact WithBot.coe_eq_coe.mp hdegree

/-- A nonzero next divisor has strictly smaller canonical coefficient width than the divisor at
the parent state.  This is the executable well-founded recursion measure. -/
theorem nextUnitPair_divisor_coefficients_length_lt
    {g : CPolynomial F} (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly)
    (dividend divisor : FiberPolynomial (F := F))
    (modulus leading inverse : CPolynomial F) (lower : List (CPolynomial F))
    (hbranch : (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) ∈
      splitLeading divisor.coefficients g)
    (hremainder :
      (nextUnitPair modulus inverse leading lower dividend).divisor.toCPolynomial ≠ 0) :
    (nextUnitPair modulus inverse leading lower dividend).divisor.coefficients.length <
      divisor.coefficients.length := by
  have hdegree := unitBranch_pairUpdate_measure_decreases hg hgmonic hgfree dividend divisor
    modulus leading inverse lower hbranch
    (by simpa only [nextUnitPair_divisor_toCPolynomial] using hremainder)
  rw [nextUnitPair_dividend_toCPolynomial, normalizedDivisor_natDegree] at hdegree
  have hcanonical : (nextUnitPair modulus inverse leading lower dividend).divisor =
      FiberPolynomial.ofCPolynomial
        (nextUnitPair modulus inverse leading lower dividend).divisor.toCPolynomial := by
    simp [nextUnitPair]
  rw [hcanonical,
    FiberPolynomial.coefficients_length_ofCPolynomial_of_ne_zero hremainder]
  have hretained := splitLeading_coefficients_length_le divisor.coefficients g
    (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) hbranch
  simp only [List.length_cons] at hretained
  omega

/-- Child invariants inherited from one returned leading-coefficient branch. -/
theorem splitLeading_child_invariants (state : TowerState (F := F))
    (branch : LeadingBranch (F := F))
    (hbranch : branch ∈ splitLeading state.divisor.coefficients state.modulus) :
    branch.modulus ≠ 0 ∧ branch.modulus.monic ∧ Squarefree branch.modulus.toPoly := by
  obtain ⟨hmonic, hfree⟩ := splitLeading_monic_squarefree state.divisor.coefficients
    state.modulus_ne_zero state.modulus_monic state.modulus_squarefree branch hbranch
  exact ⟨(CPolynomial.toPoly_eq_zero_iff branch.modulus).not.mp
    ((CPolynomial.monic_toPoly_iff branch.modulus).mp hmonic).ne_zero, hmonic, hfree⟩

/-- Recursively compute all terminal Euclidean branches in the squarefree base-factor tower. -/
def factorTower (state : TowerState (F := F)) : List (TerminalGCDBranch (F := F)) :=
  (splitLeading state.divisor.coefficients state.modulus).attach.flatMap fun attached =>
    let branch := attached.1
    match _hcoefficients : branch.coefficients, _hinverse : branch.leadingInverse with
    | [], none => [⟨branch.modulus, state.dividend, .zeroDivisor⟩]
    | leading :: lower, some inverse =>
        let next := nextUnitPair branch.modulus inverse leading lower state.dividend
        if _hzero : next.divisor.toCPolynomial = 0 then
          [⟨branch.modulus, next.dividend, .zeroRemainder⟩]
        else
          let invariants := splitLeading_child_invariants state branch attached.2
          factorTower
            { modulus := branch.modulus
              modulus_ne_zero := invariants.1
              modulus_monic := invariants.2.1
              modulus_squarefree := invariants.2.2
              dividend := next.dividend
              divisor := next.divisor }
    | _, _ => []
termination_by state.divisor.coefficients.length
decreasing_by
  have hbranch :
      (⟨branch.modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) ∈
        splitLeading state.divisor.coefficients state.modulus := by
    rw [← _hcoefficients, ← _hinverse]
    change branch ∈ splitLeading state.divisor.coefficients state.modulus
    exact attached.2
  exact nextUnitPair_divisor_coefficients_length_lt state.modulus_ne_zero state.modulus_monic
    state.modulus_squarefree state.dividend state.divisor branch.modulus leading inverse lower
    hbranch _hzero

/-- The terminal factors retain the complete base-degree budget of the initial state. -/
theorem factorTower_natDegree_sum (state : TowerState (F := F)) :
    ((factorTower state).map fun branch => branch.modulus.natDegree).sum =
      state.modulus.natDegree := by
  induction state using factorTower.induct with
  | case1 state ih =>
      rw [factorTower.eq_def]
      let branches := (splitLeading state.divisor.coefficients state.modulus).attach
      let output : (attached : {branch // branch ∈
          splitLeading state.divisor.coefficients state.modulus}) →
          List (TerminalGCDBranch (F := F)) := fun attached =>
        let branch := attached.1
        match hcoefficients : branch.coefficients, hinverse : branch.leadingInverse with
        | [], none => [⟨branch.modulus, state.dividend, .zeroDivisor⟩]
        | leading :: lower, some inverse =>
            let next := nextUnitPair branch.modulus inverse leading lower state.dividend
            if hzero : next.divisor.toCPolynomial = 0 then
              [⟨branch.modulus, next.dividend, .zeroRemainder⟩]
            else
              let invariants := splitLeading_child_invariants state branch attached.2
              factorTower
                { modulus := branch.modulus
                  modulus_ne_zero := invariants.1
                  modulus_monic := invariants.2.1
                  modulus_squarefree := invariants.2.2
                  dividend := next.dividend
                  divisor := next.divisor }
        | _, _ => []
      have houtput (attached : {branch // branch ∈
          splitLeading state.divisor.coefficients state.modulus}) :
          ((output attached).map fun branch => branch.modulus.natDegree).sum =
            attached.1.modulus.natDegree := by
        rcases attached with ⟨⟨modulus, coefficients, inverseOption⟩, hbranch⟩
        have hready := splitLeading_ready state.divisor.coefficients state.modulus
          (⟨modulus, coefficients, inverseOption⟩ : LeadingBranch (F := F)) hbranch
        cases coefficients with
        | nil =>
            cases inverseOption with
            | none => simp [output]
            | some inverse => simp [LeadingBranch.Ready] at hready
        | cons leading lower =>
            cases inverseOption with
            | none => simp [LeadingBranch.Ready] at hready
            | some inverse =>
                let attached : {branch // branch ∈
                    splitLeading state.divisor.coefficients state.modulus} :=
                  ⟨⟨modulus, leading :: lower, some inverse⟩, hbranch⟩
                let next := nextUnitPair modulus inverse leading lower state.dividend
                by_cases hzero : next.divisor.toCPolynomial = 0
                · have hzero' : reduceFiberCoefficients modulus
                      (state.dividend.toCPolynomial.modByMonic
                        (normalizedDivisor modulus inverse (leading :: lower))) = 0 := by
                    simpa only [next, nextUnitPair_divisor_toCPolynomial] using hzero
                  simp [output, hzero']
                · have hzero' : reduceFiberCoefficients modulus
                      (state.dividend.toCPolynomial.modByMonic
                        (normalizedDivisor modulus inverse (leading :: lower))) ≠ 0 := by
                    simpa only [next, nextUnitPair_divisor_toCPolynomial] using hzero
                  simpa [output, attached, next, hzero'] using
                    ih attached leading lower inverse rfl rfl hzero
      have hflat :
          (((branches.flatMap output).map fun branch => branch.modulus.natDegree).sum) =
            ((branches.map fun attached => attached.1.modulus.natDegree).sum) := by
        induction branches with
        | nil => simp
        | cons attached branches ihbranches =>
            simp only [List.flatMap_cons, List.map_append, List.sum_append,
              List.map_cons, List.sum_cons, ihbranches, houtput attached]
      change ((branches.flatMap output).map fun branch => branch.modulus.natDegree).sum = _
      rw [hflat]
      simpa [branches] using splitLeading_natDegree_sum state.divisor.coefficients
        state.modulus_ne_zero state.modulus_squarefree

/-- The product of all terminal factors is exactly the initial base modulus. -/
theorem factorTower_modulus_product (state : TowerState (F := F)) :
    ((factorTower state).map TerminalGCDBranch.modulus).prod = state.modulus := by
  induction state using factorTower.induct with
  | case1 state ih =>
      rw [factorTower.eq_def]
      let branches := (splitLeading state.divisor.coefficients state.modulus).attach
      let output : (attached : {branch // branch ∈
          splitLeading state.divisor.coefficients state.modulus}) →
          List (TerminalGCDBranch (F := F)) := fun attached =>
        let branch := attached.1
        match hcoefficients : branch.coefficients, hinverse : branch.leadingInverse with
        | [], none => [⟨branch.modulus, state.dividend, .zeroDivisor⟩]
        | leading :: lower, some inverse =>
            let next := nextUnitPair branch.modulus inverse leading lower state.dividend
            if hzero : next.divisor.toCPolynomial = 0 then
              [⟨branch.modulus, next.dividend, .zeroRemainder⟩]
            else
              let invariants := splitLeading_child_invariants state branch attached.2
              factorTower
                { modulus := branch.modulus
                  modulus_ne_zero := invariants.1
                  modulus_monic := invariants.2.1
                  modulus_squarefree := invariants.2.2
                  dividend := next.dividend
                  divisor := next.divisor }
        | _, _ => []
      have houtput (attached : {branch // branch ∈
          splitLeading state.divisor.coefficients state.modulus}) :
          ((output attached).map TerminalGCDBranch.modulus).prod = attached.1.modulus := by
        rcases attached with ⟨⟨modulus, coefficients, inverseOption⟩, hbranch⟩
        have hready := splitLeading_ready state.divisor.coefficients state.modulus
          (⟨modulus, coefficients, inverseOption⟩ : LeadingBranch (F := F)) hbranch
        cases coefficients with
        | nil =>
            cases inverseOption with
            | none => simp [output]
            | some inverse => simp [LeadingBranch.Ready] at hready
        | cons leading lower =>
            cases inverseOption with
            | none => simp [LeadingBranch.Ready] at hready
            | some inverse =>
                let attached : {branch // branch ∈
                    splitLeading state.divisor.coefficients state.modulus} :=
                  ⟨⟨modulus, leading :: lower, some inverse⟩, hbranch⟩
                let next := nextUnitPair modulus inverse leading lower state.dividend
                by_cases hzero : next.divisor.toCPolynomial = 0
                · have hzero' : reduceFiberCoefficients modulus
                      (state.dividend.toCPolynomial.modByMonic
                        (normalizedDivisor modulus inverse (leading :: lower))) = 0 := by
                    simpa only [next, nextUnitPair_divisor_toCPolynomial] using hzero
                  simp [output, hzero']
                · have hzero' : reduceFiberCoefficients modulus
                      (state.dividend.toCPolynomial.modByMonic
                        (normalizedDivisor modulus inverse (leading :: lower))) ≠ 0 := by
                    simpa only [next, nextUnitPair_divisor_toCPolynomial] using hzero
                  simpa [output, attached, next, hzero'] using
                    ih attached leading lower inverse rfl rfl hzero
      have hflat :
          (((branches.flatMap output).map TerminalGCDBranch.modulus).prod) =
            ((branches.map fun attached => attached.1.modulus).prod) := by
        induction branches with
        | nil => simp
        | cons attached branches ihbranches =>
            simp only [List.flatMap_cons, List.map_append, List.prod_append,
              List.map_cons, List.prod_cons, ihbranches, houtput attached]
      change ((branches.flatMap output).map TerminalGCDBranch.modulus).prod = _
      rw [hflat]
      simpa [branches] using splitLeading_modulus_product state.divisor.coefficients
        state.modulus_ne_zero state.modulus_squarefree

/-- Every rooted terminal factor is rooted in the initial state modulus. -/
theorem factorTower_root_sound (state : TowerState (F := F))
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (terminal : TerminalGCDBranch (F := F))
    (hterminal : terminal ∈ factorTower state)
    (hroot : terminal.modulus.toPoly.eval₂ phi x = 0) :
    state.modulus.toPoly.eval₂ phi x = 0 := by
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
              exact (splitLeading_branch_root state.divisor.coefficients state.modulus_ne_zero
                state.modulus_squarefree phi x
                (⟨modulus, [], none⟩ : LeadingBranch (F := F)) hbranch hroot).1
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
                rw [hterminalEq] at hroot
                exact (splitLeading_branch_root state.divisor.coefficients
                  state.modulus_ne_zero state.modulus_squarefree phi x
                  (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F))
                  hbranch hroot).1
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
                have hchildRoot := ih attached leading lower inverse rfl rfl hzero
                  hterminalChild
                exact (splitLeading_branch_root state.divisor.coefficients
                  state.modulus_ne_zero state.modulus_squarefree phi x
                  (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F))
                  hbranch hchildRoot).1

/-- Every geometric root of the initial state modulus is routed to a rooted terminal factor. -/
theorem factorTower_root_complete (state : TowerState (F := F))
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : state.modulus.toPoly.eval₂ phi x = 0) :
    ∃ terminal ∈ factorTower state,
      terminal.modulus.toPoly.eval₂ phi x = 0 := by
  induction state using factorTower.induct with
  | case1 state ih =>
      obtain ⟨branch, hbranch, hbranchRoot, _⟩ :=
        (eval₂_splitLeading_root_iff state.divisor.coefficients state.modulus_ne_zero
          state.modulus_squarefree phi x).mp hroot
      let attached : {candidate // candidate ∈
          splitLeading state.divisor.coefficients state.modulus} := ⟨branch, hbranch⟩
      have hready := splitLeading_ready state.divisor.coefficients state.modulus branch hbranch
      rcases branch with ⟨modulus, coefficients, inverseOption⟩
      cases coefficients with
      | nil =>
          cases inverseOption with
          | none =>
              let terminal : TerminalGCDBranch (F := F) :=
                ⟨modulus, state.dividend, .zeroDivisor⟩
              refine ⟨terminal, ?_, hbranchRoot⟩
              rw [factorTower.eq_def]
              apply List.mem_flatMap.mpr
              refine ⟨attached, by simp [attached], ?_⟩
              simp [attached, terminal]
          | some inverse => simp [LeadingBranch.Ready] at hready
      | cons leading lower =>
          cases inverseOption with
          | none => simp [LeadingBranch.Ready] at hready
          | some inverse =>
              let next := nextUnitPair modulus inverse leading lower state.dividend
              by_cases hzero : next.divisor.toCPolynomial = 0
              · let terminal : TerminalGCDBranch (F := F) :=
                  ⟨modulus, next.dividend, .zeroRemainder⟩
                refine ⟨terminal, ?_, hbranchRoot⟩
                rw [factorTower.eq_def]
                apply List.mem_flatMap.mpr
                refine ⟨attached, by simp [attached], ?_⟩
                simp [attached, next, hzero, terminal]
              · obtain ⟨terminal, hterminal, hterminalRoot⟩ :=
                  ih attached leading lower inverse rfl rfl hzero hbranchRoot
                refine ⟨terminal, ?_, hterminalRoot⟩
                rw [factorTower.eq_def]
                apply List.mem_flatMap.mpr
                refine ⟨attached, by simp [attached], ?_⟩
                have hzero' : reduceFiberCoefficients modulus
                    (state.dividend.toCPolynomial.modByMonic
                      (normalizedDivisor modulus inverse (leading :: lower))) ≠ 0 := by
                  simpa only [next, nextUnitPair_divisor_toCPolynomial] using hzero
                simpa [attached, hzero'] using hterminal

/-- Root routing through the tower is exact over every field extension. -/
theorem factorTower_root_iff (state : TowerState (F := F))
    {K : Type*} [Field K] (phi : F →+* K) (x : K) :
    state.modulus.toPoly.eval₂ phi x = 0 ↔
      ∃ terminal ∈ factorTower state,
        terminal.modulus.toPoly.eval₂ phi x = 0 := by
  constructor
  · exact factorTower_root_complete state phi x
  · rintro ⟨terminal, hterminal, hroot⟩
    exact factorTower_root_sound state phi x terminal hterminal hroot

/-- Every terminal factor retains the nonzero, monic, and squarefree base-modulus invariants. -/
theorem factorTower_terminal_invariants (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F))
    (hterminal : terminal ∈ factorTower state) :
    terminal.modulus ≠ 0 ∧ terminal.modulus.monic ∧ Squarefree terminal.modulus.toPoly := by
  induction state using factorTower.induct with
  | case1 state ih =>
      rw [factorTower.eq_def] at hterminal
      simp only [List.mem_flatMap] at hterminal
      obtain ⟨attached, _, hterminal⟩ := hterminal
      rcases attached with ⟨⟨modulus, coefficients, inverseOption⟩, hbranch⟩
      have hready := splitLeading_ready state.divisor.coefficients state.modulus
        (⟨modulus, coefficients, inverseOption⟩ : LeadingBranch (F := F)) hbranch
      have hinvariants := splitLeading_child_invariants state
        (⟨modulus, coefficients, inverseOption⟩ : LeadingBranch (F := F)) hbranch
      cases coefficients with
      | nil =>
          cases inverseOption with
          | none =>
              simp only [List.mem_singleton] at hterminal
              rcases hterminal with rfl
              exact hinvariants
          | some inverse => simp [LeadingBranch.Ready] at hready
      | cons leading lower =>
          cases inverseOption with
          | none => simp [LeadingBranch.Ready] at hready
          | some inverse =>
              let attached : {branch // branch ∈
                  splitLeading state.divisor.coefficients state.modulus} :=
                ⟨⟨modulus, leading :: lower, some inverse⟩, hbranch⟩
              let next := nextUnitPair modulus inverse leading lower state.dividend
              simp only at hterminal
              by_cases hzero : next.divisor.toCPolynomial = 0
              · have hterminalEq : terminal =
                    (⟨modulus, next.dividend, .zeroRemainder⟩ :
                      TerminalGCDBranch (F := F)) := by
                  simpa [next, hzero] using hterminal
                rw [hterminalEq]
                exact hinvariants
              · have hzero' : reduceFiberCoefficients modulus
                    (state.dividend.toCPolynomial.modByMonic
                      (normalizedDivisor modulus inverse (leading :: lower))) ≠ 0 := by
                  simpa only [next, nextUnitPair_divisor_toCPolynomial] using hzero
                have hterminalChild : terminal ∈ factorTower
                    { modulus := modulus
                      modulus_ne_zero := hinvariants.1
                      modulus_monic := hinvariants.2.1
                      modulus_squarefree := hinvariants.2.2
                      dividend := next.dividend
                      divisor := next.divisor } := by
                  simpa [hzero'] using hterminal
                exact ih attached leading lower inverse rfl rfl hzero hterminalChild

end ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5
