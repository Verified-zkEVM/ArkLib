/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.BranchwiseQuotient
public import ArkLib.Data.Polynomial.SquarefreeSupport
import Mathlib.Algebra.CharP.Algebra
import all
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.BranchwiseQuotient

/-!
# Branchwise D5 radicalization

This file applies the D5 factor tower to a bounded fiber polynomial and its derivative in the
fiber variable.  Each terminal factor is divided independently by its monic terminal gcd.  Below
the characteristic, the resulting branch polynomial is squarefree and has exactly the geometric
roots of the input fiber.  The construction keeps every base fiber and introduces no exceptional
solver branch.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance radicalTowerDecidableEqF : DecidableEq F := instDecidableEqOfLawfulBEq
local instance radicalTowerDecidableEqCPolynomial : DecidableEq (CPolynomial F) :=
  instDecidableEqOfLawfulBEq

/-- Differentiate a bounded fiber polynomial in its outer fiber variable. -/
def derivativeFiber (h : FiberPolynomial (F := F)) : FiberPolynomial (F := F) :=
  FiberPolynomial.ofCPolynomial h.toCPolynomial.derivative

/-- Fiber differentiation commutes with every geometric base specialization. -/
theorem derivativeFiber_specialize
    {K : Type*} [Field K] (h : FiberPolynomial (F := F))
    (phi : F →+* K) (x : K) :
    (derivativeFiber h).specialize phi x = (h.specialize phi x).derivative := by
  rw [derivativeFiber, FiberPolynomial.specialize_ofCPolynomial,
    specializeFiberCPolynomial, CPolynomial.derivative_toPoly,
    ← Polynomial.derivative_map]
  rfl

/-- Initial D5 state for removing the fiber derivative gcd over a squarefree base block. -/
def radicalState (g : CPolynomial F) (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly) (h : FiberPolynomial (F := F)) : TowerState (F := F) :=
  { modulus := g
    modulus_ne_zero := hg
    modulus_monic := hgmonic
    modulus_squarefree := hgfree
    dividend := h
    divisor := derivativeFiber h }

@[simp] theorem radicalState_modulus (g : CPolynomial F) (hg : g ≠ 0)
    (hgmonic : g.monic) (hgfree : Squarefree g.toPoly) (h : FiberPolynomial (F := F)) :
    (radicalState g hg hgmonic hgfree h).modulus = g := rfl

@[simp] theorem radicalState_dividend (g : CPolynomial F) (hg : g ≠ 0)
    (hgmonic : g.monic) (hgfree : Squarefree g.toPoly) (h : FiberPolynomial (F := F)) :
    (radicalState g hg hgmonic hgfree h).dividend = h := rfl

/-- Execute derivative-gcd removal independently on every terminal base factor. -/
def radicalTower (g : CPolynomial F) (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly) (h : FiberPolynomial (F := F)) :
    List (TerminalQuotientBranch (F := F)) :=
  let state := radicalState g hg hgmonic hgfree h
  (factorTower state).map fun terminal =>
    ⟨terminal, FiberPolynomial.ofCPolynomial (terminalQuotientPolynomial state terminal)⟩

/-- The radical tower retains exactly the complete terminal base-factor product. -/
theorem radicalTower_modulus_product (g : CPolynomial F) (hg : g ≠ 0)
    (hgmonic : g.monic) (hgfree : Squarefree g.toPoly) (h : FiberPolynomial (F := F)) :
    ((radicalTower g hg hgmonic hgfree h).map fun branch =>
      branch.terminal.modulus).prod = g := by
  rw [radicalTower, List.map_map]
  change ((factorTower (radicalState g hg hgmonic hgfree h)).map
    TerminalGCDBranch.modulus).prod = g
  simpa [radicalState] using
    factorTower_modulus_product (radicalState g hg hgmonic hgfree h)

/-- The radical tower preserves the exact total base degree. -/
theorem radicalTower_natDegree_sum (g : CPolynomial F) (hg : g ≠ 0)
    (hgmonic : g.monic) (hgfree : Squarefree g.toPoly) (h : FiberPolynomial (F := F)) :
    ((radicalTower g hg hgmonic hgfree h).map fun branch =>
      branch.terminal.modulus.natDegree).sum = g.natDegree := by
  rw [radicalTower, List.map_map]
  change ((factorTower (radicalState g hg hgmonic hgfree h)).map fun terminal =>
    terminal.modulus.natDegree).sum = g.natDegree
  simpa [radicalState] using
    factorTower_natDegree_sum (radicalState g hg hgmonic hgfree h)

/-- The radical tower's total base-degree times fiber-degree budget does not exceed that of its
input block. -/
theorem radicalTower_weighted_sum_le (g : CPolynomial F) (hg : g ≠ 0)
    (hgmonic : g.monic) (hgfree : Squarefree g.toPoly) (h : FiberPolynomial (F := F))
    (hhmonic : h.toCPolynomial.monic) :
    ((radicalTower g hg hgmonic hgfree h).map fun branch =>
      branch.terminal.modulus.natDegree * branch.quotient.toCPolynomial.natDegree).sum ≤
        g.natDegree * h.toCPolynomial.natDegree := by
  rw [radicalTower, List.map_map]
  change ((factorTower (radicalState g hg hgmonic hgfree h)).map fun terminal =>
    terminal.modulus.natDegree *
      (FiberPolynomial.toCPolynomial (FiberPolynomial.ofCPolynomial
        (terminalQuotientPolynomial
          (radicalState g hg hgmonic hgfree h) terminal))).natDegree).sum ≤ _
  simp only [FiberPolynomial.toCPolynomial_ofCPolynomial]
  simpa [radicalState] using
    terminalQuotient_weighted_sum_le (radicalState g hg hgmonic hgfree h) hhmonic

/-- Root multiplicity is below the characteristic whenever polynomial degree is. -/
theorem rootMultiplicity_lt_char_of_natDegree_lt
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : K[X]) (hH : H ≠ 0) (y : K) (hdegree : H.natDegree < p) :
    H.rootMultiplicity y < p := by
  have hdvd := H.pow_rootMultiplicity_dvd y
  have hle := Polynomial.natDegree_le_of_dvd hdvd hH
  have hmultiplicity : H.rootMultiplicity y ≤ H.natDegree := by
    simpa using hle
  exact hmultiplicity.trans_lt hdegree

/-- Below the characteristic, differentiation lowers the multiplicity of a root exactly once. -/
theorem derivative_rootMultiplicity_of_natDegree_lt_char
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {H : K[X]} (hH : H ≠ 0) (y : K) (hdegree : H.natDegree < p)
    (hroot : H.IsRoot y) :
    H.derivative.rootMultiplicity y = H.rootMultiplicity y - 1 := by
  apply Polynomial.derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hroot
  apply mem_nonZeroDivisors_of_ne_zero
  exact (CharP.cast_eq_zero_iff K p _).not.mpr <| Nat.not_dvd_of_pos_of_lt
    ((Polynomial.rootMultiplicity_pos hH).2 hroot)
    (rootMultiplicity_lt_char_of_natDegree_lt p H hH y hdegree)

/-- A nonconstant rooted polynomial of degree below the characteristic has nonzero derivative. -/
theorem derivative_ne_zero_of_root_of_natDegree_lt_char
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {H : K[X]} (hH : H ≠ 0) (y : K) (hdegree : H.natDegree < p)
    (hroot : H.IsRoot y) : H.derivative ≠ 0 := by
  have hnpos : 0 < H.natDegree := by
    apply Polynomial.natDegree_pos_of_eval₂_root hH (RingHom.id K)
    · simpa [Polynomial.IsRoot] using hroot
    · intro z hz
      simpa using hz
  have hnCast : (H.natDegree : K) ≠ 0 :=
    (CharP.cast_eq_zero_iff K p _).not.mpr <|
      Nat.not_dvd_of_pos_of_lt hnpos hdegree
  have hleading : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH
  intro hzero
  have hcoeff := congrArg (fun q : K[X] => q.coeff (H.natDegree - 1)) hzero
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero,
    Nat.sub_add_cancel hnpos, Polynomial.coeff_natDegree] at hcoeff
  have hcast : ((H.natDegree - 1 : ℕ) : K) + 1 = H.natDegree := by
    have hnat : H.natDegree - 1 + 1 = H.natDegree := Nat.sub_add_cancel hnpos
    have hnatCast := congrArg (fun n : ℕ => (n : K)) hnat
    simpa only [Nat.cast_add, Nat.cast_one] using hnatCast
  rw [hcast] at hcoeff
  exact mul_ne_zero hleading hnCast hcoeff

/-- A monic divisor associated to `gcd(H,H')` leaves a squarefree quotient. -/
theorem squarefree_divByMonic_of_associated_gcd_derivative
    {K : Type*} [Field K] {H D Q : K[X]}
    (hH : H ≠ 0) (_hD : D.Monic)
    (hassociated : Associated D (fieldGCD H H.derivative))
    (hfactor : D * Q = H) : Squarefree Q := by
  let _ : DecidableEq K := Classical.decEq K
  let radical := UniqueFactorizationMonoid.radical H
  let repeated := EuclideanDomain.divRadical H
  have hrepeatedDvdGCD : repeated ∣ fieldGCD H H.derivative := by
    apply @EuclideanDomain.dvd_gcd K[X] inferInstance (Classical.decEq K[X])
    · exact EuclideanDomain.divRadical_dvd_self H
    · exact divRadical_dvd_derivative H
  have hrepeatedDvdD : repeated ∣ D :=
    hassociated.dvd_iff_dvd_right.mpr hrepeatedDvdGCD
  obtain ⟨multiplier, hmultiplier⟩ := hrepeatedDvdD
  have hcancel : repeated * (multiplier * Q) = repeated * radical := by
    calc
      _ = (repeated * multiplier) * Q := (mul_assoc _ _ _).symm
      _ = D * Q := by rw [hmultiplier]
      _ = H := hfactor
      _ = radical * repeated := by
        exact (EuclideanDomain.radical_mul_divRadical (a := H)).symm
      _ = repeated * radical := mul_comm _ _
  have hquotientDvd : Q ∣ radical := by
    refine ⟨multiplier, ?_⟩
    have hnonzero : repeated ≠ 0 := EuclideanDomain.divRadical_ne_zero hH
    have := mul_left_cancel₀ hnonzero hcancel
    simpa [mul_comm] using this.symm
  exact (UniqueFactorizationMonoid.squarefree_radical (a := H)).squarefree_of_dvd hquotientDvd

/-- Below the characteristic, a monic divisor associated to `gcd(H,H')` leaves exactly the roots
of `H`. -/
theorem eval_divByMonic_gcdDerivative_eq_zero_iff
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {H D Q : K[X]} (hH : H ≠ 0) (hD : D.Monic)
    (hassociated : Associated D (fieldGCD H H.derivative))
    (hfactor : D * Q = H) (hdegree : H.natDegree < p) (y : K) :
    Q.eval y = 0 ↔ H.eval y = 0 := by
  have hDNe : D ≠ 0 := hD.ne_zero
  have hQNe : Q ≠ 0 := by
    intro hzero
    apply hH
    simpa [hzero] using hfactor.symm
  constructor
  · intro hroot
    rw [← hfactor, Polynomial.eval_mul, hroot, mul_zero]
  · intro hroot
    have hrootH : H.IsRoot y := hroot
    by_contra hnotRoot
    have hQMultiplicity : Q.rootMultiplicity y = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hnotRoot)
    have hfactorMultiplicity := congrArg (fun P : K[X] => P.rootMultiplicity y) hfactor
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hDNe hQNe), hQMultiplicity,
      add_zero] at hfactorMultiplicity
    have hDDvdDerivative : D ∣ H.derivative := by
      apply (hassociated.dvd_iff_dvd_left.mpr ?_)
      exact @EuclideanDomain.gcd_dvd_right K[X] inferInstance (Classical.decEq K[X]) H H.derivative
    have hderivativeNe :=
      derivative_ne_zero_of_root_of_natDegree_lt_char p hH y hdegree hrootH
    have hle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd
      hderivativeNe hDDvdDerivative y
    rw [hfactorMultiplicity,
      derivative_rootMultiplicity_of_natDegree_lt_char p hH y hdegree hrootH] at hle
    have hpositive := (Polynomial.rootMultiplicity_pos hH).2 hrootH
    omega

/-- Every rooted radical branch is the exact derivative-gcd quotient and is squarefree. -/
theorem radicalTower_branch_semantics
    (g : CPolynomial F) (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly) (h : FiberPolynomial (F := F))
    (hhmonic : h.toCPolynomial.monic)
    (terminal : TerminalGCDBranch (F := F))
    (hterminal : terminal ∈ factorTower (radicalState g hg hgmonic hgfree h))
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : terminal.modulus.toPoly.eval₂ phi x = 0) :
    let quotient := makeTerminalQuotientBranch
      (radicalState g hg hgmonic hgfree h) terminal
    terminal.gcdPolynomial.specialize phi x * quotient.quotient.specialize phi x =
        h.specialize phi x ∧
      Squarefree (quotient.quotient.specialize phi x) := by
  let state := radicalState g hg hgmonic hgfree h
  let quotient := makeTerminalQuotientBranch state terminal
  have hfactor := terminal_gcd_mul_terminalQuotient_specialize
    state hhmonic terminal hterminal phi x hroot
  have hassociated := factorTower_terminal_fieldGCD_associated
    state phi x terminal hterminal hroot
  have hderivative : state.divisor.specialize phi x = (h.specialize phi x).derivative := by
    exact derivativeFiber_specialize h phi x
  have hHMonic : (h.specialize phi x).Monic :=
    ((CPolynomial.monic_toPoly_iff _).mp hhmonic).map _
  have hDMonic : (terminal.gcdPolynomial.specialize phi x).Monic :=
    ((CPolynomial.monic_toPoly_iff _).mp
      (factorTower_terminal_gcd_monic state hhmonic terminal hterminal)).map _
  refine ⟨hfactor, ?_⟩
  apply squarefree_divByMonic_of_associated_gcd_derivative hHMonic.ne_zero hDMonic
  · rw [hderivative] at hassociated
    exact hassociated
  · exact hfactor

/-- Below the characteristic, each radical branch retains exactly all roots of the input fiber. -/
theorem radicalTower_branch_root_iff
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (g : CPolynomial F) (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly) (h : FiberPolynomial (F := F))
    (hhmonic : h.toCPolynomial.monic) (hhdegree : h.toCPolynomial.natDegree < p)
    (terminal : TerminalGCDBranch (F := F))
    (hterminal : terminal ∈ factorTower (radicalState g hg hgmonic hgfree h))
    {K : Type*} [Field K] (phi : F →+* K) (x y : K)
    (hroot : terminal.modulus.toPoly.eval₂ phi x = 0) :
    (((makeTerminalQuotientBranch
      (radicalState g hg hgmonic hgfree h) terminal).quotient).specialize phi x).eval y = 0 ↔
      (h.specialize phi x).eval y = 0 := by
  let _ : CharP K p := charP_of_injective_ringHom phi.injective p
  let state := radicalState g hg hgmonic hgfree h
  let quotient := makeTerminalQuotientBranch state terminal
  have hsemantics := radicalTower_branch_semantics g hg hgmonic hgfree h hhmonic terminal
    hterminal phi x hroot
  have hassociated := factorTower_terminal_fieldGCD_associated
    state phi x terminal hterminal hroot
  have hderivative : state.divisor.specialize phi x = (h.specialize phi x).derivative :=
    derivativeFiber_specialize h phi x
  have hHMonic : (h.specialize phi x).Monic :=
    ((CPolynomial.monic_toPoly_iff _).mp hhmonic).map _
  have hDMonic : (terminal.gcdPolynomial.specialize phi x).Monic :=
    ((CPolynomial.monic_toPoly_iff _).mp
      (factorTower_terminal_gcd_monic state hhmonic terminal hterminal)).map _
  have hsourceDegree : h.toCPolynomial.toPoly.natDegree < p := by
    simpa only [← CPolynomial.natDegree_toPoly] using hhdegree
  have hdegree : (h.specialize phi x).natDegree < p :=
    Polynomial.natDegree_map_le.trans_lt hsourceDegree
  apply eval_divByMonic_gcdDerivative_eq_zero_iff p hHMonic.ne_zero hDMonic
  · rw [hderivative] at hassociated
    exact hassociated
  · exact hsemantics.1
  · exact hdegree

end ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5
