/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.EuclideanInvariance
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.TerminalCoprime
import ArkLib.Data.Polynomial.BatchRemainder

/-!
# Executable coefficientwise CRT for the D5 factor tower

This file reconstructs coefficient representatives across pairwise-coprime terminal factors.
Binary and list combiners are executable and return canonical residues below the product modulus.
The empty list yields zero modulo one, and a singleton is reduced directly without an inverse.

Applying the combiner independently to every active fiber coefficient assembles one nested
polynomial.  At every geometric root of every terminal modulus, that polynomial specializes to
the branch-local gcd representative, hence to an associate of the initial specialized field gcd.
The construction does not yet claim decoder coverage or perform any exceptional-fiber removal.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

open ArkLib.PolynomialQuotient CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance coefficientCRTDecidableEqF : DecidableEq F := instDecidableEqOfLawfulBEq
local instance coefficientCRTDecidableEqCPolynomial : DecidableEq (CPolynomial F) :=
  instDecidableEqOfLawfulBEq

/-- One congruence datum: a modulus and its requested residue representative. -/
structure CRTEntry where
  modulus : CPolynomial F
  residue : CPolynomial F

/-- Executably combine two coefficient congruences by the usual coprime CRT formula. -/
def combineCRT? (left right : CRTEntry (F := F)) : Option (CRTEntry (F := F)) := do
  let inverse ← CPolynomial.inverseMod? left.modulus right.modulus
  let correction := ((right.residue - left.residue) * inverse).modByMonic right.modulus
  let modulus := left.modulus * right.modulus
  let residue := (left.residue + left.modulus * correction).modByMonic modulus
  return ⟨modulus, residue⟩

theorem quotientHom_modByMonic_of_dvd
    {factor product : CPolynomial F} (hfactor : factor.monic) (hproduct : product.monic)
    (hdivides : factor.toPoly ∣ product.toPoly) (p : CPolynomial F) :
    quotientHom factor (p.modByMonic product) = quotientHom factor p := by
  calc
    quotientHom factor (p.modByMonic product) =
        quotientHom factor ((p.modByMonic product).modByMonic factor) := by
      symm
      simpa only [reduce] using quotientHom_reduce hfactor (p.modByMonic product)
    _ = quotientHom factor (p.modByMonic factor) := by
      rw [CPolynomial.modByMonic_of_dvd p factor product hfactor hproduct hdivides]
    _ = quotientHom factor p := by
      simpa only [reduce] using quotientHom_reduce hfactor p

theorem quotientHom_eq_of_dvd {factor product a b : CPolynomial F}
    (hdivides : factor.toPoly ∣ product.toPoly)
    (h : quotientHom product a = quotientHom product b) :
    quotientHom factor a = quotientHom factor b := by
  rw [quotientHom_apply, quotientHom_apply, Ideal.Quotient.eq, modIdeal,
    Ideal.mem_span_singleton] at h ⊢
  exact hdivides.trans h

theorem combineCRT?_eq_some_of_coprime (left right : CRTEntry (F := F))
    (hleft : left.modulus.monic) (hright : right.modulus.monic)
    (hcoprime : IsCoprime left.modulus.toPoly right.modulus.toPoly) :
    ∃ output, combineCRT? left right = some output ∧
      output.modulus = left.modulus * right.modulus ∧
      output.modulus.monic ∧
      quotientHom left.modulus output.residue = quotientHom left.modulus left.residue ∧
      quotientHom right.modulus output.residue = quotientHom right.modulus right.residue ∧
      output.residue.toPoly.degree < output.modulus.toPoly.degree := by
  obtain ⟨inverse, hinverse⟩ :=
    (CPolynomial.inverseMod_exists_iff_coprime left.modulus right.modulus).mpr hcoprime
  let correction := ((right.residue - left.residue) * inverse).modByMonic right.modulus
  let modulus := left.modulus * right.modulus
  let residue := (left.residue + left.modulus * correction).modByMonic modulus
  have hmodulus : modulus.monic := by
    change (left.modulus * right.modulus).monic
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_mul]
    exact ((CPolynomial.monic_toPoly_iff _).mp hleft).mul
      ((CPolynomial.monic_toPoly_iff _).mp hright)
  refine ⟨⟨modulus, residue⟩, ?_, rfl, hmodulus, ?_, ?_, ?_⟩
  · simp [combineCRT?, hinverse, correction, modulus, residue]
  · change quotientHom left.modulus
      ((left.residue + left.modulus * correction).modByMonic modulus) = _
    rw [quotientHom_modByMonic_of_dvd hleft hmodulus
      (by
        change left.modulus.toPoly ∣ (left.modulus * right.modulus).toPoly
        rw [CPolynomial.toPoly_mul]
        exact dvd_mul_right _ _)]
    rw [map_add, map_mul, quotientHom_modulus, zero_mul, add_zero]
  · change quotientHom right.modulus
      ((left.residue + left.modulus * correction).modByMonic modulus) = _
    rw [quotientHom_modByMonic_of_dvd hright hmodulus
      (by
        change right.modulus.toPoly ∣ (left.modulus * right.modulus).toPoly
        rw [CPolynomial.toPoly_mul]
        exact dvd_mul_left _ _)]
    have hinverseQ := quotientHom_mul_inverseMod?_eq_one hright hinverse
    change quotientHom right.modulus
      (left.residue + left.modulus *
        (((right.residue - left.residue) * inverse).modByMonic right.modulus)) = _
    rw [map_add, map_mul]
    have hcorrection : quotientHom right.modulus
        (((right.residue - left.residue) * inverse).modByMonic right.modulus) =
          quotientHom right.modulus ((right.residue - left.residue) * inverse) := by
      simpa only [reduce] using
        quotientHom_reduce hright ((right.residue - left.residue) * inverse)
    rw [hcorrection]
    simp only [map_mul, map_sub]
    calc
      _ = quotientHom right.modulus left.residue +
          (quotientHom right.modulus right.residue -
            quotientHom right.modulus left.residue) *
            (quotientHom right.modulus left.modulus *
              quotientHom right.modulus inverse) := by ring
      _ = _ := by rw [hinverseQ]; ring
  · change
      ((left.residue + left.modulus * correction).modByMonic modulus).toPoly.degree <
        modulus.toPoly.degree
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hmodulus]
    exact Polynomial.degree_modByMonic_lt _
      ((CPolynomial.monic_toPoly_iff _).mp hmodulus)

/-- Product of all moduli in a coefficient CRT problem. -/
def CRTEntry.modulusProduct (entries : List (CRTEntry (F := F))) : CPolynomial F :=
  (entries.map CRTEntry.modulus).prod

/-- Executable right-associated CRT fold, with explicit empty and singleton cases. -/
def combineCRTList? : List (CRTEntry (F := F)) → Option (CRTEntry (F := F))
  | [] => some ⟨1, 0⟩
  | [entry] => some ⟨entry.modulus, entry.residue.modByMonic entry.modulus⟩
  | entry :: next :: rest => do
      let tail ← combineCRTList? (next :: rest)
      combineCRT? entry tail

/-- The empty CRT problem is represented canonically by zero modulo one. -/
@[simp]
theorem combineCRTList?_nil :
    combineCRTList? ([] : List (CRTEntry (F := F))) = some ⟨1, 0⟩ := rfl

/-- A singleton CRT problem only reduces its residue; it does not request an inverse. -/
@[simp]
theorem combineCRTList?_singleton (entry : CRTEntry (F := F)) :
    combineCRTList? [entry] =
      some ⟨entry.modulus, entry.residue.modByMonic entry.modulus⟩ := rfl

/-- In particular, the singleton unit-modulus branch reduces to zero modulo one. -/
@[simp]
theorem combineCRTList?_singleton_unit (residue : CPolynomial F) :
    combineCRTList? [⟨1, residue⟩] = some ⟨1, 0⟩ := by
  rw [combineCRTList?_singleton]
  congr 2
  change residue.modByMonic 1 = 0
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _
      (by simp [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_one]),
    CPolynomial.toPoly_one, Polynomial.modByMonic_one, CPolynomial.toPoly_zero]

/-- Predicate recording that an output satisfies every input congruence. -/
def CRTEntry.Represents (output : CRTEntry (F := F))
    (entries : List (CRTEntry (F := F))) : Prop :=
  ∀ entry ∈ entries,
    quotientHom entry.modulus output.residue = quotientHom entry.modulus entry.residue

theorem toPoly_modulusProduct (entries : List (CRTEntry (F := F))) :
    (CRTEntry.modulusProduct entries).toPoly =
      (entries.map fun entry => entry.modulus.toPoly).prod := by
  unfold CRTEntry.modulusProduct
  induction entries with
  | nil => simp [CPolynomial.toPoly_one]
  | cons entry entries ih =>
      rw [List.map_cons, List.prod_cons, CPolynomial.toPoly_mul, ih,
        List.map_cons, List.prod_cons]

theorem isCoprime_list_product {R : Type*} [CommRing R]
    (a : R) (factors : List R) (hcoprime : ∀ factor ∈ factors, IsCoprime a factor) :
    IsCoprime a factors.prod := by
  induction factors with
  | nil => exact isCoprime_one_right
  | cons factor factors ih =>
      rw [List.prod_cons]
      exact (hcoprime factor (by simp)).mul_right
        (ih fun other hother => hcoprime other (by simp [hother]))

theorem combineCRTList?_eq_some
    (entries : List (CRTEntry (F := F)))
    (hmonic : ∀ entry ∈ entries, entry.modulus.monic)
    (hpairwise : entries.Pairwise fun left right =>
      IsCoprime left.modulus.toPoly right.modulus.toPoly) :
    ∃ output, combineCRTList? entries = some output ∧
      output.modulus = CRTEntry.modulusProduct entries ∧
      output.modulus.monic ∧
      output.Represents entries ∧
      output.residue.toPoly.degree < output.modulus.toPoly.degree := by
  induction entries with
  | nil =>
      refine ⟨⟨1, 0⟩, rfl, rfl, ?_, ?_, ?_⟩
      · simp [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_one]
      · simp [CRTEntry.Represents]
      · simp [CPolynomial.toPoly_zero, CPolynomial.toPoly_one]
  | cons entry entries ih =>
      cases entries with
      | nil =>
          have hentryMonic := hmonic entry (by simp)
          refine ⟨⟨entry.modulus, entry.residue.modByMonic entry.modulus⟩,
            rfl, ?_, hentryMonic, ?_, ?_⟩
          · simp [CRTEntry.modulusProduct]
          · intro other hother
            simp only [List.mem_singleton] at hother
            subst other
            simpa only [reduce] using quotientHom_reduce hentryMonic entry.residue
          · rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hentryMonic]
            exact Polynomial.degree_modByMonic_lt _
              ((CPolynomial.monic_toPoly_iff _).mp hentryMonic)
      | cons next rest =>
          rw [List.pairwise_cons] at hpairwise
          obtain ⟨tail, htail, htailModulus, htailMonic, htailRepresents, htailDegree⟩ :=
            ih (fun other hother => hmonic other (by simp [hother])) hpairwise.2
          have hheadTail : IsCoprime entry.modulus.toPoly tail.modulus.toPoly := by
            rw [htailModulus, toPoly_modulusProduct]
            apply isCoprime_list_product
            intro factor hfactor
            rcases List.mem_map.mp hfactor with ⟨other, hother, rfl⟩
            exact hpairwise.1 other hother
          obtain ⟨output, houtput, houtputModulus, houtputMonic,
              houtputLeft, houtputRight, houtputDegree⟩ :=
            combineCRT?_eq_some_of_coprime entry tail
              (hmonic entry (by simp)) htailMonic hheadTail
          refine ⟨output, ?_, ?_, houtputMonic, ?_, houtputDegree⟩
          · simp [combineCRTList?, htail, houtput]
          · rw [houtputModulus, htailModulus]
            rfl
          · intro other hother
            simp only [List.mem_cons] at hother
            rcases hother with rfl | hother
            · exact houtputLeft
            · calc
                quotientHom other.modulus output.residue =
                    quotientHom other.modulus tail.residue := by
                  apply quotientHom_eq_of_dvd _ houtputRight
                  rw [htailModulus, toPoly_modulusProduct]
                  exact List.dvd_prod (List.mem_map.mpr
                    ⟨other, (by simpa only [List.mem_cons] using hother), rfl⟩)
                _ = quotientHom other.modulus other.residue :=
                  htailRepresents other (by simpa only [List.mem_cons] using hother)

/-- The terminal tower congruences for one fiber coefficient. -/
def terminalCoefficientEntries (state : TowerState (F := F)) (index : ℕ) :
    List (CRTEntry (F := F)) :=
  (factorTower state).map fun terminal =>
    ⟨terminal.modulus, terminal.gcdPolynomial.toCPolynomial.coeff index⟩

/-- Executably reconstruct one global fiber coefficient from all terminal branches. -/
def recombineTerminalCoefficient? (state : TowerState (F := F)) (index : ℕ) :
    Option (CRTEntry (F := F)) :=
  combineCRTList? (terminalCoefficientEntries state index)

theorem terminalCoefficientEntries_moduli (state : TowerState (F := F)) (index : ℕ) :
    (terminalCoefficientEntries state index).map CRTEntry.modulus =
      (factorTower state).map TerminalGCDBranch.modulus := by
  unfold terminalCoefficientEntries
  induction factorTower state with
  | nil => rfl
  | cons terminal terminals ih =>
      simp only [List.map_cons, ih]

theorem terminalCoefficientEntries_toPoly_moduli
    (state : TowerState (F := F)) (index : ℕ) :
    (terminalCoefficientEntries state index).map (fun entry => entry.modulus.toPoly) =
      (factorTower state).map (fun terminal => terminal.modulus.toPoly) := by
  unfold terminalCoefficientEntries
  induction factorTower state with
  | nil => rfl
  | cons terminal terminals ih =>
      simp only [List.map_cons, ih]

theorem terminalCoefficientEntries_pairwise (state : TowerState (F := F)) (index : ℕ) :
    (terminalCoefficientEntries state index).Pairwise fun left right =>
      IsCoprime left.modulus.toPoly right.modulus.toPoly := by
  apply List.pairwise_map.mp
  rw [terminalCoefficientEntries_toPoly_moduli]
  exact (factorTower_moduli_pairwise_isRelPrime state).imp fun h =>
    isRelPrime_iff_isCoprime.mp h

theorem recombineTerminalCoefficient?_eq_some (state : TowerState (F := F)) (index : ℕ) :
    ∃ output, recombineTerminalCoefficient? state index = some output ∧
      output.modulus = state.modulus ∧
      (∀ terminal ∈ factorTower state,
        quotientHom terminal.modulus output.residue =
          quotientHom terminal.modulus
            (terminal.gcdPolynomial.toCPolynomial.coeff index)) ∧
      output.residue.toPoly.degree < state.modulus.toPoly.degree := by
  have hmonic : ∀ entry ∈ terminalCoefficientEntries state index, entry.modulus.monic := by
    intro entry hentry
    rcases List.mem_map.mp hentry with ⟨terminal, hterminal, rfl⟩
    exact (factorTower_terminal_invariants state terminal hterminal).2.1
  obtain ⟨output, houtput, hmodulus, _, hrepresents, hdegree⟩ :=
    combineCRTList?_eq_some (terminalCoefficientEntries state index) hmonic
      (terminalCoefficientEntries_pairwise state index)
  have hproduct : CRTEntry.modulusProduct (terminalCoefficientEntries state index) =
      state.modulus := by
    unfold CRTEntry.modulusProduct
    rw [terminalCoefficientEntries_moduli]
    exact factorTower_modulus_product state
  refine ⟨output, houtput, hmodulus.trans hproduct, ?_, ?_⟩
  · intro terminal hterminal
    simpa only [CRTEntry.modulus, CRTEntry.residue] using
      hrepresents _ (List.mem_map.mpr ⟨terminal, hterminal, rfl⟩)
  · rwa [hmodulus, hproduct] at hdegree

/-- One more than the largest terminal gcd fiber degree, or zero for no terminals. -/
def terminalFiberWidth (state : TowerState (F := F)) : ℕ :=
  ((factorTower state).map fun terminal =>
    terminal.gcdPolynomial.toCPolynomial.natDegree + 1).foldr max 0

theorem terminal_natDegree_lt_fiberWidth (state : TowerState (F := F))
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state) :
    terminal.gcdPolynomial.toCPolynomial.natDegree < terminalFiberWidth state := by
  have hmem : terminal.gcdPolynomial.toCPolynomial.natDegree + 1 ∈
      (factorTower state).map (fun branch =>
        branch.gcdPolynomial.toCPolynomial.natDegree + 1) :=
    List.mem_map.mpr ⟨terminal, hterminal, rfl⟩
  have hle := List.le_max_of_le' 0 hmem (le_refl _)
  simpa only [terminalFiberWidth] using Nat.lt_of_lt_of_le
    (Nat.lt_succ_self terminal.gcdPolynomial.toCPolynomial.natDegree) hle

/-- Assemble the first `width` reconstructed coefficients in ascending fiber-degree order. -/
def materializePrefix? (state : TowerState (F := F)) : ℕ →
    Option (CPolynomial (CPolynomial F))
  | 0 => some 0
  | width + 1 => do
      let assembled ← materializePrefix? state width
      let coefficient ← recombineTerminalCoefficient? state width
      return assembled + CPolynomial.monomial width coefficient.residue

theorem materializePrefix?_eq_some (state : TowerState (F := F)) (width : ℕ) :
    ∃ output, materializePrefix? state width = some output ∧
      output.toPoly.degree < (width : WithBot ℕ) ∧
      ∀ index < width, ∃ coefficient,
        recombineTerminalCoefficient? state index = some coefficient ∧
          output.coeff index = coefficient.residue := by
  induction width with
  | zero =>
      refine ⟨0, rfl, ?_, ?_⟩
      · simp [CPolynomial.toPoly_zero]
      · omega
  | succ width ih =>
      obtain ⟨assembled, hassembled, hassembledDegree, hassembledCoefficients⟩ := ih
      obtain ⟨coefficient, hcoefficient, _, _, _⟩ :=
        recombineTerminalCoefficient?_eq_some state width
      let output := assembled + CPolynomial.monomial width coefficient.residue
      refine ⟨output, ?_, ?_, ?_⟩
      · simp [materializePrefix?, hassembled, hcoefficient, output]
      · change (assembled + CPolynomial.monomial width coefficient.residue).toPoly.degree < _
        rw [CPolynomial.toPoly_add, CPolynomial.toPoly_monomial]
        apply (Polynomial.degree_add_le _ _).trans_lt
        rw [max_lt_iff]
        exact ⟨hassembledDegree.trans
            (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self width)),
          (Polynomial.degree_monomial_le _ _).trans_lt
            (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self width))⟩
      · intro index hindex
        by_cases hi : index < width
        · obtain ⟨previous, hprevious, hassembledCoeff⟩ :=
            hassembledCoefficients index hi
          refine ⟨previous, hprevious, ?_⟩
          change (assembled + CPolynomial.monomial width coefficient.residue).coeff index = _
          rw [CPolynomial.coeff_add, CPolynomial.coeff_monomial]
          simp [Nat.ne_of_lt hi, hassembledCoeff]
        · have hiEq : index = width := by omega
          subst index
          refine ⟨coefficient, hcoefficient, ?_⟩
          have hassembledCoeff : assembled.coeff width = 0 := by
            rw [CPolynomial.coeff_toPoly]
            exact Polynomial.coeff_eq_zero_of_degree_lt hassembledDegree
          change (assembled + CPolynomial.monomial width coefficient.residue).coeff width = _
          rw [CPolynomial.coeff_add, CPolynomial.coeff_monomial,
            if_pos rfl, hassembledCoeff, zero_add]

/-- The executable coefficientwise CRT materialization over all terminal fiber coefficients. -/
def materializeTerminalGCD? (state : TowerState (F := F)) :
    Option (CPolynomial (CPolynomial F)) :=
  materializePrefix? state (terminalFiberWidth state)

theorem materializeTerminalGCD?_eq_some (state : TowerState (F := F)) :
    ∃ output, materializeTerminalGCD? state = some output ∧
      output.toPoly.degree < (terminalFiberWidth state : WithBot ℕ) ∧
      ∀ index < terminalFiberWidth state, ∃ coefficient,
        recombineTerminalCoefficient? state index = some coefficient ∧
          output.coeff index = coefficient.residue := by
  exact materializePrefix?_eq_some state (terminalFiberWidth state)

theorem materializeTerminalGCD?_coeff_quotient
    (state : TowerState (F := F)) {output : CPolynomial (CPolynomial F)}
    (houtput : materializeTerminalGCD? state = some output)
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state)
    (index : ℕ) :
    quotientHom terminal.modulus (output.coeff index) =
      quotientHom terminal.modulus
        (terminal.gcdPolynomial.toCPolynomial.coeff index) := by
  obtain ⟨assembled, hassembled, hassembledDegree, hassembledCoefficients⟩ :=
    materializeTerminalGCD?_eq_some state
  have hassembledEq : assembled = output :=
    Option.some.inj (hassembled.symm.trans houtput)
  subst assembled
  by_cases hindex : index < terminalFiberWidth state
  · obtain ⟨coefficient, hcoefficient, houtputCoeff⟩ :=
      hassembledCoefficients index hindex
    obtain ⟨canonical, hcanonical, _, hcanonicalRepresents, _⟩ :=
      recombineTerminalCoefficient?_eq_some state index
    have hcanonicalEq : canonical = coefficient :=
      Option.some.inj (hcanonical.symm.trans hcoefficient)
    subst canonical
    rw [houtputCoeff]
    exact hcanonicalRepresents terminal hterminal
  · have hwidthLe : terminalFiberWidth state ≤ index := Nat.le_of_not_gt hindex
    have houtputCoeff : output.coeff index = 0 := by
      rw [CPolynomial.coeff_toPoly]
      exact Polynomial.coeff_eq_zero_of_degree_lt
        (hassembledDegree.trans_le (WithBot.coe_le_coe.mpr hwidthLe))
    have hterminalCoeff : terminal.gcdPolynomial.toCPolynomial.coeff index = 0 := by
      rw [CPolynomial.coeff_toPoly]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [← CPolynomial.natDegree_toPoly]
      exact (terminal_natDegree_lt_fiberWidth state terminal hterminal).trans_le hwidthLe
    rw [houtputCoeff, hterminalCoeff]

theorem coefficientEval_eq_of_quotientHom_eq
    {modulus a b : CPolynomial F}
    (hquotient : quotientHom modulus a = quotientHom modulus b)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : modulus.toPoly.eval₂ phi x = 0) :
    a.toPoly.eval₂ phi x = b.toPoly.eval₂ phi x := by
  have hdivides : modulus.toPoly ∣ a.toPoly - b.toPoly := by
    rwa [quotientHom_apply, quotientHom_apply, Ideal.Quotient.eq, modIdeal,
      Ideal.mem_span_singleton] at hquotient
  obtain ⟨multiple, hmultiple⟩ := hdivides
  have heval := congrArg (fun p : F[X] => p.eval₂ phi x) hmultiple
  apply sub_eq_zero.mp
  simpa [Polynomial.eval₂_sub, Polynomial.eval₂_mul, hroot] using heval

/-- At every root of a terminal modulus, the single reconstructed nested polynomial specializes
to that terminal branch's local gcd representative. -/
theorem materializeTerminalGCD?_specialize
    (state : TowerState (F := F)) {output : CPolynomial (CPolynomial F)}
    (houtput : materializeTerminalGCD? state = some output)
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : terminal.modulus.toPoly.eval₂ phi x = 0) :
    specializeFiberCPolynomial output phi x = terminal.gcdPolynomial.specialize phi x := by
  ext index
  rw [specializeFiberCPolynomial, FiberPolynomial.specialize, specializeFiberCPolynomial,
    Polynomial.coeff_map, Polynomial.coeff_map,
    ← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly,
    coefficientEval_apply, coefficientEval_apply]
  exact coefficientEval_eq_of_quotientHom_eq
    (materializeTerminalGCD?_coeff_quotient state houtput terminal hterminal index)
    phi x hroot

/-- The reconstructed global polynomial therefore specializes to the initial pair's field gcd,
up to a unit, on every rooted terminal factor. -/
theorem materializeTerminalGCD?_fieldGCD_associated
    (state : TowerState (F := F)) {output : CPolynomial (CPolynomial F)}
    (houtput : materializeTerminalGCD? state = some output)
    (terminal : TerminalGCDBranch (F := F)) (hterminal : terminal ∈ factorTower state)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : terminal.modulus.toPoly.eval₂ phi x = 0) :
    Associated (specializeFiberCPolynomial output phi x)
      (fieldGCD (state.dividend.specialize phi x) (state.divisor.specialize phi x)) :=
  (Associated.of_eq
    (materializeTerminalGCD?_specialize state houtput terminal hterminal phi x hroot)).trans
    (factorTower_terminal_fieldGCD_associated state phi x terminal hterminal hroot)

theorem materializeTerminalGCD?_coefficient_degree
    (state : TowerState (F := F)) {output : CPolynomial (CPolynomial F)}
    (houtput : materializeTerminalGCD? state = some output) (index : ℕ) :
    (output.coeff index).toPoly.degree < state.modulus.toPoly.degree := by
  by_cases hindex : index < terminalFiberWidth state
  · obtain ⟨assembled, hassembled, _, hassembledCoefficients⟩ :=
      materializeTerminalGCD?_eq_some state
    have hassembledEq : assembled = output :=
      Option.some.inj (hassembled.symm.trans houtput)
    subst assembled
    obtain ⟨coefficient, hcoefficient, houtputCoeff⟩ :=
      hassembledCoefficients index hindex
    obtain ⟨canonical, hcanonical, _, _, hdegree⟩ :=
      recombineTerminalCoefficient?_eq_some state index
    have hcanonicalEq : canonical = coefficient :=
      Option.some.inj (hcanonical.symm.trans hcoefficient)
    subst canonical
    rwa [houtputCoeff]
  · obtain ⟨assembled, hassembled, hassembledDegree, _⟩ :=
      materializeTerminalGCD?_eq_some state
    have hassembledEq : assembled = output :=
      Option.some.inj (hassembled.symm.trans houtput)
    subst assembled
    have houtputCoeff : output.coeff index = 0 := by
      rw [CPolynomial.coeff_toPoly]
      exact Polynomial.coeff_eq_zero_of_degree_lt
        (hassembledDegree.trans_le
          (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hindex)))
    rw [houtputCoeff, CPolynomial.toPoly_zero]
    exact WithBot.bot_lt_iff_ne_bot.mpr
      (Polynomial.degree_ne_bot.mpr
        ((CPolynomial.monic_toPoly_iff _).mp state.modulus_monic).ne_zero)

/-- Every active reconstructed coefficient satisfies the base/fiber weighted-degree budget
obtained from canonical reduction modulo the initial modulus. -/
theorem materializeTerminalGCD?_weighted_coefficient_bound
    (state : TowerState (F := F)) {output : CPolynomial (CPolynomial F)}
    (houtput : materializeTerminalGCD? state = some output)
    (weight index : ℕ) (hindex : index < terminalFiberWidth state)
    (hcoefficient : output.coeff index ≠ 0) :
    (output.coeff index).natDegree + weight * index <
      state.modulus.natDegree + weight * terminalFiberWidth state := by
  have hbaseDegree : (output.coeff index).natDegree < state.modulus.natDegree := by
    rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
    apply (Polynomial.natDegree_lt_iff_degree_lt
      ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hcoefficient)).mpr
    rw [← Polynomial.degree_eq_natDegree
      ((CPolynomial.monic_toPoly_iff _).mp state.modulus_monic).ne_zero]
    exact materializeTerminalGCD?_coefficient_degree state houtput index
  exact Nat.add_lt_add_of_lt_of_le hbaseDegree
    (Nat.mul_le_mul_left weight (Nat.le_of_lt hindex))

end ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5
