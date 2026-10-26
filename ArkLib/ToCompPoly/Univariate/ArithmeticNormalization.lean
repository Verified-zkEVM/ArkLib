/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticPolynomialCost

import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core

/-!
# Reverse-scan normalization of measured coefficient arrays

The scan reads the original array backwards until its last nonzero coefficient is found. Its
response type refers to that same original array throughout recursion, so a zero branch returns
the recursive call directly. Canonicalization then extracts at most one prefix, reusing the
original array when that prefix is complete. No array pops or second normalization scan execute.

Profiles count the actual arithmetic requests, including zero tests and designated control ticks.
They do not count index arithmetic, prefix extraction, allocation or machine runtime. The existing
normalization programs remain available; callers select this program explicitly.
-/

@[expose] public section

open CompPoly CPolynomial OracleComp OracleSpec
namespace CompPoly.Arithmetic
variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- Scan a prefix when the remaining original-array suffix is already known to be zero. -/
def lastNonzeroFromProgram (p : Raw F) : (n : ℕ) → (hn : n ≤ p.size) →
    (hz : ∀ i, (hi : i < p.size) → n ≤ i → p[i] = 0) →
    OracleComp (ArithmeticSpec F) {idx : Option (Fin p.size) // idx = p.lastNonzero}
  | 0, _, hz => do
    tick
    pure ⟨none, (Raw.Trim.lastNonzero_none (fun i hi => hz i hi (by omega))).symm⟩
  | n + 1, hn, hz => do
    tick
    let a ← coefficientRead p n
    let e ← eq a.val 0
    have hlt : n < p.size := by omega
    have ha : a.val = p[n] := by simpa [hlt] using a.property
    if he : e.val = true then
      have hzero : p[n] = 0 := ha.symm.trans
        (of_decide_eq_true (e.property.symm.trans he))
      lastNonzeroFromProgram p n (by omega) (by
        intro i hi hni
        by_cases h : i = n
        · subst i; exact hzero
        · exact hz i hi (by omega))
    else
      have hne : p[n] ≠ 0 := by
        intro h
        apply he
        simpa [ha, h] using e.property
      pure ⟨some ⟨n, hlt⟩, (Raw.Trim.lastNonzero_some_iff.mpr
        ⟨hne, fun j hj hnj => hz j hj (by
          change n < j at hnj
          omega)⟩).symm⟩

/-- Locate the original array's final nonzero coefficient with a backwards scan. -/
def lastNonzeroProgram (p : Raw F) :
    OracleComp (ArithmeticSpec F) {idx : Option (Fin p.size) // idx = p.lastNonzero} :=
  lastNonzeroFromProgram p p.size (by omega) (by intro i hi h; omega)

/-- Scan once and extract at most one prefix to construct the existing canonical polynomial. -/
def canonicalRawProgram (p : Raw F) :
    OracleComp (ArithmeticSpec F) {q : CPolynomial F // q = CPolynomial.ofArray p} := do
  let idx ← lastNonzeroProgram p
  match hi : idx.val with
  | none =>
    pure ⟨⟨#[], Raw.Trim.isCanonical_empty⟩, by
      apply Subtype.ext
      change (#[] : Raw F) = p.trim
      simp only [Raw.trim, ← idx.property, hi]⟩
  | some i =>
    let q := if i.val + 1 = p.size then p else p.extract 0 (i.val + 1)
    have hq : q = p.extract 0 (i.val + 1) := by
      simp only [q]
      split_ifs with h
      · exact (Array.extract_eq_self_of_le h.ge).symm
      · rfl
    have htrim : p.trim = q := by
      rw [hq]
      simp only [Raw.trim, ← idx.property, hi]
    pure ⟨⟨q, by rw [← htrim]; exact Raw.Trim.isCanonical_trim p⟩, by
      apply Subtype.ext
      exact htrim.symm⟩

/-- Erasing normalization returns the existing canonical coefficient array. -/
theorem simulateQ_canonicalRawProgram (p : Raw F) :
    (simulateQ arithmeticAnswer (canonicalRawProgram p)).val = CPolynomial.ofArray p :=
  (simulateQ arithmeticAnswer (canonicalRawProgram p)).property

/-- A zero suffix scan has one control step and no coefficient request. -/
@[simp]
theorem profileArithmetic_lastNonzeroFromProgram_zero (p : Raw F)
    (hn : 0 ≤ p.size) (hz : ∀ i, (hi : i < p.size) → 0 ≤ i → p[i] = 0) :
    (profileArithmetic (lastNonzeroFromProgram p 0 hn hz)).2 =
      arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) := by
  simp [lastNonzeroFromProgram]

/-- One reverse-scan step reads the original array before testing its coefficient. -/
theorem profileArithmetic_lastNonzeroFromProgram_succ (p : Raw F) (n : ℕ)
    (hn : n + 1 ≤ p.size)
    (hz : ∀ i, (hi : i < p.size) → n + 1 ≤ i → p[i] = 0) :
    (profileArithmetic (lastNonzeroFromProgram p (n + 1) hn hz)).2 =
      arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) +
        arithmeticCost (.coefficientRead p n) + arithmeticCost (.eq p[n] 0) +
        if hzero : p[n] = 0 then
          (profileArithmetic (lastNonzeroFromProgram p n (by omega) (by
            intro i hi hni
            by_cases h : i = n
            · subst i; exact hzero
            · exact hz i hi (by omega)))).2
        else 0 := by
  have hlt : n < p.size := by omega
  by_cases h : p[n] = 0
  · funext kind
    simp [lastNonzeroFromProgram, profileArithmetic_bind, hlt, h, Nat.add_assoc]
  · funext kind
    simp [lastNonzeroFromProgram, profileArithmetic_bind, hlt, h, Nat.add_assoc]

/-- A scan reads and tests at most the unscanned prefix, with one terminal control step. -/
theorem profileArithmetic_lastNonzeroFromProgram_le (p : Raw F) (n : ℕ)
    (hn : n ≤ p.size) (hz : ∀ i, (hi : i < p.size) → n ≤ i → p[i] = 0)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (lastNonzeroFromProgram p n hn hz)).2 kind ≤
      if kind = .coefficientRead ∨ kind = .eq then n
      else if kind = .metadata then n + 1 else 0 := by
  induction n with
  | zero =>
    rw [profileArithmetic_lastNonzeroFromProgram_zero]
    cases kind <;> simp [arithmeticCost, ArithmeticOp.costKind]
  | succ n ih =>
    rw [profileArithmetic_lastNonzeroFromProgram_succ]
    by_cases hzero : p[n] = 0
    · rw [dite_eq_left hzero]
      have hi := ih (by omega) (by
        intro i hi hni
        by_cases h : i = n
        · subst i; exact hzero
        · exact hz i hi (by omega))
      cases kind <;>
        simp [arithmeticCost, ArithmeticOp.costKind] at hi ⊢ <;> omega
    · rw [dite_eq_right hzero]
      cases kind <;> simp [arithmeticCost, ArithmeticOp.costKind]

/-- Final prefix extraction makes no additional arithmetic requests. -/
theorem profileArithmetic_canonicalRawProgram (p : Raw F) :
    (profileArithmetic (canonicalRawProgram p)).2 =
      (profileArithmetic (lastNonzeroProgram p)).2 := by
  simp only [canonicalRawProgram, profileArithmetic_bind]
  split <;> simp

/-- Canonicalization reads and tests at most every coefficient, with one terminal tick. -/
theorem profileArithmetic_canonicalRawProgram_le (p : Raw F) (kind : ArithmeticCostKind) :
    (profileArithmetic (canonicalRawProgram p)).2 kind ≤
      if kind = .coefficientRead ∨ kind = .eq then p.size
      else if kind = .metadata then p.size + 1 else 0 := by
  rw [profileArithmetic_canonicalRawProgram]
  exact profileArithmetic_lastNonzeroFromProgram_le p p.size _ _ kind

/-- The reverse scan has an exact profile determined by the final nonzero index. -/
theorem profileArithmetic_lastNonzeroFromProgram (p : Raw F) (n : ℕ)
    (hn : n ≤ p.size) (hz : ∀ i, (hi : i < p.size) → n ≤ i → p[i] = 0) :
    (profileArithmetic (lastNonzeroFromProgram p n hn hz)).2 = fun kind =>
      let reads := match p.lastNonzero with | none => n | some i => n - i.val
      if kind = .coefficientRead ∨ kind = .eq then reads
      else if kind = .metadata then reads + if p.lastNonzero.isNone then 1 else 0 else 0 := by
  induction n with
  | zero =>
    have hp : p.lastNonzero = none := Raw.Trim.lastNonzero_none (fun i hi => hz i hi (by omega))
    rw [profileArithmetic_lastNonzeroFromProgram_zero]
    funext kind
    cases kind <;> simp [hp, arithmeticCost, ArithmeticOp.costKind]
  | succ n ih =>
    rw [profileArithmetic_lastNonzeroFromProgram_succ]
    by_cases hzero : p[n] = 0
    · rw [dite_eq_left hzero]
      rw [ih (by omega) (by
        intro i hi hni
        by_cases h : i = n
        · subst i; exact hzero
        · exact hz i hi (by omega))]
      cases hp : p.lastNonzero with
      | none =>
        funext kind
        cases kind <;> simp [arithmeticCost, ArithmeticOp.costKind] <;> omega
      | some i =>
        have hin : i.val < n := by
          have hne := (Raw.Trim.lastNonzero_some_iff.mp hp).1
          by_contra h
          have hni : n ≤ i.val := by omega
          by_cases heq : i.val = n
          · apply hne
            change p[i.val] = 0
            exact (getElem_congr_idx heq).trans hzero
          · exact hne (hz i.val i.isLt (by omega))
        funext kind
        cases kind <;> simp [arithmeticCost, ArithmeticOp.costKind] <;> omega
    · rw [dite_eq_right hzero]
      have hp : p.lastNonzero = some ⟨n, by omega⟩ :=
        Raw.Trim.lastNonzero_some_iff.mpr ⟨hzero, fun j hj hnj => hz j hj (by
          change n < j at hnj
          omega)⟩
      funext kind
      cases kind <;> simp [hp, arithmeticCost, ArithmeticOp.costKind]

/-- Canonicalization requests precisely the trailing-zero suffix and its preceding coefficient. -/
theorem profileArithmetic_canonicalRawProgram_exact (p : Raw F) :
    (profileArithmetic (canonicalRawProgram p)).2 = fun kind =>
      let reads := match p.lastNonzero with | none => p.size | some i => p.size - i.val
      if kind = .coefficientRead ∨ kind = .eq then reads
      else if kind = .metadata then reads + if p.lastNonzero.isNone then 1 else 0 else 0 := by
  rw [profileArithmetic_canonicalRawProgram]
  exact profileArithmetic_lastNonzeroFromProgram p p.size _ _

end CompPoly.Arithmetic
