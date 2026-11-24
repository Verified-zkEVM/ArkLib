/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticCost
public import CompPoly.Univariate.Basic

import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
-- `mulRaw` uses `CPolynomial.Raw.mulRawFast_eq_ofFn`, which is private in this module.
import all CompPoly.Univariate.Raw.Ops

/-!
# Measured canonical polynomial arithmetic

Measured raw multiplication follows the coefficient windows of CompPoly's `mulRawFast` and
certifies the padded result. Trimming charges each coefficient read and zero test.
Coefficient negation uses subtraction from zero.
-/

@[expose] public section

namespace CompPoly.Arithmetic
open OracleComp OracleSpec

section Operations
variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

private theorem trim_push_zero {R : Type} [Zero R] [DecidableEq R]
    (p : CPolynomial.Raw R) :
    CPolynomial.Raw.trim (p.push 0) = p.trim := by
  apply CPolynomial.Raw.Trim.eq_of_equiv
  intro i
  by_cases hi : i < p.size
  · simp [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_push,
      hi, Nat.ne_of_lt hi]
  · by_cases heq : i = p.size
    · subst i
      simp [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?]
    · have hgt : p.size < i := by omega
      simp [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?,
        Nat.not_lt.mpr hgt.le, Nat.not_lt.mpr (by omega : p.size + 1 ≤ i)]

/-- Remove trailing zero coefficients, charging every read and equality test. -/
def trimRaw (p : CPolynomial.Raw F) :
    OracleComp (ArithmeticSpec F) {q : CPolynomial.Raw F // q = p.trim} := do
  tick
  if hp : p.size = 0 then
    pure ⟨#[], by
      have h : p = #[] := Array.eq_empty_of_size_eq_zero hp
      rw [h]
      exact CPolynomial.Raw.Trim.canonical_empty.symm⟩
  else
    let a ← coefficientRead p (p.size - 1)
    let e ← eq a.val 0
    if he : e.val = true then
      let q ← trimRaw p.pop
      have hzero : p[p.size - 1]?.getD 0 = 0 := by
        rw [← a.property]
        exact of_decide_eq_true (e.property.symm.trans he)
      have htrim : CPolynomial.Raw.trim p.pop = p.trim := by
        obtain ⟨baseArr, c, rfl⟩ := Array.exists_push_of_size_pos (Nat.zero_lt_of_ne_zero hp)
        have hc : c = 0 := by simpa using hzero
        subst c
        simpa using (trim_push_zero baseArr).symm
      pure ⟨q.val, q.property.trans htrim⟩
    else
      have hnonzero : p[p.size - 1]?.getD 0 ≠ 0 := by
        rw [← a.property]
        intro ha
        apply he
        rw [e.property, ha]
        simp
      pure ⟨p, by
        obtain ⟨baseArr, c, rfl⟩ := Array.exists_push_of_size_pos (Nat.zero_lt_of_ne_zero hp)
        have hc : c ≠ 0 := by simpa using hnonzero
        exact (CPolynomial.Raw.Trim.push_trim baseArr c hc).symm⟩
termination_by p.size

/-- Trim a raw array and certify its canonical polynomial. -/
def canonicalRaw (p : CPolynomial.Raw F) :
    OracleComp (ArithmeticSpec F) {q : CPolynomial F // q = CPolynomial.ofArray p} := do
  let q ← trimRaw p
  let r : CPolynomial F := ⟨q.val, by
    rw [q.property]
    exact CPolynomial.Raw.Trim.isCanonical_trim p⟩
  pure ⟨r, by apply Subtype.ext; exact q.property⟩

/-- Construct a constant polynomial with its canonicalization charged. -/
def constant (x : F) :
    OracleComp (ArithmeticSpec F) {q : CPolynomial F // q = CPolynomial.C x} := do
  let q ← canonicalRaw #[x]
  pure ⟨q.val, by rw [q.property]; rfl⟩

/-- Traverse a list from the right, ticking each cell and the terminal step. -/
def certifiedFoldr {A B : Type} (f : A → B → B)
    (step : (a : A) → (b : B) → OracleComp (ArithmeticSpec F) {c : B // c = f a b}) :
    (xs : List A) → (b : B) →
      OracleComp (ArithmeticSpec F) {c : B // c = xs.foldr f b}
  | [], b => do
    tick
    pure ⟨b, rfl⟩
  | x :: xs, b => do
    tick
    let c ← certifiedFoldr f step xs b
    let d ← step x c.val
    pure ⟨d.val, by rw [d.property, c.property]; rfl⟩

/-- Accumulate `n` terms for output entry `k`, starting at left coefficient index `lo`.
Each term charges two coefficient reads, one multiplication, one addition, and one tick. -/
def convolutionEntry (p q : CPolynomial.Raw F) (k lo : ℕ) :
    (n : ℕ) → OracleComp (ArithmeticSpec F) {r : F // r =
      n.fold (fun t _ acc ↦ acc + p[lo + t]?.getD 0 * q[k - (lo + t)]?.getD 0) 0}
  | 0 => pure ⟨0, by simp⟩
  | n + 1 => do
    let acc ← convolutionEntry p q k lo n
    tick
    let a ← coefficientRead p (lo + n)
    let b ← coefficientRead q (k - (lo + n))
    let c ← mul a.val b.val
    let r ← add acc.val c.val
    pure ⟨r.val, by rw [r.property, acc.property, c.property, a.property, b.property,
      Nat.fold_succ]⟩

end Operations

section AddGroup
variable {F : Type} [AddGroup F] [Mul F] [Inv F] [DecidableEq F]

/-- Negate each coefficient through an explicit subtraction from zero. -/
def negRaw (p : CPolynomial.Raw F) :
    OracleComp (ArithmeticSpec F) {q : CPolynomial.Raw F // q = CPolynomial.Raw.neg p} := do
  let q ← certifiedOfFn (fun i : Fin p.size ↦ -p[i]) fun i ↦ do
    let a ← coefficientRead p i.val
    let b ← sub 0 a.val
    pure ⟨b.val, by simpa [a.property] using b.property⟩
  pure ⟨q.val, by
    rw [q.property]
    apply Array.ext
    · simp [CPolynomial.Raw.neg]
    · intro i hi hi'
      simp [CPolynomial.Raw.neg]⟩

end AddGroup

section Semiring
variable {F : Type} [Semiring F] [Sub F] [Inv F] [DecidableEq F]

/-- Multiply raw arrays by the coefficient windows of CompPoly's `mulRawFast`.
The output keeps the padding of `CPolynomial.Raw.mulRaw`, including for empty inputs. -/
def mulRaw (p q : CPolynomial.Raw F) :
    OracleComp (ArithmeticSpec F) {r : CPolynomial.Raw F // r = CPolynomial.Raw.mulRaw p q} := do
  if hp : p.size = 0 then
    tick
    pure ⟨#[], by
      rw [CPolynomial.Raw.mulRaw_eq_mulRawFast]
      simp [CPolynomial.Raw.mulRawFast, hp]⟩
  else
    let r ← certifiedOfFn (n := q.size + p.size - 1) _ fun k ↦
      let lo := k.val + 1 - q.size
      convolutionEntry p q k.val lo (min (k.val + 1) p.size - lo)
    pure ⟨r.val, by
      rw [r.property, CPolynomial.Raw.mulRaw_eq_mulRawFast,
        CPolynomial.Raw.mulRawFast_eq_ofFn q hp]
      simp only [Array.getD_eq_getD_getElem?]⟩

/-- Multiply canonical polynomials and charge the final trim. -/
def mulPolynomial (p q : CPolynomial F) :
    OracleComp (ArithmeticSpec F) {r : CPolynomial F // r = p * q} := do
  let a ← mulRaw p.val q.val
  let r ← canonicalRaw a.val
  pure ⟨r.val, by rw [r.property, a.property]; rfl⟩

end Semiring

section Ring
variable {F : Type} [Ring F] [Inv F] [DecidableEq F]

/-- Subtract canonical polynomials and charge negation, addition, and trimming. -/
def subPolynomial (p q : CPolynomial F) :
    OracleComp (ArithmeticSpec F) {r : CPolynomial F // r = p - q} := do
  let n ← negRaw q.val
  let a ← addRaw p.val n.val
  let r ← canonicalRaw a.val
  pure ⟨r.val, by rw [r.property, a.property, n.property]; rfl⟩

end Ring

end CompPoly.Arithmetic
