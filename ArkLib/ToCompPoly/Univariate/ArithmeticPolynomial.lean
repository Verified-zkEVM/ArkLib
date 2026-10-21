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
import all CompPoly.Univariate.Raw.Ops

/-!
# Measured canonical polynomial arithmetic

Raw convolution preserves padding until the requested canonicalization. Trimming exposes
all coefficient reads and zero tests; coefficient negation uses subtraction from zero.
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

/-- Accumulate consecutive rows of the padded convolution. -/
def mulRawFrom (p q : CPolynomial.Raw F) (i : ℕ) (acc : CPolynomial.Raw F) :
    (t : ℕ) → OracleComp (ArithmeticSpec F) {r : CPolynomial.Raw F // r =
      (List.range' i t).foldl (fun a j ↦ CPolynomial.Raw.addRaw a
        (CPolynomial.Raw.mulPowX j (CPolynomial.Raw.smul (p[j]?.getD 0) q))) acc}
  | 0 => do
    tick
    pure ⟨acc, rfl⟩
  | t + 1 => do
    tick
    let a ← coefficientRead p i
    let b ← smulRaw a.val q
    let c ← addRaw acc (CPolynomial.Raw.mulPowX i b.val)
    let r ← mulRawFrom p q (i + 1) c.val t
    pure ⟨r.val, by rw [r.property, c.property, b.property, a.property]; rfl⟩

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

private theorem toList_zipIdx_eq_range {R : Type} [Zero R] (p : Array R) :
    p.zipIdx.toList = (List.range' 0 p.size).map (fun i ↦ (p[i]?.getD 0, i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have h : i < p.size := by simpa using hi
    simp [List.getElem_range', h]

/-- Multiply coefficient arrays without trimming intermediate rows. -/
def mulRaw (p q : CPolynomial.Raw F) :
    OracleComp (ArithmeticSpec F) {r : CPolynomial.Raw F // r = CPolynomial.Raw.mulRaw p q} := do
  let r ← mulRawFrom p q 0 #[] p.size
  pure ⟨r.val, by
    rw [r.property, CPolynomial.Raw.mulRaw, ← Array.foldl_toList,
      toList_zipIdx_eq_range, List.foldl_map]⟩

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
