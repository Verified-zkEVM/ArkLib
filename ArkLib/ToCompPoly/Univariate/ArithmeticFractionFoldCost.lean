/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticFractionFold

/-!
# Instruction profiles of padded coefficient folds

Exact recurrences retain the selected accumulator arrays. Width bounds apply separately to
additions, coefficient reads and designated control ticks. The fraction bound applies to each
supported cost coordinate, not to their sum. Array allocation and machine index arithmetic
are outside these instruction profiles.
-/

@[expose] public section

open OracleComp OracleSpec
namespace CompPoly.Arithmetic

variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- The empty accumulating traversal returns its input without instructions. -/
theorem profileArithmetic_sumRawFrom_nil (acc : CPolynomial.Raw F) :
    profileArithmetic (sumRawFrom [] acc) = (acc, 0) := by simp [sumRawFrom]

/-- A selected array charges one cell tick, its padded addition and the remaining traversal. -/
theorem profileArithmetic_sumRawFrom_cons
    (p : CPolynomial.Raw F) (ps : List (CPolynomial.Raw F)) (acc : CPolynomial.Raw F) :
    (profileArithmetic (sumRawFrom (p :: ps) acc)).2 =
      arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) +
        (profileArithmetic (addRaw acc p)).2 +
          (profileArithmetic (sumRawFrom ps (CPolynomial.Raw.addRaw acc p))).2 := by
  funext kind
  simp [sumRawFrom, List.foldlM_cons, profileArithmetic_bind, Nat.add_assoc]

/-- The padded sum adds its initialization tick to the accumulating traversal profile. -/
theorem profileArithmetic_sumRaw (ps : List (CPolynomial.Raw F)) :
    (profileArithmetic (sumRaw ps)).2 =
      arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) +
        (profileArithmetic (sumRawFrom ps #[])).2 := by
  simp [sumRaw, profileArithmetic_bind]

/-- A common coefficient-count bound gives separate addition, read and control bounds. -/
theorem profileArithmetic_sumRawFrom_le (ps : List (CPolynomial.Raw F))
    (acc : CPolynomial.Raw F) (d : ℕ) (hacc : acc.size ≤ d)
    (hps : ∀ p ∈ ps, p.size ≤ d) (kind : ArithmeticCostKind) :
    (profileArithmetic (sumRawFrom ps acc)).2 kind ≤
      if kind = .add then ps.length * d
      else if kind = .coefficientRead then 2 * (ps.length * d)
      else if kind = .metadata then ps.length * (d + 2) else 0 := by
  induction ps generalizing acc with
  | nil => simp [profileArithmetic_sumRawFrom_nil]
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hm : max acc.size p.size ≤ d := max_le hacc hp
    have ha : (CPolynomial.Raw.addRaw acc p).size ≤ d := by
      rw [CPolynomial.Raw.size_addRaw]
      exact hm
    have ht := ih _ ha (fun q hq => hps q (List.mem_cons_of_mem p hq))
    rw [profileArithmetic_sumRawFrom_cons]
    cases kind <;>
      simp [profileArithmetic_addRaw, arithmeticCost, ArithmeticOp.costKind,
        Nat.add_mul, Nat.mul_add] at ht ⊢ <;> omega


/-- A padded sum has a linear bound in its input count and retained maximum width. -/
theorem profileArithmetic_sumRaw_le (ps : List (CPolynomial.Raw F))
    (d : ℕ) (hps : ∀ p ∈ ps, p.size ≤ d) (kind : ArithmeticCostKind) :
    (profileArithmetic (sumRaw ps)).2 kind ≤
      if kind = .add then ps.length * d
      else if kind = .coefficientRead then 2 * (ps.length * d)
      else if kind = .metadata then ps.length * (d + 2) + 1 else 0 := by
  have ht := profileArithmetic_sumRawFrom_le ps #[] d (by simp) hps kind
  rw [profileArithmetic_sumRaw]
  cases kind <;> simp [arithmeticCost, ArithmeticOp.costKind] at ht ⊢ <;> omega

end CompPoly.Arithmetic

namespace CompPoly.Arithmetic

variable {F : Type} [CommSemiring F] [Sub F] [Inv F] [DecidableEq F]

/-- The coefficient-pair circuit charges its three convolutions and one padded addition. -/
theorem profileArithmetic_fractionCombine (p q : FractionPair (CPolynomial.Raw F)) :
    (profileArithmetic (fractionCombine p q)).2 =
      (profileArithmetic (mulRaw p.numerator q.denominator)).2 +
        (profileArithmetic (mulRaw p.denominator q.numerator)).2 +
          (profileArithmetic (addRaw
            (CPolynomial.Raw.mulRaw p.numerator q.denominator)
            (CPolynomial.Raw.mulRaw p.denominator q.numerator))).2 +
          (profileArithmetic (mulRaw p.denominator q.denominator)).2 := by
  funext kind
  simp [fractionCombine, Nat.add_assoc]

/-- The empty fraction fold charges only its terminal traversal tick. -/
theorem profileArithmetic_fractionSum_nil :
    (profileArithmetic (fractionSum ([] : List (FractionPair (CPolynomial.Raw F))))).2 =
      arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) := by
  simp [fractionSum_nil]

/-- A fresh cell adds one traversal tick and its circuit to the tail profile. -/
theorem profileArithmetic_fractionSum_cons (p : FractionPair (CPolynomial.Raw F))
    (ps : List (FractionPair (CPolynomial.Raw F))) :
    (profileArithmetic (fractionSum (p :: ps))).2 =
      (profileArithmetic (fractionSum ps)).2 +
        arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) +
          (profileArithmetic (fractionCombine p (CPolynomial.Raw.fractionSum ps))).2 := by
  rw [fractionSum_cons, profileArithmetic_bind]
  dsimp only
  rw [profileArithmetic_fractionSum_fst]
  funext kind
  simp [profileArithmetic_bind, Nat.add_assoc]


/-- Each supported instruction coordinate has a linear bound for two-coefficient fresh factors. -/
theorem profileArithmetic_fractionCombine_le
    (p q : FractionPair (CPolynomial.Raw F)) (s : ℕ)
    (hp : p.numerator.size ≤ 2 ∧ p.denominator.size ≤ 2)
    (hq : q.numerator.size ≤ s + 1 ∧ q.denominator.size ≤ s + 1)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (fractionCombine p q)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .coefficientRead ∨ kind = .metadata then
        39 * (s + 1) else 0 := by
  have h₁ := profileArithmetic_mulRaw_le_of_size_le_two p.numerator q.denominator hp.1 kind
  have h₂ := profileArithmetic_mulRaw_le_of_size_le_two p.denominator q.numerator hp.2 kind
  have h₃ := profileArithmetic_mulRaw_le_of_size_le_two p.denominator q.denominator hp.2 kind
  have hs₁ : (CPolynomial.Raw.mulRaw p.numerator q.denominator).size ≤ s + 2 := by
    have h := CPolynomial.Raw.size_mulRaw_le p.numerator q.denominator
    omega
  have hs₂ : (CPolynomial.Raw.mulRaw p.denominator q.numerator).size ≤ s + 2 := by
    have h := CPolynomial.Raw.size_mulRaw_le p.denominator q.numerator
    omega
  have hm := max_le hs₁ hs₂
  rw [profileArithmetic_fractionCombine]
  cases kind <;>
    simp [profileArithmetic_addRaw, Nat.mul_add] at h₁ h₂ h₃ ⊢ <;> omega

/-- Each supported instruction coordinate has a quadratic bound for affine fraction folds. -/
theorem profileArithmetic_fractionSum_le
    (ps : List (FractionPair (CPolynomial.Raw F)))
    (hps : ∀ p ∈ ps, p.numerator.size ≤ 2 ∧ p.denominator.size ≤ 2)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (fractionSum ps)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .coefficientRead ∨ kind = .metadata then
        40 * ps.length ^ 2 + 1 else 0 := by
  induction ps with
  | nil =>
    cases kind <;> simp [profileArithmetic_fractionSum_nil,
      arithmeticCost, ArithmeticOp.costKind]
  | cons p ps ih =>
    have hp := hps p (by simp)
    have htail : ∀ q ∈ ps, q.numerator.size ≤ 2 ∧ q.denominator.size ≤ 2 :=
      fun q hq => hps q (List.mem_cons_of_mem p hq)
    have ht := ih htail
    have hs := CPolynomial.Raw.size_fractionSum_le ps htail
    have hc := profileArithmetic_fractionCombine_le p
      (CPolynomial.Raw.fractionSum ps) ps.length hp hs kind
    rw [profileArithmetic_fractionSum_cons]
    cases kind <;>
      simp only [Pi.add_apply, arithmeticCost, ArithmeticOp.costKind, reduceCtorEq,
        or_self, or_false, or_true, ite_true, ite_false, List.length_cons] at ht hc ⊢ <;>
        first | omega | nlinarith

end CompPoly.Arithmetic
