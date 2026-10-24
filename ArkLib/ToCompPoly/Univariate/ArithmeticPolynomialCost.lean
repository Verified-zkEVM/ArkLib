/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticPolynomial

import all CompPoly.Univariate.Raw.Ops

/-!
# Profiles of padded and canonical polynomial operations

The recurrences record executed coefficient requests and zero tests, including trailing
zeros and the terminal control step. They apply to every coefficient array.
-/

@[expose] public section

namespace CompPoly.Arithmetic
open OracleComp OracleSpec
variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- Constructing a padded affine row requests exactly its slope subtraction. -/
theorem profileArithmetic_affineRaw (a b : F) :
    profileArithmetic (affineRaw a b) =
      (⟨CPolynomial.Raw.affine a b, rfl⟩, arithmeticCost (ArithmeticOp.sub b a)) := by
  simp [affineRaw, CPolynomial.Raw.affine]

/-- Trimming charges one control step and, when nonempty, a read and zero test. -/
theorem profileArithmetic_trimRaw (p : CPolynomial.Raw F) :
    (profileArithmetic (trimRaw p)).2 =
      arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) +
        if p.size = 0 then 0 else
          arithmeticCost (.coefficientRead p (p.size - 1)) +
          arithmeticCost (.eq (p[p.size - 1]?.getD 0) 0) +
          if p[p.size - 1]?.getD 0 = 0 then (profileArithmetic (trimRaw p.pop)).2 else 0 := by
  by_cases hp : p.size = 0
  · rw [trimRaw]
    simp [hp]
  · by_cases hc : p[p.size - 1]?.getD 0 = 0
    · funext kind
      rw [trimRaw]
      simp [hp, hc, profileArithmetic_bind, Nat.add_assoc]
    · rw [trimRaw]
      simp [hp, hc, profileArithmetic_bind]

/-- Trimming reads and tests at most every coefficient, with one additional terminal tick. -/
theorem profileArithmetic_trimRaw_le (p : CPolynomial.Raw F) (kind : ArithmeticCostKind) :
    (profileArithmetic (trimRaw p)).2 kind ≤
      if kind = .coefficientRead ∨ kind = .eq then p.size
      else if kind = .metadata then p.size + 1 else 0 := by
  induction hs : p.size using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hp : p.size = 0
    · rw [profileArithmetic_trimRaw]
      cases kind <;> simp [hp, arithmeticCost, ArithmeticOp.costKind]
    · have hpop : p.pop.size < n := by simp only [Array.size_pop]; omega
      have hi := ih p.pop.size hpop p.pop rfl
      by_cases hc : p[p.size - 1]?.getD 0 = 0
      · rw [profileArithmetic_trimRaw]
        cases kind <;>
          simp [hp, hc, arithmeticCost, ArithmeticOp.costKind] at hi ⊢ <;> omega
      · rw [profileArithmetic_trimRaw]
        cases kind <;> simp [hp, hc, arithmeticCost, ArithmeticOp.costKind] <;> omega

/-- Canonicalization has exactly the trim profile. -/
theorem profileArithmetic_canonicalRaw (p : CPolynomial.Raw F) :
    (profileArithmetic (canonicalRaw p)).2 = (profileArithmetic (trimRaw p)).2 := by
  simp [canonicalRaw]

end CompPoly.Arithmetic

namespace CompPoly.Arithmetic
open OracleComp OracleSpec

section Operations
variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- A constant's profile is precisely the trim of its singleton coefficient array. -/
theorem profileArithmetic_constant (x : F) :
    (profileArithmetic (constant x)).2 = (profileArithmetic (trimRaw #[x])).2 := by
  simp [constant, profileArithmetic_canonicalRaw]

/-- A right fold charges the tail, selected cell program, and one control step. -/
theorem profileArithmetic_certifiedFoldr_cons {A B : Type} (f : A → B → B)
    (step : (a : A) → (b : B) → OracleComp (ArithmeticSpec F) {c : B // c = f a b})
    (x : A) (xs : List A) (b : B) :
    (profileArithmetic (certifiedFoldr f step (x :: xs) b)).2 =
      arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) +
        (profileArithmetic (certifiedFoldr f step xs b)).2 +
        (profileArithmetic (step x (xs.foldr f b))).2 := by
  funext kind
  simp [certifiedFoldr, profileArithmetic_bind, Nat.add_assoc]

/-- Constant construction reads and tests at most its singleton coefficient. -/
theorem profileArithmetic_constant_le (x : F) (kind : ArithmeticCostKind) :
    (profileArithmetic (constant x)).2 kind ≤
      if kind = .coefficientRead ∨ kind = .eq then 1
      else if kind = .metadata then 2 else 0 := by
  simpa [profileArithmetic_constant] using profileArithmetic_trimRaw_le #[x] kind

end Operations

section AddGroup
variable {F : Type} [AddGroup F] [Mul F] [Inv F] [DecidableEq F]

/-- Negation reads each coefficient and subtracts it from zero. -/
theorem profileArithmetic_negRaw (p : CPolynomial.Raw F) :
    (profileArithmetic (negRaw p)).2 = fun kind ↦
      if kind = .sub ∨ kind = .coefficientRead then p.size
      else if kind = .metadata then p.size + 1 else 0 := by
  funext kind
  cases kind <;>
    simp [negRaw, profileArithmetic_certifiedOfFn,
      arithmeticCost, ArithmeticOp.costKind]

/-- Padded subtraction charges coefficient negation and addition, with no trailing-zero tests. -/
theorem profileArithmetic_subRaw (p q : CPolynomial.Raw F) :
    (profileArithmetic (subRaw p q)).2 = fun kind ↦
      let m := max p.size q.size
      if kind = .add then m
      else if kind = .sub then q.size
      else if kind = .coefficientRead then q.size + 2 * m
      else if kind = .metadata then q.size + m + 2 else 0 := by
  have hneg : (CPolynomial.Raw.neg q).size = q.size := by simp [CPolynomial.Raw.neg]
  funext kind
  cases kind <;>
    simp [subRaw, profileArithmetic_negRaw, profileArithmetic_addRaw, hneg,
      Nat.add_assoc, Nat.add_left_comm]

end AddGroup

section Semiring
variable {F : Type} [Semiring F] [Sub F] [Inv F] [DecidableEq F]

/-- Canonical multiplication adds a trim to its padded convolution profile. -/
theorem profileArithmetic_mulPolynomial (p q : CPolynomial F) :
    (profileArithmetic (mulPolynomial p q)).2 =
      (profileArithmetic (mulRaw p.val q.val)).2 +
        (profileArithmetic (trimRaw (CPolynomial.Raw.mulRaw p.val q.val))).2 := by
  funext kind
  simp [mulPolynomial, profileArithmetic_canonicalRaw]

end Semiring

section Ring
variable {F : Type} [Ring F] [Inv F] [DecidableEq F]

/-- Canonical subtraction charges negation, padded addition, and its final trim. -/
theorem profileArithmetic_subPolynomial (p q : CPolynomial F) :
    (profileArithmetic (subPolynomial p q)).2 =
      (profileArithmetic (negRaw q.val)).2 +
        (profileArithmetic (addRaw p.val (CPolynomial.Raw.neg q.val))).2 +
        (profileArithmetic (trimRaw
          (CPolynomial.Raw.addRaw p.val (CPolynomial.Raw.neg q.val)))).2 := by
  funext kind
  simp [subPolynomial, profileArithmetic_canonicalRaw, Nat.add_assoc]

/-- Canonical subtraction has linear coefficient, equality-test, and control bounds. -/
theorem profileArithmetic_subPolynomial_le (p q : CPolynomial F) (kind : ArithmeticCostKind) :
    (profileArithmetic (subPolynomial p q)).2 kind ≤
      let m := max p.val.size q.val.size
      if kind = .add then m
      else if kind = .sub then q.val.size
      else if kind = .coefficientRead then q.val.size + 3 * m
      else if kind = .eq then m
      else if kind = .metadata then q.val.size + 2 * m + 3 else 0 := by
  have hneg : (CPolynomial.Raw.neg q.val).size = q.val.size := by
    simp [CPolynomial.Raw.neg]
  have hsize : (CPolynomial.Raw.addRaw p.val (CPolynomial.Raw.neg q.val)).size =
      max p.val.size q.val.size := by
    rw [CPolynomial.Raw.add_size, hneg]
  have ht := profileArithmetic_trimRaw_le
    (CPolynomial.Raw.addRaw p.val (CPolynomial.Raw.neg q.val)) kind
  cases kind <;>
    simp [profileArithmetic_subPolynomial, profileArithmetic_negRaw, profileArithmetic_addRaw,
      hneg, hsize] at ht ⊢ <;>
    omega

end Ring
end CompPoly.Arithmetic
