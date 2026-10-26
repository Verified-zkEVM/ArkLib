/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.Raw.Fold
public import ArkLib.ToCompPoly.Univariate.ArithmeticConvolutionCost

/-!
# Measured padded coefficient folds

The programs execute certified primitive arithmetic through standard monadic list folds.
Fraction effects proceed from the tail toward the head; fresh affine factors stay on the
left of each convolution. Their results refine explicit raw arrays without canonicalizing
intermediate padding.
-/

@[expose] public section

open OracleComp OracleSpec

namespace CompPoly.Arithmetic

variable {F A B : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

private theorem profileArithmetic_foldlM_fst
    (step : A → B → OracleComp (ArithmeticSpec F) A) (f : A → B → A)
    (h : ∀ a b, (profileArithmetic (step a b)).1 = f a b) (xs : List B) (acc : A) :
    (profileArithmetic (xs.foldlM step acc)).1 = xs.foldl f acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldlM_cons, profileArithmetic_bind, h]
    exact ih (f acc x)

private theorem profileArithmetic_foldrM_fst
    (step : A → B → OracleComp (ArithmeticSpec F) B) (f : A → B → B)
    (h : ∀ a b, (profileArithmetic (step a b)).1 = f a b) (xs : List A) (acc : B) :
    (profileArithmetic (xs.foldrM step acc)).1 = xs.foldr f acc := by
  rw [List.foldrM]
  rw [profileArithmetic_foldlM_fst (f := fun b a => f a b) (h := fun b a => h a b)]
  exact List.foldr_eq_foldl_reverse.symm

/-- Accumulate padded coefficient arrays from the left, ticking each selected addition. -/
def sumRawFrom (ps : List (CPolynomial.Raw F)) (acc : CPolynomial.Raw F) :
    OracleComp (ArithmeticSpec F) (CPolynomial.Raw F) :=
  ps.foldlM (fun a p => do
    tick
    let r ← addRaw a p
    pure r.val) acc

/-- Sum padded coefficient arrays and charge one initialization tick. -/
def sumRaw (ps : List (CPolynomial.Raw F)) :
    OracleComp (ArithmeticSpec F) (CPolynomial.Raw F) := do
  tick
  sumRawFrom ps #[]

/-- Executing the accumulating program returns the explicit padded left fold. -/
theorem profileArithmetic_sumRawFrom_fst
    (ps : List (CPolynomial.Raw F)) (acc : CPolynomial.Raw F) :
    (profileArithmetic (sumRawFrom ps acc)).1 = ps.foldl CPolynomial.Raw.addRaw acc := by
  apply profileArithmetic_foldlM_fst
  intro a p
  simp [profileArithmetic_bind]

/-- Executing the padded sum program returns the generic coefficient-array sum. -/
theorem profileArithmetic_sumRaw_fst (ps : List (CPolynomial.Raw F)) :
    (profileArithmetic (sumRaw ps)).1 = CPolynomial.Raw.sumRaw ps := by
  simp [profileArithmetic_bind, sumRaw, CPolynomial.Raw.sumRaw, profileArithmetic_sumRawFrom_fst]

end CompPoly.Arithmetic

namespace CompPoly.Arithmetic

variable {F : Type} [CommSemiring F] [Sub F] [Inv F] [DecidableEq F]

/-- Cross-multiply raw coefficient pairs using three certified products with fresh factors
on the left, without canonicalizing either component. -/
def fractionCombine (fresh acc : FractionPair (CPolynomial.Raw F)) :
    OracleComp (ArithmeticSpec F) {p : FractionPair (CPolynomial.Raw F) //
      p = CPolynomial.Raw.fractionCombine fresh acc} := do
  let n₁ ← mulRaw fresh.numerator acc.denominator
  let n₂ ← mulRaw fresh.denominator acc.numerator
  let n ← addRaw n₁.val n₂.val
  let d ← mulRaw fresh.denominator acc.denominator
  pure ⟨⟨n.val, d.val⟩, by rw [n.property, n₁.property, n₂.property, d.property]; rfl⟩

/-- Fold raw coefficient fractions tail first through the standard monadic right fold,
charging one cell tick and one terminal tick while preserving all intermediate padding. -/
def fractionSum (ps : List (FractionPair (CPolynomial.Raw F))) :
    OracleComp (ArithmeticSpec F) (FractionPair (CPolynomial.Raw F)) := do
  tick
  ps.foldrM (fun fresh acc => do
    tick
    let r ← fractionCombine fresh acc
    pure r.val) ⟨#[], #[1]⟩

/-- The empty fraction fold charges its terminal tick and returns the raw neutral pair. -/
theorem fractionSum_nil : fractionSum ([] : List (FractionPair (CPolynomial.Raw F))) = (do
    tick
    pure ⟨#[], #[1]⟩) := rfl

/-- A nonempty fold performs the tail effects before the fresh cell's certified arithmetic. -/
theorem fractionSum_cons (p : FractionPair (CPolynomial.Raw F))
    (ps : List (FractionPair (CPolynomial.Raw F))) :
    fractionSum (p :: ps) = (do
      let acc ← fractionSum ps
      tick
      let r ← fractionCombine p acc
      pure r.val) := by
  simp only [fractionSum, List.foldrM_cons, bind_assoc]

private theorem profileArithmetic_fractionSumFold_fst
    (ps : List (FractionPair (CPolynomial.Raw F))) :
    (profileArithmetic (ps.foldrM (fun fresh acc => do
      tick
      let r ← fractionCombine fresh acc
      pure r.val) ⟨#[], #[1]⟩)).1 = CPolynomial.Raw.fractionSum ps := by
  apply profileArithmetic_foldrM_fst
  intro fresh acc
  simp [profileArithmetic_bind]

/-- Executing the measured fraction fold returns the explicit generic raw fraction fold. -/
theorem profileArithmetic_fractionSum_fst
    (ps : List (FractionPair (CPolynomial.Raw F))) :
    (profileArithmetic (fractionSum ps)).1 = CPolynomial.Raw.fractionSum ps := by
  rw [fractionSum, profileArithmetic_bind]
  exact profileArithmetic_fractionSumFold_fst ps

end CompPoly.Arithmetic
