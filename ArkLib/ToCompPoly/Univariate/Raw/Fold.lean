/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.Data.Fraction
public import ArkLib.ToCompPoly.Univariate.Raw.Basic
public import ArkLib.ToCompPoly.Univariate.Raw.Size

import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops

/-!
# Padded coefficient sums and fraction folds

The explicit array operations refine formal polynomial sums and the generic unnormalized
fraction fold. Keeping fresh factors on the left bounds padded convolution work when those
factors are affine. No polynomial or fraction algebra instances are installed on raw arrays.
-/

@[expose] public section

namespace CompPoly.CPolynomial.Raw

/-- Sum coefficient arrays using a tail-recursive padded-add traversal. -/
def sumRaw {R : Type*} [Zero R] [Add R] (ps : List (Raw R)) : Raw R :=
  ps.foldl addRaw #[]

private theorem toPoly_foldl_addRaw {R : Type*} [Semiring R]
    (ps : List (Raw R)) (acc : Raw R) :
    (ps.foldl addRaw acc).toPoly = acc.toPoly + (ps.map toPoly).sum := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, ih, toPoly_addRaw, List.map_cons, List.sum_cons]
    exact _root_.add_assoc _ _ _

/-- Interpreting the padded array sum gives the sum of the formal polynomials. -/
theorem toPoly_sumRaw {R : Type*} [Semiring R] (ps : List (Raw R)) :
    (sumRaw ps).toPoly = (ps.map toPoly).sum := by
  rw [sumRaw, toPoly_foldl_addRaw]
  have h : toPoly (#[] : Raw R) = 0 := toPoly_zero
  rw [h, _root_.zero_add]

/-- Cross-multiply raw numerator/denominator pairs with each fresh factor on the left.
Padding is retained, so a zero polynomial need not be stored as an empty array. -/
def fractionCombine {R : Type*} [CommSemiring R]
    (fresh acc : FractionPair (Raw R)) : FractionPair (Raw R) :=
  ⟨addRaw (mulRaw fresh.numerator acc.denominator) (mulRaw fresh.denominator acc.numerator),
    mulRaw fresh.denominator acc.denominator⟩

/-- Fold raw coefficient fractions from the right while retaining all intermediate padding. -/
def fractionSum {R : Type*} [CommSemiring R]
    (ps : List (FractionPair (Raw R))) : FractionPair (Raw R) :=
  ps.foldr fractionCombine ⟨#[], #[1]⟩

/-- The circuit with fresh factors on the left represents unnormalized fraction addition. -/
theorem map_toPoly_fractionCombine {R : Type*} [CommSemiring R]
    (p q : FractionPair (Raw R)) :
    FractionPair.map toPoly (fractionCombine p q) =
      FractionPair.combine (FractionPair.map toPoly p) (FractionPair.map toPoly q) := by
  apply FractionPair.ext <;>
    simp [fractionCombine, FractionPair.map, FractionPair.combine,
      toPoly_addRaw, toPoly_mulRaw, mul_comm]

/-- Interpreting the raw fraction fold gives the generic formal fraction fold. -/
theorem map_toPoly_fractionSum {R : Type*} [CommSemiring R]
    (ps : List (FractionPair (Raw R))) :
    FractionPair.map toPoly (fractionSum ps) =
      FractionPair.sum (ps.map (FractionPair.map toPoly)) := by
  induction ps with
  | nil =>
    have h0 : toPoly (#[] : Raw R) = 0 := by
      change (0 : Raw R).toPoly = 0
      exact toPoly_zero
    have h1 : toPoly (#[1] : Raw R) = 1 := by
      change (1 : Raw R).toPoly = 1
      exact toPoly_one
    apply FractionPair.ext <;>
      simp only [fractionSum, List.foldr_nil, List.map_nil, FractionPair.sum_nil,
        FractionPair.map, FractionPair.unit, h0, h1]
  | cons p ps ih =>
    change FractionPair.map toPoly (fractionCombine p (fractionSum ps)) = _
    rw [map_toPoly_fractionCombine, ih, List.map_cons, FractionPair.sum_cons]

private theorem size_foldl_addRaw_le {R : Type*} [Zero R] [Add R]
    (ps : List (Raw R)) (acc : Raw R) (d : ℕ) (hacc : acc.size ≤ d)
    (hps : ∀ p ∈ ps, p.size ≤ d) : (ps.foldl addRaw acc).size ≤ d := by
  induction ps generalizing acc with
  | nil => exact hacc
  | cons p ps ih =>
    rw [List.foldl_cons]
    apply ih
    · rw [size_addRaw]
      exact max_le hacc (hps p (by simp))
    · intro q hq
      exact hps q (List.mem_cons_of_mem p hq)

/-- A padded sum retains at most the common bound on its input coefficient counts. -/
theorem size_sumRaw_le {R : Type*} [Zero R] [Add R]
    (ps : List (Raw R)) (d : ℕ) (hps : ∀ p ∈ ps, p.size ≤ d) :
    (sumRaw ps).size ≤ d :=
  size_foldl_addRaw_le ps #[] d (by simp) hps

/-- Fractions with at most two coefficients per fresh component grow by at most one
coefficient per fold step, including all zero denominators and padded zero arrays. -/
theorem size_fractionSum_le {R : Type*} [CommSemiring R]
    (ps : List (FractionPair (Raw R)))
    (hps : ∀ p ∈ ps, p.numerator.size ≤ 2 ∧ p.denominator.size ≤ 2) :
    (fractionSum ps).numerator.size ≤ ps.length + 1 ∧
      (fractionSum ps).denominator.size ≤ ps.length + 1 := by
  induction ps with
  | nil => simp [fractionSum]
  | cons p ps ih =>
    have hp := hps p (by simp)
    have ht := ih (fun q hq => hps q (List.mem_cons_of_mem p hq))
    have h₁ := size_mulRaw_le p.numerator (fractionSum ps).denominator
    have h₂ := size_mulRaw_le p.denominator (fractionSum ps).numerator
    have h₃ := size_mulRaw_le p.denominator (fractionSum ps).denominator
    constructor
    · change (addRaw (mulRaw p.numerator (fractionSum ps).denominator)
        (mulRaw p.denominator (fractionSum ps).numerator)).size ≤ _
      rw [size_addRaw]
      apply max_le <;> simp only [List.length_cons] <;> omega
    · change (mulRaw p.denominator (fractionSum ps).denominator).size ≤ _
      simp only [List.length_cons]
      omega

end CompPoly.CPolynomial.Raw
