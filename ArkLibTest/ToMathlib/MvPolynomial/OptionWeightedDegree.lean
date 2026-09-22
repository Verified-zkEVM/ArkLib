/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree
import ArkLib.Data.MvPolynomial.WeightedDegree
import ArkLib.Data.MvPolynomial.WeightedDegree.Products
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance tests for weighted degree through `optionEquivRight`

The examples evaluate the split-exponent weight formula, compute the image of a monomial and its
total degree, derive the product and divisor statements for the weight that ignores `none` from
the all-weight theorems, and show that the product statement fails over `ZMod 4`, which has zero
divisors.
-/

open MvPolynomial

/-- The exponent vector with `none`-coordinate `3` and `some 0`-coordinate `2` has weight
`5 * 3 + 2 * 7 = 29` when `none` has weight `5` and `some 0` has weight `7`. -/
example :
    ((Finsupp.single (0 : Fin 1) 2).optionElim 3).weight
      (fun v : Option (Fin 1) ↦ v.elim 5 (fun _ ↦ 7)) = 29 := by
  rw [Finsupp.weight_optionElim]
  simp [Finsupp.weight_single]

/-- The weight-zero coordinate is ignored: `weight_optionElim_zero_one`, the case `c = 0`,
`w = 1`. -/
example (m : Fin 3 →₀ ℕ) (i : ℕ) :
    (m.optionElim i).weight (fun v ↦ v.elim 0 (fun _ ↦ 1)) = m.degree :=
  weight_optionElim_zero_one m i

/-- `X none ^ 5 * X (some 0)` is sent to `X 0` with coefficient `Polynomial.X ^ 5`. -/
example :
    optionEquivRight ℚ (Fin 1)
        (monomial (Finsupp.single none 5 + Finsupp.single (some 0) 1) (1 : ℚ)) =
      monomial (Finsupp.single 0 1) (Polynomial.monomial 5 1) := by
  rw [optionEquivRight_monomial]
  congr 1
  · ext j
    simp
  · simp

/-- The image of `X none ^ 5 * X (some 0)` has total degree one: the power of `none` is invisible
after moving it into the coefficient ring. -/
example :
    (optionEquivRight ℚ (Fin 1)
        (monomial (Finsupp.single none 5 + Finsupp.single (some 0) 1) (1 : ℚ))).totalDegree =
      1 := by
  rw [totalDegree_optionEquivRight, weightedTotalDegree_monomial _ _ _ one_ne_zero]
  rw [map_add]
  simp [Finsupp.weight_single]

/-- Over a ring without zero divisors, the weighted degree for the weight that ignores `none` is
additive on products: `weightedTotalDegree_mul` for that weight. -/
example {R σ : Type*} [CommSemiring R] [NoZeroDivisors R]
    (p q : MvPolynomial (Option σ) R) (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) =
      p.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) +
        q.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) :=
  weightedTotalDegree_mul _ p q hp hq

/-- Over a ring without zero divisors, the weighted degree for the weight that ignores `none` is
monotone under divisibility into a nonzero polynomial: `weightedTotalDegree_le_of_dvd` for that
weight. The hypothesis `p ≠ 0` is unused. -/
example {R σ : Type*} [CommSemiring R] [NoZeroDivisors R]
    (p q : MvPolynomial (Option σ) R) (_hp : p ≠ 0) (hq : q ≠ 0) (hdiv : p ∣ q) :
    p.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) ≤
      q.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) :=
  weightedTotalDegree_le_of_dvd _ hdiv hq

/-- Without `NoZeroDivisors` the product statement fails: over `ZMod 4`, `p = 2 * X (some 0)` has
weighted degree one but `p * p = 0`. -/
example :
    let p : MvPolynomial (Option (Fin 1)) (ZMod 4) := monomial (Finsupp.single (some 0) 1) 2
    p ≠ 0 ∧
      (p * p).weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) ≠
        p.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) +
          p.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) := by
  intro p
  have h2 : (2 : ZMod 4) ≠ 0 := by decide
  have hpp : p * p = 0 := by
    simp only [p, monomial_mul_monomial]
    have : (2 : ZMod 4) * 2 = 0 := by decide
    rw [this, monomial_zero]
  refine ⟨by simpa [p] using h2, ?_⟩
  rw [hpp, weightedTotalDegree_monomial _ _ _ h2, weightedTotalDegree_zero]
  simp [Finsupp.weight_single]
