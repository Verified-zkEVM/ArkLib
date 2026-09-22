/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedBidegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedDegree

/-!
# Acceptance tests for polynomials of bounded degree with a capped variable

The examples count capped exponents on `Fin 2` and compute a dimension, state the dimension in
the form `(c + 1) * (b + 1) - c * (c + 1) / 2`, check that the cap is no condition when it exceeds
the bound on the degree, derive the total-degree and `X 1`-degree bounds of the monomial map and
the linear lift, and show that surjectivity of the monomial map needs a positive cap.
-/

open MvPolynomial

namespace CappedDegreeTest

/-- In two variables with cap `1` on the second, there are `5` exponents of degree at most `2`:
`1`, `x₀`, `x₀ ^ 2`, `x₁` and `x₀ * x₁`. -/
example : (cappedDegreeExponents (Fin 2) 1 2 1).ncard = 5 := by
  have h := Finsupp.two_mul_ncard_setOf_degree_le_and_apply_one_le 2 1 (by norm_num)
  change 2 * (cappedDegreeExponents (Fin 2) 1 2 1).ncard = _ at h
  omega

/-- The corresponding polynomials form a space of dimension `5`. -/
example : Module.finrank ℚ (restrictCappedDegree (Fin 2) ℚ 1 2 1) = 5 := by
  have h := Finsupp.two_mul_ncard_setOf_degree_le_and_apply_one_le 2 1 (by norm_num)
  rw [finrank_restrictCappedDegree]
  change 2 * (cappedDegreeExponents (Fin 2) 1 2 1).ncard = _ at h
  omega

/-- For `c ≤ b`, the capped polynomials on `Fin 2` have dimension
`(c + 1) * (b + 1) - c * (c + 1) / 2`. -/
example {k : Type*} [Field k] (b c : ℕ) (hcb : c ≤ b) :
    Module.finrank k (restrictCappedDegree (Fin 2) k 1 b c) =
      (c + 1) * (b + 1) - c * (c + 1) / 2 := by
  have h := Finsupp.two_mul_ncard_setOf_degree_le_and_apply_one_le b c hcb
  rw [finrank_restrictCappedDegree]
  change 2 * (cappedDegreeExponents (Fin 2) 1 b c).ncard = _ at h
  have hdiv : c * (c + 1) / 2 * 2 = c * (c + 1) :=
    Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self c))
  zify [show c * (c + 1) / 2 ≤ (c + 1) * (b + 1) by nlinarith,
    show c ≤ 2 * b + 2 by omega] at h hdiv ⊢
  nlinarith

/-- A cap at least the bound on the degree is no condition. -/
example {σ : Type*} (i : σ) (b : ℕ) :
    cappedDegreeExponents σ i b (b + 1) = {e | e.degree ≤ b} :=
  cappedDegreeExponents_eq_setOf_degree_le (Nat.le_succ b)

/-- The bounds of a product of capped polynomials add. -/
example {P Q : MvPolynomial (Fin 2) ℚ} (hP : P ∈ restrictCappedDegree (Fin 2) ℚ 1 2 1)
    (hQ : Q ∈ restrictCappedDegree (Fin 2) ℚ 1 1 1) :
    P * Q ∈ restrictCappedDegree (Fin 2) ℚ 1 3 2 :=
  mul_mem_restrictCappedDegree hP hQ

/-- The monomial map of the capped exponents multiplies total degree by at most `b`. -/
example {k : Type*} [Field k] (b c : ℕ)
    (P : MvPolynomial (cappedDegreeExponents (Fin 2) 1 b c) k) :
    (monomialMap k _ P).totalDegree ≤ b * P.totalDegree :=
  Finset.sup_le fun _ he ↦ (monomialMap_mem_restrictCappedDegree le_rfl he).1

/-- The monomial map of the capped exponents multiplies total degree into `X 1`-degree at most
`c`. -/
example {k : Type*} [Field k] (b c : ℕ)
    (P : MvPolynomial (cappedDegreeExponents (Fin 2) 1 b c) k) :
    (monomialMap k _ P).degreeOf 1 ≤ c * P.totalDegree :=
  degreeOf_le_iff.mpr fun _ he ↦ (monomialMap_mem_restrictCappedDegree le_rfl he).2

/-- A capped polynomial has a linear preimage under the monomial map. -/
example {k : Type*} [Field k] (b c : ℕ) (P : MvPolynomial (Fin 2) k)
    (hP : P ∈ restrictCappedDegree (Fin 2) k 1 b c) :
    monomialMap k _ (monomialLift P hP) = P ∧ (monomialLift P hP).totalDegree ≤ 1 :=
  ⟨monomialMap_monomialLift P hP, totalDegree_monomialLift_le_one P hP⟩

/-- `monomialMap_cappedDegreeExponents_surjective` needs `0 < c`: with cap `0` no exponent
involves `1`, so the points `0` and `Pi.single 1 1` have the same point of monomial values, and
`X 1` is not in the image. -/
example : ¬Function.Surjective (monomialMap ℚ (cappedDegreeExponents (Fin 2) 1 1 0)) := by
  intro h
  obtain ⟨P, hP⟩ := h (X 1)
  have hpt : monomialPoint (cappedDegreeExponents (Fin 2) 1 1 0) (0 : Fin 2 → ℚ) =
      monomialPoint _ (Pi.single 1 1) := funext fun m ↦ by
    rw [monomialPoint_apply, monomialPoint_apply]
    refine Finsupp.prod_congr fun v hv ↦ ?_
    have hv1 : v ≠ 1 := by
      rintro rfl
      exact Finsupp.mem_support_iff.mp hv (Nat.le_zero.mp m.2.2)
    rw [Pi.single_eq_of_ne hv1, Pi.zero_apply]
  have h0 := aeval_monomialPoint (R := ℚ) (0 : Fin 2 → ℚ) P
  have h1 := aeval_monomialPoint (R := ℚ) (Pi.single 1 (1 : ℚ)) P
  rw [hP, aeval_X] at h0 h1
  rw [hpt, h1] at h0
  simp at h0

end CappedDegreeTest
