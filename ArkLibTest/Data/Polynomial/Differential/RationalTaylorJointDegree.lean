/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.RationalTaylorJointDegree

/-!
# Acceptance tests for the joint degree of rational Taylor numerators

The main example is the equation `y' + t y = 0` with a parameter `t`, written as `Y₁ + t Y₀`
over `ℚ[t]`. It has total jet degree `1` and coefficient degree `1` in `t`, so the numerator of
`c_l` has joint degree at most `2(l - 1)` for `l ≥ 2`, and with the exponent `2K` every common
numerator of `c_l` with `l < K` has joint degree at most `1 + 2K`.

The file also derives the bounds for all `l < K` at the exponent `2K`, through
`taylorExponentSufficient_two_mul`, including the form whose jet degree hypothesis is a weighted
total degree, and checks the bound for the constant equation
`Q = 1`, where `jetTotalDegree Q = 0`: no positivity of the jet degree is needed.

The constant center is needed for `coeffNatDegreeLE_universalTaylorResidual`: at the center `t`,
the residual of the equation `X`, whose coefficients are constant, has the coefficient `t`.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- With the exponent `2K`, bounds on the separant and on the numerators of `c_l` for `l < K`
give the bound `1 + 2K * b` on every common numerator of `c_l` with `l < K`. -/
example {F : Type*} [Field F] {r : ℕ} (center : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) (b K : ℕ)
    (hS : jointTotalDegree (initialJetSeparant center Q) ≤ b)
    (hN : ∀ l < K, jointTotalDegree (rationalTaylorNumeratorOver F center Q l) ≤
      (2 * (l - r) - 1) * b + 1) (l : Fin K) :
    jointTotalDegree (commonTaylorNumeratorOver F center Q (2 * K) l) ≤ 1 + 2 * K * b :=
  jointTotalDegree_commonTaylorNumeratorOver_le center Q b (2 * K) l
    (taylorExponentSufficient_two_mul r K l) hS (hN l l.isLt)

/-- The jet degree is the weighted total degree with weight `0` on `X` and `1` on each `Y_j`. -/
private theorem jetTotalDegree_eq_weightedTotalDegree {F : Type*} [CommSemiring F] {r : ℕ}
    (Q : DifferentialPolynomial F r) :
    jetTotalDegree Q = Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) := by
  unfold jetTotalDegree
  congr
  funext i
  cases i <;> rfl

/-- At a constant center, with the jet degree bounded as a weighted total degree and the default
exponent `2K`, every common numerator of `c_l` with `l < K` has joint degree at most
`1 + 2K * (v - 1 + h)`. -/
example {F : Type*} [Field F] {r : ℕ} (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (v h K : ℕ)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hQ : CoeffNatDegreeLE Q h) (l : Fin K) :
    jointTotalDegree (commonTaylorNumeratorOver F (Polynomial.C center) Q (2 * K) l) ≤
      1 + 2 * K * (v - 1 + h) :=
  jointTotalDegree_commonTaylorNumeratorOver_le_of_coeffNatDegreeLE center Q v h (2 * K) l
    (taylorExponentSufficient_two_mul r K l)
    ((jetTotalDegree_eq_weightedTotalDegree Q).trans_le hjet) hQ

/-- The equation `y' + t y = 0`, as `Y₁ + t Y₀` over `ℚ[t]`. -/
private abbrev scaledExpEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  X (some 1) + C Polynomial.X * X (some 0)

/-- `Y₁ + t Y₀` has total jet degree `1`. -/
private theorem jetTotalDegree_scaledExpEquation_le : jetTotalDegree scaledExpEquation ≤ 1 := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  rcases Finset.mem_union.mp (support_add hu) with hu | hu
  · rw [support_X, Finset.mem_singleton] at hu
    simp [hu, totalJetDegree_eq_sum, Finsupp.single_apply]
  · rw [C_mul_X_eq_monomial] at hu
    rw [Finset.mem_singleton.mp (support_monomial_subset hu)]
    simp [totalJetDegree_eq_sum, Finsupp.single_apply]

/-- The coefficients of `Y₁ + t Y₀` have degree at most `1` in `t`. -/
private theorem coeffNatDegreeLE_scaledExpEquation : CoeffNatDegreeLE scaledExpEquation 1 :=
  ((coeffNatDegreeLE_X _).mono (by norm_num)).add
    ((coeffNatDegreeLE_C (by simp)).mul (coeffNatDegreeLE_X _))

/-- The numerator of `c_l` for `Y₁ + t Y₀` at center `0` has joint degree at most
`2(l - 1) - 1 + 1`. -/
example (l : ℕ) :
    jointTotalDegree (rationalTaylorNumeratorOver ℚ (Polynomial.C 0) scaledExpEquation l) ≤
      2 * (l - 1) - 1 + 1 := by
  simpa using jointTotalDegree_rationalTaylorNumeratorOver_le_of_coeffNatDegreeLE 0
    scaledExpEquation 1 1 jetTotalDegree_scaledExpEquation_le
    coeffNatDegreeLE_scaledExpEquation l

/-- With the exponent `2K`, every common numerator of `c_l` with `l < K` for `Y₁ + t Y₀` at
center `0` has joint degree at most `1 + 2K`. -/
example (K : ℕ) (l : Fin K) :
    jointTotalDegree (commonTaylorNumeratorOver ℚ (Polynomial.C 0) scaledExpEquation (2 * K) l) ≤
      1 + 2 * K := by
  simpa using jointTotalDegree_commonTaylorNumeratorOver_le_of_coeffNatDegreeLE 0
    scaledExpEquation 1 1 (2 * K) l (by omega)
    jetTotalDegree_scaledExpEquation_le coeffNatDegreeLE_scaledExpEquation

/-- For the constant equation `Q = 1`, with `jetTotalDegree Q = 0` and constant coefficients, the
numerator bound is `1` at every index. -/
example (l : ℕ) :
    jointTotalDegree
      (rationalTaylorNumeratorOver ℚ (Polynomial.C 0)
        (1 : DifferentialPolynomial (Polynomial ℚ) 1) l) ≤ 1 := by
  have h0 : jetTotalDegree (1 : DifferentialPolynomial (Polynomial ℚ) 1) = 0 := by
    simpa using (jetTotalDegree_le_iff (1 : DifferentialPolynomial (Polynomial ℚ) 1) 0).mpr
      (by simp [totalJetDegree])
  have h1 : CoeffNatDegreeLE (1 : DifferentialPolynomial (Polynomial ℚ) 1) 0 := by
    simpa using coeffNatDegreeLE_C (σ := JetVariable 1) (p := (1 : Polynomial ℚ)) (by simp)
  simpa using jointTotalDegree_rationalTaylorNumeratorOver_le_of_coeffNatDegreeLE 0
    (1 : DifferentialPolynomial (Polynomial ℚ) 1) 0 0 h0.le h1 l

/-- At the nonconstant center `t`, the residual of the equation `X` has the coefficient `t`,
although `X` has constant coefficients. -/
example :
    CoeffNatDegreeLE (X none : DifferentialPolynomial (Polynomial ℚ) 0) 0 ∧
      ¬ CoeffNatDegreeLE (universalTaylorResidual 1 (Polynomial.X : Polynomial ℚ)
        (X none : DifferentialPolynomial (Polynomial ℚ) 0)) 0 := by
  refine ⟨coeffNatDegreeLE_X none, fun h ↦ ?_⟩
  have := h 0
  simp [universalTaylorResidual, coeff_X] at this

end

end PolynomialDifferential
