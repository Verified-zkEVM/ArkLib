/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter (Least Authority)
-/

import ArkLib.Data.CodingTheory.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
  # Conversion of Univariate polynomials to Multilinear polynomials

  Univariate polynomials of degree < 2ᵐ can be writen as degree wise linear
  m-variate polynomials by `∑ aᵢ Xⁱ → ∑ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))` -/

namespace LinearMvExtension

noncomputable section

open MvPolynomial

variable {F : Type*} [CommSemiring F] {m : ℕ}

/-- Given integers m and i this computes monomial exponents
  `( σ(0), ..., σ(m-1) ) = ( bit₀(i), ..., bitₘ₋₁(i) )`
  such that we have `X_0^σ(0)⬝  ⋯  ⬝ X_(m-1)^σ(m-1)`.
  For `i ≥ 2ᵐ` this is the bit reprsentation of `(i mod 2ᵐ)` -/
def bitExpo (i : ℕ) : (Fin m) →₀ ℕ :=
  Finsupp.onFinset Finset.univ
    (fun j => if Nat.testBit i j.1 then 1 else 0)
    (by intro j hj; simp)

/-- The linear map that maps univariate polynomials of degree < 2ᵐ onto
    degree wise linear m-variate polynomials, sending
    `aᵢ Xⁱ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))`, where `bitⱼ(i)` is the j-th binary digit of `(i mod 2ᵐ)`. -/
def linearMvExtension :
  Polynomial.degreeLT F (2^m) →ₗ[F] MvPolynomial (Fin m) F where
    -- p(X) = aᵢ Xᶦ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))
    toFun p := (p : Polynomial F).sum fun i a =>
      MvPolynomial.monomial (bitExpo i) a
    map_add' := by
      rintro p q
      simp [Polynomial.sum_add_index]
    map_smul' := by
      rintro c p
      simp [Polynomial.sum_smul_index]
      simp_rw [← smul_eq_mul, ← smul_monomial]
      unfold Polynomial.sum
      simp_rw [← Finset.smul_sum]

/-- `partialEval` takes a m-variate polynomial f and a k-vector α as input,
  partially evaluates f(X_0, X_1,..X_(m-1)) at {X_0 = α_0, X_1 = α_1,.., X_{k-1} = α_{k-1}}
  and returns a (m-k)-variate polynomial. -/
def partialEval {k : ℕ} (f : MvPolynomial (Fin m) F) (α : Fin k → F) (h : k ≤ m) :
    MvPolynomial (Fin (m - k)) F :=
  let φ : Fin m → MvPolynomial (Fin (m - k)) F := fun i =>
    if h' : i.val < k then
      C (α ⟨i.val, h'⟩)
    else
      let j := i.val - k
      let j' : Fin (m - k) := ⟨j, by omega⟩
      X j'
  eval₂ C φ f

/-- The Semiring morphism that maps m-variate polynomials onto univariate
    polynomials by evaluating them at `(X^(2⁰), ... , X^(2ᵐ⁻¹))`, i.e. sending
    `aₑ X₀^σ(0) ⬝ ⋯ ⬝ Xₘ₋₁^σ(m-1) →  aₑ (X^(2⁰))^σ(0) ⬝ ⋯ ⬝ (X^(2ᵐ⁻¹))^σ(m-1)`
    for all `σ : Fin m → ℕ` -/
def powAlgHom :
  MvPolynomial (Fin m) F →ₐ[F] Polynomial F :=
   aeval fun j => Polynomial.X ^ (2 ^ (j : ℕ))

/- The linear map optained by forgetting the multiplicative structure-/
def powContraction :
  MvPolynomial (Fin m) F →ₗ[F] Polynomial F :=
  powAlgHom.toLinearMap

private lemma binary_repr_sum (m i : ℕ) (hi : i < 2 ^ m) :
    ∑ j ∈ Finset.range m, (if Nat.testBit i j then 2 ^ j else 0) = i := by
  induction m generalizing i with
  | zero => simp_all
  | succ m ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.testBit_zero, pow_zero, decide_eq_true_eq]
    have key : ∑ x ∈ Finset.range m,
        (if i.testBit (x + 1) then 2 ^ (x + 1) else 0) =
      2 * ∑ x ∈ Finset.range m,
        (if (i / 2).testBit x then 2 ^ x else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp [Nat.testBit_add_one, pow_succ]
      ring_nf
    have hi2 : i / 2 < 2 ^ m := by rw [pow_succ] at hi; omega
    rw [key, ih (i / 2) hi2]
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h] <;> omega

/- Evaluating m-variate polynomials on (X^(2⁰), ... , X^(2ᵐ⁻¹) ) is
   right inverse to linear multivariate extensions on F^(< 2ᵐ)[X]  -/
lemma powContraction_is_right_inverse_to_linearMvExtension
  (p : Polynomial.degreeLT F (2^m)) :
    powContraction.comp linearMvExtension p = p  := by
  have h_comp : powContraction (linearMvExtension p) =
      ∑ i ∈ Finset.range (2 ^ m), p.val.coeff i • Polynomial.X ^ i := by
    unfold powContraction linearMvExtension
    simp +decide [Polynomial.sum_over_range', powAlgHom]
    simp +decide [Polynomial.sum_over_range', aeval_def]
    rw [Polynomial.sum_over_range']
    all_goals norm_num [Polynomial.smul_eq_C_mul]
    refine' Finset.sum_congr rfl fun i hi => _
    · simp +decide [← pow_mul, Finsupp.prod]
      have h_sum : ∑ x : Fin m, 2 ^ (x : ℕ) * (bitExpo i) x = i := by
        convert binary_repr_sum m i (Finset.mem_range.mp hi) using 1
        rw [Finset.sum_range]
        unfold bitExpo; aesop
      rw [Finset.prod_pow_eq_pow_sum, h_sum]
    · have h_deg : Polynomial.degree (p : Polynomial F) < 2 ^ m :=
        Polynomial.mem_degreeLT.mp p.2
      contrapose! h_deg
      rw [Polynomial.degree_eq_natDegree] <;> norm_cast; aesop
  convert h_comp using 1
  convert Polynomial.as_sum_range' p.val (2 ^ m) _ using 1
  · simp +decide [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul_X_pow_eq_monomial]
  · have := Polynomial.mem_degreeLT.mp p.2
    contrapose! this
    rw [Polynomial.degree_eq_natDegree] <;> norm_cast; aesop

end

end LinearMvExtension
