/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter (Least Authority)
-/

import ArkLib.Data.CodingTheory.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Univariate polynomials of degree < 2ᵐ can be writen as degree wise linear
    m-variate polynomials by ∑ aᵢ Xⁱ → ∑ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))` -/

namespace LinearMvExtension

noncomputable section

open MvPolynomial

variable {F : Type*} [CommSemiring F] {m : ℕ}

/- Given integers m and i this computes monomial exponents
   ( σ(0), ..., σ(m-1) ) = ( bit₀(i), ..., bitₘ₋₁(i) )
   such that we have X_0^σ(0)⬝  ⋯  ⬝ X_(m-1)^σ(m-1).
   For i ≥ 2ᵐ this is the bit reprsentation of (i mod 2ᵐ) -/
def bitExpo (i : ℕ ) : (Fin m) →₀ ℕ :=
  Finsupp.onFinset Finset.univ
    (fun j => if Nat.testBit i j.1 then 1 else 0)
    (by intro j hj; simpa using hj)

/-- The linear map that maps univariate polynomials of degree < 2ᵐ onto
    degree wise linear m-variate polynomials, sending
    aᵢ Xⁱ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i)), where bitⱼ(i) is the j-th binary digit of (i mod 2ᵐ). -/
def linearMvExtension :
  Polynomial.degreeLT F (2^m) →ₗ[F] MvPolynomial (Fin m) F where
    -- p(X) = aᵢ Xᶦ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))
    toFun p := (p : Polynomial F).sum fun i a =>
      MvPolynomial.monomial (bitExpo i)  a
    map_add' := by
      rintro p q
      simp [Polynomial.sum_add_index]
    map_smul' := by
      rintro c p
      simp [Polynomial.sum_smul_index]
      sorry

/--partialEval takes a m-variate polynomial f and a k-vector α as input,
  partially evaluates f(X_0, X_1,..X_(m-1)) at {X_0 = α_0, X_1 = α_1,.., X_{k-1} = α_{k-1}}
  and returns a (m-k)-variate polynomial. -/
def partialEval {F : Type*} [CommRing F] {m k : ℕ}
  (f : MvPolynomial (Fin m) F) (α : Fin k → F) (h : k ≤ m) : MvPolynomial (Fin (m - k)) F :=
  let φ : Fin m → MvPolynomial (Fin (m - k)) F := fun i =>
    if h' : i.val < k then
      C (α ⟨i.val, h'⟩)
    else
      let j := i.val - k
      let j' : Fin (m - k) := ⟨j, sorry⟩
      X j'
  eval₂ C φ f

/-- The Semiring morphism that maps m-variate polynomials onto univariate
    polynomials by evaluating them at (X^(2⁰), ... , X^(2ᵐ⁻¹) ) , i.e. sending
    aₑ X₀^σ(0) ⬝ ⋯ ⬝ Xₘ₋₁^σ(m-1) →  aₑ (X^(2⁰))^σ(0) ⬝ ⋯ ⬝ (X^(2ᵐ⁻¹))^σ(m-1)
    for all σ : Fin m → ℕ  -/
def powAlgHom :
  MvPolynomial (Fin m) F →ₐ[F] Polynomial F :=
   aeval fun j => Polynomial.X ^ (2 ^ (j : ℕ))

/- The linear map optained by forgetting the multiplicative structure-/
def powContraction :
  MvPolynomial (Fin m) F →ₗ[F] Polynomial F :=
  powAlgHom.toLinearMap

/- Evaluating m-variate polynomials on (X^(2⁰), ... , X^(2ᵐ⁻¹) ) is
   right inverse to linear multivariate extensions on F^(< 2ᵐ)[X]  -/
lemma powContraction_is_right_inverse_to_linearMvExtension (m: ℕ )
  (p : Polynomial.degreeLT F (2^m)) :
    powContraction.comp linearMvExtension p  = p  := by sorry

end

end LinearMvExtension
