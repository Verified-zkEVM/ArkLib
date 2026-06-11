/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Mirco Richter (Least Authority), Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.MvPolynomial.Multilinear
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
def linearMvExtension (p : Polynomial.degreeLT F (2 ^ m)) : MvPolynomial (Fin m) F :=
  p.val.sum fun i a ↦ monomial (bitExpo i) a

@[simp]
lemma linearMvExtension_add_comm {p q : Polynomial.degreeLT F (2 ^ m)} :
  linearMvExtension (p + q) = linearMvExtension p + linearMvExtension q := by
  simp [linearMvExtension, Polynomial.sum_add_index]

@[simp]
lemma linearMvExtension_smul_comm {c : F} {p : Polynomial.degreeLT F (2 ^ m)} :
  linearMvExtension (c • p) = c • linearMvExtension p := by
  simp only [linearMvExtension, SetLike.val_smul]
  rw [Polynomial.sum_smul_index _ _ _ (by simp)]
  aesop
    (add simp
      [smul_monomial,
        Polynomial.sum,
        Finset.smul_sum])

lemma bitExpo_apply (i : ℕ) (j : Fin m) :
  (bitExpo i : Fin m →₀ ℕ) j = if Nat.testBit i j.1 then 1 else 0 := by
  simp [bitExpo, Finsupp.onFinset_apply]

lemma bitExpo_le_one (i : ℕ) (j : Fin m) :
  (bitExpo i : Fin m →₀ ℕ) j ≤ 1 := by aesop (add simp [bitExpo_apply])

lemma linearMvExtension_degreeOf_lt {p : Polynomial.degreeLT F (2 ^ m)} {i : Fin m} :
  MvPolynomial.degreeOf i (linearMvExtension p) ≤ 1 := by
  have h_monomial_degrees {x} (hx : x ∈ p.val.support) :
      (degreeOf i (monomial (bitExpo x) (p.val.coeff x))) ≤ 1 := by
    aesop (add simp [degreeOf_eq_sup, bitExpo_le_one])
  have h_sum_degrees :
    (degreeOf i (p.val.sum fun i a ↦ monomial (bitExpo i) a)) ≤
      (Finset.sup p.val.support
        (fun x ↦ degreeOf i (monomial (bitExpo x) (p.val.coeff x)))) := by
    convert MvPolynomial.degreeOf_sum_le _ _ _
  exact h_sum_degrees.trans (Finset.sup_le @h_monomial_degrees)


/-- The linear map that maps univariate polynomials of degree < 2ᵐ onto
    degree wise linear m-variate polynomials, sending
    `aᵢ Xⁱ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))`, where `bitⱼ(i)` is the j-th binary digit of `(i mod 2ᵐ)`.
    This is a linear map version. -/
def linearMvExtensionLMap :
    Polynomial.degreeLT F (2^m) →ₗ[F] MvPolynomial (Fin m) F where
    -- p(X) = aᵢ Xᶦ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))
    toFun p := linearMvExtension p
    map_add' := by simp
    map_smul' := by simp

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

lemma powAlgHom_of_restrict_degree_natDegree {p : MvPolynomial.restrictDegree (Fin m) F 1} :
  (powAlgHom p.1).natDegree ≤ (2 ^ m - 1) := by
  have h_monomial_deg : ∀ d ∈ p.val.support, (∑ j : Fin m, d j * 2 ^ j.val) ≤ 2 ^ m - 1 := by
    have h_deg {d} (hd : d ∈ p.val.support) :
      (∑ j : Fin m, d j * 2 ^ j.val) ≤ ∑ j : Fin m, 2 ^ j.val := by
      have h_deg {j : Fin m} : d j ≤ 1 := by
        have := p.2
        simp_all only [restrictDegree, mem_support_iff, ne_eq, SetLike.coe_mem, ge_iff_le]
        have := p.2
        rw [mem_restrictDegree] at this
        exact this d (by aesop) j
      exact Finset.sum_le_sum fun i _ ↦ mul_le_of_le_one_left (Nat.zero_le _) h_deg
    convert (fun d hd ↦ h_deg (d := d) hd) using 3
    exact Nat.sub_eq_of_eq_add
      (by exact Nat.recOn m (by norm_num) fun n ih ↦
        by simp [Fin.sum_univ_castSucc, pow_succ'] at *; linarith)
  exact le_trans (Polynomial.natDegree_sum_le _ _) <| Finset.sup_le <| fun d hd ↦ by
    specialize h_monomial_deg d hd
    simp_all only [Finsupp.mem_support_iff, ne_eq, Polynomial.algebraMap_eq, Finsupp.prod_pow,
      Function.comp_apply, Polynomial.natDegree_le_iff_coeff_eq_zero, Polynomial.coeff_C_mul]
    simp_all only [←pow_mul', Finset.prod_pow_eq_pow_sum, Polynomial.coeff_X_pow, mul_ite, mul_one,
      mul_zero, ite_eq_right_iff, imp_false]
    exact fun N hN ↦ ne_of_gt (lt_of_le_of_lt h_monomial_deg hN)

lemma powAlgHom_natDegree {p : MvPolynomial (Fin m) F} :
  (powAlgHom p).natDegree ≤ p.totalDegree * (2 ^ m - 1) := by
  have h_deg {d} (hd : d ∈ p.support) :
    (powAlgHom (MvPolynomial.monomial d (p.coeff d))).natDegree ≤
        d.sum (fun i k => 2^i.val * k) := by
    simp only [
      powAlgHom,
      aeval_def,
      Polynomial.algebraMap_eq,
      eval₂_monomial,
      Finsupp.prod]
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) <| by
      exact le_trans (Polynomial.natDegree_prod_le _ _) <| by
        simp only [←pow_mul, Finsupp.sum]
        exact Finset.sum_le_sum fun i _ ↦ Polynomial.natDegree_X_pow_le _
  have h_le {d} (hd : d ∈ p.support) :
    (powAlgHom (MvPolynomial.monomial d (p.coeff d))).natDegree ≤ p.totalDegree * (2^m - 1) := by
    have h_sum : d.sum (fun i k ↦ 2^i.val * k) ≤
      p.totalDegree * (2^m - 1) := by
      have h_sum : d.sum (fun i k ↦ 2^i.val * k) ≤
        d.sum (fun _ k => k) * (2^m - 1) := by
        rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul _ _ _]
        exact Finset.sum_le_sum fun i hi ↦ by
          rw [mul_comm]
          exact Nat.mul_le_mul_left _
            (Nat.le_sub_one_of_lt (pow_lt_pow_right₀ (by decide) (Fin.is_lt i)))
      exact h_sum.trans
        (Nat.mul_le_mul_right _ (Finset.le_sup (f := fun s ↦ s.sum fun x k ↦ k) hd))
    exact le_trans (h_deg hd) h_sum
  have h_sum_le : (powAlgHom p).natDegree ≤
    Finset.sup p.support (fun d ↦ (powAlgHom (MvPolynomial.monomial d (p.coeff d))).natDegree) := by
    have h_sum : powAlgHom p =
      ∑ d ∈ p.support, powAlgHom (MvPolynomial.monomial d (p.coeff d)) := by
      rw [MvPolynomial.as_sum p, map_sum]
      simp [MvPolynomial.support_sum_monomial_coeff]
    exact h_sum.symm ▸ Polynomial.natDegree_sum_le _ _
  exact h_sum_le.trans (Finset.sup_le (fun d hd ↦ h_le hd))

lemma powAlgHom_degree {p : MvPolynomial (Fin m) F} :
  (powAlgHom p).degree ≤ ↑(p.totalDegree * (2 ^ m - 1)) := by
  rw [←Polynomial.natDegree_le_iff_degree_le]
  exact powAlgHom_natDegree

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
    (p : Polynomial.degreeLT F (2 ^ m)) :
    powContraction.comp linearMvExtensionLMap p = p := by
  have h_comp : powContraction (linearMvExtensionLMap p) =
      ∑ i ∈ Finset.range (2 ^ m), p.val.coeff i • Polynomial.X ^ i := by
    unfold powContraction linearMvExtensionLMap linearMvExtension
    simp +decide only [LinearMap.coe_mk, AddHom.coe_mk, AlgHom.toLinearMap_apply, powAlgHom]
    rw [MvPolynomial.aeval_def]
    have h_sum_range :
        (p : Polynomial F).sum (fun i a => MvPolynomial.monomial (bitExpo (m := m) i) a) =
          ∑ i ∈ Finset.range (2 ^ m),
            MvPolynomial.monomial (bitExpo (m := m) i) ((p : Polynomial F).coeff i) := by
      rw [Polynomial.sum_over_range'
        (p := (p : Polynomial F))
        (f := fun i a => MvPolynomial.monomial (bitExpo (m := m) i) a)
        (h := by
          intro n
          simp)
        (n := 2 ^ m)]
      have h_deg := Polynomial.mem_degreeLT.mp p.2
      rcases eq_or_ne (↑p : Polynomial F) 0 with hp | hp
      · rw [hp, Polynomial.natDegree_zero]; positivity
      · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr h_deg
    rw [h_sum_range, MvPolynomial.eval₂_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp +decide only [Polynomial.algebraMap_eq, eval₂_monomial, Finsupp.prod_pow]
    have h_sum : ∑ x : Fin m, 2 ^ (x : ℕ) * (bitExpo i) x = i := by
      convert binary_repr_sum m i (Finset.mem_range.mp hi) using 1
      rw [Finset.sum_range]
      unfold bitExpo; aesop
    simp_rw [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, h_sum]
    simp [Polynomial.smul_eq_C_mul]
  convert h_comp using 1
  convert Polynomial.as_sum_range' p.val (2 ^ m) _ using 1
  · simp +decide [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul_X_pow_eq_monomial]
  · have := Polynomial.mem_degreeLT.mp p.2
    rcases eq_or_ne (↑p : Polynomial F) 0 with hp | hp
    · rw [hp, Polynomial.natDegree_zero]; positivity
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr this

lemma powAlgHom_is_right_inverse_to_linearMvExtension
  (p : Polynomial.degreeLT F (2 ^ m)) :
  powAlgHom (linearMvExtension p) = p := by
  rw [←powContraction_is_right_inverse_to_linearMvExtension]
  rfl

end

end LinearMvExtension
