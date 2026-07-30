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
    change degreeOf i (∑ x ∈ p.val.support,
      monomial (bitExpo x) (p.val.coeff x)) ≤ _
    exact MvPolynomial.degreeOf_sum_le _ _ _
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
  have hnat : (p : Polynomial F).natDegree < 2 ^ m := by
    have hdeg := Polynomial.mem_degreeLT.mp p.2
    by_cases hp : (p : Polynomial F) = 0
    · simp [hp]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hdeg
  have h_comp : powContraction (linearMvExtensionLMap p) =
      ∑ i ∈ Finset.range (2 ^ m), p.val.coeff i • Polynomial.X ^ i := by
    unfold powContraction linearMvExtensionLMap linearMvExtension
    simp +decide only [LinearMap.coe_mk, AddHom.coe_mk, AlgHom.toLinearMap_apply, powAlgHom]
    rw [MvPolynomial.aeval_def]
    have h_sum_range :
        (p : Polynomial F).sum (fun i a => MvPolynomial.monomial (bitExpo (m := m) i) a) =
          ∑ i ∈ Finset.range (2 ^ m),
            MvPolynomial.monomial (bitExpo (m := m) i) ((p : Polynomial F).coeff i) := by
      exact Polynomial.sum_over_range' (p : Polynomial F) (by intro n; simp) (2 ^ m) hnat
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
  change powContraction (linearMvExtensionLMap p) = (p : Polynomial F)
  rw [h_comp]
  convert (Polynomial.as_sum_range' p.val (2 ^ m) hnat).symm using 1
  simp +decide [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul_X_pow_eq_monomial]

lemma powAlgHom_is_right_inverse_to_linearMvExtension
    (p : Polynomial.degreeLT F (2 ^ m)) :
    powAlgHom (linearMvExtension p) = p := by
  rw [←powContraction_is_right_inverse_to_linearMvExtension]
  rfl

end

/-! ## Axis-cross vanishing does not determine a multilinear polynomial -/

open MvPolynomial

variable {F : Type*} [CommRing F]

/-- A checked counterexample to the uniform-vector argument in Hachi [NOZ26, Lemma 10]. For any
axis-cross center `(a, b)`, the nonzero multilinear polynomial
`(X₀ - a) * (X₁ - b)` vanishes whenever either coordinate is fixed at the center. Thus arbitrarily
many evaluations along the two arms of a coordinate-wise star do not imply a polynomial identity.
The Kronecker-curve construction below avoids this obstruction by reducing identity testing to a
single univariate polynomial. -/
theorem exists_nonzero_vanishing_on_axis_cross [Nontrivial F] (a b : F) :
    ∃ H : MvPolynomial (Fin 2) F,
      H ≠ 0 ∧ (∀ y, eval ![a, y] H = 0) ∧ ∀ x, eval ![x, b] H = 0 := by
  refine ⟨(X 0 - C a) * (X 1 - C b), ?_, fun y => by simp, fun x => by simp⟩
  intro h
  have he := congrArg (eval ![a + 1, b + 1]) h
  simp at he

/-! ## The Kronecker-curve challenge encoding and injectivity of `powAlgHom` on multilinears

This section is the algebraic core of the *repaired* Hachi zero-check (Hachi [NOZ26], §4.3, Fig. 5,
Lemma 10). The paper's stated coordinate-wise special soundness for that round is not provable: a
"star" of accepting transcripts only forces a multilinear `H` to vanish on the axis cross through
its centre, and for `m ≥ 2` cross-vanishing does **not** imply `H ≡ 0` (e.g. `(t₁-a)(t₂-b)`).
The adopted repair restricts each random evaluation point to the **Kronecker curve**
`κ_m(τ) = (τ^(2⁰), τ^(2¹), …, τ^(2^(m-1)))`. On that curve a multilinear `H` pulls back to
the *univariate* polynomial `powAlgHom H`, which has degree `< 2^m` and — crucially — is a
**deterministic identity equivalence**: `powAlgHom H = 0 ↔ H = 0`. Univariate root-counting on the
pullback then makes ordinary / coordinate-wise special soundness go through with `k = D = 2^m`
distinct scalar seeds.

The map `powAlgHom` and its degree bound `powAlgHom_of_restrict_degree_natDegree` are above; the
missing companion — injectivity of `powAlgHom` on the per-variable-degree-`≤ 1` (multilinear)
subtype — is `powAlgHom_eq_zero_iff` / `powAlgHom_injective_on_multilinear` below. -/

noncomputable section

open MvPolynomial

variable {F : Type*} [CommRing F] {m : ℕ}

/-- The Kronecker-curve point `κ_m(τ) = (τ^(2⁰), τ^(2¹), …, τ^(2^(m-1)))`. Restricting the
zero-check challenge to this curve is what makes the univariate pullback `powAlgHom` information
complete for multilinear polynomials (repaired Hachi [NOZ26] Lemma 10, §4.3). -/
def kroneckerPoint (τ : F) : Fin m → F := fun j => τ ^ (2 ^ (j : ℕ))

/-- Evaluating the univariate pullback `powAlgHom H` at `τ` agrees with evaluating `H` on the
Kronecker-curve point `κ_m(τ)`. This holds for *every* polynomial; multilinearity is only needed
downstream for injectivity. It is the bridge that turns a zero-check evaluation `H(κ_m(τ)) = 0`
into a univariate root of `powAlgHom H`. -/
lemma eval_powAlgHom_eq_eval_kronecker (H : MvPolynomial (Fin m) F) (τ : F) :
    Polynomial.eval τ (powAlgHom H) = MvPolynomial.eval (kroneckerPoint (m := m) τ) H := by
  have h : (Polynomial.aeval τ).comp
        (powAlgHom : MvPolynomial (Fin m) F →ₐ[F] Polynomial F)
      = MvPolynomial.aeval (kroneckerPoint (m := m) τ) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [powAlgHom, kroneckerPoint]
  have hH := AlgHom.congr_fun h H
  simpa [AlgHom.comp_apply, Polynomial.coe_aeval_eq_eval, MvPolynomial.aeval_eq_eval] using hH

/-- The Kronecker exponent `⟨d⟩ = ∑ⱼ dⱼ·2ʲ` attached to a monomial exponent vector `d`.
Under `powAlgHom`, the multilinear monomial `∏ⱼ Xⱼ^(dⱼ)` becomes the univariate power `X^⟨d⟩`;
on `{0,1}^m` the assignment `d ↦ ⟨d⟩` is the base-2 bijection onto `{0, …, 2^m-1}`. -/
def kroneckerExp (d : Fin m →₀ ℕ) : ℕ := ∑ j : Fin m, d j * 2 ^ (j : ℕ)

/-- `powAlgHom` sends the multilinear monomial `monomial d c` to the univariate monomial of degree
`⟨d⟩ = ∑ⱼ dⱼ·2ʲ`. -/
lemma powAlgHom_monomial (d : Fin m →₀ ℕ) (c : F) :
    powAlgHom (MvPolynomial.monomial d c) = Polynomial.monomial (kroneckerExp d) c := by
  simp only [powAlgHom, MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq, Finsupp.prod_pow]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum,
    show (∑ i : Fin m, 2 ^ (i : ℕ) * d i) = kroneckerExp d from
      Finset.sum_congr rfl (fun i _ => mul_comm _ _),
    Polynomial.C_mul_X_pow_eq_monomial]

/-- On `{0,1}^m` the Kronecker exponent `d ↦ ⟨d⟩ = ∑ⱼ dⱼ·2ʲ` is injective: it is the base-2
encoding, so distinct multilinear monomials become distinct univariate powers. This is exactly
what `finFunctionFinEquiv` (the base-2 digit bijection) records. -/
lemma kroneckerExp_injective_on_le_one {d e : Fin m →₀ ℕ}
    (hd : ∀ j, d j ≤ 1) (he : ∀ j, e j ≤ 1)
    (hde : kroneckerExp d = kroneckerExp e) : d = e := by
  have hval : finFunctionFinEquiv (fun j => (⟨d j, Nat.lt_succ_of_le (hd j)⟩ : Fin 2))
            = finFunctionFinEquiv (fun j => (⟨e j, Nat.lt_succ_of_le (he j)⟩ : Fin 2)) := by
    apply Fin.ext
    simp only [finFunctionFinEquiv_apply]
    exact hde
  have hfun := finFunctionFinEquiv.injective hval
  ext j
  have hj := congrFun hfun j
  simpa using congrArg Fin.val hj

/-- **Coefficient extraction along the Kronecker curve.** For a multilinear `H`, the coefficient of
the multilinear monomial `e` equals the coefficient of `X^⟨e⟩` in the univariate pullback
`powAlgHom H`. This is where multilinearity is used: injectivity of `⟨·⟩` on the support stops
different monomials from colliding at the exponent `⟨e⟩`. -/
lemma powAlgHom_coeff_kroneckerExp {H : MvPolynomial (Fin m) F}
    (hH : H ∈ MvPolynomial.restrictDegree (Fin m) F 1)
    {e : Fin m →₀ ℕ} (he : ∀ j, e j ≤ 1) :
    Polynomial.coeff (powAlgHom H) (kroneckerExp e) = MvPolynomial.coeff e H := by
  have hHsupp : ∀ s ∈ H.support, ∀ j, s j ≤ 1 :=
    (MvPolynomial.mem_restrictDegree (Fin m) H 1).mp hH
  have hexp : powAlgHom H
      = ∑ d ∈ H.support, Polynomial.monomial (kroneckerExp d) (MvPolynomial.coeff d H) := by
    conv_lhs => rw [H.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun d _ => powAlgHom_monomial d (MvPolynomial.coeff d H))
  rw [hexp, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  have key : ∀ d ∈ H.support,
      (if kroneckerExp d = kroneckerExp e then MvPolynomial.coeff d H else 0)
        = (if d = e then MvPolynomial.coeff d H else 0) := by
    intro d hd
    by_cases hde : d = e
    · subst hde; simp
    · have hne : kroneckerExp d ≠ kroneckerExp e :=
        fun h => hde (kroneckerExp_injective_on_le_one (hHsupp d hd) he h)
      rw [if_neg hne, if_neg hde]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  by_cases he' : e ∈ H.support
  · rw [if_pos he']
  · rw [if_neg he', MvPolynomial.notMem_support_iff.mp he']

/-- **Kronecker injectivity (the repaired Lemma 10 kernel).** For a multilinear `H`, the univariate
pullback `powAlgHom H` is zero *iff* `H` is zero. Unlike a Schwartz–Zippel statement this is a
deterministic polynomial-identity equivalence, and it is exactly what the paper's coordinate-wise
star fails to provide. -/
theorem powAlgHom_eq_zero_iff {H : MvPolynomial (Fin m) F}
    (hH : H ∈ MvPolynomial.restrictDegree (Fin m) F 1) :
    powAlgHom H = 0 ↔ H = 0 := by
  constructor
  · intro h0
    refine MvPolynomial.ext _ _ (fun e => ?_)
    rw [MvPolynomial.coeff_zero]
    by_cases he : ∀ j, e j ≤ 1
    · rw [← powAlgHom_coeff_kroneckerExp hH he, h0, Polynomial.coeff_zero]
    · rw [← MvPolynomial.notMem_support_iff]
      intro hmem
      obtain ⟨j, hj⟩ := not_forall.mp he
      exact absurd ((MvPolynomial.mem_restrictDegree (Fin m) H 1).mp hH e hmem j) hj
  · intro h; rw [h, map_zero]

/-- **Injectivity of `powAlgHom` on multilinear polynomials** — the generic algebra lemma the
repaired zero-check needs. Distinct multilinear polynomials have distinct univariate pullbacks, so
recovering `H` from `powAlgHom H` (hence from finitely many curve evaluations) is deterministic. -/
theorem powAlgHom_injective_on_multilinear :
    Function.Injective (fun H : MvPolynomial.restrictDegree (Fin m) F 1 => powAlgHom H.val) := by
  intro H H' h
  dsimp only at h
  have hmem : (H.val - H'.val) ∈ MvPolynomial.restrictDegree (Fin m) F 1 :=
    Submodule.sub_mem _ H.2 H'.2
  have hz : powAlgHom (H.val - H'.val) = 0 := by rw [map_sub, h, sub_self]
  exact Subtype.ext (sub_eq_zero.mp ((powAlgHom_eq_zero_iff hmem).mp hz))

/-- **Root-counting on the Kronecker curve (the extraction step of repaired Lemma 10).** If a
multilinear `H` vanishes on the curve at `2^m` distinct scalar seeds, then `H = 0`. Concretely: the
pullback `powAlgHom H` has degree `< 2^m` but acquires `≥ 2^m` distinct roots, so it is the zero
polynomial, whence `H = 0` by Kronecker injectivity. This is the deterministic replacement for the
false "vanishes on the star ⇒ zero polynomial" step, giving `k = D = 2^m`-special soundness. -/
theorem multilinear_eq_zero_of_kronecker_roots [IsDomain F]
    {H : MvPolynomial.restrictDegree (Fin m) F 1} {s : Finset F}
    (hcard : 2 ^ m ≤ s.card)
    (hroots : ∀ τ ∈ s, MvPolynomial.eval (kroneckerPoint (m := m) τ) H.val = 0) :
    H.val = 0 := by
  have hp : powAlgHom H.val = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (powAlgHom H.val) s
      (fun τ hτ => ?_) ?_
    · rw [eval_powAlgHom_eq_eval_kronecker]; exact hroots τ hτ
    · have h1 : (powAlgHom H.val).natDegree ≤ 2 ^ m - 1 :=
        powAlgHom_of_restrict_degree_natDegree (p := H)
      have h2 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
      omega
  exact (powAlgHom_eq_zero_iff H.2).mp hp

/-- **The `2^m` root count is sharp: `2^m − 1` Kronecker seeds never suffice.** For *any* finite
set `s` of at most `2^m − 1` scalar seeds there is a **nonzero** multilinear `H` vanishing on the
curve at every seed of `s`. Take the univariate `p = ∏_{ρ ∈ s} (X − ρ)`, of degree `≤ 2^m − 1`, and
push it up with `linearMvExtension`; `powAlgHom` inverts that, so `H ≠ 0`, while
`eval_powAlgHom_eq_eval_kronecker` turns each root of `p` into a curve evaluation of `H`.

This is the exact companion of `multilinear_eq_zero_of_kronecker_roots`, and it is why the Hachi
zero-check's seam relations must carry the range *identity* rather than deriving it from their point
evaluation: the extractor's collision branch shares an opening across only `2^m − 1` seeds — one
short of the root count — so it could never conclude `H₀ ≡ 0` for a single colliding opening. See
`ArkLib/Commitments/Functional/Hachi/ZeroCheck/Reduction.lean` (`relZeroCheck`) and
`docs/kb/audits/noz26-zero-check-lemma10.md`. -/
theorem exists_nonzero_multilinear_vanishing_on_kronecker_seeds [Nontrivial F] (s : Finset F)
    (hcard : s.card ≤ 2 ^ m - 1) :
    ∃ H : MvPolynomial.restrictDegree (Fin m) F 1,
      H.val ≠ 0 ∧ ∀ τ ∈ s, MvPolynomial.eval (kroneckerPoint (m := m) τ) H.val = 0 := by
  classical
  set p : Polynomial F := ∏ ρ ∈ s, (Polynomial.X - Polynomial.C ρ) with hpdef
  have hmonic : p.Monic :=
    hpdef ▸ Polynomial.monic_prod_of_monic _ _ fun ρ _ => Polynomial.monic_X_sub_C ρ
  have hpne : p ≠ 0 := hmonic.ne_zero
  have hnat : p.natDegree = s.card := by
    rw [hpdef, Polynomial.natDegree_prod_of_monic _ _ fun ρ _ => Polynomial.monic_X_sub_C ρ]
    simp
  -- `p` lies in the degree-`< 2^m` window, so it has a multilinear extension.
  have hlt : p.degree < (2 ^ m : ℕ) := by
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    rw [Polynomial.degree_eq_natDegree hpne]
    exact Nat.cast_lt.mpr (by omega)
  have hpm : p ∈ Polynomial.degreeLT F (2 ^ m) := Polynomial.mem_degreeLT.mpr hlt
  have hinv : powAlgHom (linearMvExtension (⟨p, hpm⟩ : Polynomial.degreeLT F (2 ^ m))) = p :=
    powAlgHom_is_right_inverse_to_linearMvExtension _
  have hmemH : linearMvExtension (⟨p, hpm⟩ : Polynomial.degreeLT F (2 ^ m)) ∈
      MvPolynomial.restrictDegree (Fin m) F 1 :=
    (MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mpr fun _ => linearMvExtension_degreeOf_lt
  -- nonzero, since `powAlgHom` recovers the nonzero `p`
  have hne : linearMvExtension (⟨p, hpm⟩ : Polynomial.degreeLT F (2 ^ m)) ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hinv
    exact hpne hinv.symm
  have hroots : ∀ τ ∈ s, MvPolynomial.eval (kroneckerPoint (m := m) τ)
      (linearMvExtension (⟨p, hpm⟩ : Polynomial.degreeLT F (2 ^ m))) = 0 := by
    intro τ hτ
    rw [← eval_powAlgHom_eq_eval_kronecker, hinv, hpdef, Polynomial.eval_prod]
    exact Finset.prod_eq_zero hτ (by simp)
  exact ⟨⟨_, hmemH⟩, hne, hroots⟩

end

end LinearMvExtension
