/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Polynomials whose monomials satisfy a weight inequality

Fix two additive weights `a b : (σ →₀ ℕ) →+ ℕ` on monomial exponents. The polynomials all of
whose monomials `m` satisfy `a m ≤ b m` form a subalgebra, because both weights add under
multiplication of monomials. Substitution preserves this subalgebra when every substituted
polynomial lies in it.

The intended use compares two gradings of a polynomial in a distinguished variable `none` and
further variables `some i`. Take `b` to be the exponent of `none` and `a` a weighted degree in the
other variables. Then every coefficient of `none ^ h` has weighted degree at most `h`.

The file also records a denominator budget for exponent vectors. If `∑ t i * m i ≤ h` and every
index in the support of `m` has `t i ≤ h - 1`, then `∑ (2 * t i - 1) * m i ≤ 2 * h - 2`. With
`t i = i - r` this is the number of powers of a separant needed to clear the denominators of
the rational Taylor coefficients of an order-`r` differential equation.

## Main statements

* `MvPolynomial.supportWeightLE`, the subalgebra, with `mem_supportWeightLE` and
  `supportWeightLE_toSubmodule`, which identifies it with Mathlib's `restrictSupport`.
* `MvPolynomial.aeval_mem_supportWeightLE`: substitution preserves the inequality.
* `MvPolynomial.weight_le_of_mem_coeff_optionEquivLeft`: coefficient extraction in the
  distinguished variable.
* `MvPolynomial.weightedTotalDegree_coeff_optionEquivLeft_le`: coefficient extraction does not
  increase a weighted degree that ignores the distinguished variable.
* `Finsupp.weight_two_mul_sub_one_le`: the denominator budget.

## References

These declarations are ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
`supportWeightLE`, `monomial_mem_supportWeightLE`, `aeval_mem_supportWeightLE`,
`weight_le_of_mem_coeff_optionEquivLeft`, and `weightedTotalDegree_coeff_optionEquivLeft_le` come
from `ArkLib/ToMathlib/MvPolynomial/SupportWeight.lean`; `supportWeightLE` is now built from
Mathlib's `MvPolynomial.restrictSupport`, whose multiplicativity lemma `restrictSupport_add`
supplies closure under products. `Finsupp.weight_two_mul_sub_one_le` generalizes
`taylor_denominator_weight_le` from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Taylor/Denominator.lean`: the
index type is arbitrary instead of `Fin (r + h)`, the weight `t` is arbitrary instead of
`l ↦ l - r`, and the source hypothesis `0 < h` is removed.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

open scoped Pointwise

variable {R σ τ : Type*} [CommSemiring R]

/-- The subalgebra of polynomials each of whose monomials `m` satisfies `a m ≤ b m`.

Its underlying submodule is `restrictSupport R {m | a m ≤ b m}`. The zero exponent satisfies the
inequality, and the set of admissible exponents is closed under addition because `a` and `b` are
additive, so the submodule contains `1` and is closed under multiplication. -/
def supportWeightLE (a b : (σ →₀ ℕ) →+ ℕ) : Subalgebra R (MvPolynomial σ R) :=
  (restrictSupport R {m | a m ≤ b m}).toSubalgebra
    (by
      rw [← C_1, ← monomial_zero', monomial_mem_restrictSupport]
      left
      simp)
    (by
      classical
      intro p q hp hq
      have hpq : p * q ∈ restrictSupport R ({m | a m ≤ b m} + {m | a m ≤ b m}) := by
        rw [restrictSupport_add]
        exact Submodule.mul_mem_mul hp hq
      refine restrictSupport_mono R ?_ hpq
      rintro _ ⟨u, hu, v, hv, rfl⟩
      simp only [Set.mem_ofPred_eq, map_add] at hu hv ⊢
      omega)

/-- `supportWeightLE a b` is Mathlib's `restrictSupport` for the admissible exponents. -/
theorem supportWeightLE_toSubmodule (a b : (σ →₀ ℕ) →+ ℕ) :
    Subalgebra.toSubmodule (supportWeightLE (R := R) a b) =
      restrictSupport R {m | a m ≤ b m} :=
  rfl

/-- A polynomial lies in `supportWeightLE a b` exactly when every monomial in its support
satisfies `a m ≤ b m`. -/
theorem mem_supportWeightLE {a b : (σ →₀ ℕ) →+ ℕ} {p : MvPolynomial σ R} :
    p ∈ supportWeightLE a b ↔ ∀ m ∈ p.support, a m ≤ b m := by
  change p ∈ restrictSupport R _ ↔ _
  rw [mem_restrictSupport_iff]
  rfl

/-- A monomial lies in `supportWeightLE a b` when its exponent satisfies the inequality. The
coefficient is arbitrary; a zero coefficient gives the zero polynomial. -/
theorem monomial_mem_supportWeightLE (a b : (σ →₀ ℕ) →+ ℕ)
    (m : σ →₀ ℕ) (r : R) (h : a m ≤ b m) :
    monomial m r ∈ supportWeightLE a b := by
  change monomial m r ∈ restrictSupport R _
  rw [monomial_mem_restrictSupport]
  exact Or.inl h

/-- Substituting polynomials from `supportWeightLE a b` for every variable keeps a polynomial in
`supportWeightLE a b`. The source polynomial `p` is arbitrary: its own support is not constrained,
because every source monomial becomes a product of admissible polynomials. -/
theorem aeval_mem_supportWeightLE (a b : (τ →₀ ℕ) →+ ℕ)
    (v : σ → MvPolynomial τ R) (hv : ∀ i, v i ∈ supportWeightLE a b)
    (p : MvPolynomial σ R) : aeval v p ∈ supportWeightLE a b := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (supportWeightLE a b).algebraMap_mem c
  | add p q hp hq => simpa using (supportWeightLE a b).add_mem hp hq
  | mul_X p i hp => simpa using (supportWeightLE a b).mul_mem hp (hv i)

/-- Let `p` be a polynomial in a distinguished variable `none` and variables `some i`, and
suppose every monomial of `p` has `w`-weight in the variables `some i` at most its exponent of
`none`. Then every monomial of the coefficient of `none ^ h` has `w`-weight at most `h`. -/
theorem weight_le_of_mem_coeff_optionEquivLeft
    (w : σ → ℕ) (p : MvPolynomial (Option σ) R)
    (hp : p ∈ supportWeightLE
      (Finsupp.weight (fun i ↦ i.elim 0 w)) (Finsupp.applyAddHom none))
    (h : ℕ) (m : σ →₀ ℕ)
    (hm : m ∈ ((optionEquivLeft R σ p).coeff h).support) :
    Finsupp.weight w m ≤ h := by
  have hbound := mem_supportWeightLE.mp hp (m.optionElim h)
    ((mem_support_coeff_optionEquivLeft R).mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_option_index] at hbound
  · simpa [Finsupp.weight_apply] using hbound
  · intro i
    simp
  · intro i c d
    exact add_smul c d _

/-- Extracting the coefficient of `none ^ h` does not increase a weighted degree in which the
distinguished variable `none` has weight zero. -/
theorem weightedTotalDegree_coeff_optionEquivLeft_le (w : σ → ℕ)
    (p : MvPolynomial (Option σ) R) (h : ℕ) :
    ((optionEquivLeft R σ p).coeff h).weightedTotalDegree w ≤
      p.weightedTotalDegree (fun i ↦ i.elim 0 w) := by
  apply Finset.sup_le_iff.mpr
  intro m hm
  have hbound := le_weightedTotalDegree (fun i ↦ i.elim 0 w)
    ((mem_support_coeff_optionEquivLeft R).mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_option_index] at hbound
  · simpa [Finsupp.weight_apply] using hbound
  · intro i
    simp
  · intro i c d
    exact add_smul c d _

end

end MvPolynomial

namespace Finsupp

open scoped BigOperators

/-- Denominator budget. Suppose `∑ t i * m i ≤ h` and every index `i` in the support of `m` has
`t i ≤ h - 1`. Then `∑ (2 * t i - 1) * m i ≤ 2 * h - 2`, with natural subtraction.

The support hypothesis is necessary: for `h ≥ 1`, `m = single i 1` and `t i = h`, the left side
is `2 * h - 1`. Indices with `t i = 0` contribute nothing to either sum. The case `h = 0` is
included; both sides are then zero. -/
theorem weight_two_mul_sub_one_le {ι : Type*} (t : ι → ℕ) {h : ℕ} (m : ι →₀ ℕ)
    (hm : Finsupp.weight t m ≤ h) (ht : ∀ i ∈ m.support, t i ≤ h - 1) :
    Finsupp.weight (fun i ↦ 2 * t i - 1) m ≤ 2 * h - 2 := by
  classical
  let W := Finsupp.weight t m
  let D := Finsupp.weight (fun i ↦ 2 * t i - 1) m
  let C := Finsupp.weight (fun i ↦ if 0 < t i then 1 else 0) m
  have heq : D + C = 2 * W := by
    simp only [D, C, W, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < t i
    · simp only [hi, ↓reduceIte]
      have ht' : 2 * t i - 1 + 1 = 2 * t i := by omega
      nlinarith
    · simp [Nat.eq_zero_of_not_pos hi]
  have hmax : W ≤ (h - 1) * C := by
    simp only [W, C, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hti : 0 < t i
    · simp only [hti, ↓reduceIte, mul_one]
      nlinarith [ht i hi]
    · simp [Nat.eq_zero_of_not_pos hti]
  change D ≤ 2 * h - 2
  by_cases hC : 2 ≤ C
  · omega
  · have hc : C = 0 ∨ C = 1 := by omega
    rcases hc with hc | hc <;> rw [hc] at hmax heq <;>
      simp only [mul_zero, mul_one] at hmax <;> omega

end Finsupp
