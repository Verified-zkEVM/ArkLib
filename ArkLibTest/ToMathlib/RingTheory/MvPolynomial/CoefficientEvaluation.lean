/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.CoefficientEvaluation
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AwayPresentation

/-!
# Acceptance tests for coefficient-evaluation equations

The examples compute dimension bounds for small ideals over `ℚ`: an equation `2 * x₀ = x₁ * x₂`
eliminates `x₀` in three variables, two fixed evaluations at distinct points cut the plane of
linear polynomials to dimension zero, and one polynomial evaluation in one coefficient leaves
dimension one. The zero ideal in one coefficient variable contains no evaluation equation.

The boundary examples show the hypotheses are needed. Evaluating twice at the point `1` gives a
line in the plane, of dimension `1 > 2 - 2`. With no coefficient variables, the evaluation
equation for `received = 0` is zero, so `⊥` in the single variable `z` contains it and has
dimension `1 > 0 + 1 - 1`. The unit ideal contains both fixed evaluation equations in one
coefficient variable, so positive dimension is needed in the count of equations.

The last examples derive the conjunction form of the count for a prime and the dimension bound
through a surjection of localizations of prime quotients.
-/

open MvPolynomial

namespace CoefficientEvaluationTest

/-- The points `0` and `1` of `ℚ`. -/
def zeroOne : Fin 2 ↪ ℚ := ⟨![0, 1], by decide⟩

/-- The first of three variables. -/
def firstVariable : Fin 1 ↪ Fin 3 := ⟨fun _ ↦ 0, Function.injective_of_subsingleton _⟩

/-- The fixed evaluation equation has total degree at most one. -/
example : (fixedCoefficientEvaluation 3 (2 : ℚ) 5).totalDegree ≤ 1 :=
  totalDegree_fixedCoefficientEvaluation_le 3 2 5

/-- The equation `2 * x₀ - x₁ * x₂` eliminates `x₀`: the ideal it generates has dimension at
most `2`. -/
example : (affineHilbertPolynomial
    (Ideal.span {C 2 * X 0 - X 1 * X 2} : Ideal (MvPolynomial (Fin 3) ℚ))).natDegree ≤ 2 := by
  have h := natDegree_affineHilbertPolynomial_le_card_sub_of_isUnit_det
    (I := Ideal.span {C 2 * X 0 - X 1 * X 2}) firstVariable !![(2 : ℚ)] (by simp)
    (fun _ ↦ C 2 * X 0 - X 1 * X 2) (fun _ ↦ Ideal.subset_span rfl) fun i ↦ by
      obtain rfl : i = 0 := Subsingleton.elim _ _
      rw [Fin.sum_univ_one]
      change (C 2 * X 0 - X 1 * X 2 : MvPolynomial (Fin 3) ℚ) - (2 : ℚ) • X 0 ∈
        supported ℚ (Set.range firstVariable)ᶜ
      rw [← C_mul', sub_sub_cancel_left]
      refine Subalgebra.neg_mem _ (Subalgebra.mul_mem _ ?_ ?_) <;>
        exact X_mem_supported.mpr fun ⟨_, h⟩ ↦ by simp [firstVariable] at h
  simpa using h

/-- The fixed evaluations at `0` and `1` cut the plane of linear polynomials to dimension zero. -/
example (y : Fin 2 → ℚ) : (affineHilbertPolynomial (Ideal.span (Set.range fun i ↦
    fixedCoefficientEvaluation 2 (zeroOne i) (y i)))).natDegree = 0 :=
  Nat.le_zero.mp (natDegree_affineHilbertPolynomial_le_of_fixedCoefficientEvaluation_mem zeroOne
    y fun i ↦ Ideal.subset_span ⟨i, rfl⟩)

/-- One polynomial evaluation in one coefficient variable leaves dimension at most one. -/
example (a : ℚ) (received : Polynomial ℚ) : (affineHilbertPolynomial (Ideal.span
    {polynomialCoefficientEvaluation 1 a received})).natDegree ≤ 1 :=
  natDegree_affineHilbertPolynomial_le_of_polynomialCoefficientEvaluation_mem le_rfl
    ⟨fun _ ↦ a, fun _ _ _ ↦ Subsingleton.elim _ _⟩ (fun _ ↦ received)
    fun _ ↦ Ideal.subset_span rfl

/-- Affine evaluations at `0` and `1` in two coefficient variables leave dimension at most one. -/
example (f g : Fin 2 → ℚ) : (affineHilbertPolynomial (Ideal.span (Set.range fun i ↦
    affineCoefficientEvaluation 2 (zeroOne i) (f i) (g i)))).natDegree ≤ 1 :=
  natDegree_affineHilbertPolynomial_le_of_affineCoefficientEvaluation_mem le_rfl zeroOne f g
    fun i ↦ Ideal.subset_span ⟨i, rfl⟩

/-- The zero ideal in one coefficient variable has dimension one, so it contains none of the
fixed evaluation equations. -/
example {n : ℕ} (α : Fin n ↪ ℚ) (y : Fin n → ℚ) :
    {i | fixedCoefficientEvaluation 1 (α i) (y i) ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))}.ncard =
      0 := by
  have hdim : (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))).natDegree = 1 := by
    simp [natDegree_affineHilbertPolynomial_bot]
  have h := natDegree_affineHilbertPolynomial_add_ncard_le_of_fixedCoefficientEvaluation α y
    (hdim ▸ one_pos)
  omega

/-! ### The hypotheses are needed -/

/-- Distinct points are needed: the evaluations at the point `1` twice generate the line
`x₀ + x₁ = 0`, of dimension `1 > 2 - 2`. -/
example :
    ¬ (affineHilbertPolynomial (Ideal.span {fixedCoefficientEvaluation 2 (1 : ℚ) 0})).natDegree ≤
      2 - 2 := by
  have hne : fixedCoefficientEvaluation 2 (1 : ℚ) 0 ≠ 0 := fun h ↦ by
    simpa [fixedCoefficientEvaluation, Fin.sum_univ_two] using congrArg (eval ![1, 0]) h
  have hproper : Ideal.span {fixedCoefficientEvaluation 2 (1 : ℚ) 0} ≠ ⊤ := fun h ↦ by
    rw [Ideal.span_singleton_eq_top] at h
    have := h.map (eval (0 : Fin 2 → ℚ))
    simp [fixedCoefficientEvaluation] at this
  have h := natDegree_affineHilbertPolynomial_span_singleton_add_one hne hproper
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

/-- `c ≤ m` is needed in the polynomial evaluation bound: with no coefficient variables and
`received = 0`, the equation is zero, and `⊥` has dimension `1 > 0 + 1 - 1`. -/
example : polynomialCoefficientEvaluation 0 (0 : ℚ) 0 ∈
      (⊥ : Ideal (MvPolynomial (Option (Fin 0)) ℚ)) ∧
    ¬ (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Option (Fin 0)) ℚ))).natDegree ≤
      0 + 1 - 1 := by
  refine ⟨by simp [polynomialCoefficientEvaluation], ?_⟩
  simp [natDegree_affineHilbertPolynomial_bot]

/-- Positive dimension is needed in the count: the unit ideal in one coefficient variable
contains both evaluation equations at `0` and `1`, and `0 + 2 > 1`. -/
example (y : Fin 2 → ℚ) :
    ¬ (affineHilbertPolynomial (⊤ : Ideal (MvPolynomial (Fin 1) ℚ))).natDegree +
      {i | fixedCoefficientEvaluation 1 (zeroOne i) (y i) ∈
        (⊤ : Ideal (MvPolynomial (Fin 1) ℚ))}.ncard ≤ 1 := by
  simp [Set.ncard_univ]

/-! ### Derived forms -/

/-- For a prime `P` of positive dimension in `m` coefficient variables, `natDegree P_P ≤ m` and
at most `m - natDegree P_P` of the fixed evaluation equations at distinct points lie in `P`. -/
example {k : Type*} [Field k] {n m : ℕ} (α : Fin n ↪ k) (y : Fin n → k)
    (P : Ideal (MvPolynomial (Fin m) k)) (_hP : P.IsPrime)
    (hd : 0 < (affineHilbertPolynomial P).natDegree) :
    (affineHilbertPolynomial P).natDegree ≤ m ∧
      {i | fixedCoefficientEvaluation m (α i) (y i) ∈ P}.ncard ≤
        m - (affineHilbertPolynomial P).natDegree := by
  have h := natDegree_affineHilbertPolynomial_add_ncard_le_of_fixedCoefficientEvaluation α y hd
  omega

/-- For primes `J` of dimension at most `d` and `P`, with `t ∉ J` and `s ∉ P`, a surjection
`(k[τ] ⧸ J)_t → (k[σ] ⧸ P)_s` gives `P` dimension at most `d`. -/
example {k σ τ : Type*} [Field k] [Finite σ] [Finite τ] {d : ℕ}
    {J : Ideal (MvPolynomial τ k)} {t : MvPolynomial τ k}
    (hJdim : (affineHilbertPolynomial J).natDegree ≤ d)
    {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime) {s : MvPolynomial σ k} (hs : s ∉ P)
    (g : Localization.Away (Ideal.Quotient.mk J t) →ₐ[k]
      Localization.Away (Ideal.Quotient.mk P s))
    (hg : Function.Surjective g) :
    (affineHilbertPolynomial P).natDegree ≤ d :=
  have := hP
  (natDegree_affineHilbertPolynomial_le_of_surjective_away_away
    (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)) g hg).trans hJdim

end CoefficientEvaluationTest
