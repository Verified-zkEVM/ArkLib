/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.StandardMonomials

/-!
# Acceptance tests for standard monomials and the affine Hilbert function

The examples derive the `degLex` count from the statement for an arbitrary graded monomial order,
compute the Hilbert function of the zero ideal, and compute both sides of the count for the ideal
`(X₀ - X₁²)` at degree bound `1`. For `degLex` the leading exponent is `X₁²`, all three monomials
`1, X₀, X₁` are standard, and the Hilbert function is `3`. For `lex` the leading exponent is `X₀`,
only `1, X₁` are standard, and the count is `2`. So the graded hypothesis on the monomial order
cannot be dropped.
-/

open MvPolynomial MonomialOrder Finsupp

namespace StandardMonomialsTest

/-- The `degLex` count, derived from the statement for any graded order. -/
example {σ k : Type*} [Field k] [LinearOrder σ] [WellFoundedGT σ] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (N : ℕ) :
    affineHilbertFunction I N =
      {e : σ →₀ ℕ | e ∈ degLex.standardExponents I ∧ e.degree ≤ N}.ncard :=
  degLex.affineHilbertFunction_eq_ncard_standardExponents
    (fun _ _ h ↦ degree_le_degree_of_degLex_le h) I N

/-- With no relations, the three monomials `1, X₀, X₁` span the degree-one piece. -/
example : affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) 1 = 3 := by
  rw [affineHilbertFunction_bot]
  simp

/-- For the unit ideal there are no standard exponents, matching the zero Hilbert function. -/
example (N : ℕ) :
    {e : Fin 2 →₀ ℕ | e ∈ degLex.standardExponents (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      e.degree ≤ N}.ncard = 0 := by
  simp

/-- The binomial `X₀ - X₁²`. -/
noncomputable abbrev binomial : MvPolynomial (Fin 2) ℚ := X 0 - monomial (single 1 2) 1

/-- Under `degLex` the leading exponent of `X₀ - X₁²` is `X₁²`. -/
theorem degLex_degree_binomial : degLex.degree binomial = single 1 2 := by
  classical
  have hlt : degLex.degree (X 0 : MvPolynomial (Fin 2) ℚ) ≺[degLex]
      degLex.degree (monomial (single 1 2) (1 : ℚ)) := by
    rw [degree_X, degree_monomial, ite_eq_right one_ne_zero, degLex_lt_iff, DegLex.lt_iff]
    left
    simp
  rw [binomial, ← neg_sub, degree_neg, degree_sub_of_lt hlt, degree_monomial,
    ite_eq_right one_ne_zero]

/-- Under `lex` the leading exponent of `X₀ - X₁²` is `X₀`. -/
theorem lex_degree_binomial : lex.degree binomial = single 0 1 := by
  classical
  have hlt : lex.degree (monomial (single 1 2) (1 : ℚ)) ≺[lex]
      lex.degree (X 0 : MvPolynomial (Fin 2) ℚ) := by
    rw [degree_X, degree_monomial, ite_eq_right one_ne_zero, lex_lt_iff, Finsupp.Lex.lt_iff]
    exact ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), by simp⟩
  rw [binomial, degree_sub_of_lt hlt, degree_X]

/-- The binomial is nonzero, since its `lex` leading exponent is nonzero. -/
theorem binomial_ne_zero : binomial ≠ 0 := by
  intro h
  have := lex_degree_binomial
  rw [h, degree_zero] at this
  exact absurd (congrArg (· 0) this) (by simp)

/-- For `degLex` every exponent of degree at most one is standard for `(X₀ - X₁²)`, so the Hilbert
function at `1` is `3`. -/
theorem affineHilbertFunction_binomial_one :
    affineHilbertFunction (Ideal.span {binomial}) 1 = 3 := by
  rw [affineHilbertFunction_eq_standard_count]
  have hset : {e : Fin 2 →₀ ℕ | e ∈ degLex.standardExponents (Ideal.span {binomial}) ∧
      e.degree ≤ 1} = {e | e.degree ≤ 1} := by
    ext e
    simp only [Set.mem_ofPred_eq, degLex.mem_standardExponents_span_singleton binomial_ne_zero,
      degLex_degree_binomial, and_iff_right_iff_imp]
    intro he hle
    have := degree_mono hle
    simp at this
    omega
  rw [hset, ncard_setOf_degree_le]
  simp

/-- For `lex` only `1` and `X₁` are standard of degree at most one, so the lex count is `2`, not
the Hilbert function value `3`. -/
theorem lex_count_binomial_one :
    {e : Fin 2 →₀ ℕ | e ∈ lex.standardExponents (Ideal.span {binomial}) ∧ e.degree ≤ 1}.ncard =
      2 := by
  have hset : {e : Fin 2 →₀ ℕ | e ∈ lex.standardExponents (Ideal.span {binomial}) ∧
      e.degree ≤ 1} = {0, single 1 1} := by
    ext e
    simp only [Set.mem_ofPred_eq, lex.mem_standardExponents_span_singleton binomial_ne_zero,
      lex_degree_binomial, single_le_iff, degree_eq_sum, Fin.sum_univ_two, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finsupp.ext_iff, Fin.forall_fin_two]
    simp
    omega
  rw [hset, Set.ncard_pair]
  intro h
  simpa using congrArg (· 1) h

/-- The graded hypothesis is needed: the count of standard exponents for `lex` differs from the
affine Hilbert function. -/
example :
    affineHilbertFunction (Ideal.span {binomial}) 1 ≠
      {e : Fin 2 →₀ ℕ | e ∈ lex.standardExponents (Ideal.span {binomial}) ∧
        e.degree ≤ 1}.ncard := by
  rw [affineHilbertFunction_binomial_one, lex_count_binomial_one]
  decide

/-- The Hilbert function of `(X₀ - X₁²)` agrees for large degree bounds with a polynomial of degree
at most two. -/
example :
    ∃ P : Polynomial ℚ, P.natDegree ≤ 2 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      P.eval (N : ℚ) = affineHilbertFunction (Ideal.span {binomial}) N := by
  simpa using exists_eval_eq_affineHilbertFunction ℚ (Ideal.span {binomial})

/-- Standard exponents for a principal ideal are those not above the leading exponent of the
generator. -/
example (e : Fin 2 →₀ ℕ) :
    e ∈ degLex.standardExponents (Ideal.span {binomial}) ↔ e 1 < 2 := by
  rw [degLex.mem_standardExponents_span_singleton binomial_ne_zero, degLex_degree_binomial,
    single_le_iff]
  omega

end StandardMonomialsTest
