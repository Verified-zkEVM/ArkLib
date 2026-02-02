/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import ArkLib.Data.CodingTheory.BerlekampWelch.Condition

namespace BerlekampWelch

variable {α : Type} {F : Type} [Field F]
         {n e k : ℕ} {p : Polynomial F}
         {ωs f : Fin n → F}
         [DecidableEq F]

open Polynomial

private noncomputable def E (ωs : Fin n → F)
  (f : Fin n → F) (p : Polynomial F) (e : ℕ) : Polynomial F :=
  X ^ (e - (Δ₀(f, p.eval ∘ ωs) : ℕ)) * ElocPolyF ωs f p

private lemma natDegree_E
  (h : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) :
  (E (ωs := ωs) f p e).natDegree = e := by
  simp only [E]
  rw [natDegree_mul (by aesop) (by aesop)]
  aesop
    (add simp natDegree_mul)
    (erase simp BerlekampWelch.elocPolyF_eq_elocPoly')
    (add safe (by omega))

@[simp]
private lemma E_ne_zero : (E ωs f p e) ≠ 0 := by
  aesop (add simp E)

private lemma errors_are_roots_of_E {i : Fin n}
  (h : f i ≠ p.eval (ωs i)) : (E ωs f p e).eval (ωs i) = 0  := by
  aesop
    (erase simp [BerlekampWelch.elocPolyF_eq_elocPoly'])
    (add simp [E, BerlekampWelch.errors_are_roots_of_elocPolyF])

@[simp]
private lemma leadingCoeff_E : (E ωs f p e).leadingCoeff = 1 := by
  simp [E]

private lemma leadingCoeff_E'
  (h_dist : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  : (E ωs f p e).coeff e = 1 := by
  generalize he : (E ωs f p e) = E
  rw [←natDegree_E h_dist]
  aesop

private noncomputable def Q (ωs : Fin n → F)
  (f : Fin n → F) (p : Polynomial F) (e : ℕ) : Polynomial F :=
  p * (E ωs f p e)

private lemma natDegree_Q
  (h : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e) :
  (Q ωs f p e).natDegree ≤ e + p.natDegree := by
  by_cases p = 0 <;>
  aesop
    (add simp [Q, natDegree_mul, E_ne_zero, natDegree_E])
    (add safe (by omega))

private lemma Q_ne_zero (hne : p ≠ 0) : Q ωs f p e ≠ 0 := by
  aesop (add simp [Q, E_ne_zero])

private lemma solutionToQ_from_Q
  (h_p_deg : p.natDegree < k)
  (h_dist : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  : solutionToQ e k (E_and_Q_to_a_solution e (E ωs f p e) (Q ωs f p e)) = Q ωs f p e := by
  refine Polynomial.ext fun i ↦ ?p₁
  simp [Fin.liftF]
  split_ifs <;>
  · by_cases hne : p = 0
    · simp [Q, hne]
    · by_contra hq
      have hdeg := Polynomial.le_degree_of_ne_zero (n := i) (p := Q ωs f p e) (by aesop)
      aesop
        (add safe forward (natDegree_Q h_dist))
        (add simp [Q_ne_zero, Polynomial.degree_eq_natDegree])
        (add safe (by omega))

private lemma solutionToE_from_E
  (h_p_deg : p.natDegree < k)
  (h_dist : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  : solutionToE e k (E_and_Q_to_a_solution e (E ωs f p e) (Q ωs f p e)) = E ωs f p e := by
  apply Polynomial.ext
  intro i
  simp
  split_ifs <;>
    try aesop (config := {warnOnNonterminal := false})
              (add simp [Fin.liftF, leadingCoeff_E'])
              (add safe (by omega))
  by_contra he
  have hdeg := Polynomial.le_degree_of_ne_zero (n := i) (p := E ωs f p e) (by aesop)
  aesop
    (add safe forward natDegree_E)
    (add simp [E_ne_zero, Polynomial.degree_eq_natDegree])
    (add safe (by omega))

private lemma E_and_Q_BerlekampWelch_condition
  (h_p_deg : p.natDegree < k)
  (h_dist : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  : BerlekampWelchCondition e k ωs f (E ωs f p e) (Q ωs f p e) := by
  exact ⟨
  by {
    intro i
    by_cases hi : f i = p.eval (ωs i)
      <;>
      aesop
        (erase simp BerlekampWelch.elocPolyF_eq_elocPoly')
        (add simp [E, Q, BerlekampWelch.errors_are_roots_of_elocPolyF])
  },
  by simp [natDegree_E h_dist],
  by simp [leadingCoeff_E' h_dist],
  by sorry
  -- by aesop
  --   (add safe forward (natDegree_Q h_dist))
    -- (add safe (by omega))
  ⟩

/-- If there has happened up to `e` errors
  then any other `E'` and `Q'` satifying Berlekamp-Welch
  condition will result in the same quotient
  `Q' \ E' = p`.
-/
lemma Q'_div_E'_eq_p
  [NeZero n]
  {E' Q' : Polynomial F}
  {ωs f : Fin n → F}
  (hp_deg : p.natDegree < k)
  (he : 2 * e < n - k + 1)
  (hk_n : k ≤ n)
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  (h_diff : Function.Injective ωs)
  (h_Q' : Q' ≠ 0)
  (hp : p ≠ 0)
  (h_cond : BerlekampWelchCondition e k ωs f E' Q')
  : E' ∣ Q' ∧ Q' / E' = p  := by
  have h_eq := E_and_Q_unique he hk_n (Q_ne_zero hp) h_Q' h_diff
    (E_and_Q_BerlekampWelch_condition hp_deg h_ham)
    h_cond
  have : Q' = E' * p := by
    simp [Q] at h_eq
    rw [←mul_assoc, mul_comm (E' * _)] at h_eq; simp_all
  simp_all

/-- If only up to `e` errors happened `linsolve` cannot fail to find a solution. -/
lemma linsolve_always_some_berlekamp_welch
  [NeZero n]
  (hp_deg : p.natDegree < k)
  (h_ham : (Δ₀(f, p.eval ∘ ωs) : ℕ) ≤ e)
  : linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f) ≠ none := fun contr ↦ by
    refine linsolve_none contr ⟨E_and_Q_to_a_solution e (E ωs f p e) (Q ωs f p e), ?p₁⟩
    rw [←IsBerlekampWelchSolution_def]
    simp [
      BerlekampWelchCondition_iff_Solution,
      solutionToQ_from_Q hp_deg h_ham,
      solutionToE_from_E hp_deg h_ham,
      E_and_Q_BerlekampWelch_condition hp_deg h_ham]

end BerlekampWelch
