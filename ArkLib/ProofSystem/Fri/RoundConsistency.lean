import Mathlib.LinearAlgebra.Lagrange
import ArkLib.Data.Polynomial.SplitFold

/-!
# FRI Round Consistency

Defines the round consistency check for FRI and proves its completeness. The check verifies that
the Lagrange interpolant through evaluation points at scaled roots of unity equals the polynomial
fold at the challenge point.
-/

open Polynomial

namespace RoundConsistency

variable {𝔽 : Type} [CommSemiring 𝔽] [NoZeroDivisors 𝔽]

/--
The generalized round consistency check: checks that the Lagrange-interpolating polynomial through
`pts` evaluates to `β` at the challenge `γ`. Used in FRI to verify that the next-round value equals
the fold evaluated at the challenge.
-/
noncomputable def roundConsistencyCheck [Field 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (γ : 𝔽) (pts : Fin n → 𝔽 × 𝔽) (β : 𝔽) : Bool :=
  let p := Lagrange.interpolate Finset.univ (fun i => (pts i).1) (fun i => (pts i).2)
  p.eval γ == β

omit [CommSemiring 𝔽] in
private lemma poly_eq_of [Field 𝔽] {p q : 𝔽[X]} {n : ℕ}
      (hp : p.degree < .some n) (hq : q.degree < .some n) (s : Finset 𝔽) :
    s.card ≥ n → (∀ x ∈ s, p.eval x = q.eval x) → p = q := by
  intros h h'
  by_cases h'' : p = 0 ∧ q = 0
  · rw [h''.1, h''.2]
  · have h'' : p ≠ 0 ∨ q ≠ 0 := by tauto
    have : p - q = 0 → p = q := by rw [sub_eq_zero]; exact id
    apply this
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ s
    · intros x h''
      specialize h' x h''
      simp only [eval_sub]
      rw [h']
      simp
    · have {x} : @Nat.cast (WithBot ℕ) WithBot.addMonoidWithOne.toNatCast x = .some x := by rfl
      refine lt_of_lt_of_le ?_ h
      rcases h'' with h'' | h''
      · rw [Polynomial.degree_eq_natDegree h'', this, WithBot.coe_lt_coe] at hp
        apply lt_of_le_of_lt
        · exact Polynomial.natDegree_sub_le _ _
        · by_cases q_eq : q = 0
          · rw [q_eq]
            simp [hp]
          · rw [Polynomial.degree_eq_natDegree q_eq, this, WithBot.coe_lt_coe] at hq
            simp [hp, hq]
      · rw [Polynomial.degree_eq_natDegree h'', this, WithBot.coe_lt_coe] at hq
        apply lt_of_le_of_lt
        · exact Polynomial.natDegree_sub_le _ _
        · by_cases p_eq : p = 0
          · rw [p_eq]
            simp [hq]
          · rw [Polynomial.degree_eq_natDegree p_eq, this, WithBot.coe_lt_coe] at hp
            simp [hp, hq]

/--
Completeness of the round consistency check.

Given a polynomial `f`, challenge `γ`, and `n`-th roots of unity `ω`, when `f` is honestly
evaluated at the scaled points `{ω i * s₀}`, the round consistency check succeeds with the
value `(foldNth n f γ).eval (s₀^n)`. This establishes that the Lagrange interpolant through
the evaluation points matches the n-way folding operation at the challenge point.
-/
lemma generalised_round_consistency_completeness
  {𝔽 : Type} [inst1 : Field 𝔽] [DecidableEq 𝔽] {f : Polynomial 𝔽}
  {n : ℕ} [inst : NeZero n]
  {γ : 𝔽}
  {s₀ : 𝔽}
  {ω : Fin n ↪ 𝔽}
  (h : ∀ i, (ω i) ^ n = 1)
  (h₁ : s₀ ≠ 0)
  :
    roundConsistencyCheck
      γ
      (fun i => (ω i * s₀, f.eval (ω i * s₀))) 
      ((FoldingPolynomial.polyFold f n γ).eval (s₀ ^ n)) = true := by
  unfold roundConsistencyCheck
  simp only [beq_iff_eq]
  have eval_eval₂_pow_eq_eval_pow {s : 𝔽} (i) :
      eval s (eval₂ C (X ^ n) (splitNth f n i)) = (splitNth f n i).eval (s ^ n) := by
    rw [eval₂_eq_sum]
    unfold Polynomial.eval
    rw [Polynomial.eval₂_sum, eval₂_eq_sum]
    congr
    ext e a
    rw [←eval]
    simp
  simp only [polyFold_eq_sum_of_splitNth, map_pow]
  rw [eval_finset_sum]
  conv =>
    rhs
    rhs
    ext i
    rw [eval_mul]
    simp

  apply Eq.trans (b := eval γ <| ∑ i : Fin n, X ^ (↑i : ℕ) * C (eval (s₀ ^ n) (f.splitNth n i)))
  · rw [Lagrange.eq_interpolate (ι := Fin n) 
        (v := fun i => ω i * s₀) 
        (s := Finset.univ)
        (f := (∑ i : Fin n, X ^ (↑i : ℕ) * C (eval (s₀ ^ n) (f.splitNth n i)))) (by {
    simp
    intro x y hxy
    simp at hxy
    tauto
  }) (by {
      simp
      apply lt_of_le_of_lt
      apply Polynomial.degree_sum_le
      simp only [WithBot.bot_lt_natCast, Finset.sup_lt_iff]
      intro b _
      simp
      by_cases heq: eval (s₀ ^ n) (f.splitNth n b) = 0
      · rw [heq,]
        simp
      · rw [degree_C]
        simp
        tauto
    })]
    congr
    ext i
    conv =>
      lhs
      rw [splitNth_def n f]
    rw [eval_finset_sum, eval_finset_sum]
    conv =>
      lhs
      rhs
      ext j
      rw [eval_mul, eval_eval₂_pow_eq_eval_pow]
      simp
    conv =>
      rhs
      rhs
      ext j
      rw [eval_mul]
      simp
      rw [←one_mul (s₀ ^ n), ←h i]
    rw [mul_pow]
  · rw [eval_finset_sum]
    conv =>
      lhs
      rhs
      ext i
      rw [eval_mul]
      simp
  
end RoundConsistency
