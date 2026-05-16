import Mathlib.LinearAlgebra.Lagrange
import ArkLib.Data.Polynomial.SplitFold
import CompPoly.Univariate.Lagrange
import CompPoly.Univariate.ToPoly.Impl

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

Implemented via `CompPoly.CPolynomial`'s computable Lagrange interpolation, so the check itself is
computable.
-/
def roundConsistencyCheck [Field 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (γ : 𝔽) (pts : Fin n → 𝔽 × 𝔽) (β : 𝔽) : Bool :=
  let p := CompPoly.CPolynomial.CLagrange.interpolate
    (Finset.univ : Finset (Fin n)) (fun i => (pts i).1) (fun i => (pts i).2)
  p.eval γ == β

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
  rw [CompPoly.CPolynomial.eval_toPoly,
      CompPoly.CPolynomial.CLagrange.cinterpolate_eq_interpolate]
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
    simp only [Finset.coe_univ, Set.injOn_univ]
    intro x y hxy
    simp at hxy
    tauto
  }) (by {
      simp only [X_pow_mul_C, Finset.card_univ, Fintype.card_fin]
      apply lt_of_le_of_lt
      · apply Polynomial.degree_sum_le
      · simp only [WithBot.bot_lt_natCast, Finset.sup_lt_iff]
        intro b _
        simp only [degree_mul, degree_pow, degree_X, nsmul_eq_mul, mul_one]
        by_cases heq: eval (s₀ ^ n) (f.splitNth n b) = 0
        · rw [heq,]
          simp
        · rw [degree_C]
          · simp only [zero_add, Nat.cast_lt, Fin.is_lt]
          · tauto
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
