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
    (γ : 𝔽) (pts : List (𝔽 × 𝔽)) (β : 𝔽) : Bool :=
  let p := Lagrange.interpolate Finset.univ (fun i => (pts.get i).1) (fun i => (pts.get i).2)
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
      (List.map (fun i => (ω i * s₀, f.eval (ω i * s₀))) (List.finRange n))
      ((foldNth n f γ).eval (s₀^n)) = true := by
  unfold roundConsistencyCheck
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
    beq_iff_eq]
  unfold foldNth
  conv =>
    left
    rw [splitNth_def n f]
  rw [Polynomial.eval_finset_sum]
  simp only [eval_mul, eval_C, eval_pow]
  conv =>
    left
    congr
    · skip
    rhs
    ext i
    rw [Polynomial.eval_finset_sum]
    congr
    · skip
    ext j
    rw [eval_mul, eval_pow, eval_X, splitNth_eval_comp_pow]
    rhs
    rw [mul_pow, h, one_mul]
  generalize heq : @Lagrange.interpolate 𝔽 inst1 (Fin _) _ _ _ _ = p'
  have :
    p' = ∑ j, Polynomial.X ^ j.1 * Polynomial.C (eval (s₀ ^ n) (splitNth f n j)) := by
    have p'_deg : p'.degree < .some n := by
      rw [←heq]
      have : n = (Finset.univ : Finset (Fin n)).card := by simp
      simp_rw [this]
      conv =>
        lhs
        congr
        rhs
        ext i
        rw [Finset.sum_fin_eq_sum_range]
      have interp_deg :=
        @Lagrange.degree_interpolate_lt 𝔽 _ (Fin n) _ Finset.univ
          (fun i ↦ ω i * s₀)
          (fun i ↦ ∑ i_1 ∈ Finset.range n,
                      if h : i_1 < n
                      then
                        (ω i * s₀) ^ i_1 *
                        eval (s₀ ^ (Finset.univ : Finset (Fin n)).card) (splitNth f n ⟨i_1, h⟩)
                      else 0
          )
          (by
            intros x₁ _ x₂ _
            simp only [mul_eq_mul_right_iff, EmbeddingLike.apply_eq_iff_eq]
            intros h
            rcases h with h | h
            · exact h
            · exfalso; apply h₁; exact h
          )
      have :
        (List.map
          (fun i ↦ (ω i * s₀, eval (ω i * s₀) (∑ i, X ^ i.1 * eval₂ C (X ^ n) (splitNth f n i))))
          (List.finRange n)
        ).length = n := by simp
      convert interp_deg
      congr
      exact (Fin.heq_fun_iff this).mpr (congrFun rfl)
      exact (Fin.heq_fun_iff this).mpr (congrFun rfl)
      rw [this]
      exact (Fin.heq_fun_iff this).mpr (congrFun rfl)
      exact (Fin.heq_fun_iff this).mpr (congrFun rfl)

      -- rw [this]
      exact (Fin.heq_fun_iff this).mpr (congrFun rfl)
      exact (Fin.heq_fun_iff this).mpr (congrFun rfl)
    have h₂ : (∑ (j : Fin n), X ^ j.1 * C (eval (s₀ ^ n) (splitNth f n j))).degree < .some n := by
      apply lt_of_le_of_lt
      exact Polynomial.degree_sum_le Finset.univ
            (fun j => X ^ j.1 * C (eval (s₀ ^ n) (splitNth f n j)))
      simp only [X_pow_mul_C, degree_mul, degree_pow, degree_X, nsmul_eq_mul, mul_one,
        WithBot.bot_lt_coe, Finset.sup_lt_iff, Finset.mem_univ, forall_const]
      intros b
      by_cases h' : (eval (s₀ ^ n) (splitNth f n b)) = 0
      · simp [h']
      · simp only [ne_eq, h', not_false_eq_true, degree_C, zero_add]
        erw [WithBot.coe_lt_coe]
        simp
    let fmul : 𝔽 ↪ 𝔽 := ⟨fun x => x * s₀, by intros _; aesop⟩
    apply poly_eq_of p'_deg h₂ (Finset.map (Function.Embedding.trans ω fmul) Finset.univ) (by simp)
    intros x h'
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at h'
    rcases h' with ⟨a, h'⟩
    simp only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, fmul] at h'
    rw [←h', ←heq]
    simp only [Lagrange.interpolate_apply, map_sum, map_mul, map_pow, X_pow_mul_C]
    rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    conv =>
      lhs
      congr
      · skip
      ext x
      rw [Polynomial.eval_finset_sum]
      lhs
      congr
      · skip
      ext i
      rw [eval_mul, eval_C, eval_pow, eval_mul, eval_C, eval_C]
    have sum_eq :=
      Finset.sum_eq_single (s := Finset.univ)
        (f := fun x => (∑ i, (ω x * s₀) ^ i.1 * eval (s₀ ^ n) (splitNth f n i)) *
      eval (ω a * s₀) (Lagrange.basis Finset.univ (fun (i : Fin n) ↦ ω i * s₀) x)) a
    rw
      [
        Lagrange.eval_basis_self (v := fun i ↦ ω i * s₀) (by intro x₁ _ x₂ _ h; exact ω.injective (mul_right_cancel₀ h₁ h)) (Finset.mem_univ a),
        mul_one
      ] at sum_eq
    have sum_eq := sum_eq
      (by
        intros i h h'
        apply mul_eq_zero_of_right
        exact Lagrange.eval_basis_of_ne (v := fun i ↦ ω i * s₀) h' (Finset.mem_univ _)
      ) (by simp)
    conv at sum_eq =>
      rhs
      congr
      · skip
      ext i
      rw [mul_comm]
    rw [←sum_eq]
    have eq :
      (List.map
        (fun i ↦
          (ω i * s₀, eval (ω i * s₀) (∑ i : Fin n, X ^ i.1 * eval₂ C (X ^ n) (splitNth f n i))))
        (List.finRange n)
      ).length = n := by simp
    rw [Finset.sum_fin_eq_sum_range]; conv_rhs => rw [Finset.sum_fin_eq_sum_range]
    congr
    simp
    ext i
    congr
    ext j
    congr 2
    congr 1
    simp
    swap
    congr 1
    simp
    congr 1
    swap
    exact (Fin.heq_fun_iff eq).mpr (congrFun rfl)
    swap
    exact (Fin.heq_ext_iff eq).mpr rfl
    rw [eq]
  rw [this, Polynomial.eval_finset_sum]
  conv =>
    lhs
    congr
    · skip
    ext i
    rw [eval_mul, eval_pow, eval_X, eval_C]

end RoundConsistency
