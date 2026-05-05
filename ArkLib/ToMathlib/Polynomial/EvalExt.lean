import Mathlib.LinearAlgebra.Lagrange

namespace Polynomial

variable {𝔽 : Type*} [Field 𝔽] 

lemma eq_of_eval_eq_degree {p q : 𝔽[X]} {n : ℕ}
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

lemma eq_of_eval_eq_natDegree {p q : 𝔽[X]} {n : ℕ}
      (hp : p.natDegree < n) (hq : q.natDegree < n) (s : Finset 𝔽) :
    s.card ≥ n → (∀ x ∈ s, p.eval x = q.eval x) → p = q := by
    intros hs h_eval; use eq_of_eval_eq_degree (by
    exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (WithBot.coe_lt_coe.mpr hp)) (by
    exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (WithBot.coe_lt_coe.mpr hq)) s hs h_eval

end Polynomial
