import Mathlib

theorem my_favorite_theorem {a b : ℝ} (h₀ : a^3 - 3*a*b^2 = 39) (h₁ : b^3 - 3*a^2*b = 26) :
    a^2 + b^2 = 13 := by
  have h2 : (a ^ 3 - 3 * a * b ^ 2) ^ 2 + (b ^ 3 - 3 * a ^ 2 * b) ^ 2 = (39 : ℝ) ^ 2 + (26 : ℝ) ^ 2 := by
    rw [h₀, h₁]
  have h3 : (a ^ 3 - 3 * a * b ^ 2) ^ 2 + (b ^ 3 - 3 * a ^ 2 * b) ^ 2 = (a^2 + b^2) ^ 3 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b), sq_nonneg (a + b), sq_nonneg (a - b)]
  rw [h3] at h2
  have h4 : (a ^ 2 + b ^ 2) ^ 3 = (13 : ℝ) ^ 3 := by
    norm_num at h2 ⊢
    nlinarith
  have h5 : a ^ 2 + b ^ 2 = (13 : ℝ) := by
    have h6 : (a ^ 2 + b ^ 2 : ℝ) ^ 3 = (13 : ℝ) ^ 3 := h4
    have h7 : a ^ 2 + b ^ 2 = (13 : ℝ) := by
      have h8 : (a ^ 2 + b ^ 2 : ℝ) ^ 3 - (13 : ℝ) ^ 3 = 0 := by linarith
      have h9 : (a ^ 2 + b ^ 2 - (13 : ℝ)) * ((a ^ 2 + b ^ 2) ^ 2 + (a ^ 2 + b ^ 2) * (13 : ℝ) + (13 : ℝ) ^ 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- Case where $a^2 + b^2 - 13 = 0$
        linarith
      · -- Case where $(a^2 + b^2)^2 + (a^2 + b^2) \cdot 13 + 13^2 = 0$
        nlinarith [sq_nonneg (a ^ 2 + b ^ 2 - (13 / 2 : ℝ)), sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg (b ^ 2), sq_nonneg (a ^ 2)]
    exact h7
  nlinarith
