/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-- A type class for fields of characteristic ≠ 2, extending `Field`. -/
class NonBinaryField (F : Type*) extends Field F where
  char_neq_2 : (2 : F) ≠ 0

export NonBinaryField (char_neq_2)

attribute [simp] char_neq_2

section NonBinaryField

variable {F : Type*} [NonBinaryField F]

@[simp]
lemma two_mul_inv_two : (2 : F) * 2⁻¹ = 1 := by simp

@[simp]
lemma inv_two_mul_two : 2⁻¹ * (2 : F) = 1 := by simp

end NonBinaryField

section

variable {F : Type*} [Field F]

open Polynomial

private lemma coeffs_of_comp_minus_x_pos_degree {f : Polynomial F} {n : ℕ} (h : 0 < f.degree) :
    (f.comp (-X)).coeff n = if Even n then f.coeff n else -f.coeff n := by
  revert n
  apply degree_pos_induction_on (h0 := h) (P := fun f => _)
  · aesop (add simp coeff_X)
  · rintro _ _ _ (_ | _) <;> aesop (add simp [Nat.even_add_one, Nat.even_iff])
  · rintro _ _ _ _ (_ | _) <;> aesop

theorem coeffs_of_comp_minus_x {f : Polynomial F} {n : ℕ} :
    (f.comp (-X)).coeff n = if Even n then f.coeff n else -f.coeff n := by
    by_cases hpos : 0 < f.degree
    · rw [coeffs_of_comp_minus_x_pos_degree hpos]
    · have : f.natDegree = 0 := by aesop (add simp natDegree_pos_iff_degree_pos.symm)
      cases n <;> aesop (add simp natDegree_eq_zero)

private lemma comp_x_square_coeff_pos_deg {f : Polynomial F} {n : ℕ} (h : 0 < f.degree) :
  (f.comp (X * X)).coeff n = if Even n then f.coeff (n / 2) else 0 := by
  revert n
  apply degree_pos_induction_on (h0 := h) (P := fun f => _)
  · rintro _ _ (_ | n) <;>
    aesop (add simp [coeff_X, Even]) (add safe [(by existsi 1), (by omega)])
  · rintro _ _ _ (_ | _ | n) <;> try simp [←mul_assoc]
    have : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
    split <;> aesop (add safe (by omega)) (add simp [Nat.even_iff])
  · rintro _ _ _ _ (_ | _ | n) <;> try simp_all
    have : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
    simp_all only [coeff_C_succ, add_zero]

theorem comp_x_square_coeff {f : Polynomial F} {n : ℕ} :
  (f.comp (X * X)).coeff n = if Even n then f.coeff (n / 2) else 0 := by
  by_cases hpos : 0 < f.degree
  · rw [comp_x_square_coeff_pos_deg hpos]
  · obtain ⟨_, hx⟩ := show ∃ x, C x = f by
      aesop (add simp [natDegree_pos_iff_degree_pos.symm, natDegree_eq_zero])
    rcases n with _ | _ | n <;> (subst hx; simp_all)
    have : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
    aesop

lemma eq_poly_deg_one {a b c d : F} {x₁ x₂ : F}
  (h1 : a + b * x₁ = c + d * x₁)
  (h2 : a + b * x₂ = c + d * x₂)
  (h1_2 : x₁ ≠ x₂) :
  Polynomial.C a + Polynomial.C b * Polynomial.X
    = Polynomial.C c + Polynomial.C d * Polynomial.X := by
  by_cases h_b_d : b = d
  · aesop
  · exact absurd
            (by apply mul_left_cancel₀ (sub_ne_zero_of_ne (show d ≠ b by aesop))
                linear_combination -(1 * h1) + h2)
            h1_2

end
