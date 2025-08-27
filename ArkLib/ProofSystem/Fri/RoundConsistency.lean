/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.EvenAndOdd

/-!
  # Round consistency check for FRI

  We define the fold operation lying at the core
  of the FRI protocol. We define the round consistency
  check that is performed in transition between
  rounds in the FRI protocol and prove it is
  (perfectly) complete.
-/

variable {F : Type*} [NonBinaryField F] [DecidableEq F]

open Polynomial

/-- The fold operations used in the FRI protocol.
  Takes a polynomial `f` a challenge `α` and
  "folds" the even and the odd parts of the polynomial
  with the coefficient `α`.
-/
noncomputable def Polynomial.foldEvenOdd (f : Polynomial F) (α : F) : Polynomial F
    := (evenPart_x f) + (Polynomial.C α) * (oddPart_x f)

/-- The unique linear polynomial passing through
  the points `a₀` and `a₁`.
-/
noncomputable def line_through_two_points (a₀ a₁ : F × F) : Polynomial F :=
  let x₀ := a₀.1
  let y₀ := a₀.2
  let x₁ := a₁.1
  let y₁ := a₁.2
  let m := (y₁ - y₀) / (x₁ - x₀)
  Polynomial.C (y₀ - m * x₀) + Polynomial.C m * Polynomial.X

/-- The round consistency check.
  Check that `(s₀, α₀)`, `(s₁, α₁)`, and `(x₀, β)`
  lie on the same line.
-/
noncomputable def consistency_check (x₀ : F) (s₀ s₁ : F) (α₀ α₁ β : F) : Bool :=
  let p := line_through_two_points (s₀, α₀) (s₁, α₁)
  let p_x₀ := p.eval x₀
  p_x₀ == β

omit [DecidableEq F] in
/-- The identity for a line passing through
  two evaluations of a polynomial on two square
  roots of the same field element.
-/
private lemma line_passing_through_a_poly
  {f : Polynomial F}
  {s₀ : F}
  (h₁ : s₀ ≠ 0)
  :
  line_through_two_points (s₀, f.eval s₀) (-s₀, f.eval (-s₀)) =
    Polynomial.C (Polynomial.eval (s₀^2) (evenPart_x f))
      + (Polynomial.C (Polynomial.eval (s₀^2) (oddPart_x f))) * Polynomial.X  := by
  simp only [line_through_two_points, pow_two]
  apply eq_poly_deg_one (x₁ := s₀) (x₂ := -s₀)
  · rw (occs := [1]) [f_eq_evenPart_plus_x_oddPart (f := f)]
    aesop (add simp [evenPart_x_eval_eq, oddPart_x_eval_eq], unsafe (by ring))
  · rw [evenPart_x_eval_eq, oddPart_x_eval_eq]
    conv_lhs => rw [f_eq_evenPart_plus_x_oddPart (f := f)]
    aesop (add simp [even_eval, evenPart_even, oddPart_even], safe (by field_simp; ring))
  · exact fun c ↦ absurd (mul_left_cancel₀ NonBinaryField.char_neq_2
      (by rw (occs := [1]) [two_mul _, c]; simp)) h₁

/-- The completeness property of the round consistency
  check. I.e., `(s₀, f(s₀))`, `(-s₀, f(-s₀))`, and
  `(s₀², (folda f)(x₀))` lie on the same line for nonzero `s₀`.
-/
lemma consistency_check_comp {f : Polynomial F}
  {x₀ : F}
  {s₀ : F}
  (h₁ : s₀ ≠ 0)
  : consistency_check x₀ s₀
    (-s₀)
    (f.eval s₀)
    (f.eval (-s₀))
    (Polynomial.eval (s₀ ^ 2) (foldEvenOdd f x₀)) = true := by
  aesop (add simp [
    consistency_check, line_passing_through_a_poly, foldEvenOdd, oddPart_x_eval_eq], safe (by ring)
  )
