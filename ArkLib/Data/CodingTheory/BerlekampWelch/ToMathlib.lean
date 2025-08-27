/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Polynomial.Basic

theorem polynomial_sum_ext.{u, u_1}
  {R : Type u}
  [Semiring R]
  {S : Type u_1}
  [AddCommMonoid S]
  {p : Polynomial R} {f g : ℕ → R → S}
  (h : ∀ i x, f i x = g i x)
  : p.sum f = p.sum g := by
  aesop (add simp [Polynomial.sum])
