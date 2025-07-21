/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Sqrt

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.Polynomial.Bivariate

namespace GuruswamiSudan 

variable {F : Type} [Field F]
variable [DecidableEq F]
variable {n : ℕ}

open Polynomial

/--
Guruswami-Sudan conditions for the polynomial searched by the decoder.
As in the Berlekamp-Welch case, this can be shown to be equivalent to a 
a system of linear equations.
-/
structure GuruswamiSudanCondition (k r D : ℕ) (ωs f : Fin n → F) (Q : Polynomial (Polynomial F)) where 
  /-- Q ≠ 0 -/
  Q_ne_0 : Q ≠ 0
  /-- Degree of the polynomial. -/
  Q_deg : Bivariate.weightedDegree Q 1 (k-1) ≤ D 
  /-- (ωs i, f i) must be root of the polynomial Q. -/
  Q_roots : ∀ i, (Q.eval (C <| f i)).eval (ωs i) = 0
  /-- Multiplicity of the roots is equal to r. -/
  Q_multiplicity : ∀ i, r = Bivariate.rootMultiplicity Q (ωs i) (f i)

/-- Guruswami-Sudan decoder. -/
opaque decoder (k r D e : ℕ) (ωs f : Fin n → F) : List F[X] := sorry

/-- Each decoded codeword has to be e-far from the received message. -/
theorem decoder_mem_impl_dist {k r D e : ℕ} {ωs f : Fin n → F} {p : F[X]}
  (h_in : p ∈ decoder k r D e ωs f)
  (h_e : e ≤ n - Real.sqrt (k * n))
  :
  Δ₀(f, p.eval ∘ ωs) ≤ e := by sorry

/-- If a codeword is e-far from the received message it appears in the output of 
the decoder.
-/
theorem decoder_dist_impl_mem {k r D e : ℕ} {ωs f : Fin n → F} {p : F[X]}
  (h_e : e ≤ n - Real.sqrt (k * n))
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e)
  :
  p ∈ decoder k r D e ωs f := by sorry 

noncomputable def proximity_gap_degree_bound (k m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  Nat.floor ((((m : ℚ) + (1 : ℚ)/2)*(Real.sqrt rho))*n)

noncomputable def proximity_gap_johnson (k m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  Nat.floor ((1 : ℝ) - Real.sqrt rho - Real.sqrt rho / (2 * m))

/-- Lemma 5.3 from the Proximity gap paper -/ 
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs f : Fin n → F} :
  ∃ Q, GuruswamiSudanCondition k m (proximity_gap_degree_bound (n := n) k m) ωs f Q := by
  sorry

lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs f : Fin n → F} 
  {Q : F[X][X]} {p : F[X]} 
  (h : Δ₀(f, p.eval ∘ f) ≤ proximity_gap_johnson (n := n) k m)
  :
  ((X : F[X][X]) - C p) ∣ Q := by sorry 

end GuruswamiSudan 
