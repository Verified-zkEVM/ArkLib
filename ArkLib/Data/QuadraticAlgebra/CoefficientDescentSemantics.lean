/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.CoefficientDescentMachine
public import ArkLib.Data.Polynomial.DegreeTruncationSemantics

/-!
# Exact base-coordinate descent and polynomial preservation

Successful descent means exactly that the original vector is the coefficientwise embedding
of the returned base vector. There is no promise that every extension-field candidate descends.
The polynomial statement uses descending Horner coefficients, matching the candidate filter.
-/

@[expose] public section

namespace QuadraticAlgebra.CoefficientDescentMachine

variable {F : Type*} {a b : F} [Zero F] [DecidableEq F]

/-- Every materialized base-coordinate vector survives the checked scan. -/
theorem result_map_base (xs : List F) :
    result (xs.map fun x => (⟨x, 0⟩ : QuadraticAlgebra F a b)) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [result, ih]

/-- Successful descent certifies every coordinate, including leading zero coefficients. -/
theorem result_represents (xs : List (QuadraticAlgebra F a b)) (out : List F)
    (h : result xs = some out) : xs = out.map (fun x => ⟨x, 0⟩) := by
  induction xs generalizing out with
  | nil => cases h; rfl
  | cons x xs ih =>
      by_cases hx : x.im = 0
      · cases hr : result xs with
        | none => simp [result, hx, hr] at h
        | some ys =>
            simp only [result, if_pos hx, hr, Option.map_some, Option.some.injEq] at h
            subst out
            rw [List.map_cons, ← ih ys hr]
            congr 1
            ext <;> simp [hx]
      · simp [result, hx] at h

/-- The returned vector is exactly the unique coordinatewise descent, not just a sound candidate. -/
theorem result_eq_some_iff (xs : List (QuadraticAlgebra F a b)) (out : List F) :
    result xs = some out ↔ xs = out.map (fun x => ⟨x, 0⟩) := by
  constructor
  · exact result_represents xs out
  · intro h
    rw [h, result_map_base]

/-- Accepted vectors preserve their physical width. -/
theorem result_length {xs : List (QuadraticAlgebra F a b)} {out : List F}
    (h : result xs = some out) : out.length = xs.length := by
  rw [result_represents xs out h, List.length_map]

end QuadraticAlgebra.CoefficientDescentMachine

namespace Polynomial.JetHornerMachine

variable {F G : Type*} [CommSemiring F] [CommSemiring G]

/-- Mapping descending coefficients commutes with their Horner polynomial interpretation. -/
theorem map_coefficientPolynomial (f : F →+* G) (cs : List F) :
    (coefficientPolynomial cs).map f = coefficientPolynomial (cs.map f) := by
  induction cs with
  | nil => simp [coefficientPolynomial]
  | cons a cs ih =>
      simp [coefficientPolynomial_cons, ih]

end Polynomial.JetHornerMachine

namespace QuadraticAlgebra.CoefficientDescentMachine

open Polynomial JetHornerMachine

variable {F : Type*} [CommSemiring F] [DecidableEq F] {a b : F}

/-- A successful execution emits a base polynomial whose embedding is the original polynomial,
with exact acceptance at the coefficient-vector level and a bound on that same execution. -/
theorem descent_runFuel_correct (xs : List (QuadraticAlgebra F a b)) :
    ∃ out c, runFuel (2 * xs.length + 4) (.start xs) = (.done out, c) ∧
      (∀ ys, out = some ys ↔ xs = ys.map (algebraMap F (QuadraticAlgebra F a b))) ∧
      (∀ ys, out = some ys → ys.length = xs.length ∧
        (coefficientPolynomial ys).map (algebraMap F (QuadraticAlgebra F a b)) =
          coefficientPolynomial xs) ∧
      c.total ≤ 8 * (2 * xs.length + 4) := by
  obtain ⟨c, hr, hc⟩ := descent_runFuel xs
  refine ⟨result xs, c, hr, ?_, ?_, hc⟩
  · intro ys
    exact result_eq_some_iff xs ys
  · intro ys hy
    refine ⟨result_length hy, ?_⟩
    rw [map_coefficientPolynomial, result_represents xs ys hy]
    rfl

end QuadraticAlgebra.CoefficientDescentMachine
