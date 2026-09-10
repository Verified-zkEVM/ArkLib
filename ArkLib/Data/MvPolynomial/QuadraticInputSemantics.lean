/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.QuadraticInputMachine
public import ArkLib.Data.MvPolynomial.DenseNormalizeRefinement

/-!
# Exact polynomial meaning of materialized quadratic inputs

The actual coefficient-conversion program implements the canonical scalar embedding on the
represented sparse polynomial. It preserves the factor layout, ordering and term count needed
by root enumeration. Sparse coefficients are not supplied by a specification oracle.
-/

@[expose] public section

namespace MvPolynomial.EvaluationMachine

variable {F G : Type*} [CommSemiring F] [CommSemiring G]

/-- A coefficient homomorphism leaves the monomial factor interpretation unchanged. -/
theorem map_factorsPolynomial (f : F →+* G) (fs : List (ℕ × ℕ)) :
    MvPolynomial.map f (factorsPolynomial fs) = factorsPolynomial fs := by
  induction fs with
  | nil => simp [factorsPolynomial]
  | cons p fs ih =>
      rcases p with ⟨i, e⟩
      simp [factorsPolynomial, ih]

/-- Pointwise coefficient mapping commutes with the ordered sparse polynomial interpretation. -/
theorem map_sparsePolynomial (f : F →+* G) (ts : List (Term F)) :
    MvPolynomial.map f (sparsePolynomial ts) =
      sparsePolynomial (ts.map (fun t => (f t.1, t.2))) := by
  induction ts with
  | nil => simp [sparsePolynomial]
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      simp [sparsePolynomial, map_factorsPolynomial, ih]

end MvPolynomial.EvaluationMachine

namespace MvPolynomial.QuadraticInputMachine

variable {F : Type*} [CommSemiring F] {a : F}

/-- Coordinate allocation is pointwise the canonical algebra map. -/
theorem embedded_eq_map (ts : List (Term F)) :
    embedded (a := a) ts =
      ts.map (fun t => (algebraMap F (QuadraticAlgebra F a 0) t.1, t.2)) := by
  apply List.map_congr_left
  intro t _
  congr 1

/-- The output polynomial is exactly the scalar embedding of the input polynomial. -/
theorem sparsePolynomial_embedded (ts : List (Term F)) :
    EvaluationMachine.sparsePolynomial (embedded (a := a) ts) =
      MvPolynomial.map (algebraMap F (QuadraticAlgebra F a 0))
        (EvaluationMachine.sparsePolynomial ts) := by
  rw [embedded_eq_map, EvaluationMachine.map_sparsePolynomial]

/-- Conversion preserves every factor vector, including zero exponents and their order. -/
theorem embedded_factors (ts : List (Term F)) :
    (embedded (a := a) ts).map Prod.snd = ts.map Prod.snd := by
  simp [embedded, List.map_map, Function.comp_def]

/-- Every physical term is retained, without merging or dropping zero coefficients. -/
theorem embedded_length (ts : List (Term F)) : (embedded (a := a) ts).length = ts.length := by
  simp [embedded]

/-- The root finder's fixed variable layout is unchanged by coefficient allocation. -/
theorem embedded_layout (vars : List ℕ) (ts : List (Term F))
    (h : DenseNormalizeMachine.DenseLayout vars ts) :
    DenseNormalizeMachine.DenseLayout vars (embedded (a := a) ts) := by
  refine ⟨h.1, ?_⟩
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact h.2 u hu

/-- Nonzeroness is preserved by the injective scalar embedding. -/
theorem embedded_nonzero (ts : List (Term F))
    (h : EvaluationMachine.sparsePolynomial ts ≠ 0) :
    EvaluationMachine.sparsePolynomial (embedded (a := a) ts) ≠ 0 := by
  rw [sparsePolynomial_embedded]
  exact fun hz => h ((MvPolynomial.map_injective _
    (QuadraticAlgebra.algebraMap_injective (R := F) (a := a) (b := 0)))
      (by simpa using hz))

/-- Execution, exact represented polynomial and linear observed cost concern the same run. -/
theorem evaluation_runFuel_correct (ts : List (Term F)) :
    ∃ out c, runFuel (2 * ts.length + 3) (.scan ts [] : Configuration F a) = (.done out, c) ∧
      out.length = ts.length ∧ out.map Prod.snd = ts.map Prod.snd ∧
      EvaluationMachine.sparsePolynomial out =
        MvPolynomial.map (algebraMap F (QuadraticAlgebra F a 0))
          (EvaluationMachine.sparsePolynomial ts) ∧ c.total = 18 * ts.length + 11 := by
  obtain ⟨c, hr, hc⟩ := evaluation_runFuel (a := a) ts
  exact ⟨embedded ts, c, hr, embedded_length ts, embedded_factors ts,
    sparsePolynomial_embedded ts, hc⟩

end MvPolynomial.QuadraticInputMachine
