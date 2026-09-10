/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.DirectRegularCoefficient
/-!
# Deterministic direct regular lifting

Direct affine coefficient solves replace exhaustive field scans. The executable definitions require
no finite enumeration and retain only a single optional prefix. A final degree and full-residual
filter is essential: locally valid prefixes need not solve the full differential equation.

For a regular initial jet below the characteristic, the returned singleton or empty set equals the
existing complete exhaustive solver. This includes requested degrees below the initial jet order,
where no lift runs and the final degree check can reject the supplied prefix. Outside regularity,
`none` can also mean that a zero-slope affine solve was unavailable.

This is functional refinement only. Residual evaluation and polynomial operations still lack the
closed operational cost adequacy required for a lifting runtime theorem.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open CompPoly

variable {F : Type*} [Field F] [DecidableEq F] {r : ℕ}

/-- Iterate direct coefficient solves at residual orders `1` through `steps`. -/
def directRegularIteration (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) : ℕ → Option (CPolynomial F)
  | 0 => some P
  | steps + 1 => (directRegularIteration Q center P steps).bind fun previous ↦
      (effectiveDirectRegularCoefficient Q center previous (steps + 1)).map fun gamma ↦
        effectiveRegularCandidate (steps + 1) r previous gamma

/-- Retain a direct candidate only after checking its degree and complete residual. -/
def directRegularSolution (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (jet : Fin (r + 1) → F) (D : ℕ) : Option (CPolynomial F) :=
  (directRegularIteration Q center (effectiveInitialPrefix jet) (D - r)).bind fun candidate ↦
    if candidate.natDegree ≤ D ∧ effectiveResidual Q center candidate = 0 then
      some candidate else none

/-- Every successful direct prefix respects its construction depth, independently of regularity.
This supplies the degree premise for scalar residual sampling at intermediate stages. -/
theorem directRegularIteration_natDegree_le
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (initial : CPolynomial F)
    (hdegree : initial.natDegree ≤ r) (steps : ℕ) (P : CPolynomial F)
    (hresult : directRegularIteration Q center initial steps = some P) :
    P.natDegree ≤ r + steps := by
  induction steps generalizing P with
  | zero =>
      simp only [directRegularIteration, Option.some.injEq] at hresult
      simpa only [← hresult, Nat.add_zero] using hdegree
  | succ steps ih =>
      cases hprevious : directRegularIteration Q center initial steps with
      | none => simp [directRegularIteration, hprevious] at hresult
      | some previous =>
          cases hnext : effectiveDirectRegularCoefficient Q center previous (steps + 1) with
          | none => simp [directRegularIteration, hprevious, hnext] at hresult
          | some gamma =>
              simp only [directRegularIteration, hprevious, Option.bind_some, hnext,
                Option.map_some, Option.some.injEq] at hresult
              rw [← hresult, effectiveRegularCandidate]
              apply CPolynomial.natDegree_add_le _ _ |>.trans
              apply max_le
              · have h := ih previous hprevious
                omega
              · by_cases hgamma : gamma = 0
                · rw [CPolynomial.natDegree_toPoly, CPolynomial.monomial_toPoly]
                  simp [hgamma]
                · rw [CPolynomial.natDegree_monomial hgamma]
                  omega

/-- The actual initial jet satisfies the initial bound used by the direct-prefix invariant. -/
theorem natDegree_effectiveInitialPrefix_le (jet : Fin (r + 1) → F) :
    (effectiveInitialPrefix jet).natDegree ≤ r := by
  rw [CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_le_of_degree_le (degree_effectiveInitialPrefix_toPoly_le jet)

/-- Every permitted direct stage succeeds and is the unique exhaustive-scan survivor. -/
theorem directRegularIteration_eq_some_and_candidates [Fintype F]
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (jet : Fin (r + 1) → F)
    (hregular : IsRegularJet (semanticEquation Q) (Fin.last r) center jet)
    (D : ℕ) (hD : D < ringChar F) (steps : ℕ) (hsteps : steps ≤ D - r) :
    ∃ P, directRegularIteration Q center (effectiveInitialPrefix jet) steps = some P ∧
      (effectiveRegularIteration Q center (effectiveInitialPrefix jet) steps).candidates = {P} := by
  induction steps with
  | zero => exact ⟨effectiveInitialPrefix jet, rfl, rfl⟩
  | succ steps ih =>
      obtain ⟨previous, hdirect, hset⟩ := ih (by omega)
      have hprevious : previous ∈
          (effectiveRegularIteration Q center (effectiveInitialPrefix jet) steps).candidates := by
        rw [hset]
        exact Finset.mem_singleton_self _
      obtain ⟨gamma, hgamma, hscan⟩ := effectiveDirectRegularCoefficient_exists_of_survivor
        Q center jet hregular D steps (by omega) hD previous hprevious
      refine ⟨effectiveRegularCandidate (steps + 1) r previous gamma, ?_, ?_⟩
      · simp only [directRegularIteration, hdirect, Option.bind_some, hgamma, Option.map_some]
      · ext candidate
        rw [mem_effectiveRegularIteration_succ_candidates]
        simp only [hset, Finset.mem_singleton, exists_eq_left, hscan]
        simp [eq_comm]

/-- With regularity and characteristic hypotheses, the final optional result equals the entire
exhaustive solution set, including the zero-stage case `D < r`. -/
theorem directRegularSolution_toFinset_eq [Fintype F]
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (jet : Fin (r + 1) → F)
    (hregular : IsRegularJet (semanticEquation Q) (Fin.last r) center jet)
    (D : ℕ) (hD : D < ringChar F) :
    (directRegularSolution Q center jet D).toFinset =
      effectiveRegularSolutions Q center (effectiveInitialPrefix jet) D := by
  obtain ⟨P, hdirect, hset⟩ := directRegularIteration_eq_some_and_candidates
    Q center jet hregular D hD (D - r) le_rfl
  rw [directRegularSolution, hdirect]
  simp only [Option.bind_some, effectiveRegularSolutions, effectiveRegularPrefixes, hset]
  by_cases h : P.natDegree ≤ D ∧ effectiveResidual Q center P = 0
  · simp only [h.1, h.2, and_self, ↓reduceIte, Option.toFinset_some]
    ext candidate
    simp only [Finset.mem_filter, Finset.mem_singleton, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq, iff_self_and]
    rintro rfl
    exact h
  · simp only [h, ↓reduceIte, Option.toFinset_none]
    ext candidate
    simp only [Finset.notMem_empty, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Finset.mem_filter, Finset.mem_singleton, false_iff, not_and]
    rintro rfl hdegree hzero
    exact h ⟨hdegree, hzero⟩

/-- Exact bounded-equation and initial-jet specification of the deterministic solver. -/
theorem directRegularSolution_eq_some_iff [Finite F]
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (jet : Fin (r + 1) → F)
    (hregular : IsRegularJet (semanticEquation Q) (Fin.last r) center jet)
    (D : ℕ) (hD : D < ringChar F) (P : CPolynomial F) :
    directRegularSolution Q center jet D = some P ↔
      P.natDegree ≤ D ∧
        differentialSpecialization (semanticEquation Q) (unshift center P) = 0 ∧
          polynomialJet center (unshift center P) = jet := by
  let := Fintype.ofFinite F
  have h := mem_effectiveRegularSolutions_iff_solution_jet Q center jet P D
  rw [← directRegularSolution_toFinset_eq Q center jet hregular D hD] at h
  simpa only [Option.mem_toFinset, Option.mem_def] using h

end ReedSolomon.HiddenDerivative
