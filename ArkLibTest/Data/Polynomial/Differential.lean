/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TaylorChartBaseChange
import Mathlib.Tactic.NormNum

/-!
# Acceptance test for Taylor chart solution embeddings

The rational equation `Y₀ = 0` has a bounded regular solution whose chart jet satisfies the
initial equation, nonzero separant, a nonvacuous high Taylor cut, and agreement at two positions.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- The equation `Y₀ = 0` over a field. -/
private abbrev zeroOrderEquation (F : Type*) [Field F] : DifferentialPolynomial F 0 :=
  X (some 0)

/-- A concrete rational solution family satisfies all conclusions of the exponent theorem. -/
example :
    ∃ (center : ℚ) (J : Finset (Fin 1 → ℚ)), J.card = 1 ∧
      ∀ jet ∈ J,
        aeval jet (initialJetEquation center
          (MvPolynomial.map (RingHom.id ℚ) (zeroOrderEquation ℚ))) = 0 ∧
        aeval jet (initialJetSeparant center
          (MvPolynomial.map (RingHom.id ℚ) (zeroOrderEquation ℚ))) ≠ 0 ∧
        aeval jet (commonTaylorNumerator center
          (MvPolynomial.map (RingHom.id ℚ) (zeroOrderEquation ℚ)) 4 1) = 0 ∧
        2 ≤ (Finset.univ.filter (fun i : Fin 2 ↦
          aeval jet (taylorAgreementEquation center
            (MvPolynomial.map (RingHom.id ℚ) (zeroOrderEquation ℚ)) 2 4
            (RingHom.id ℚ (i.val : ℚ)) (0 : ℚ)) = 0)).card := by
  classical
  let domain : Fin 2 → ℚ := fun i ↦ (i.val : ℚ)
  let received : Fin 2 → ℚ := fun _ ↦ 0
  have hτ : TaylorExponentSufficient 0 2 4 := by
    simpa using taylorExponentSufficient_two_mul 0 2
  have hdegree : ∀ P ∈ ({0} : Finset (Polynomial ℚ)), P.degree < 1 := by
    intro P hP
    rw [Finset.mem_singleton.mp hP]
    norm_num
  have hsol : ∀ P ∈ ({0} : Finset (Polynomial ℚ)),
      differentialSpecialization (zeroOrderEquation ℚ) P = 0 := by
    intro P hP
    rw [Finset.mem_singleton.mp hP]
    simp [zeroOrderEquation]
  have hsep : ∀ P ∈ ({0} : Finset (Polynomial ℚ)),
      differentialSpecialization (separant (zeroOrderEquation ℚ) (Fin.last 0)) P ≠ 0 := by
    intro P hP
    rw [Finset.mem_singleton.mp hP]
    simp [zeroOrderEquation, separant, differentialSpecialization,
      differentialSpecializationHom]
  have hbin : ∀ i, 0 < i → i < 2 → (i.choose 0 : ℚ) ≠ 0 := by
    intro i hi hi2
    simp
  have hagree : ∀ P ∈ ({0} : Finset (Polynomial ℚ)),
      2 ≤ (Finset.univ.filter (fun i : Fin 2 ↦ P.eval (domain i) = received i)).card := by
    intro P hP
    rw [Finset.mem_singleton.mp hP]
    simp [domain, received]
  obtain ⟨center, J, hcard, hproperties⟩ :=
    exists_regular_solution_jet_family_of_exponent
      (f := RingHom.id ℚ) (Q := zeroOrderEquation ℚ) (K := 2) (k := 1) (τ := 4)
      (hτ := hτ) (hkK := by norm_num) (S := {0}) (A := 2)
      (domain := domain) (received := received) (hdegree := hdegree) (hsol := hsol)
      (hsep := hsep) (hbin := hbin) (hagree := by
        intro P hP
        simpa [domain, received] using hagree P hP)
  refine ⟨center, J, ?_, ?_⟩
  · simpa using hcard
  · intro jet hj
    rcases hproperties jet hj with ⟨hinitial, hregular, hcuts, hagree⟩
    refine ⟨hinitial, hregular, ?_, ?_⟩
    · simpa using hcuts ⟨1, by omega⟩ (by norm_num)
    · simpa [domain, received] using hagree

end

end PolynomialDifferential
