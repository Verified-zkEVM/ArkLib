import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra

open MvPolynomial PolynomialDifferential

noncomputable section

private def coordinateEquation : DifferentialPolynomial (Polynomial ℚ) 0 :=
  MvPolynomial.X (some 0)

example : jointTotalDegree (initialJetEquation (Polynomial.C 0) coordinateEquation) ≤ 1 := by
  apply jointTotalDegree_initialJetEquation_le_of_coeffNatDegreeLE 0 coordinateEquation 1 0
  · rw [jetTotalDegree_le_iff]
    intro u hu
    simp only [coordinateEquation, MvPolynomial.support_X, Finset.mem_singleton] at hu
    subst u
    simp [totalJetDegree, Finsupp.weight_single]
  · exact coeffNatDegreeLE_X (some 0)

example :
    jointTotalDegree (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0)
      coordinateEquation 0 0 (Polynomial.C 0) (Polynomial.C 0 + Polynomial.X)) = 1 := by
  simp [taylorAgreementEquationOver, initialJetSeparant, coordinateEquation,
    jointTotalDegree]

private def singularEquation : DifferentialPolynomial ℚ 0 :=
  MvPolynomial.X (none : Option (Fin 1))

/-- At a singular jet, a common numerator can be nonzero while the divided coefficient is zero.
-/
example :
    rationalTaylorCoefficient (0 : ℚ) singularEquation
      (fun _ ↦ (0 : ℚ)) 1 = 0 ∧
    MvPolynomial.aeval (fun _ : Fin 1 ↦ (0 : ℚ))
      (commonTaylorNumerator (0 : ℚ) singularEquation 1 1) = (-1 : ℚ) := by
  constructor <;>
    simp [rationalTaylorCoefficient, commonTaylorNumerator, rationalTaylorNumerator,
      clearedSubstitution, universalTaylorResidual, universalTaylorJet,
      initialJetSeparant, separant, singularEquation]

private def firstDerivativeEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  MvPolynomial.X (some (1 : Fin 2))

example (i : ℕ) (hi : ¬2 ∣ i) :
    (Polynomial.taylor (0 : ℚ)
      (rationalTaylorPolynomial (0 : ℚ)
        (MvPolynomial.map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
          firstDerivativeEquation) 2 (fun _ ↦ 0))).coeff i =
      0 := by
  have hS : MvPolynomial.aeval (fun _ : Fin 2 ↦ (0 : ℚ))
      (MvPolynomial.map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
        (initialJetSeparant (Polynomial.C (0 : ℚ)) firstDerivativeEquation)) ≠ 0 := by
    rw [map_initialJetSeparant]
    simp [firstDerivativeEquation, initialJetSeparant, separant]
  have hcuts : ∀ l : Fin 2, ¬2 ∣ l.val →
      MvPolynomial.aeval (fun _ : Fin 2 ↦ (0 : ℚ))
        (MvPolynomial.map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
          (commonTaylorNumeratorOver ℚ (Polynomial.C (0 : ℚ)) firstDerivativeEquation 4
            l.val)) = 0 := by
    intro l hl
    fin_cases l
    · exact (hl (by decide)).elim
    · rw [map_commonTaylorNumeratorOver, commonTaylorNumeratorOver,
        rationalTaylorNumeratorOver_eq]
      simp [rationalTaylorNumerator, firstDerivativeEquation, initialJetSeparant, separant]
  simpa using sparse_rationalTaylorPolynomial_of_symbolic_cuts
    (φ := Polynomial.aeval (R := ℚ) (0 : ℚ)) (center := Polynomial.C (0 : ℚ))
    (Q := firstDerivativeEquation)
    (K := 2) (s := 2) (τ := 4) (hτ := taylorExponentSufficient_two_mul 1 2)
    (jet := fun _ ↦ (0 : ℚ)) hS hcuts i hi

end
