import ArkLib.Data.Polynomial.Differential.ContentExceptions
import Mathlib.Data.Rat.Defs

open PolynomialDifferential

example :
    ∃ exceptional : Finset ℚ, exceptional.card ≤ 0 ∧
      ∀ w ∉ exceptional, ∀ P : Polynomial ℚ,
        differentialSpecialization
          (challengeSpecialization (1 : DifferentialPolynomial (Polynomial ℚ) 0) w) P ≠ 0 := by
  have hheight :
      MvPolynomial.CoeffNatDegreeLE (1 : DifferentialPolynomial (Polynomial ℚ) 0) 0 := by
    change MvPolynomial.CoeffNatDegreeLE
      (MvPolynomial.C (Polynomial.C (1 : ℚ)) : DifferentialPolynomial (Polynomial ℚ) 0) 0
    exact MvPolynomial.coeffNatDegreeLE_C (σ := JetVariable 0) (R := ℚ)
      (p := Polynomial.C (1 : ℚ)) (h := 0) (by simp)
  exact exists_exceptional_jet_independent_content
    (Q := (1 : DifferentialPolynomial (Polynomial ℚ) 0)) (h := 0)
    (hQ := one_ne_zero) (hdegree := by simp) hheight
