/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.JetPrefixPresentation

/-!
# Acceptance tests for presentations at the highest active jet

* In depth `2`, `Y₁ * X` has the presentation `Y₁ * X` in depth `1` at `Y₁`. It has the same total
  jet degree, degree `1` in its top variable, which is its highest active jet, and the renamed
  separant `X`. Every presentation at `Y₁` is this one.
* The forms after a coefficient map into a field follow from the unmapped statements applied to
  `JetPrefixPresentation.map`.
* `X` in depth `2` has the presentation `X` in depth `0` at `Y₀`, whose top variable is not
  active: `isHighestActiveJet_last` needs `DependsOnJet`.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- `Y₁ * X` in depth `2`. -/
private abbrev productEquation : DifferentialPolynomial ℚ 2 :=
  X (some 1) * X none

private theorem jetDegree_productEquation (j : Fin 3) :
    jetDegree productEquation j = if j = 1 then 1 else 0 := by
  classical
  rw [jetDegree, degreeOf_mul_X_of_ne _ (Option.some_ne_none j), degreeOf_X]
  simp

private theorem isHighestActiveJet_productEquation : IsHighestActiveJet productEquation 1 := by
  refine ⟨by simp [DependsOnJet, jetDegree_productEquation], fun j hj ↦ ?_⟩
  simp [DependsOnJet, jetDegree_productEquation, hj.ne']

/-- The presentation `Y₁ * X` in depth `1`. -/
private def productPresentation : JetPrefixPresentation productEquation 1 where
  equation := X (some (Fin.last 1)) * X none
  rename_equation := by simp [productEquation]

/-! ### An explicit presentation -/

example : Nonempty (JetPrefixPresentation productEquation 1) :=
  nonempty_jetPrefixPresentation _ isHighestActiveJet_productEquation

/-- Every presentation of `Y₁ * X` at `Y₁` is `Y₁ * X` in depth `1`. -/
example (A : JetPrefixPresentation productEquation 1) :
    A.equation = X (some (Fin.last 1)) * X none := by
  rw [Subsingleton.elim A productPresentation]
  rfl

example : productPresentation.equation ≠ 0 :=
  productPresentation.equation_ne_zero (by simp [productEquation])

example (u : JetVariable 1 →₀ ℕ) :
    productPresentation.equation.coeff u =
      productEquation.coeff (u.mapDomain (jetPrefixEmbedding 1)) :=
  productPresentation.coeff_equation u

example : jetTotalDegree productPresentation.equation = jetTotalDegree productEquation :=
  productPresentation.jetTotalDegree_equation

/-- The degree of the presentation in its top variable is `1`. -/
example : jetDegree productPresentation.equation (Fin.last 1) = 1 := by
  refine productPresentation.jetDegree_equation_last.trans ?_
  rw [jetDegree_productEquation]
  rfl

/-- The degree of the presentation in `Y₀` is `0`. -/
example : jetDegree productPresentation.equation 0 = 0 := by
  rw [productPresentation.jetDegree_equation, jetDegree_productEquation]
  rfl

example : IsHighestActiveJet productPresentation.equation (Fin.last 1) :=
  productPresentation.isHighestActiveJet_last isHighestActiveJet_productEquation.1

/-- The separant of the presentation in its top variable renames to the separant `X` of
`Y₁ * X` in `Y₁`. -/
example : rename (jetPrefixEmbedding (1 : Fin 3))
    (separant productPresentation.equation (Fin.last 1)) = X none := by
  refine productPresentation.rename_separant_equation.trans ?_
  simp [productEquation, separant, pderiv_X]

example (P : Polynomial ℚ) :
    differentialSpecialization productPresentation.equation P =
      differentialSpecialization productEquation P :=
  productPresentation.differentialSpecialization_equation P

example (c : ℚ) (jet : Fin 3 → ℚ) :
    jetEvaluation productPresentation.equation c (restrictJet 1 jet) =
      jetEvaluation productEquation c jet :=
  productPresentation.jetEvaluation_equation c jet

example (c : ℚ) (P : Polynomial ℚ) :
    IsRegularJet productPresentation.equation (Fin.last 1) c (polynomialJet c P) ↔
      IsRegularJet productEquation 1 c (polynomialJet c P) :=
  productPresentation.isRegularJet_equation_iff c P

/-! ### Forms after a coefficient map -/

section Mapped

variable {R E : Type*} [CommSemiring R] [Field E] {d : ℕ} (φ : R →+* E)
  {Q : DifferentialPolynomial R d} {s : Fin (d + 1)} (A : JetPrefixPresentation Q s)

example (P : Polynomial E) :
    differentialSpecialization (MvPolynomial.map φ A.equation) P =
      differentialSpecialization (MvPolynomial.map φ Q) P :=
  (A.map φ).differentialSpecialization_equation P

example (center : E) (jet : Fin (d + 1) → E) :
    jetEvaluation (MvPolynomial.map φ A.equation) center (restrictJet s jet) =
      jetEvaluation (MvPolynomial.map φ Q) center jet :=
  (A.map φ).jetEvaluation_equation center jet

example (P : Polynomial E) :
    differentialSpecialization (separant (MvPolynomial.map φ A.equation) (Fin.last s.val)) P =
      differentialSpecialization (separant (MvPolynomial.map φ Q) s) P :=
  (A.map φ).differentialSpecialization_separant_equation P

example (center : E) (P : Polynomial E) :
    IsRegularJet (MvPolynomial.map φ A.equation) (Fin.last s.val) center
        (polynomialJet center P) ↔
      IsRegularJet (MvPolynomial.map φ Q) s center (polynomialJet center P) :=
  (A.map φ).isRegularJet_equation_iff center P

/-- The top variable is the highest active jet when `Y_s` is the computed highest active jet. -/
example (hs : highestActiveJet Q = some s) : IsHighestActiveJet A.equation (Fin.last s.val) :=
  A.isHighestActiveJet_last (isHighestActiveJet_of_highestActiveJet_eq_some hs).1

end Mapped

/-- Over `F[X]`, a coefficient height bound passes to the presentation. -/
example {F : Type*} [Field F] {d : ℕ} {Q : DifferentialPolynomial (Polynomial F) d}
    {s : Fin (d + 1)} (A : JetPrefixPresentation Q s) {h : ℕ}
    (hQ : ∀ u, (Q.coeff u).natDegree ≤ h) : ∀ u, (A.equation.coeff u).natDegree ≤ h :=
  A.natDegree_coeff_equation_le hQ

/-! ### `DependsOnJet` is needed -/

/-- `X` in depth `2` presented at `Y₀` by `X` in depth `0`. -/
private def constantPresentation :
    JetPrefixPresentation (X none : DifferentialPolynomial ℚ 2) 0 where
  equation := X none
  rename_equation := by simp

/-- The top variable of the presentation of `X` at `Y₀` is not active. -/
example : ¬ IsHighestActiveJet constantPresentation.equation (Fin.last 0) := fun h ↦ by
  have h' := h.1
  simp [constantPresentation, DependsOnJet, jetDegree, degreeOf_X] at h'

end

end PolynomialDifferential
