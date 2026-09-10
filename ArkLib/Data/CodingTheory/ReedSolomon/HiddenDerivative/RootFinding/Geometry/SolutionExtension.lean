/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.SolutionGeometry
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.Extension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure


/-! # Faithful extension transport for regular solution geometry -/

@[expose] public section

open PolynomialDifferential


noncomputable section
namespace ReedSolomon.HiddenDerivative
variable {F E : Type*} [Field F] [Field E] {r : ℕ}

/-- The separant commutes with every coefficient-field embedding. -/
theorem map_separant (f : F →+* E) (Q : DifferentialPolynomial F r) (j : Fin (r + 1)) :
    MvPolynomial.map f (separant Q j) = separant (MvPolynomial.map f Q) j := by
  exact MvPolynomial.pderiv_map.symm

open Classical in
/-- Mapping a finite family into an extension preserves its exact cardinality. -/
theorem card_image_polynomial_map (f : F →+* E) (S : Finset (Polynomial F)) :
    (S.image (Polynomial.map f)).card = S.card := by
  exact Finset.card_image_of_injective _ (Polynomial.map_injective f f.injective)

open Classical in
/-- All bounded regular differential-solution hypotheses survive coefficient extension. -/
theorem mapped_regular_solution_family
    (f : F →+* E) (Q : DifferentialPolynomial F r) (S : Finset (Polynomial F)) (k : ℕ)
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0) :
    ∀ P ∈ S.image (Polynomial.map f),
      P.degree < k ∧ differentialSpecialization (MvPolynomial.map f Q) P = 0 ∧
      differentialSpecialization (separant (MvPolynomial.map f Q) (Fin.last r)) P ≠ 0 := by
  intro P hP
  obtain ⟨P, hPS, rfl⟩ := Finset.mem_image.mp hP
  refine ⟨Polynomial.degree_map_le.trans_lt (hdegree P hPS), ?_, ?_⟩
  · rw [← map_differentialSpecialization, hsol P hPS, Polynomial.map_zero]
  · rw [← map_separant, ← map_differentialSpecialization]
    exact fun h ↦ hsep P hPS ((Polynomial.map_injective f f.injective)
      (by simpa using h))

/-- Every finite regular family over an arbitrary field has a common regular
center after the explicit coefficient embedding into any infinite extension. -/
theorem exists_common_regular_center_extension [Infinite E]
    (f : F →+* E) (Q : DifferentialPolynomial F r) (S : Finset (Polynomial F))
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0) :
    ∃ center : E, ∀ P ∈ S,
      jetEvaluation (separant (MvPolynomial.map f Q) (Fin.last r)) center
        (polynomialJet center (P.map f)) ≠ 0 := by
  classical
  obtain ⟨center, hc⟩ := exists_common_regular_center (MvPolynomial.map f Q)
    (S.image (Polynomial.map f)) (by
      intro P hP
      obtain ⟨P, hPS, rfl⟩ := Finset.mem_image.mp hP
      rw [← map_separant, ← map_differentialSpecialization]
      exact fun h ↦ hsep P hPS ((Polynomial.map_injective f f.injective)
        (by simpa using h)))
  exact ⟨center, fun P hP ↦ hc _ (Finset.mem_image.mpr ⟨P, hP, rfl⟩)⟩

open Classical in
/-- Agreement predicates, hence their exact finite counts, are preserved by field extension. -/
theorem mapped_agreement_count (f : F →+* E) {n : ℕ}
    (domain received : Fin n → F) (P : Polynomial F) :
    (Finset.univ.filter fun i ↦ (P.map f).eval (f (domain i)) = f (received i)).card =
      (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card := by
  simp only [Polynomial.eval_map_apply, f.injective.eq_iff]

/-- The binomial pivot contract transports without strengthening the characteristic. -/
theorem map_binomial_pivots (f : F →+* E) (K : ℕ)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    ∀ i, r < i → i < K → (i.choose r : E) ≠ 0 := by
  intro i hi hK hzero
  apply hbin i hi hK
  apply f.injective
  simpa using hzero

/-- In particular the common center exists in the actual algebraic closure of the base field. -/
theorem exists_common_regular_center_algebraicClosure
    (Q : DifferentialPolynomial F r) (S : Finset (Polynomial F))
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0) :
    ∃ center : AlgebraicClosure F, ∀ P ∈ S,
      jetEvaluation
        (separant (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) Q) (Fin.last r))
        center (polynomialJet center (P.map (algebraMap F (AlgebraicClosure F)))) ≠ 0 := by
  exact exists_common_regular_center_extension _ Q S hsep

end ReedSolomon.HiddenDerivative
