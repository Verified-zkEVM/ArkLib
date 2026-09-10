/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorWitnessEmbedding
public import ArkLib.ToMathlib.Polynomial.SeparableResultant
public import Mathlib.Algebra.Polynomial.Bivariate
public import ArkLib.ToMathlib.MvPolynomial.RootContraction
/-!
# Presenting an ordinary symbolic equation as a polynomial in its root

The coefficient variables are ordered as the independent coordinate, then challenge.
The outer variable is the root, so the resultant is a polynomial in the challenge with
polynomial coefficients in the independent coordinate.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open Polynomial MvPolynomial PolynomialDifferential

variable {F : Type*} [Field F]

/-- The root polynomial has coefficient order `F[T][W]`, with root variable outermost. -/
def ordinaryRootPresentation (Q : DifferentialPolynomial F[X] 0) : F[X][X][X] :=
  Polynomial.map (Polynomial.Bivariate.swap (R := F)).toRingHom
    (Polynomial.map (uniqueAlgEquiv F[X] (Fin 1)).toRingHom
      (optionEquivLeft F[X] (Fin 1)
        (renameEquiv F[X] (Equiv.swap none (some 0)) Q)))

/-- The outer degree is exactly the original ordinary jet degree. -/
theorem natDegree_ordinaryRootPresentation (Q : DifferentialPolynomial F[X] 0) :
    (ordinaryRootPresentation Q).natDegree = Q.degreeOf (some 0) := by
  rw [ordinaryRootPresentation,
    Polynomial.natDegree_map_eq_of_injective
      (f := (Polynomial.Bivariate.swap (R := F)).toRingHom)
      (Polynomial.Bivariate.swap (R := F)).injective,
    Polynomial.natDegree_map_eq_of_injective
      (f := (uniqueAlgEquiv F[X] (Fin 1)).toRingHom)
      (uniqueAlgEquiv F[X] (Fin 1)).injective,
    natDegree_optionEquivLeft]
  simpa only [renameEquiv_apply, Equiv.swap_apply_right] using
    degreeOf_rename_of_injective (p := Q)
      (Equiv.swap none (some (0 : Fin 1))).injective (some 0)

/-- The root presentation preserves nonzero equations. -/
theorem ordinaryRootPresentation_ne_zero {Q : DifferentialPolynomial F[X] 0} (hQ : Q ≠ 0) :
    ordinaryRootPresentation Q ≠ 0 := by
  intro hz
  apply hQ
  apply (renameEquiv F[X] (Equiv.swap none (some (0 : Fin 1)))).injective
  apply (optionEquivLeft F[X] (Fin 1)).injective
  apply Polynomial.map_injective (uniqueAlgEquiv F[X] (Fin 1)).toRingHom
    (uniqueAlgEquiv F[X] (Fin 1)).injective
  apply Polynomial.map_injective (Polynomial.Bivariate.swap (R := F)).toRingHom
    (Polynomial.Bivariate.swap (R := F)).injective
  simpa only [ordinaryRootPresentation, map_zero, Polynomial.map_zero] using hz

/-- Reordering polynomial coordinates preserves irreducibility. -/
theorem irreducible_ordinaryRootPresentation {Q : DifferentialPolynomial F[X] 0}
    (hQ : Irreducible Q) : Irreducible (ordinaryRootPresentation Q) := by
  have h₁ := hQ.map (renameEquiv F[X] (Equiv.swap none (some (0 : Fin 1))))
  have h₂ := h₁.map (optionEquivLeft F[X] (Fin 1))
  have h₃ := h₂.map (Polynomial.mapEquiv (uniqueAlgEquiv F[X] (Fin 1)).toRingEquiv)
  exact h₃.map (Polynomial.mapEquiv (Polynomial.Bivariate.swap (R := F)).toRingEquiv)

/-- Ordinary jet differentiation becomes outer polynomial differentiation. -/
theorem derivative_ordinaryRootPresentation (Q : DifferentialPolynomial F[X] 0) :
    (ordinaryRootPresentation Q).derivative =
      ordinaryRootPresentation (pderiv (some 0) Q) := by
  unfold ordinaryRootPresentation
  rw [Polynomial.derivative_map, Polynomial.derivative_map,
    ← optionEquivLeft_pderiv_none]
  congr 3
  simpa only [renameEquiv_apply, Equiv.swap_apply_right] using
    pderiv_rename (Equiv.swap none (some (0 : Fin 1))).injective (some 0) Q

/-- An irreducible ordinary equation with nonzero root derivative has a nonzero
challenge resultant before choosing a Taylor center. -/
theorem separableResultant_ordinaryRootPresentation_ne_zero
    {Q : DifferentialPolynomial F[X] 0} (hQ : Irreducible Q)
    (hpos : 0 < Q.degreeOf (some 0)) (hder : pderiv (some 0) Q ≠ 0) :
    Polynomial.separableResultant (ordinaryRootPresentation Q) (Q.degreeOf (some 0)) ≠ 0 := by
  let A := ordinaryRootPresentation Q
  let L := FractionRing F[X][X]
  have hirr : Irreducible A := irreducible_ordinaryRootPresentation hQ
  have hdegree : A.natDegree = Q.degreeOf (some 0) := natDegree_ordinaryRootPresentation Q
  have hprimitive : A.IsPrimitive := hirr.isPrimitive (by omega)
  have hmapIrreducible : Irreducible (A.map (algebraMap F[X][X] L)) :=
    (hprimitive.irreducible_iff_irreducible_map_fraction_map (K := L)).mp hirr
  have hderA : A.derivative ≠ 0 := by
    rw [show A = ordinaryRootPresentation Q from rfl, derivative_ordinaryRootPresentation]
    exact ordinaryRootPresentation_ne_zero hder
  have hmapDerivative : derivative (A.map (algebraMap F[X][X] L)) ≠ 0 := by
    rw [Polynomial.derivative_map]
    exact (Polynomial.map_ne_zero_iff (p := A.derivative)
      (IsFractionRing.injective F[X][X] L)).mpr hderA
  exact Polynomial.separableResultant_ne_zero_of_map_separable A hdegree
    ((Polynomial.separable_iff_derivative_ne_zero hmapIrreducible).mpr hmapDerivative)

/-- Explicit monomial coordinates of the root presentation. -/
theorem ordinaryRootPresentation_monomial (m : Option (Fin 1) →₀ ℕ) (c : F[X]) :
    ordinaryRootPresentation (monomial m c) =
      Polynomial.C (c.map Polynomial.C * Polynomial.C (Polynomial.X ^ m none)) *
        Polynomial.X ^ m (some 0) := by
  classical
  simp [ordinaryRootPresentation, MvPolynomial.monomial_eq, Finsupp.prod_fintype,
    Polynomial.Bivariate.swap_C, Polynomial.Bivariate.swap_Y,
    Polynomial.C_mul, mul_assoc]

/-- Coefficient reordering preserves the advertised challenge height. -/
theorem degreeX_ordinaryRootPresentation_le (Q : DifferentialPolynomial F[X] 0)
    {h : ℕ} (hQ : ChallengeHeightLE Q h) :
    Polynomial.Bivariate.degreeX (ordinaryRootPresentation Q) ≤ h := by
  classical
  have hsum : ordinaryRootPresentation Q =
      ∑ m ∈ Q.support, ordinaryRootPresentation (monomial m (MvPolynomial.coeff m Q)) := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    simp only [ordinaryRootPresentation, map_sum, Polynomial.map_sum]
  rw [hsum]
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i _
  rw [Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  rw [ordinaryRootPresentation_monomial, Polynomial.coeff_C_mul_X_pow]
  split_ifs
  · exact (Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C, Nat.add_zero] using
        (Polynomial.natDegree_map_le (p := MvPolynomial.coeff m Q)
          (f := Polynomial.C)).trans (hQ m)))
  · simp

/-- Evaluation of the root presentation agrees with actual ordinary specialization. -/
theorem eval_ordinaryRootPresentation (Q : DifferentialPolynomial F[X] 0)
    (w : F) (P : F[X]) :
    ((ordinaryRootPresentation Q).map (Polynomial.evalRingHom (Polynomial.C w))).eval P =
      differentialSpecialization (challengeSpecialization Q w) P := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    simp [ordinaryRootPresentation, challengeSpecialization, differentialSpecialization,
      Polynomial.Bivariate.swap_C, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  | add Q R hQ hR =>
    simpa [ordinaryRootPresentation, challengeSpecialization, differentialSpecialization]
      using congrArg₂ (· + ·) hQ hR
  | mul_X Q i hQ =>
    cases i with
    | none =>
      simpa [ordinaryRootPresentation, challengeSpecialization, differentialSpecialization,
        Polynomial.Bivariate.swap_Y] using congrArg (· * Polynomial.X) hQ
    | some i =>
      have hi : i = 0 := by omega
      subst i
      simpa [ordinaryRootPresentation, challengeSpecialization, differentialSpecialization]
        using congrArg (· * P) hQ

/-- Away from the resultant, every actual ordinary polynomial solution has nonzero separant. -/
theorem ordinary_separant_ne_zero_of_resultant_eval_ne_zero
    (Q : DifferentialPolynomial F[X] 0) (hpos : 0 < Q.degreeOf (some 0))
    (w : F) (P : F[X])
    (hresultant : (Polynomial.separableResultant (ordinaryRootPresentation Q)
      (Q.degreeOf (some 0))).eval (Polynomial.C w) ≠ 0)
    (hroot : differentialSpecialization (challengeSpecialization Q w) P = 0) :
    differentialSpecialization (separant (challengeSpecialization Q w) (Fin.last 0)) P ≠ 0 := by
  have hroot' : ((ordinaryRootPresentation Q).map
      (Polynomial.evalRingHom (Polynomial.C w))).eval P = 0 := by
    rw [eval_ordinaryRootPresentation]
    exact hroot
  have h := Polynomial.eval_derivative_ne_zero_of_separableResultant_map_ne_zero
    (ordinaryRootPresentation Q) hpos (natDegree_ordinaryRootPresentation Q).le
    (Polynomial.evalRingHom (Polynomial.C w)) P hresultant hroot'
  rw [Polynomial.derivative_map, derivative_ordinaryRootPresentation,
    eval_ordinaryRootPresentation] at h
  simpa only [challengeSpecialization, separant, MvPolynomial.pderiv_map,
    show Fin.last 0 = (0 : Fin 1) from rfl] using h

open Classical in
/-- The actual resultant supplies one exceptional challenge set for all ordinary roots. -/
theorem exists_exceptional_ordinary_separant
    {Q : DifferentialPolynomial F[X] 0} (hQ : Irreducible Q)
    (hpos : 0 < Q.degreeOf (some 0)) (hder : pderiv (some 0) Q ≠ 0)
    {h : ℕ} (hheight : ChallengeHeightLE Q h) :
    ∃ exceptional : Finset F,
      exceptional.card ≤ (2 * Q.degreeOf (some 0) - 1) * h ∧
      ∀ w ∉ exceptional, ∀ P : F[X],
        differentialSpecialization (challengeSpecialization Q w) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q w) (Fin.last 0)) P ≠ 0 := by
  classical
  let B := Polynomial.separableResultant (ordinaryRootPresentation Q) (Q.degreeOf (some 0))
  have hB : B ≠ 0 := separableResultant_ordinaryRootPresentation_ne_zero hQ hpos hder
  have hfinite : {w : F | B.eval (Polynomial.C w) = 0}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hB).preimage Polynomial.C_injective.injOn
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply le_trans (Polynomial.finite_polynomial_specializations_eq_zero_card_le B hB
      hfinite.toFinset (fun w hw ↦ hfinite.mem_toFinset.mp hw))
    exact Polynomial.natDegree_separableResultant_le_of_height (ordinaryRootPresentation Q)
      (natDegree_ordinaryRootPresentation Q) hpos (degreeX_ordinaryRootPresentation_le Q hheight)
  · intro w hw P hroot
    apply ordinary_separant_ne_zero_of_resultant_eval_ne_zero Q hpos w P _ hroot
    intro hzero
    exact hw (hfinite.mem_toFinset.mpr hzero)

end ReedSolomon.HiddenDerivative
