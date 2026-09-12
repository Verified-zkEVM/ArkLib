/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.Euclidean
public import ArkLib.Data.Polynomial.ModularInverse
public import ArkLib.Data.Polynomial.ResultantDegree
public import ArkLib.ToMathlib.Polynomial.SeparableResultant
public import CompPoly.Bivariate.Deriv
public import CompPoly.Bivariate.ToPoly
public import Mathlib.Algebra.Polynomial.Degree.Domain

/-!
# Executable regular-center obstructions

For a nested stored polynomial `T : F[X][Y]`, this file computes

`lcY(T) * ResY(partialY T, T)`

using the determinant of the fixed-size Sylvester matrix.  The fixed sizes are the original
`Y`-degrees, so specialization cannot hide a degree drop by shrinking the matrix.

The input contract records primitivity and coprimality with the `Y`-derivative after passage to
`F(X)[Y]`.  The latter hypothesis is essential in positive characteristic: primitivity alone does
not exclude `Y`-inseparable inputs such as `Y^p - X`.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.RegularCenterObstruction

open CompPoly CPolynomial Polynomial.Bivariate

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The proof-facing image of a stored nested polynomial in `F(X)[Y]`. -/
noncomputable def functionFieldPolynomial (T : CBivariate F) : Polynomial (RatFunc F) :=
  (CBivariate.toPoly T).map (algebraMap F[X] (RatFunc F))

/-- Certified input supplied by ordinary normalization.  The obstruction itself remains a pure
computation on `polynomial`; these fields justify its mathematical contracts. -/
structure Input (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  /-- Primitive nested polynomial in `F[X][Y]`. -/
  polynomial : CBivariate F
  /-- No nonconstant polynomial in `F[X]` divides every `Y`-coefficient. -/
  primitive : (CBivariate.toPoly polynomial).IsPrimitive
  /-- The polynomial genuinely depends on `Y`. -/
  positiveDegree : 0 < polynomial.natDegree
  /-- The normalized polynomial is regular over the function field. -/
  coprimeDerivative : IsCoprime (functionFieldPolynomial polynomial)
    (functionFieldPolynomial polynomial).derivative

/-- The fixed-size Sylvester matrix read directly from stored coefficient arrays. -/
def storedSylvester {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (m n : ℕ) : Matrix (Fin (m + n)) (Fin (m + n)) R :=
  Matrix.of fun i j ↦ j.addCases
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + n) then
      q.coeff ((i : ℕ) - j₁) else 0)
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + m) then
      p.coeff ((i : ℕ) - j₁) else 0)

/-- The actual fixed-size Sylvester determinant over stored coefficients.  In the obstruction
application `R = CPolynomial F`, so the result is again a stored polynomial in `X`. -/
def sylvesterResultant {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (m n : ℕ) : R :=
  (storedSylvester p q m n).det

/-- The stored computation is definitionally Mathlib's Sylvester resultant of the represented
polynomials. -/
theorem sylvesterResultant_eq {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (m n : ℕ) :
    sylvesterResultant p q m n = Polynomial.resultant p.toPoly q.toPoly m n := by
  rw [sylvesterResultant, Polynomial.resultant]
  apply congrArg Matrix.det
  ext i j
  induction j using Fin.addCases <;>
    simp only [storedSylvester, Polynomial.sylvester, Matrix.of_apply,
      Fin.addCases_left, Fin.addCases_right]
  all_goals split_ifs <;> simp [CPolynomial.coeff_toPoly]

/-- The derivative resultant, padded with the original outer degree. -/
def derivativeResultant (T : CBivariate F) : CPolynomial F :=
  sylvesterResultant T.derivative T (T.natDegree - 1) T.natDegree

/-- The regular-center obstruction `lcY(T) * ResY(partialY T, T)`. -/
def obstruction (T : CBivariate F) : CPolynomial F :=
  T.leadingCoeff * derivativeResultant T

/-- Run the obstruction producer on a certified input. -/
def Input.produce (input : Input F) : CPolynomial F :=
  RegularCenterObstruction.obstruction input.polynomial

/-- Specialize the coefficient variable, retaining a stored polynomial in `Y`. -/
def fiber (T : CBivariate F) (center : F) : CPolynomial F :=
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  CBivariate.evalX center T

noncomputable section

/-- The stored resultant represents the mathematical fixed-size resultant. -/
theorem derivativeResultant_toPoly (T : CBivariate F) :
    (derivativeResultant T).toPoly =
      Polynomial.separableResultant (CBivariate.toPoly T) T.natDegree := by
  let _ : DecidableEq F := instDecidableEqOfLawfulBEq
  rw [derivativeResultant, sylvesterResultant_eq, Polynomial.separableResultant]
  conv_lhs => rw [← CPolynomial.toPolyRingHom_apply]
  rw [← Polynomial.resultant_map_map]
  congr 2
  · rw [← CBivariate.partialDerivY_toPoly T]
    simpa [CBivariate.partialDerivY, CPolynomial.toPolyRingHom] using
      (CBivariate.toPoly_eq_map (CBivariate.partialDerivY T)).symm
  · simpa [CPolynomial.toPolyRingHom] using (CBivariate.toPoly_eq_map T).symm

/-- The implementation's `Res(partialY T, T)` order equals the assignment's
`Res(T, partialY T)` order: the sign exponent `b * (b - 1)` is always even. -/
theorem derivativeResultant_toPoly_assignment_order (T : CBivariate F) :
    (derivativeResultant T).toPoly =
      Polynomial.resultant (CBivariate.toPoly T) (CBivariate.toPoly T).derivative
        T.natDegree (T.natDegree - 1) := by
  rw [derivativeResultant_toPoly, Polynomial.separableResultant,
    Polynomial.resultant_comm]
  have heven : Even ((T.natDegree - 1) * T.natDegree) := by
    simpa [Nat.mul_comm] using Nat.even_mul_pred_self T.natDegree
  rw [Even.neg_one_pow heven, one_mul]

/-- Semantic form of the stored obstruction. -/
theorem obstruction_toPoly (T : CBivariate F) :
    (obstruction T).toPoly =
      (CBivariate.toPoly T).leadingCoeff *
        Polynomial.separableResultant (CBivariate.toPoly T) T.natDegree := by
  rw [obstruction, CPolynomial.toPoly_mul, derivativeResultant_toPoly,
    show T.leadingCoeff.toPoly = (CBivariate.toPoly T).leadingCoeff by
      simpa [CBivariate.leadingCoeffY] using CBivariate.leadingCoeffY_toPoly T]

/-- The certified function-field condition is exactly separability. -/
theorem Input.functionField_separable (input : Input F) :
    (functionFieldPolynomial input.polynomial).Separable :=
  input.coprimeDerivative

/-- Function-field regularity makes the stored derivative resultant nonzero. -/
theorem derivativeResultant_ne_zero (input : Input F) :
    derivativeResultant input.polynomial ≠ 0 := by
  apply (CPolynomial.toPoly_eq_zero_iff _).not.mp
  rw [derivativeResultant_toPoly]
  apply Polynomial.separableResultant_ne_zero_of_map_separable
    (L := RatFunc F)
    (CBivariate.toPoly input.polynomial)
      (by simpa [CBivariate.natDegreeY] using
        CBivariate.natDegreeY_toPoly input.polynomial)
  exact input.functionField_separable

/-- A certified positive-degree regular input has a nonzero executable obstruction. -/
theorem obstruction_ne_zero (input : Input F) : input.produce ≠ 0 := by
  rw [Input.produce, obstruction]
  intro hzero
  have hzeroPoly := congrArg CPolynomial.toPoly hzero
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_zero] at hzeroPoly
  have hlc : input.polynomial.leadingCoeff.toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff _).not.mpr
      (CPolynomial.leadingCoeff_ne_zero (fun hT => by
        have hp := input.positiveDegree
        rw [hT] at hp
        rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero,
          Polynomial.natDegree_zero] at hp
        omega))
  have hres : (derivativeResultant input.polynomial).toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff _).not.mpr (derivativeResultant_ne_zero input)
  exact (_root_.mul_ne_zero hlc hres) hzeroPoly

/-- The obstruction has the concrete `2 * degreeY * degreeX` bound used by center search. -/
theorem obstruction_natDegree_le (T : CBivariate F) (hpositive : 0 < T.natDegree) :
    (obstruction T).natDegree ≤
      2 * T.natDegree * Polynomial.Bivariate.degreeX (CBivariate.toPoly T) := by
  rw [CPolynomial.natDegree_toPoly, obstruction_toPoly]
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hlc : (CBivariate.toPoly T).leadingCoeff.natDegree ≤
      Polynomial.Bivariate.degreeX (CBivariate.toPoly T) := by
    rw [Polynomial.leadingCoeff]
    exact Polynomial.Bivariate.coeff_natDegree_le_degreeX _ _
  have hres := Polynomial.natDegree_separableResultant_le_of_height
    (CBivariate.toPoly T)
      (by simpa [CBivariate.natDegreeY] using CBivariate.natDegreeY_toPoly T)
      hpositive le_rfl
  calc
    _ ≤ Polynomial.Bivariate.degreeX (CBivariate.toPoly T) +
        (2 * T.natDegree - 1) * Polynomial.Bivariate.degreeX (CBivariate.toPoly T) :=
      Nat.add_le_add hlc hres
    _ = 2 * T.natDegree * Polynomial.Bivariate.degreeX (CBivariate.toPoly T) := by
      calc
        _ = 1 * Polynomial.Bivariate.degreeX (CBivariate.toPoly T) +
            (2 * T.natDegree - 1) * Polynomial.Bivariate.degreeX
              (CBivariate.toPoly T) := by rw [one_mul]
        _ = (1 + (2 * T.natDegree - 1)) *
            Polynomial.Bivariate.degreeX (CBivariate.toPoly T) :=
          (Nat.add_mul _ _ _).symm
        _ = _ := by congr 1; omega

/-- Stored specialization agrees with coefficient evaluation of the mathematical bivariate. -/
theorem fiber_toPoly (T : CBivariate F) (center : F) :
    (fiber T center).toPoly =
      (CBivariate.toPoly T).map (Polynomial.evalRingHom center) := by
  let _ : DecidableEq F := instDecidableEqOfLawfulBEq
  ext j
  rw [fiber, CBivariate.evalX_toPoly_coeff]
  simp

/-- Exact facts consumed by the regular-center application adapter. -/
structure FiberFacts (T : CBivariate F) (center : F) : Prop where
  /-- The outer leading coefficient survives specialization. -/
  leadingCoeff_ne_zero : CPolynomial.eval center T.leadingCoeff ≠ 0
  /-- Hence the stored fiber is nonzero. -/
  fiber_ne_zero : fiber T center ≠ 0
  /-- The original `Y`-degree is preserved. -/
  degree_eq : (fiber T center).natDegree = T.natDegree
  /-- The specialized polynomial has no repeated irreducible factor. -/
  squarefree : Squarefree (fiber T center).toPoly
  /-- Euclid actually returns an inverse of the specialized `Y`-derivative modulo the fiber. -/
  inverse : ∃ inverse, CPolynomial.inverseMod? (fiber T center).derivative
    (fiber T center) = some inverse
  /-- The same specialized derivative has an executed inverse modulo the monic fiber. -/
  monicInverse : ∃ inverse, CPolynomial.inverseMod? (fiber T center).derivative
    (CPolynomial.monicNormalize (fiber T center)) = some inverse

/-- A nonzero obstruction value gives all regular-fiber facts, including the executed modular
inverse needed by Personal 4's `goodCenter`. -/
theorem fiberFacts_of_eval_obstruction_ne_zero (T : CBivariate F) (center : F)
    (hpositive : 0 < T.natDegree)
    (h : CPolynomial.eval center (obstruction T) ≠ 0) : FiberFacts T center := by
  let _ : DecidableEq F := instDecidableEqOfLawfulBEq
  have hproduct :
      (CBivariate.toPoly T).leadingCoeff.eval center *
        (Polynomial.separableResultant (CBivariate.toPoly T) T.natDegree).eval center ≠ 0 := by
    have heval := congrArg (Polynomial.eval center) (obstruction_toPoly T)
    rw [Polynomial.eval_mul, ← CPolynomial.eval_toPoly] at heval
    rwa [heval] at h
  have hlcPoly : (CBivariate.toPoly T).leadingCoeff.eval center ≠ 0 :=
    left_ne_zero_of_mul hproduct
  have hresultant :
      (Polynomial.separableResultant (CBivariate.toPoly T) T.natDegree).eval center ≠ 0 :=
    right_ne_zero_of_mul hproduct
  have hseparable :
      ((CBivariate.toPoly T).map (Polynomial.evalRingHom center)).Separable :=
    Polynomial.specialization_separable_of_separableResultant_eval_ne_zero
      (CBivariate.toPoly T) hpositive
        (by simpa [CBivariate.natDegreeY] using (CBivariate.natDegreeY_toPoly T).le)
        center hresultant
  have hfiberSeparable : (fiber T center).toPoly.Separable := by
    rw [fiber_toPoly]
    exact hseparable
  have hfiberDegree : (fiber T center).natDegree = T.natDegree := by
    rw [CPolynomial.natDegree_toPoly, fiber_toPoly]
    calc
      ((CBivariate.toPoly T).map (Polynomial.evalRingHom center)).natDegree =
          (CBivariate.toPoly T).natDegree :=
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (by simpa using hlcPoly)
      _ = T.natDegree := by
        simpa [CBivariate.natDegreeY] using CBivariate.natDegreeY_toPoly T
  have hfiberNe : fiber T center ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff _).not.mp hfiberSeparable.ne_zero
  refine ⟨?_, hfiberNe, hfiberDegree, hfiberSeparable.squarefree, ?_, ?_⟩
  · change CPolynomial.eval center (CBivariate.leadingCoeffY T) ≠ 0
    rw [CPolynomial.eval_toPoly, CBivariate.leadingCoeffY_toPoly]
    exact hlcPoly
  · rw [CPolynomial.inverseMod_exists_iff_coprime]
    rw [CPolynomial.derivative_toPoly]
    exact hfiberSeparable.symm
  · rw [CPolynomial.inverseMod_exists_iff_coprime,
      CPolynomial.derivative_toPoly, CPolynomial.monicNormalize_toPoly_eq_normalize]
    exact IsCoprime.mono dvd_rfl (normalize_associated _).dvd hfiberSeparable.symm

/-- Evaluating the obstruction commutes with every coefficient-field embedding. -/
theorem map_eval_obstruction {K : Type*} [Field K] (embedding : F →+* K)
    (T : CBivariate F) (center : F) :
    embedding (CPolynomial.eval center (obstruction T)) =
      ((obstruction T).toPoly.map embedding).eval (embedding center) := by
  rw [CPolynomial.eval_toPoly, Polynomial.eval_map, Polynomial.eval₂_hom]

/-- After a coefficient embedding, the mapped stored obstruction is the same leading-coefficient
times fixed-size Sylvester resultant formula for the mapped bivariate polynomial. -/
theorem map_obstruction_toPoly {K : Type*} [Field K] (embedding : F →+* K)
    (T : CBivariate F) :
    (obstruction T).toPoly.map embedding =
      ((CBivariate.toPoly T).map (Polynomial.mapRingHom embedding)).leadingCoeff *
        Polynomial.separableResultant
          ((CBivariate.toPoly T).map (Polynomial.mapRingHom embedding)) T.natDegree := by
  rw [obstruction_toPoly, Polynomial.map_mul]
  have hinjective : Function.Injective (Polynomial.mapRingHom embedding) :=
    Polynomial.map_injective embedding embedding.injective
  rw [Polynomial.leadingCoeff_map_of_injective hinjective]
  congr 1
  simp only [Polynomial.separableResultant]
  have hmap := Polynomial.resultant_map_map
    (f := (CBivariate.toPoly T).derivative) (g := CBivariate.toPoly T)
    (m := T.natDegree - 1) (n := T.natDegree)
    (Polynomial.mapRingHom embedding)
  rw [Polynomial.derivative_map]
  exact hmap.symm

end

end Polynomial.FunctionFieldAlgorithms.RegularCenterObstruction
