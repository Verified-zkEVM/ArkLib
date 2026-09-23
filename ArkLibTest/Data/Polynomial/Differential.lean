/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TaylorChartBaseChange
import ArkLib.Data.Polynomial.Differential.RationalTaylorBidegree
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for Taylor chart coefficient extension and bidegrees

The rational equation `Y₀ = 0` has a bounded regular solution whose chart jet satisfies the
initial equation, nonzero separant, a nonvacuous high Taylor cut, and agreement at two positions.
A concrete nonempty family over `ZMod 2` has a common regular center after extension to its
algebraic closure. Concrete bidegree examples check common numerators and agreement equations.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial Polynomial

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

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

/-- A nonempty regular family over `ZMod 2` has a common center in its algebraic closure. -/
example :
    let Q : DifferentialPolynomial (ZMod 2) 0 :=
      (MvPolynomial.X none ^ 2 - MvPolynomial.X none) * MvPolynomial.X (some 0)
    ∃ center : AlgebraicClosure (ZMod 2),
      ∀ P ∈ ({(0 : (ZMod 2)[X])} : Finset ((ZMod 2)[X])),
        jetEvaluation
          (separant
            (MvPolynomial.map (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))) Q) 0)
          center
          (polynomialJet center
            (P.map (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))))) ≠ 0 := by
  intro Q
  have hspec : differentialSpecialization (separant Q 0) (0 : (ZMod 2)[X]) =
      (Polynomial.X ^ 2 - Polynomial.X : (ZMod 2)[X]) := by
    simp [Q, separant, differentialSpecialization, differentialSpecializationHom]
  have hspec_ne : differentialSpecialization (separant Q 0) (0 : (ZMod 2)[X]) ≠ 0 := by
    rw [hspec]
    intro h
    have hc := congrArg (fun P : (ZMod 2)[X] ↦ P.coeff 2) h
    norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  have hregular : ∀ P ∈ ({(0 : (ZMod 2)[X])} : Finset ((ZMod 2)[X])),
      differentialSpecialization (separant Q 0) P ≠ 0 := by
    intro P hP
    have hP0 : P = 0 := Finset.mem_singleton.mp hP
    subst P
    exact hspec_ne
  let f : ZMod 2 →+* AlgebraicClosure (ZMod 2) := algebraMap _ _
  exact exists_forall_jetEvaluation_ne_zero_map f f.injective Q {0} 0 hregular

private abbrev oneJet : DifferentialPolynomial (Polynomial ℚ) 0 := X (some 0)

private theorem oneJet_jetDegree : jetTotalDegree oneJet ≤ 1 := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  rw [MvPolynomial.support_X] at hu
  simp only [Finset.mem_singleton] at hu
  subst u
  rw [totalJetDegree_eq_sum]
  simp

/-- The first coordinate of a zero-order equation has bidegree `(0, 1)` after flattening. -/
example :
    (optionEquivRight ℚ (Fin 1)).symm
        (commonTaylorNumeratorOver ℚ (Polynomial.C (0 : ℚ)) oneJet 0 0) ∈
      restrictBidegree (Fin 1) ℚ 0 1 := by
  exact commonTaylorNumeratorOver_mem_restrictBidegree (F := ℚ) (r := 0) 0 oneJet
    0 1 1 0 (by norm_num [TaylorExponentSufficient]) (coeffNatDegreeLE_X (some 0))
    (by norm_num) oneJet_jetDegree ⟨0, by decide⟩

/-- Agreement at the origin with the zero received value keeps the same bidegree bound. -/
example :
    (optionEquivRight ℚ (Fin 1)).symm
        (taylorAgreementEquationOver (F := ℚ) (A := Polynomial ℚ)
          (Polynomial.C 0) oneJet 1 (Polynomial.C 0) (0 : Polynomial ℚ) (τ := 0)) ∈
      restrictBidegree (Fin 1) ℚ 0 1 := by
  exact taylorAgreementEquationOver_mem_restrictBidegree (F := ℚ) (r := 0)
    0 0 0 oneJet 0 0 1 1 0 (by norm_num [TaylorExponentSufficient]) (by norm_num)
    (coeffNatDegreeLE_X (some 0)) (by norm_num) oneJet_jetDegree

end

end PolynomialDifferential
