/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLineComponent
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic
import ArkLib.ToMathlib.RingTheory.Nullstellensatz

/-!
# Acceptance tests for joint Taylor chart recognition

The joint chart example uses one concrete sample and a regular point with a nonzero challenge.
The component example uses a prime line and exhibits a regular point on its zero locus.
-/

open MvPolynomial Polynomial PolynomialDifferential

namespace ReedSolomon.GraphLineComponentTest

noncomputable section

private def domain : Fin 1 ↪ ℚ :=
  ⟨fun _ ↦ 0, by intro i j _; exact Subsingleton.elim _ _⟩

private def componentWord : Fin 1 → ℚ := fun _ ↦ 0

private abbrev equation : DifferentialPolynomial ℚ[X] 0 := X (some 0)
private abbrev componentEquation {E : Type*} [CommSemiring E] :
    DifferentialPolynomial E[X] 0 := X (some 0)

private abbrev componentVariable {E : Type*} [CommSemiring E] :
    MvPolynomial (Option (Fin 1)) E := X (some (0 : Fin 1))

private def componentIdeal {E : Type*} [CommSemiring E] :
    Ideal (MvPolynomial (Option (Fin 1)) E) := Ideal.span {componentVariable}

private abbrev ComponentField := AlgebraicClosure ℚ

private def componentPoint : Option (Fin 1) → ComponentField
  | none => 2
  | some _ => 0

private theorem componentIdeal_isPrime :
    (componentIdeal (E := ComponentField)).IsPrime := by
  change (Ideal.span {(X (some (0 : Fin 1)) :
    MvPolynomial (Option (Fin 1)) ComponentField)}).IsPrime
  exact (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime

private theorem componentIdeal_degree_pos :
    0 < (affineHilbertPolynomial (componentIdeal (E := ComponentField))).natDegree := by
  have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
    (f := componentVariable (E := ComponentField)) (X_ne_zero _) componentIdeal_isPrime.ne_top
  have hcard : Nat.card (Option (Fin 1)) = 2 := by simp
  have h' : (affineHilbertPolynomial (componentIdeal (E := ComponentField))).natDegree + 1 = 2 := by
    simpa [componentIdeal, componentVariable, hcard] using h
  omega

private theorem componentIdeal_one_notMem :
    (1 : MvPolynomial (Option (Fin 1)) ComponentField) ∉
      componentIdeal (E := ComponentField) := by
  intro h
  exact componentIdeal_isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

private theorem component_separant_notMem :
    jointInitialJetSeparant (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) ∉ componentIdeal := by
  simpa [jointInitialJetSeparant, componentEquation, initialJetSeparant,
    separant, Fin.last] using componentIdeal_one_notMem

private theorem component_generator_mem :
    componentVariable (E := ComponentField) ∈ componentIdeal :=
  Ideal.subset_span (by simp)

private theorem component_initialEquation_mem :
    jointInitialJetEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) ∈ componentIdeal := by
  change (optionEquivRight ComponentField (Fin 1)).symm
    (initialJetEquation (Polynomial.C (0 : ComponentField))
      (componentEquation (E := ComponentField))) ∈ componentIdeal
  rw [show initialJetEquation (Polynomial.C (0 : ComponentField))
      (componentEquation (E := ComponentField)) =
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) (Polynomial ComponentField)) by
    simp [initialJetEquation, componentEquation]]
  simp only [optionEquivRight_symm_X]
  exact component_generator_mem

private theorem component_highCuts : ∀ l : Fin 1, 1 ≤ l.val →
    jointCommonTaylorNumerator (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) 1 l ∈ componentIdeal := by
  intro l hl
  omega

private theorem component_cut_eq :
    taylorAgreementEquationOver (F := ComponentField) (Polynomial.C (0 : ComponentField))
      (componentEquation (E := ComponentField)) 1 (0 : ComponentField[X]) 0 (τ := 1) =
        initialJetEquation (Polynomial.C (0 : ComponentField))
          (componentEquation (E := ComponentField)) := by
  simp [taylorAgreementEquationOver, commonTaylorNumeratorOver,
    rationalTaylorNumeratorOver, initialJetEquation, initialJetSeparant, separant, Fin.last,
    componentEquation]

private theorem component_agreementCuts : ∀ i ∈ Finset.univ,
    jointTaylorAgreementEquation (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField)) 1 1
      (Polynomial.C ((algebraMap ℚ ComponentField) (domain i)))
      (Polynomial.C ((algebraMap ℚ ComponentField) (componentWord i)) +
        Polynomial.X * Polynomial.C ((algebraMap ℚ ComponentField) (componentWord i))) ∈
        componentIdeal := by
  intro i hi
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst i
  have hd0 : domain (0 : Fin 1) = 0 := rfl
  have hxval : Polynomial.C ((algebraMap ℚ ComponentField) (domain 0)) =
      (0 : ComponentField[X]) := by
    rw [hd0]
    simp
  have hyval : Polynomial.C ((algebraMap ℚ ComponentField) (componentWord 0)) +
      Polynomial.X * Polynomial.C ((algebraMap ℚ ComponentField) (componentWord 0)) =
        (0 : ComponentField[X]) := by simp [componentWord]
  change (optionEquivRight ComponentField (Fin 1)).symm
    (taylorAgreementEquationOver (F := ComponentField) (Polynomial.C (0 : ComponentField))
      (componentEquation (E := ComponentField)) 1
      (Polynomial.C ((algebraMap ℚ ComponentField) (domain 0)))
      (Polynomial.C ((algebraMap ℚ ComponentField) (componentWord 0)) +
        Polynomial.X * Polynomial.C ((algebraMap ℚ ComponentField) (componentWord 0)))
      (τ := 1)) ∈ componentIdeal
  rw [hxval, hyval, component_cut_eq]
  exact component_initialEquation_mem

private theorem componentPoint_mem_zeroLocus :
    componentPoint ∈ zeroLocus ComponentField (componentIdeal (E := ComponentField)) := by
  rw [MvPolynomial.mem_zeroLocus_iff_le_ker_aeval]
  apply Ideal.span_le.mpr
  intro q hq
  rw [Set.mem_singleton_iff.mp hq]
  simp [componentPoint, componentVariable]

private theorem componentPoint_regular :
    aeval componentPoint (jointInitialJetSeparant (r := 0) (0 : ComponentField)
      (componentEquation (E := ComponentField))) ≠ 0 := by
  simp [jointInitialJetSeparant, componentEquation, initialJetSeparant,
    separant, Fin.last]

/-- A regular joint-chart point with challenge `2` reconstructs the pair fixed at the sample. -/
example :
    ∃ P₀ P₁ : ℚ[X], P₀.degree < 1 ∧ P₁.degree < 1 ∧
      P₀.eval 0 = 0 ∧ P₁.eval 0 = 0 ∧
      rationalTaylorPolynomial (0 : ℚ)
        (map (Polynomial.evalRingHom 2) equation) 1 (fun _ : Fin 1 ↦ 0) =
          P₀.map (RingHom.id ℚ) + Polynomial.C 2 * P₁.map (RingHom.id ℚ) := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsample, hrecognize⟩ :=
    exists_graphLine_pair_of_joint_taylor_chart (n := 1) (k := 1) (K := 1) (r := 0)
      domain (fun _ ↦ 0) (fun _ ↦ 0) Finset.univ (by simp) (RingHom.id ℚ) 0 equation
      (by omega) 1 (by intro l; omega)
  let x : Option (Fin 1) → ℚ
    | none => 2
    | some _ => 0
  have hS : aeval x (jointInitialJetSeparant (r := 0) 0 equation) ≠ 0 := by
    simp [jointInitialJetSeparant, initialJetSeparant, equation, separant, Fin.last, x]
  have hhigh : ∀ l : Fin 1, 1 ≤ l.val →
      aeval x (jointCommonTaylorNumerator (r := 0) 0 equation 1 l) = 0 := by
    intro l hl
    omega
  have hcuts : ∀ i ∈ Finset.univ,
      aeval x (jointTaylorAgreementEquation (r := 0) 0 equation 1 1
        (Polynomial.C (domain i))
        (Polynomial.C 0 + Polynomial.X * Polynomial.C 0)) = 0 := by
    intro i hi
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    simp [jointTaylorAgreementEquation, equation,
      commonTaylorNumeratorOver, rationalTaylorNumeratorOver,
      initialJetSeparant, separant, Fin.last, x]
  have hresult := hrecognize x hS hhigh hcuts
  have hd0 : domain (0 : Fin 1) = 0 := rfl
  refine ⟨P₀, P₁, hP₀, hP₁, ?_, ?_, hresult.1⟩
  · simpa only [hd0] using (hsample 0 (by simp)).1
  · simpa only [hd0] using (hsample 0 (by simp)).2

/-- A regular point of a prime line component lies on the graph returned by recognition. -/
example :
    ∃ P₀ P₁ : ℚ[X], ∃ z : ComponentField,
      P₀.eval 0 = 0 ∧ P₁.eval 0 = 0 ∧ z = 2 := by
  have hprime : (componentIdeal (E := ComponentField)).IsPrime := componentIdeal_isPrime
  have hcomponent := exists_graphLine_pair_of_regular_component
    (domain := domain) (f := componentWord) (g := componentWord) (sample := Finset.univ)
    (hsample := by simp) (iota := algebraMap ℚ ComponentField) (center := 0)
    (Q := componentEquation (E := ComponentField)) (hK := by omega) (τ := 1)
    (hτ := by intro l; omega) (P := componentIdeal (E := ComponentField))
    (hs := component_separant_notMem) (hd := componentIdeal_degree_pos)
    (hinit := component_initialEquation_mem) (hhigh := component_highCuts)
    (hcuts := component_agreementCuts)
  obtain ⟨P₀, P₁, -, -, hsample, hgraph, -, -, -, -, -⟩ := hcomponent
  obtain ⟨z, hxgraph⟩ := hgraph componentPoint
    ⟨componentPoint_mem_zeroLocus, componentPoint_regular⟩
  have hz : componentPoint none = z := by
    have h := congrFun hxgraph none
    simpa [componentPoint, affinePairCurve] using h
  have hd0 : domain (0 : Fin 1) = 0 := rfl
  exact ⟨P₀, P₁, z,
    by simpa [componentWord, hd0] using (hsample 0 (by simp)).1,
    by simpa [componentWord, hd0] using (hsample 0 (by simp)).2,
    by simpa [componentPoint] using hz.symm⟩

end

end ReedSolomon.GraphLineComponentTest
