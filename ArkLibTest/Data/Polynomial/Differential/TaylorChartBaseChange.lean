/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TaylorChartBaseChange
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for rational Taylor chart coefficient extension

* A singleton family solving `Y₀ = 0` over `ℚ` produces a one-element regular jet family and
  keeps agreement at two finite coordinates.
* The source-shaped `Fin n` hypothesis on binomial pivots over the base field implies the more
  general chart-field pivot condition.
* In characteristic two, `0` and `X²` solve `Y₁ = 0`, have the same jet at `0`, and the pivot
  `(2 choose 1)` vanishes, so their polynomial-jet image loses cardinality.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- The equation `Y₀ = 0` over a field. -/
private abbrev zeroOrderEquation (F : Type*) [Field F] : DifferentialPolynomial F 0 :=
  X (some 0)

/-- A singleton regular solution family over `ℚ` yields a one-element chart family on the initial
hypersurface. -/
example : ∃ center : ℚ, ∃ J : Finset (Fin 1 → ℚ), J.card = 1 ∧
    ∀ jet ∈ J,
      aeval jet (initialJetEquation center
        (MvPolynomial.map (RingHom.id ℚ) (zeroOrderEquation ℚ))) = 0 := by
  classical
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
  obtain ⟨center, hfamily⟩ := exists_regular_solution_jet_family
    (f := RingHom.id ℚ) (Q := zeroOrderEquation ℚ) (K := 1) (k := 1) (A := 2)
    (hkK := le_rfl) (S := {0}) (domain := fun _ : Fin 2 ↦ (0 : ℚ))
    (received := fun _ ↦ (0 : ℚ)) hdegree hsol hsep
    (by intro i hi hiK; omega)
    (by intro P hP; rw [Finset.mem_singleton.mp hP]; norm_num)
  obtain ⟨J, hcard, hproperties⟩ := hfamily
  exact ⟨center, J, by simpa using hcard, fun jet hjet ↦
    (hproperties jet hjet).1⟩

open Classical in
/-- The `Fin n` form with base-field pivot hypotheses follows from chart-field pivots by
injectivity of the coefficient map. -/
example {F E : Type*} [Field F] [Field E] [Infinite E] {r : ℕ}
    (f : F →+* E) (Q : DifferentialPolynomial F r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hkK : k ≤ K)
    (S : Finset (Polynomial F)) {n A : ℕ} (domain received : Fin n → F)
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i : Fin n ↦ P.eval (domain i) = received i).card) :
    ∃ (center : E) (J : Finset (Fin (r + 1) → E)), J.card = S.card ∧
      ∀ jet ∈ J,
        aeval jet (initialJetEquation center (MvPolynomial.map f Q)) = 0 ∧
        aeval jet (initialJetSeparant center (MvPolynomial.map f Q)) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval jet (commonTaylorNumerator center (MvPolynomial.map f Q) τ l.val) = 0) ∧
        A ≤ (Finset.univ.filter (fun i : Fin n ↦
          aeval jet (taylorAgreementEquation center (MvPolynomial.map f Q) K τ
            (f (domain i)) (f (received i))) = 0)).card := by
  exact exists_regular_solution_jet_family_of_exponent f Q K k τ hτ hkK S domain received
    hdegree hsol hsep (by
      intro i hi hiK hzero
      apply hbin i hi hiK
      apply f.injective
      simpa using hzero) hagree

/-- In characteristic two, `0` and `X²` solve `Y₁ = 0`, have the same initial jet at `0`, and
the pivot `(2 choose 1)` vanishes, so their jet image has cardinality one instead of two. -/
example :
    differentialSpecialization
        (MvPolynomial.X (some (Fin.last 1)) : DifferentialPolynomial (ZMod 2) 1)
        (0 : Polynomial (ZMod 2)) = 0 ∧
      differentialSpecialization
        (MvPolynomial.X (some (Fin.last 1)) : DifferentialPolynomial (ZMod 2) 1)
        (Polynomial.X ^ 2) = 0 ∧
      differentialSpecialization
        (separant (MvPolynomial.X (some (Fin.last 1))) (Fin.last 1))
        (0 : Polynomial (ZMod 2)) ≠ 0 ∧
      (0 : Polynomial (ZMod 2)).degree < 3 ∧
      (Polynomial.X ^ 2 : Polynomial (ZMod 2)).degree < 3 ∧
      polynomialJet (d := 1) (0 : ZMod 2) (0 : Polynomial (ZMod 2)) =
        polynomialJet 0 (Polynomial.X ^ 2) ∧
      (Nat.choose 2 1 : ZMod 2) = 0 ∧
      ({0, Polynomial.X ^ 2} : Finset (Polynomial (ZMod 2))).card = 2 ∧
      (({0, Polynomial.X ^ 2} : Finset (Polynomial (ZMod 2))).image
        (polynomialJet (d := 1) (0 : ZMod 2))).card = 1 := by
  have hjet : polynomialJet (d := 1) (0 : ZMod 2) (0 : Polynomial (ZMod 2)) =
      polynomialJet 0 (Polynomial.X ^ 2) := by
    funext i
    fin_cases i <;> simp [polynomialJet]
  have hne : (0 : Polynomial (ZMod 2)) ≠ Polynomial.X ^ 2 := by
    intro h
    have heval := congrArg (Polynomial.eval 1) h
    norm_num at heval
  refine ⟨?_, ?_, ?_, by exact WithBot.bot_lt_coe 3, ?_, hjet, by decide, ?_, ?_⟩
  · simp [differentialSpecialization_jet]
  · simp [differentialSpecialization_jet, Polynomial.hasseDeriv_one,
      one_add_one_eq_two, CharTwo.two_eq_zero]
  · simp [separant, differentialSpecialization, differentialSpecializationHom]
  · rw [Polynomial.degree_X_pow]
    norm_num
  · simp [hne]
  · simp [hjet]

end

end PolynomialDifferential
