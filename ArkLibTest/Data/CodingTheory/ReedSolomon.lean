/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold
import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic.NormNum

/-!
# Reed–Solomon acceptance tests

Concrete instances check the agreement threshold, its distance interpretation, codeword
determination, and the single-word power-agreement guarantee.
-/

open Polynomial ReedSolomon CoreDefinitions

namespace ReedSolomonAcceptance

-- Block length `10`, message length `3`, gap `1 / 4`: the threshold is `3 + ⌈5 / 2⌉ = 6`.
example : agreementThreshold (1 / 4) 10 3 = 6 := by
  have hceil : ⌈(5 / 2 : ℝ)⌉₊ = 3 := by
    rw [Nat.ceil_eq_iff (by decide)]
    norm_num
  apply Nat.le_antisymm
  · exact (agreementThreshold_le_iff_real (by norm_num) 10 3 6).2 (by norm_num)
  · norm_num [agreementThreshold, hceil]

example :
    agreementThreshold (1 / 4) 4 2 ≤ Code.agree ![false, false, false, false]
        ![true, false, false, false] ∧
      (Code.relHammingDist ![true, false, false, false] ![false, false, false, false] : ℝ) ≤
        capacityRadius (1 / 4) 4 2 ∧
      Code.agree ![false, false, false, false] ![true, false, false, false] = 3 ∧
      (Code.relHammingDist ![true, false, false, false] ![false, false, false, false] : ℝ) =
        1 / 4 ∧ capacityRadius (1 / 4) 4 2 = 1 / 4 := by
  have hthreshold : agreementThreshold (1 / 4) 4 2 ≤ 3 := by
    exact (agreementThreshold_le_iff_real (by norm_num) 4 2 3).2 (by norm_num)
  have hagree : Code.agree ![false, false, false, false] ![true, false, false, false] = 3 := by
    decide
  have hdist : (Code.relHammingDist ![true, false, false, false]
      ![false, false, false, false] : ℝ) = 1 / 4 := by
    norm_num [Code.relHammingDist, hammingDist]
    decide
  have hradius : capacityRadius (1 / 4) 4 2 = 1 / 4 := by
    norm_num [capacityRadius]
  constructor
  · simpa [hagree] using hthreshold
  · constructor
    · exact (relHammingDist_le_capacityRadius_iff_agreementThreshold_le
        (delta := 1 / 4) (messageDim := 2) (by norm_num) (by decide)
        ![false, false, false, false] ![true, false, false, false]).mpr
          (by simpa [hagree] using hthreshold)
    · exact ⟨hagree, hdist, hradius⟩

end ReedSolomonAcceptance

namespace PowerAgreementTest

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The evaluation points `0, 1, 2` in `ℚ`. -/
def domain3 : Fin 3 ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

example : Code.DeterminedByAgreement (code domain3 2) 2 :=
  determinedByAgreement_code domain3 le_rfl

-- A single received word has uniform exact power agreement with no exceptional challenge.
example : UniformExactPowerAgreement domain3 ![![1, 2, 5]] 2 0 0 :=
  uniformExactPowerAgreement_singleton domain3 _ 2 0

private noncomputable def domain2 : Fin 2 ↪ ZMod 2 :=
  ⟨fun i ↦ (i.val : ZMod 2), fun a b h ↦ by
    fin_cases a <;> fin_cases b <;> simp_all⟩

private noncomputable def twoWords : Fin 2 → Fin 2 → ZMod 2 :=
  fun t i ↦ if t = 0 then 0 else if i = 0 then 1 else 0

private noncomputable def twoPolynomials : Fin 2 → (ZMod 2)[X] :=
  fun t ↦ if t = 0 then 0 else 1

-- The two constituent polynomials have exactly one common agreement; at most one challenge
-- creates an extra agreement after batching.
example :
    commonCurveAgreementSet domain2 twoWords twoPolynomials = {0} ∧
      ∃ exceptional : Finset (ZMod 2), exceptional.card ≤ 1 ∧
        ∀ z ∉ exceptional,
          polynomialAgreementSet domain2 (powerBatchedWord twoWords z)
              (powerBatchedPolynomial twoPolynomials z) = {0} := by
  have hcommon : commonCurveAgreementSet domain2 twoWords twoPolynomials = {0} := by
    ext i
    fin_cases i
    · simp [commonCurveAgreementSet, twoWords, twoPolynomials, domain2, Fin.forall_fin_two]
    · simp [commonCurveAgreementSet, twoWords, twoPolynomials, domain2, Fin.forall_fin_two]
  refine ⟨hcommon, ?_⟩
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_powerBatched_agreement domain2 twoWords twoPolynomials 1 (by
      rw [hcommon]
      simp)
  refine ⟨exceptional, ?_, fun z hz ↦ ?_⟩
  · simpa [Fintype.card_fin] using hcard
  · simpa [hcommon] using hgood z hz

end PowerAgreementTest

namespace FrobeniusPowerCoordinateTest

-- Three values produce the sparse polynomial `1 + 2 * X^2 + 3 * X^4`.
example :
    (frobeniusPowerCoordinate 2 (![1, 2, 3] : Fin 3 → ℚ)).eval 2 = 57 ∧
      (frobeniusPowerCoordinate 2 (![1, 2, 3] : Fin 3 → ℚ)).natDegree ≤ 4 := by
  constructor
  · norm_num [frobeniusPowerCoordinate_eval, Fin.sum_univ_succ]
  · simpa using
      (frobeniusPowerCoordinate_natDegree_le (s := 2)
        (values := (![1, 2, 3] : Fin 3 → ℚ)))

end FrobeniusPowerCoordinateTest

namespace ReedSolomonAgreementAcceptance

noncomputable section

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2
local instance : DecidableEq E₄ := Classical.decEq _

private def twoPointDomain : Fin 2 ↪ ZMod 2 where
  toFun i := if i.val = 0 then 0 else 1
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- The polynomial `X` agrees with zero at the first of two evaluation points, over the base
field and its degree-two extension. -/
example :
    polynomialAgreementSet twoPointDomain (fun _ ↦ 0) (X : (ZMod 2)[X]) = {0} ∧
      polynomialAgreementSet
        (twoPointDomain.trans
          ⟨algebraMap (ZMod 2) E₄, (algebraMap (ZMod 2) E₄).injective⟩)
        (fun _ ↦ algebraMap (ZMod 2) E₄ (0 : ZMod 2))
        ((X : (ZMod 2)[X]).map (algebraMap (ZMod 2) E₄)) = {0} ∧
      polynomialAgreementSet
        (twoPointDomain.trans
          ⟨algebraMap (ZMod 2) E₄, (algebraMap (ZMod 2) E₄).injective⟩)
        (fun _ ↦ algebraMap (ZMod 2) E₄ (0 : ZMod 2))
        ((X : (ZMod 2)[X]).map (algebraMap (ZMod 2) E₄)) =
          polynomialAgreementSet twoPointDomain (fun _ ↦ 0) (X : (ZMod 2)[X]) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> norm_num [polynomialAgreementSet, twoPointDomain, Polynomial.eval_X]
  · ext i
    fin_cases i <;> norm_num [polynomialAgreementSet, twoPointDomain, Polynomial.eval_X]
  · exact polynomialAgreementSet_map twoPointDomain (algebraMap (ZMod 2) E₄)
      (algebraMap (ZMod 2) E₄).injective (fun _ ↦ 0) (X : (ZMod 2)[X])

private def repeatedDomain : Fin 3 → ZMod 2 := fun i => if i.val = 1 then 1 else 0

/-- Agreement counts are preserved on a finite indexed domain with repeated evaluation points. -/
example :
    (Finset.univ.filter fun i : Fin 3 =>
      (X : (ZMod 2)[X]).eval (repeatedDomain i) = (0 : ZMod 2)).card = 2 ∧
      (Finset.univ.filter fun i : Fin 3 =>
        ((X : (ZMod 2)[X]).map (algebraMap (ZMod 2) E₄)).eval
            (algebraMap (ZMod 2) E₄ (repeatedDomain i)) = (0 : E₄)).card = 2 := by
  have hsource : (Finset.univ.filter fun i : Fin 3 =>
      (X : (ZMod 2)[X]).eval (repeatedDomain i) = (0 : ZMod 2)).card = 2 := by
    have hset : (Finset.univ.filter fun i : Fin 3 =>
        (X : (ZMod 2)[X]).eval (repeatedDomain i) = (0 : ZMod 2)) = {0, 2} := by
      ext i
      fin_cases i <;> norm_num [Polynomial.eval_X, repeatedDomain]
    rw [hset]
    norm_num
  refine ⟨hsource, ?_⟩
  simpa [Polynomial.eval_X] using
    (card_polynomialAgreement_map (algebraMap (ZMod 2) E₄)
      (algebraMap (ZMod 2) E₄).injective repeatedDomain
      (fun _ ↦ 0) X).trans hsource

/-- The equation `Y₀ = 0` has one degree-`< 1` solution agreeing with one received symbol. -/
example :
    (({(0 : Polynomial ℚ)} : Finset (Polynomial ℚ)).card : ℚ) ≤ 1 := by
  let Q : PolynomialDifferential.DifferentialPolynomial ℚ 0 :=
    MvPolynomial.X (some 0)
  let domain : Fin 1 ↪ ℚ :=
    ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  let S : Finset (Polynomial ℚ) := {0}
  have hQ : Q ≠ 0 := by simp [Q]
  have hcast : ∀ j, PolynomialDifferential.JetDegreeCastsNeZero Q j := by
    intro j
    apply PolynomialDifferential.jetDegreeCastsNeZero_of_ringChar
    exact Or.inl (ringChar.eq_zero : ringChar ℚ = 0)
  have hdegree : PolynomialDifferential.jetTotalDegree Q ≤ 1 := by
    change MvPolynomial.weightedTotalDegree
      PolynomialDifferential.jetDegreeWeight (MvPolynomial.X (some 0)) ≤ 1
    have hX : (MvPolynomial.X (some 0) : PolynomialDifferential.DifferentialPolynomial
        ℚ 0) = MvPolynomial.monomial (Finsupp.single (some 0) 1) 1 := by
      rw [← MvPolynomial.C_mul_X_eq_monomial]
      simp
    rw [hX, MvPolynomial.weightedTotalDegree_monomial]
    · simp [Finsupp.weight, PolynomialDifferential.jetDegreeWeight]
    · norm_num
  have hsol : ∀ P ∈ S, PolynomialDifferential.differentialSpecialization Q P = 0 := by
    intro P hP
    simp only [S, Finset.mem_singleton] at hP
    subst P
    simp [Q, PolynomialDifferential.differentialSpecialization,
      PolynomialDifferential.differentialSpecializationHom]
  have hS : ∀ P ∈ S, P ∈ closePolynomialSet domain (fun _ ↦ 0) 1 1 := by
    intro P hP
    simp only [S, Finset.mem_singleton] at hP
    subst P
    simp [closePolynomialSet, polynomialAgreementSet, domain]
  have hcount := closePolynomialSet_card_le_of_differential_equation Q
    1 1 1 (by norm_num) (by norm_num) hQ hcast hdegree domain (fun _ ↦ 0)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro r hr i hir hi; omega) S hsol hS
  norm_num [S] at hcount ⊢

/-- A two-coordinate close list satisfies the geometric equation bound over `ℚ`. -/
example : (({(0 : Polynomial ℚ)} : Finset (Polynomial ℚ)).card : ℝ) ≤ 1 := by
  let domain : Fin 2 ↪ ℚ := {
    toFun := fun i ↦ (i.val : ℚ)
    inj' := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num at *
  }
  let received : Fin 2 → ℚ := fun _ ↦ 0
  let Q : PolynomialDifferential.DifferentialPolynomial ℚ 0 := MvPolynomial.X (some 0)
  let S : Finset (Polynomial ℚ) := {0}
  have hQ : Q ≠ 0 := by simp [Q]
  have hdegree : PolynomialDifferential.jetTotalDegree Q ≤ 1 := by
    simpa [Q, PolynomialDifferential.jetDegree] using
      PolynomialDifferential.jetTotalDegree_le_sum_jetDegree Q
  have hsol : ∀ P ∈ S, PolynomialDifferential.differentialSpecialization Q P = 0 := by
    intro P hP
    simp only [S, Finset.mem_singleton] at hP
    subst P
    simp [Q, PolynomialDifferential.differentialSpecialization,
      PolynomialDifferential.differentialSpecializationHom]
  have hS : ∀ P ∈ S, P ∈ closePolynomialSet domain received 1 2 := by
    intro P hP
    simp only [S, Finset.mem_singleton] at hP
    subst P
    simp [closePolynomialSet, polynomialAgreementSet, domain, received]
  have haccepts : ∀ P ∈ S, P ∈ closePolynomialSet domain received 1 2 := hS
  let accepts : Polynomial ℚ → Prop := fun P ↦ P ∈ closePolynomialSet domain received 1 2
  have hagreement : ∀ P, accepts P ↔
      P.degree < 1 ∧ 2 ≤ (Finset.univ.filter fun i ↦
        P.eval (domain i) = received i).card := by
    intro P
    simp [accepts, closePolynomialSet, polynomialAgreementSet]
  have h := PolynomialDifferential.finite_solutions_card_le_sq_totalJetDegree_of_agreementGap
    (δ := 1 / 2) Q 2 1 1 (by norm_num) (by norm_num) hQ hdegree domain received
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
    accepts hagreement S hsol haccepts
  norm_num [S] at h ⊢

end
end ReedSolomonAgreementAcceptance
