/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TupleSpecialization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for Reed–Solomon mutual correlated agreement -/

open Polynomial Finset ReedSolomon PolynomialDifferential

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2
private def pointDomain : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩
private noncomputable def agreementEquation : DifferentialPolynomial (ZMod 2)[X] 0 :=
  MvPolynomial.X (some 0) - MvPolynomial.C (Polynomial.X)

noncomputable section

local instance : DecidableEq E₄ := Classical.decEq E₄

/-- A nonzero affine line descends from the degree-two extension. -/
example : HasExactCorrelatedPair pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
    (RingHom.id (ZMod 2)) 2 1 (1 + X) :=
  HasExactCorrelatedPair.descend pointDomain _ _ (algebraMap (ZMod 2) E₄) 2 1 (1 + X)
    ⟨(1, X), by norm_num, by norm_num, by simp [correlatedPairSpecialization], by
      ext i
      fin_cases i
      simp [polynomialAgreementSet, commonPolynomialAgreementSet, pointDomain]⟩

/-- The equation `Y = X` descends from `E₄`: its constant solution at `z = 1` is correlated. -/
example : HasExactCorrelatedPair pointDomain (fun _ ↦ (0 : ZMod 2)) (fun _ ↦ 1)
    (RingHom.id (ZMod 2)) 2 1 (C 1) := by
  obtain ⟨exceptional, hcard, hdescend⟩ :=
    exists_exceptional_equation_correlatedAgreement_descend pointDomain (fun _ ↦ (0 : ZMod 2))
      (fun _ ↦ 1) (algebraMap (ZMod 2) E₄) agreementEquation 2 1 ∅ fun z _ P _ _ hroot ↦ by
        obtain rfl : P = C z := sub_eq_zero.mp (by
          simpa [agreementEquation, challengeSpecialization, differentialSpecialization,
            differentialSpecializationHom] using hroot)
        refine ⟨(0, 1), by rw [degree_zero]; exact WithBot.bot_lt_coe 2, by norm_num,
          by simp [correlatedPairSpecialization], ?_⟩
        ext i; fin_cases i; simp [polynomialAgreementSet, commonPolynomialAgreementSet, pointDomain]
  exact hdescend 1 (by simp_all) (C 1) (by simp) (by simp [pointDomain, polynomialAgreementSet])
    (by simp [agreementEquation, challengeSpecialization, differentialSpecialization,
      differentialSpecializationHom])

end

private theorem singletonLineExactBound : LineExactAgreementBound pointDomain 1 1 0 :=
  fun f g ↦ ⟨∅, by simp, fun z _ P hP hclose ↦ by
    have hagree : polynomialAgreementSet pointDomain (fun i ↦ f i + z * g i) P = Finset.univ :=
      Finset.eq_univ_of_card _
        (le_antisymm (Finset.card_le_univ _) (by simpa [Fintype.card_fin] using hclose))
    have heval := (mem_polynomialAgreementSet ..).mp (hagree ▸ Finset.mem_univ (0 : Fin 1))
    refine ⟨C (f 0), C (g 0), degree_C_le.trans_lt (by norm_num),
      degree_C_le.trans_lt (by norm_num), ?_, ?_⟩
    · rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hP), coeff_zero_eq_eval_zero,
        ← C_mul, ← C_add, ← heval]; rfl
    · rw [hagree]; ext i; fin_cases i; simp [commonPolynomialAgreementSet, pointDomain]⟩

private def affineValues : Fin 2 → Fin 1 → ZMod 2 := ![fun _ ↦ 1, fun _ ↦ 0]

example := exists_affine_exceptionalSet_full_agreement_of_exactLine pointDomain 0
  singletonLineExactBound 0 (by norm_num [pointDomain]) (by norm_num) affineValues

private def fullDomain : Fin 2 ↪ ℚ where
  toFun i := ((i : ℕ) : ℚ)
  inj' _i _j h := Fin.ext (Nat.cast_injective (R := ℚ) h)

/-- The graph-line recognizer accepts the computed candidate `1 + 2X` at challenge `1`. -/
example : ∃ F₀ G₀ : ℚ[X], F₀.degree < 2 ∧ G₀.degree < 2 ∧
    (∀ i ∈ (Finset.univ : Finset (Fin 2)),
      F₀.eval (fullDomain i) = ![1, 2] i ∧ G₀.eval (fullDomain i) = ![0, 1] i) ∧
    C 1 + C 2 * X = F₀ + C 1 * G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, hsample, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample fullDomain ![1, 2] ![0, 1] univ (card_univ.trans rfl)
  refine ⟨F₀, G₀, hF₀, hG₀, hsample, ?_⟩
  refine (hrecognize (RingHom.id ℚ) 1 (C 1 + C 2 * X) (by compute_degree!) fun i _ ↦ ?_).trans
    (by simp)
  fin_cases i <;> norm_num [fullDomain]
  exacts [rfl, show (1 + 2 * 1 : ℚ) = 3 by norm_num]

/-- The exceptional bound is attained when the graph agrees at only one coordinate. -/
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 1 ∧ 0 ∈ exceptional := by
  obtain ⟨exceptional, hcard, hagreement⟩ :=
    exists_exceptional_graphLine_challenges fullDomain ![0, 0] ![0, 1] (0 : ℚ[X]) 0 (RingHom.id ℚ)
  have hcommon : commonPolynomialAgreementSet fullDomain ![0, 0] ![0, 1] 0 0 = {0} := by
    ext i; fin_cases i <;> simp [commonPolynomialAgreementSet, fullDomain]
  refine ⟨exceptional, by simpa [hcommon, Fintype.card_fin] using hcard, by_contra fun hz ↦ ?_⟩
  have hone : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := by
    rw [← hcommon, ← hagreement 0 hz]; simp [polynomialAgreementSet, fullDomain]
  simp at hone

private noncomputable def tupleOne : Fin 2 → ℚ[X] := ![1, 0]
private noncomputable def tupleChallenge : Fin 2 → ℚ[X] := ![0, 1]
private theorem tuples_ne : tupleOne ≠ tupleChallenge := fun h ↦ by
  simpa [tupleOne, tupleChallenge] using congrFun h 0

example :
    {z : ℚ | powerBatchedPolynomial (fun t ↦ (tupleOne t).map (RingHom.id ℚ)) z =
      powerBatchedPolynomial (fun t ↦ (tupleChallenge t).map (RingHom.id ℚ)) z}.Finite :=
  finite_polynomialTuple_collisions (RingHom.id ℚ) tuples_ne

example : ∃ z : ℚ, z ≠ 1 ∧ z ≠ 0 ∧
    powerBatchedPolynomial (fun t ↦ (tupleOne t).map (RingHom.id ℚ)) z ≠
      powerBatchedPolynomial (fun t ↦ (tupleChallenge t).map (RingHom.id ℚ)) z := by
  classical
  obtain ⟨z, hz, hinj, hroot⟩ := exists_polynomialTuple_specialization_injective_avoiding_roots
    (RingHom.id ℚ) {tupleOne, tupleChallenge} {1} {X} (by simp [X_ne_zero])
  refine ⟨z, by simpa using hz, by simpa using hroot X (by simp), fun heq ↦ ?_⟩
  exact tuples_ne (hinj (by simp) (by simp) heq)
