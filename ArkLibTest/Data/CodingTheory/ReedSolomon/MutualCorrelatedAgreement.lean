/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FullDimension
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.SingularTail
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TupleSpecialization
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.Finite.Extension

open Polynomial Finset ReedSolomon ReedSolomon.FirstOrder.Squarefree

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2
private def pointDomain : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

noncomputable section

local instance : DecidableEq E₄ := Classical.decEq E₄

/-- A nonzero affine line descends from the degree-two extension. -/
example : HasExactCorrelatedPair pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
    (RingHom.id (ZMod 2)) 2 1 (1 + X) := by
  let ι : ZMod 2 →+* E₄ := algebraMap (ZMod 2) E₄
  have hext : HasExactCorrelatedPair pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
      ι 2 (ι 1) ((1 + X : (ZMod 2)[X]).map ι) := by
    refine ⟨(1, X), by norm_num, by norm_num, ?_, ?_⟩
    · simp [correlatedPairSpecialization]
    · ext i
      fin_cases i
      simp [polynomialAgreementSet, commonPolynomialAgreementSet, pointDomain]
  exact HasExactCorrelatedPair.descend pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
    ι 2 1 (1 + X) hext

end

private def fullDomain : Fin 2 ↪ ℚ where
  toFun i := ((i : ℕ) : ℚ)
  inj' _i _j h := Fin.ext (Nat.cast_injective (R := ℚ) h)

/-- At challenge `1`, the candidate `1 + 2X` is explained by one pair on both coordinates. -/
example : ∃ F₀ G₀ : ℚ[X], C 1 + C 2 * X = F₀ + C 1 * G₀ ∧
    commonPolynomialAgreementSet fullDomain ![1, 2] ![0, 1] F₀ G₀ = univ := by
  obtain ⟨F₀, G₀, -, -, hpair⟩ :=
    exists_exactPair_fullDimension fullDomain ![1, 2] ![0, 1]
  have hagree : polynomialAgreementSet fullDomain (fun i ↦ ![1, 2] i + 1 * ![0, 1] i)
      (C 1 + C 2 * X) = univ := by
    ext i
    fin_cases i
    · norm_num [fullDomain, polynomialAgreementSet]
      change (0 : ℚ) = 0
      rfl
    · norm_num [fullDomain, polynomialAgreementSet]
      change 1 + 2 * (1 : ℚ) = 3
      norm_num
  obtain ⟨hP, hset⟩ := hpair 1 (C 1 + C 2 * X) (by
    rw [Fintype.card_fin]
    compute_degree!) (by rw [hagree, card_univ])
  exact ⟨F₀, G₀, hP, hset.symm.trans hagree⟩

/-- Graph-line recognition for the concrete sample `0, 1` at challenge `1`. -/
example : ∃ F₀ G₀ : ℚ[X], C 1 + C 2 * X = F₀ + C 1 * G₀ := by
  obtain ⟨F₀, G₀, -, -, -, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample fullDomain ![1, 2] ![0, 1] univ
      (card_univ.trans rfl)
  have h := hrecognize (RingHom.id ℚ) 1 (C 1 + C 2 * X) (by
    rw [Fintype.card_fin]
    compute_degree!) (by
    intro i _
    fin_cases i
    · norm_num [fullDomain]
      change (0 : ℚ) = 0
      rfl
    · norm_num [fullDomain]
      change 1 + 2 * (1 : ℚ) = 3
      norm_num)
  exact ⟨F₀, G₀, by simpa using h⟩

/-- A double root of `X²` kills the specialized singular tail. -/
example : singularTail (1 : ℚ[X]) (X ^ 2 : ℚ[X][X]) 2 = 0 := by
  have h := singularTail_map_eq_zero_of_common_root (1 : ℚ[X]) (X ^ 2 : ℚ[X][X]) two_pos
    (by simp) (RingHom.id ℚ[X]) 0 (by simp) (by simp)
  simpa using h

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
