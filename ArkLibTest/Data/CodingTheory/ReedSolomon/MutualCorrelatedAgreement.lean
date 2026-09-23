/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FullDimension
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.SingularTail
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TupleSpecialization
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.Finite.Extension

open Polynomial Finset ReedSolomon ReedSolomon.FirstOrder.Squarefree PolynomialDifferential

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

example : HasExactCorrelatedPair pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0)
    (RingHom.id (ZMod 2)) 1 1 (C 1) := by
  let ι : ZMod 2 →+* E₄ := algebraMap (ZMod 2) E₄
  have hgood : ∀ z ∉ (∅ : Finset E₄), ∀ P : E₄[X], P.degree < 1 →
      1 ≤ (polynomialAgreementSet (pointDomain.trans ⟨ι, ι.injective⟩)
        (fun i ↦ ι ((fun _ : Fin 1 ↦ (1 : ZMod 2)) i) +
          z * ι ((fun _ : Fin 1 ↦ (0 : ZMod 2)) i)) P).card →
      differentialSpecialization
        (challengeSpecialization
          (MvPolynomial.map (Polynomial.mapRingHom ι)
            (0 : DifferentialPolynomial (ZMod 2)[X] 0)) z) P = 0 →
      HasExactCorrelatedPair pointDomain (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0) ι 1 z P := by
    intro z _ P hP hagree _
    have hfull : polynomialAgreementSet (pointDomain.trans ⟨ι, ι.injective⟩)
        (fun i ↦ ι ((fun _ : Fin 1 ↦ (1 : ZMod 2)) i) +
          z * ι ((fun _ : Fin 1 ↦ (0 : ZMod 2)) i)) P = Finset.univ :=
      Finset.eq_univ_of_card _
        (le_antisymm (Finset.card_le_univ _) (by simpa [Fintype.card_fin] using hagree))
    have heval := (mem_polynomialAgreementSet ..).mp
      (hfull ▸ Finset.mem_univ (0 : Fin 1))
    have hcoeff : P.coeff 0 = ι 1 := by
      have hpoint : (pointDomain.trans ⟨ι, ι.injective⟩) 0 = 0 := by
        change ι 0 = 0
        exact map_zero ι
      rw [hpoint] at heval
      calc
        P.coeff 0 = P.eval 0 := coeff_zero_eq_eval_zero P
        _ = ι 1 := by simpa using heval
    have hPconst : P = C (ι 1) := by
      rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hP), hcoeff]
    refine ⟨(C 1, C 0), by simp, by simp, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using hPconst
    · rw [hfull]
      ext i
      fin_cases i
      simp [commonPolynomialAgreementSet, pointDomain]
  obtain ⟨exceptional, hcard, hdescend⟩ :=
    exists_exceptional_equation_correlatedAgreement_descend pointDomain
      (fun _ ↦ (1 : ZMod 2)) (fun _ ↦ 0) ι
      (0 : DifferentialPolynomial (ZMod 2)[X] 0) 1 1 ∅ hgood
  have hex : exceptional = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
  have hroot : differentialSpecialization (challengeSpecialization
      (0 : DifferentialPolynomial (ZMod 2)[X] 0) 1) (C 1) = 0 := by
    have hchallenge : challengeSpecialization
        (0 : DifferentialPolynomial (ZMod 2)[X] 0) 1 = 0 := by
      simp [challengeSpecialization]
    rw [hchallenge, differentialSpecialization]
    exact map_zero _
  apply hdescend 1 (by simp [hex]) (C 1) (by simp)
  · simp [pointDomain, polynomialAgreementSet]
  · exact hroot

end

private theorem singletonLineExactBound : LineExactAgreementBound pointDomain 1 1 0 := by
  intro f g
  refine ⟨∅, by simp, fun z _ P hP hclose ↦ ?_⟩
  have hagree :
      polynomialAgreementSet pointDomain (fun i ↦ f i + z * g i) P = Finset.univ :=
    Finset.eq_univ_of_card _
      (le_antisymm (Finset.card_le_univ _) (by simpa [Fintype.card_fin] using hclose))
  have heval := (mem_polynomialAgreementSet ..).mp
    (hagree ▸ Finset.mem_univ (0 : Fin 1))
  have hcoeff : P.coeff 0 = f 0 + z * g 0 := by
    have hpoint : pointDomain 0 = 0 := rfl
    rw [hpoint] at heval
    exact (coeff_zero_eq_eval_zero P).trans heval
  have hPconst : P = C (f 0 + z * g 0) := by
    rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hP), hcoeff]
  refine ⟨C (f 0), C (g 0), (degree_C_le).trans_lt (by norm_num),
    (degree_C_le).trans_lt (by norm_num), ?_, ?_⟩
  · calc
      P = C (f 0 + z * g 0) := hPconst
      _ = C (f 0) + C z * C (g 0) := by simp
  · rw [hagree]
    ext i
    fin_cases i
    simp [commonPolynomialAgreementSet, pointDomain]

private def affineValues : Fin 2 → Fin 1 → ZMod 2 := ![fun _ ↦ 1, fun _ ↦ 0]

example := exists_affine_exceptionalSet_full_agreement_of_exactLine pointDomain 0
  singletonLineExactBound 0 (by norm_num [pointDomain]) (by norm_num) affineValues

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

/-- The graph-line recognizer accepts the computed candidate `1 + 2X` at challenge `1`. -/
example : ∃ F₀ G₀ : ℚ[X], F₀.degree < 2 ∧ G₀.degree < 2 ∧
    (∀ i ∈ (Finset.univ : Finset (Fin 2)),
      F₀.eval (fullDomain i) = ![1, 2] i ∧ G₀.eval (fullDomain i) = ![0, 1] i) ∧
    Polynomial.eval (fullDomain 0) (C 1 + C 2 * X : ℚ[X]) = ![1, 2] 0 + 1 * ![0, 1] 0 ∧
    Polynomial.eval (fullDomain 1) (C 1 + C 2 * X : ℚ[X]) = ![1, 2] 1 + 1 * ![0, 1] 1 ∧
    C 1 + C 2 * X = F₀ + C 1 * G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, hsample, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample fullDomain ![1, 2] ![0, 1] univ
      (card_univ.trans rfl)
  have hP : (C 1 + C 2 * X : ℚ[X]).degree < 2 := by compute_degree!
  have heval : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      Polynomial.eval (fullDomain i) (C 1 + C 2 * X : ℚ[X]) = ![1, 2] i + 1 * ![0, 1] i := by
    intro i hi
    fin_cases i
    · norm_num [fullDomain]
      change (0 : ℚ) = 0
      rfl
    · norm_num [fullDomain]
      change 1 + 2 * (1 : ℚ) = 3
      norm_num
  exact ⟨F₀, G₀, hF₀, hG₀, hsample, heval 0 (by simp), heval 1 (by simp),
    by simpa using hrecognize (RingHom.id ℚ) 1 (C 1 + C 2 * X) hP heval⟩

/-- The exceptional bound is attained when the graph agrees at only one coordinate. -/
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 1 ∧ 0 ∈ exceptional := by
  obtain ⟨exceptional, hcard, hagreement⟩ :=
    exists_exceptional_graphLine_challenges fullDomain ![0, 0] ![0, 1]
      (0 : ℚ[X]) 0 (RingHom.id ℚ)
  have hcommon : commonPolynomialAgreementSet fullDomain ![0, 0] ![0, 1] 0 0 = {0} := by
    ext i
    fin_cases i <;> simp [commonPolynomialAgreementSet, fullDomain]
  have hcard' : exceptional.card ≤ 1 := by
    simpa [hcommon, Fintype.card_fin] using hcard
  have hzero : 0 ∈ exceptional := by
    by_contra hz
    have hset := hagreement 0 hz
    have hleft : polynomialAgreementSet fullDomain (fun _ : Fin 2 ↦ 0) (0 : ℚ[X]) = univ := by
      ext i
      simp [polynomialAgreementSet]
    have hzero : (fun i : Fin 2 ↦ ![0, 0] i) = fun _ ↦ (0 : ℚ) := by
      funext i
      fin_cases i <;> norm_num
    have hset'' : polynomialAgreementSet fullDomain (fun i : Fin 2 ↦ ![0, 0] i)
        (0 : ℚ[X]) = commonPolynomialAgreementSet fullDomain ![0, 0] ![0, 1] 0 0 := by
      simpa using hset
    have hset' : polynomialAgreementSet fullDomain (fun _ : Fin 2 ↦ 0) (0 : ℚ[X]) =
        commonPolynomialAgreementSet fullDomain ![0, 0] ![0, 1] 0 0 := by
      rw [← hzero]
      exact hset''
    rw [hleft, hcommon] at hset'
    have hone : (1 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ _
    rw [hset'] at hone
    simp at hone
  exact ⟨exceptional, hcard', hzero⟩

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
