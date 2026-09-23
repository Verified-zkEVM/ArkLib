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
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for Reed–Solomon mutual correlated agreement -/

open Polynomial Finset ReedSolomon ReedSolomon.FirstOrder.Squarefree PolynomialDifferential

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2
private def pointDomain : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩
private noncomputable def agreementEquation : DifferentialPolynomial (ZMod 2)[X] 0 :=
  MvPolynomial.X (some 0) - MvPolynomial.C (Polynomial.X)

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

example : agreementEquation ≠ 0 ∧
    ∃ exceptional : Finset (ZMod 2), exceptional.card ≤ 0 ∧
      HasExactCorrelatedPair pointDomain (fun _ ↦ (0 : ZMod 2)) (fun _ ↦ 1)
        (RingHom.id (ZMod 2)) 2 1 (C 1) ∧
      differentialSpecialization
        (challengeSpecialization
          (MvPolynomial.map (Polynomial.mapRingHom (algebraMap (ZMod 2) E₄)) agreementEquation)
          (algebraMap (ZMod 2) E₄ 1)) (C (algebraMap (ZMod 2) E₄ 1)) = 0 ∧
      polynomialAgreementSet
        (pointDomain.trans ⟨algebraMap (ZMod 2) E₄,
          (algebraMap (ZMod 2) E₄).injective⟩)
        (fun _ ↦ algebraMap (ZMod 2) E₄ 0 + algebraMap (ZMod 2) E₄ 1 *
          algebraMap (ZMod 2) E₄ 1)
        (C (algebraMap (ZMod 2) E₄ 1)) = Finset.univ := by
  let ι : ZMod 2 →+* E₄ := algebraMap (ZMod 2) E₄
  have hnonzero : agreementEquation ≠ 0 := by
    intro heq
    have hcoeff := congrArg
      (fun q : DifferentialPolynomial (ZMod 2)[X] 0 =>
        q.coeff (Finsupp.single (some (0 : Fin 1)) 1)) heq
    have hindex : (0 : JetVariable 0 →₀ ℕ) ≠ Finsupp.single (some (0 : Fin 1)) 1 := by
      intro h
      have hvalue := congrArg (fun f : JetVariable 0 →₀ ℕ => f (some (0 : Fin 1))) h
      simp at hvalue
    norm_num [agreementEquation, hindex] at hcoeff
  have hgood : ∀ z ∉ (∅ : Finset E₄), ∀ P : E₄[X], P.degree < 2 →
      1 ≤ (polynomialAgreementSet (pointDomain.trans ⟨ι, ι.injective⟩)
        (fun i ↦ ι ((fun _ : Fin 1 ↦ (0 : ZMod 2)) i) +
          z * ι ((fun _ : Fin 1 ↦ (1 : ZMod 2)) i)) P).card →
      differentialSpecialization
        (challengeSpecialization
          (MvPolynomial.map (Polynomial.mapRingHom ι)
            agreementEquation) z) P = 0 →
      HasExactCorrelatedPair pointDomain (fun _ ↦ (0 : ZMod 2)) (fun _ ↦ 1) ι 2 z P := by
    intro z _ P hP hagree hroot
    have hpoly : P - C z = 0 := by
      simpa [agreementEquation, challengeSpecialization, differentialSpecialization,
        differentialSpecializationHom] using hroot
    have hPconst : P = C z := sub_eq_zero.mp hpoly
    subst P
    have hfull : polynomialAgreementSet (pointDomain.trans ⟨ι, ι.injective⟩)
        (fun i ↦ ι ((fun _ : Fin 1 ↦ (0 : ZMod 2)) i) +
          z * ι ((fun _ : Fin 1 ↦ (1 : ZMod 2)) i)) (C z) = Finset.univ :=
      Finset.eq_univ_of_card _
        (le_antisymm (Finset.card_le_univ _) (by simpa [Fintype.card_fin] using hagree))
    refine ⟨(0, 1), (by simpa using
      (show (⊥ : WithBot ℕ) < (2 : WithBot ℕ) by decide)), by norm_num, ?_, ?_⟩
    · simp [correlatedPairSpecialization]
    · rw [hfull]
      ext i
      fin_cases i
      simp [commonPolynomialAgreementSet, pointDomain]
  obtain ⟨exceptional, hcard, hdescend⟩ :=
    exists_exceptional_equation_correlatedAgreement_descend pointDomain
      (fun _ ↦ (0 : ZMod 2)) (fun _ ↦ 1) ι
      agreementEquation 2 1 ∅ hgood
  have hex : exceptional = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
  have hroot : differentialSpecialization (challengeSpecialization
      agreementEquation 1) (C 1) = 0 := by
    simp [agreementEquation, challengeSpecialization, differentialSpecialization,
      differentialSpecializationHom]
  have hpair := hdescend 1 (by simp [hex]) (C 1) (by simp) (by
    simp [pointDomain, polynomialAgreementSet]) hroot
  have hmappedRoot : differentialSpecialization
      (challengeSpecialization (MvPolynomial.map (Polynomial.mapRingHom ι) agreementEquation) (ι 1))
      (C (ι 1)) = 0 := by
    simp [agreementEquation, challengeSpecialization, differentialSpecialization,
      differentialSpecializationHom]
  have hmappedAgreement : polynomialAgreementSet
      (pointDomain.trans ⟨ι, ι.injective⟩)
      (fun _ ↦ ι 0 + ι 1 * ι 1) (C (ι 1)) = Finset.univ := by
    ext i
    fin_cases i
    simp [polynomialAgreementSet, pointDomain]
  exact ⟨hnonzero, exceptional, hcard, hpair, hmappedRoot, hmappedAgreement⟩

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

private theorem affineCandidateEvaluation (i : Fin 2) :
    Polynomial.eval (fullDomain i) (C 1 + C 2 * X : ℚ[X]) =
      ![1, 2] i + 1 * ![0, 1] i := by
  fin_cases i
  · norm_num [fullDomain]
    change (0 : ℚ) = 0
    rfl
  · norm_num [fullDomain]
    change 1 + 2 * (1 : ℚ) = 3
    norm_num

/-- At challenge `1`, the candidate `1 + 2X` is explained by one pair on both coordinates. -/
example : ∃ F₀ G₀ : ℚ[X], C 1 + C 2 * X = F₀ + C 1 * G₀ ∧
    commonPolynomialAgreementSet fullDomain ![1, 2] ![0, 1] F₀ G₀ = univ := by
  obtain ⟨F₀, G₀, -, -, hpair⟩ :=
    exists_exactPair_fullDimension fullDomain ![1, 2] ![0, 1]
  have hagree : polynomialAgreementSet fullDomain (fun i ↦ ![1, 2] i + 1 * ![0, 1] i)
      (C 1 + C 2 * X) = univ := by
    ext i
    simpa only [mem_polynomialAgreementSet, Finset.mem_univ, iff_true] using
      affineCandidateEvaluation i
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
    exact affineCandidateEvaluation i
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

namespace ReedSolomon.PowerBatchedPointRecognitionTest

noncomputable section

private abbrev E₉ := FiniteField.Extension (ZMod 3) 3 2

/-- The one-point evaluation domain at zero over `ZMod 3`. -/
private def domain : Fin 1 ↪ ZMod 3 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- The two-point evaluation domain in `ZMod 3`. -/
private def exceptionalDomain : Fin 2 ↪ ZMod 3 :=
  ⟨fun i ↦ (i.val : ZMod 3), by
    intro i j hij
    fin_cases i
    · fin_cases j
      · rfl
      · norm_num at hij
    · fin_cases j
      · norm_num at hij
      · rfl⟩

/-- The tuple agrees at zero, while its second word component creates one bad challenge. -/
private def exceptionalWords : Fin 2 → Fin 2 → ZMod 3 :=
  fun t i ↦ if t = 0 then 0 else if i = 0 then 0 else 1

/-- The zero polynomial tuple matching `exceptionalWords` at zero. -/
private def exceptionalPolynomials : Fin 2 → Polynomial (ZMod 3) :=
  fun _ ↦ 0

/-- Nonzero second word component with a zero batched value at challenge `1`. -/
private def recognitionWords : Fin 2 → Fin 1 → ZMod 3 :=
  fun t _ ↦ if t = 0 then 2 else 1

/-- The differential equation whose regular chart reconstructs the zero polynomial. -/
private def recognitionChart : DifferentialPolynomial (Polynomial (ZMod 3)) 0 :=
  MvPolynomial.X (some (0 : Fin 1))

/-- The chart specialized at the recognition challenge `1`. -/
private def recognitionChartAt : DifferentialPolynomial (ZMod 3) 0 :=
  MvPolynomial.map (Polynomial.evalRingHom (1 : ZMod 3)) recognitionChart

/-- The recognition jet used at the regular chart point. -/
private def recognitionJet : Fin 1 → ZMod 3 := fun _ ↦ 0

/-- The common agreement set computed with the classical equality decision. -/
private def classicalAgreementSet (domain : Fin 2 ↪ ZMod 3) (w : Fin 2 → Fin 2 → ZMod 3)
    (P : Fin 2 → Polynomial (ZMod 3)) : Finset (Fin 2) :=
  @commonCurveAgreementSet (ZMod 3) (Fin 2) _ 1 (Classical.decEq _) _ domain w P

/-- The common agreement set after extension to `E₉`. -/
private def extensionCommonAgreementSet (domain : Fin 2 ↪ E₉)
    (w : Fin 2 → Fin 2 → E₉) (P : Fin 2 → Polynomial E₉) : Finset (Fin 2) :=
  @commonCurveAgreementSet E₉ (Fin 2) _ 1 (Classical.decEq _) _ domain w P

/-- The polynomial agreement set after extension to `E₉`. -/
private def extensionPolynomialAgreementSet (domain : Fin 2 ↪ E₉)
    (w : Fin 2 → E₉) (P : Polynomial E₉) : Finset (Fin 2) :=
  @polynomialAgreementSet E₉ _ (Classical.decEq _) (Fin 2) _ domain w P

/-- A two-component tuple has one exceptional challenge; scalar extension preserves its concrete
common agreement set. -/
example :
    ∃ exceptional : Finset E₉, exceptional.card ≤ 1 ∧
      (∀ z ∉ exceptional,
        extensionPolynomialAgreementSet
          (exceptionalDomain.trans ⟨algebraMap (ZMod 3) E₉,
            (algebraMap (ZMod 3) E₉).injective⟩)
          (powerBatchedWord (fun t i ↦ algebraMap (ZMod 3) E₉ (exceptionalWords t i)) z)
          (powerBatchedPolynomial
            (fun t ↦ (exceptionalPolynomials t).map (algebraMap (ZMod 3) E₉)) z) =
        classicalAgreementSet exceptionalDomain exceptionalWords exceptionalPolynomials) ∧
      classicalAgreementSet exceptionalDomain exceptionalWords exceptionalPolynomials =
        ({0} : Finset (Fin 2)) ∧
      extensionCommonAgreementSet
          (exceptionalDomain.trans ⟨algebraMap (ZMod 3) E₉,
            (algebraMap (ZMod 3) E₉).injective⟩)
          (fun t i ↦ algebraMap (ZMod 3) E₉ (exceptionalWords t i))
          (fun t ↦ (exceptionalPolynomials t).map (algebraMap (ZMod 3) E₉)) =
        classicalAgreementSet exceptionalDomain exceptionalWords exceptionalPolynomials := by
  have hbase : classicalAgreementSet exceptionalDomain exceptionalWords
      exceptionalPolynomials = ({0} : Finset (Fin 2)) := by
    ext i
    fin_cases i
    · simp only [classicalAgreementSet, commonCurveAgreementSet, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro _
        trivial
      · intro _ t
        fin_cases t <;> simp [exceptionalWords, exceptionalPolynomials, exceptionalDomain]
    · simp only [classicalAgreementSet, commonCurveAgreementSet, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        have hbad := h 1
        norm_num [exceptionalWords, exceptionalPolynomials, exceptionalDomain] at hbad
      · intro h
        have : False := (by decide : (1 : Fin 2) ≠ 0) h
        exact False.elim this
  have hcommon : 1 ≤ (classicalAgreementSet exceptionalDomain exceptionalWords
      exceptionalPolynomials).card := by
    rw [hbase]
    simp
  let ι : ZMod 3 →+* E₉ := algebraMap (ZMod 3) E₉
  obtain ⟨exceptional, hbound, hgood⟩ :=
    exists_exceptional_powerBatched_extension exceptionalDomain exceptionalWords
      exceptionalPolynomials ι 1 hcommon
  have hbound' : exceptional.card ≤ 1 := by
    simpa using hbound
  refine ⟨exceptional, hbound', ?_, hbase, ?_⟩
  · intro z hz
    exact hgood z hz
  · exact commonCurveAgreementSet_map exceptionalDomain exceptionalWords exceptionalPolynomials
      ι

/-- Batching `X^2` with twice `X + 1` at `z = 2` has initial jet `(5, 4)` at `1` in `ℚ`.
-/
example :
    polynomialJet (d := 1) (1 : ℚ)
      (powerBatchedPolynomial (fun i : Fin 2 ↦
        if i = 0 then (Polynomial.X ^ 2 : Polynomial ℚ) else Polynomial.X + 1) 2) =
      ![5, 4] := by
  rw [polynomialJet_powerBatched]
  ext j
  fin_cases j <;> norm_num [powerBatchedJetGraph, powerBatchedCoordinate_eval,
    powerBatchedCoordinate, polynomialJet, Polynomial.hasseJet, Fin.sum_univ_succ]

/-- A sample with a nonzero second component and a nontrivial high cut yields all three
recognition conclusions at the regular chart point. -/
example :
    ∃ P : Fin 2 → Polynomial (ZMod 3),
      (∀ t, (P t).degree < 1) ∧
      (∀ i ∈ ({0} : Finset (Fin 1)), ∀ t,
        (P t).eval (domain i) = recognitionWords t i) ∧
      rationalTaylorPolynomial (0 : ZMod 3) recognitionChartAt 2 recognitionJet =
        powerBatchedPolynomial (fun t ↦ (P t).map (RingHom.id _)) 1 ∧
      (recognitionJet = fun j ↦ Polynomial.eval 1
        (powerBatchedJetGraph (r := 0) (0 : ZMod 3)
          (fun t ↦ (P t).map (RingHom.id _)) j)) ∧
      ∀ l : Fin 2,
        MvPolynomial.aeval recognitionJet
          (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 l.val) =
        MvPolynomial.aeval recognitionJet
            (initialJetSeparant (0 : ZMod 3) recognitionChartAt) ^ 4 *
          (Polynomial.taylor 0
            (powerBatchedPolynomial (fun t ↦ (P t).map (RingHom.id _)) 1)).coeff l.val := by
  obtain ⟨P, hP, hs, hrecognize⟩ :=
    exists_polynomialGraph_of_symbolic_sample_of_exponent (k := 1) (K := 2) (r := 0)
      domain recognitionWords {0} (by simp) (RingHom.id _) 0 recognitionChart (by omega) 4
      (taylorExponentSufficient_two_mul 0 2)
  have hS : MvPolynomial.aeval recognitionJet
      (initialJetSeparant (0 : ZMod 3) recognitionChartAt) ≠ 0 := by
    simp [recognitionChartAt, recognitionChart, initialJetSeparant, separant]
  have hsolution :
      differentialSpecialization recognitionChartAt (0 : Polynomial (ZMod 3)) = 0 := by
    simp [recognitionChartAt, recognitionChart, differentialSpecialization,
      differentialSpecializationHom]
  have hseparant : jetEvaluation (separant recognitionChartAt (Fin.last 0)) 0
      (polynomialJet 0 (0 : Polynomial (ZMod 3))) ≠ 0 := by
    simp [recognitionChartAt, recognitionChart, separant, jetEvaluation, polynomialJet,
      Polynomial.hasseJet]
  have hhigh : ∀ l : Fin 2, 1 ≤ l.val →
      MvPolynomial.aeval recognitionJet
        (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 l.val) = 0 := by
    intro l hl
    fin_cases l
    · simp at hl
    · have hcoeff := aeval_commonTaylorNumerator_polynomialJet (0 : ZMod 3)
        recognitionChartAt (0 : Polynomial (ZMod 3)) hsolution hseparant
        (τ := 4) (l := 1) (by norm_num) (by
          intro i hir hi
          have : i = 1 := by omega
          subst i
          norm_num)
      have hjetZero : recognitionJet = polynomialJet 0 (0 : Polynomial (ZMod 3)) := by
        funext j
        fin_cases j
        simp [recognitionJet, polynomialJet, Polynomial.hasseJet]
      have hcoeffZero : MvPolynomial.aeval (fun _ : Fin 1 ↦ (0 : ZMod 3))
          (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 1) = 0 := by
        change MvPolynomial.aeval recognitionJet
          (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 1) = 0
        rw [hjetZero, hcoeff]
        simp [polynomialJet, Polynomial.hasseJet]
      change MvPolynomial.aeval (fun _ : Fin 1 ↦ (0 : ZMod 3))
        (commonTaylorNumerator (0 : ZMod 3) recognitionChartAt 4 1) = 0
      exact hcoeffZero
  have hcuts : ∀ i ∈ ({0} : Finset (Fin 1)),
      MvPolynomial.aeval recognitionJet
        (taylorAgreementEquation (0 : ZMod 3) recognitionChartAt 2 4
          (RingHom.id _ (domain i))
          (Polynomial.eval 1
            (powerBatchedCoordinate (fun t : Fin 2 ↦ RingHom.id _ (recognitionWords t i))))) =
        0 := by
    intro i hi
    fin_cases i
    apply (taylorAgreementEquation_eq_zero_iff (0 : ZMod 3) recognitionChartAt
      (taylorExponentSufficient_two_mul 0 2) recognitionJet hS
      (RingHom.id _ (domain 0))
      (Polynomial.eval 1
          (powerBatchedCoordinate (fun t : Fin 2 ↦ RingHom.id _ (recognitionWords t 0))))).2
    have hc0 : rationalTaylorCoefficient (0 : ZMod 3) recognitionChartAt
        recognitionJet 0 = recognitionJet 0 := by
      simpa using rationalTaylorCoefficient_initial (0 : ZMod 3) recognitionChartAt
        recognitionJet ⟨0, by omega⟩
    have hy : Polynomial.eval 1
        (powerBatchedCoordinate (fun t : Fin 2 ↦ RingHom.id _ (recognitionWords t 0))) = 0 := by
      rw [powerBatchedCoordinate_eval]
      norm_num [recognitionWords, Fin.sum_univ_succ]
      exact ZMod.natCast_self 3
    have hx : RingHom.id (ZMod 3) (domain (0 : Fin 1)) = 0 := by
      rfl
    calc
      (rationalTaylorPolynomial (0 : ZMod 3) recognitionChartAt 2 recognitionJet).eval
          (RingHom.id _ (domain 0)) = 0 := by
        rw [eval_rationalTaylorPolynomial]
        simp [hc0, recognitionJet, Fin.sum_univ_succ, hx]
      _ = Polynomial.eval 1
          (powerBatchedCoordinate (fun t : Fin 2 ↦ RingHom.id _ (recognitionWords t 0))) :=
        hy.symm
  obtain ⟨hpoly, hjet, hcoeff⟩ := hrecognize 1 recognitionJet hS hhigh hcuts
  exact ⟨P, hP, hs, hpoly, hjet, hcoeff⟩

end

end ReedSolomon.PowerBatchedPointRecognitionTest
