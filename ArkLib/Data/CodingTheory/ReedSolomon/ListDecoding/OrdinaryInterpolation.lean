/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness
import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness
import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Fast
import CompPoly.Univariate.BatchEval.Context
import CompPoly.Univariate.ToPoly
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ExactOutput
/-!
# Executable ordinary Reed--Solomon interpolation

This module instantiates Lee--O'Sullivan interpolation over an arbitrary field with direct
vanishing polynomials, Horner batch evaluation, and the verified fast Mulders--Storjohann row
reducer. Its correctness contract is functional: a successful run returns a valid multiplicity
interpolant, and dimension slack plus distinct evaluation points makes the run succeed.

The final theorem connects the interpolation inequality to `Code.agree`. It claims no specific
bit or quasi-linear running time for the generic backend.
-/

namespace ReedSolomon.ListDecoding.OrdinaryInterpolation

open CompPoly CompPoly.GuruswamiSudan

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- Pack a received Reed--Solomon word into the point format used by CompPoly. -/
def receivedPoints {n : ℕ} (domain : Fin n → F) (received : Fin n → F) :
    Array (F × F) :=
  Array.ofFn (fun i => (domain i, received i))

/-- Canonical concrete representation of a mathematical univariate polynomial. -/
def concretePolynomial (P : Polynomial F) : CPolynomial F :=
  ⟨P.toImpl, CPolynomial.Raw.isCanonical_toImpl P⟩

/-- Generic-field Lee--O'Sullivan interpolation with actual verified component backends. -/
def interpolationContext : GSInterpContext F :=
  LeeOSullivan.leeOSullivanInterpContext
    (CPolynomial.VanishingPolynomialContext.direct (F := F))
    (CPolynomial.BatchEvalContext.horner F)
    (PolynomialMatrix.muldersStorjohannFastReducerContext F)

/-- Execute the ordinary multiplicity interpolation stage at supplied GS parameters. -/
def run (points : Array (F × F)) (params : GSInterpParams) : Option (CBivariate F) :=
  interpolationContext.interpolate points params

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
@[simp]
theorem concretePolynomial_toPoly (P : Polynomial F) :
    (concretePolynomial P).toPoly = P := by
  exact CPolynomial.toPoly_mk_toImpl P

omit [DecidableEq F] in
@[simp]
theorem concretePolynomial_eval (P : Polynomial F) (x : F) :
    CPolynomial.eval x (concretePolynomial P) = P.eval x := by
  rw [CPolynomial.eval_toPoly, concretePolynomial_toPoly]

omit [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem receivedPoints_distinct {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) :
    DistinctXCoordinates (receivedPoints domain received) := by
  unfold DistinctXCoordinates receivedPoints
  rw [Array.toList_ofFn, List.map_ofFn]
  exact List.nodup_ofFn.mpr domain.injective

omit [LawfulBEq F] [DecidableEq F] in
private theorem matchingPointCount_eq_countP (points : Array (F × F))
    (p : CPolynomial F) :
    matchingPointCount points p =
      points.toList.countP (fun point => CPolynomial.eval point.1 p == point.2) := by
  unfold matchingPointCount
  rw [← Array.foldl_toList]
  let pred : F × F → Bool := fun point => CPolynomial.eval point.1 p == point.2
  let step : Nat → F × F → Nat :=
    fun count point => if pred point then count + 1 else count
  have hfold : ∀ (xs : List (F × F)) acc,
      xs.foldl step acc = acc + xs.countP pred := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons point tail ih =>
        intro acc
        rw [List.foldl_cons, ih]
        cases hpred : pred point <;> simp [step, hpred, Nat.add_assoc, Nat.add_comm]
  simpa only [pred, step, Nat.zero_add] using hfold points.toList 0

theorem matchingPointCount_receivedPoints {n : ℕ} (domain : Fin n ↪ F)
    (received : Fin n → F) (P : Polynomial F) :
    matchingPointCount (receivedPoints domain received) (concretePolynomial P) =
      Code.agree (evalOnPoints domain P) received := by
  rw [matchingPointCount_eq_countP, receivedPoints, Array.toList_ofFn]
  rw [List.ofFn_comp' (fun i : Fin n => i)
    (fun i => (domain i, received i)), List.countP_map]
  have hnodup : (List.ofFn (fun i : Fin n => i)).Nodup :=
    List.nodup_ofFn.mpr Function.injective_id
  have hcount := hnodup.card_eq_countP
    (P := fun i : Fin n => P.eval (domain i) = received i)
  have htoFinset : (List.ofFn (fun i : Fin n => i)).toFinset = Finset.univ := by
    ext i
    simp
  have hpred :
      ((fun point : F × F => CPolynomial.eval point.1 (concretePolynomial P) == point.2) ∘
        fun i : Fin n => (domain i, received i)) =
      (fun i => decide (P.eval (domain i) = received i)) := by
    funext i
    simp only [Function.comp_apply, concretePolynomial_eval, beq_eq_decide]
  rw [hpred, ← hcount, htoFinset]
  rfl

/-- A successful interpolation run returns the exact semantic GS witness. -/
theorem run_sound {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (hrun : run points params = some Q) :
    ValidInterpolationWitness points params Q :=
  interpolationContext.sound points params Q hrun

/-- Dimension slack and distinct inputs make the actual Lee--O'Sullivan run succeed. -/
theorem run_exists_of_dimension_slack {points : Array (F × F)}
    {params : GSInterpParams} (hdistinct : DistinctXCoordinates points)
    (hslack : HasInterpolationDimensionSlack points params) :
    ∃ Q, run points params = some Q := by
  obtain ⟨witness, hwitness⟩ :=
    denseInterpolate_exists_of_dimension_slack points params hslack
  apply interpolationContext.complete points params hdistinct
  exact ⟨witness, denseInterpolate_sound hwitness⟩

/-- Every sufficiently agreeing degree-bounded message roots the computed interpolant. -/
theorem run_solution_of_agreement {n k A : ℕ} (domain : Fin n ↪ F)
    (received : Fin n → F) (params : GSInterpParams)
    (hdegreeParam : params.messageDegree = k)
    (hbound : params.weightedDegreeBound < params.multiplicity * A)
    {Q : CBivariate F}
    (hrun : run (receivedPoints domain received) params = some Q)
    (P : Polynomial F) (hdegree : P.degree < k)
    (hagreement : A ≤ Code.agree (evalOnPoints domain P) received) :
    CBivariate.composeY Q (concretePolynomial P) = 0 := by
  apply composeY_eq_zero_of_enough_matching_multiplicity_points (run_sound hrun)
  · unfold degreeLt
    rw [CPolynomial.degree_toPoly, concretePolynomial_toPoly, hdegreeParam]
    exact hdegree
  · exact receivedPoints_distinct domain received
  · rw [matchingPointCount_receivedPoints]
    exact hbound.trans_le (Nat.mul_le_mul_left params.multiplicity hagreement)

end ReedSolomon.ListDecoding.OrdinaryInterpolation
