/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness
public import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness
public import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Fast
public import CompPoly.Univariate.BatchEval.Context
public import CompPoly.Univariate.ToPoly
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ExactOutput
public import ArkLib.ToCompPoly.Bivariate.CMv
public import ArkLib.ToCompPoly.Bivariate.Content

/-!
# Executable ordinary Reed--Solomon interpolation

This module instantiates Lee--O'Sullivan interpolation over an arbitrary field. The interpolation
polynomial `Q(X,Y)` vanishes to the requested multiplicity at every received point and has bounded
`(1,k-1)`-weighted degree. Direct vanishing polynomials, Horner batch evaluation, and the verified
fast Mulders--Storjohann row reducer supply the concrete operations. A successful run returns a
valid multiplicity interpolant, and dimension slack plus distinct evaluation points makes the run
succeed.

The final theorem connects the interpolation inequality to `Code.agree`. It claims no specific
bit or quasi-linear running time for the generic backend.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.OrdinaryInterpolation

open CompPoly CompPoly.GuruswamiSudan

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- Pair each distinct evaluation point with its received symbol. The embedding carried by
`domain` later discharges the interpolation algorithm's distinct-X-coordinate premise. -/
def receivedPoints {n : ℕ} (domain : Fin n → F) (received : Fin n → F) :
    Array (F × F) :=
  Array.ofFn (fun i => (domain i, received i))

/-- Canonical concrete representation of a mathematical message polynomial. This is the boundary
between the specification's `Polynomial` and CompPoly's executable coefficient array. -/
def concretePolynomial (P : Polynomial F) : CPolynomial F :=
  ⟨P.toImpl, CPolynomial.Raw.isCanonical_toImpl P⟩

/-- Generic-field Lee--O'Sullivan interpolation with verified component backends. The direct
vanishing polynomial builds the interpolation module, Horner evaluation supplies point values,
and Mulders--Storjohann selects a row of sufficiently small weighted degree. -/
def interpolationContext : GSInterpContext F :=
  LeeOSullivan.leeOSullivanInterpContext
    (CPolynomial.VanishingPolynomialContext.direct (F := F))
    (CPolynomial.BatchEvalContext.horner F)
    (PolynomialMatrix.muldersStorjohannFastReducerContext F)

/-- Execute multiplicity interpolation at the caller's GS parameters. These parameters record the
message-degree cutoff `k`, multiplicity `m`, and weighted-degree bound `W`. -/
def run (points : Array (F × F)) (params : GSInterpParams) : Option (CBivariate F) :=
  interpolationContext.interpolate points params

/-- Remove the common F[X] factor from all Y-coefficients, then materialize in order `[X,Y]`.
Content removal preserves every polynomial root Q(X,P(X))=0 and prevents an X-only factor from
making every branch singular at its roots. Squarefree normalization over F(X) is a later stage. -/
def runCMv (points : Array (F × F)) (params : GSInterpParams) :
    Option (CPoly.CMvPolynomial 2 F) :=
  (run points params).map fun Q => CBivariate.toOrdinaryCMv (CBivariate.primitivePartY Q)

theorem runCMv_eq_some_iff {points : Array (F × F)} {params : GSInterpParams}
    {Q : CPoly.CMvPolynomial 2 F} :
    runCMv points params = some Q ↔
      ∃ Qb, run points params = some Qb ∧
        CBivariate.toOrdinaryCMv (CBivariate.primitivePartY Qb) = Q := by
  rw [runCMv, Option.map_eq_some_iff]

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
  -- CompPoly implements the count as an array fold; expose it as `List.countP` so it can be
  -- identified with the finite-set agreement statistic used by the decoder specification.
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
  -- With every position listed once, counting a true equality is the cardinality of the same
  -- predicate on `Finset.univ`, which is exactly `Code.agree`.
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

/-- Dimension slack and distinct inputs make the actual Lee--O'Sullivan run succeed. The slack
inequality says that the allowed weighted-degree monomials outnumber all multiplicity constraints;
the dense existence theorem supplies a witness, and backend completeness makes the executable
module reducer return one. -/
theorem run_exists_of_dimension_slack {points : Array (F × F)}
    {params : GSInterpParams} (hdistinct : DistinctXCoordinates points)
    (hslack : HasInterpolationDimensionSlack points params) :
    ∃ Q, run points params = some Q := by
  obtain ⟨witness, hwitness⟩ :=
    denseInterpolate_exists_of_dimension_slack points params hslack
  apply interpolationContext.complete points params hdistinct
  exact ⟨witness, denseInterpolate_sound hwitness⟩

/-- Dimension slack also makes the materialized CMv interpolation run succeed. -/
theorem runCMv_exists_of_dimension_slack {points : Array (F × F)}
    {params : GSInterpParams} (hdistinct : DistinctXCoordinates points)
    (hslack : HasInterpolationDimensionSlack points params) :
    ∃ Q, runCMv points params = some Q := by
  obtain ⟨Q, hQ⟩ := run_exists_of_dimension_slack hdistinct hslack
  exact ⟨CBivariate.toOrdinaryCMv (CBivariate.primitivePartY Q),
    Option.map_eq_some_iff.mpr ⟨Q, hQ, rfl⟩⟩

/-- Every sufficiently agreeing degree-bounded message roots the computed interpolant. In the
paper's notation, `hbound` is `W < m A`: agreement at `A` positions gives at least `m A` roots of
`Q(X,P(X))`, while its degree is at most `W`, forcing the composition to vanish identically. -/
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
  -- The three inputs to the multiplicity root argument are the message degree, distinct domain,
  -- and the conversion from agreement count to total matching multiplicity.
  · unfold degreeLt
    rw [CPolynomial.degree_toPoly, concretePolynomial_toPoly, hdegreeParam]
    exact hdegree
  · exact receivedPoints_distinct domain received
  · rw [matchingPointCount_receivedPoints]
    exact hbound.trans_le (Nat.mul_le_mul_left params.multiplicity hagreement)

/-- The materialized interpolant satisfies the equation consumed by ordinary root finding. -/
theorem runCMv_solution_of_agreement {n k A : ℕ} (domain : Fin n ↪ F)
    (received : Fin n → F) (params : GSInterpParams)
    (hdegreeParam : params.messageDegree = k)
    (hbound : params.weightedDegreeBound < params.multiplicity * A)
    {Q : CPoly.CMvPolynomial 2 F}
    (hrun : runCMv (receivedPoints domain received) params = some Q)
    (P : Polynomial F) (hdegree : P.degree < k)
    (hagreement : A ≤ Code.agree (evalOnPoints domain P) received) :
    MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
        (CPoly.fromCMvPolynomial Q) = 0 := by
  obtain ⟨Qb, hrunQb, rfl⟩ := runCMv_eq_some_iff.mp hrun
  rw [CBivariate.eval₂_fromCMvPolynomial_toOrdinaryCMv]
  have hroot := run_solution_of_agreement domain received params hdegreeParam hbound hrunQb P
    hdegree hagreement
  -- The interpolation witness is nonzero, so dividing out its Y-content loses no message root.
  have hprimitive := (CBivariate.composeY_primitivePartY_eq_zero_iff
    (run_sound hrunQb).1 (concretePolynomial P)).mpr hroot
  have hrootPoly := congrArg CPolynomial.toPoly hprimitive
  simpa only [GuruswamiSudan.composeY_toPoly, concretePolynomial_toPoly,
    CPolynomial.toPoly_zero] using
    hrootPoly

end ReedSolomon.ListDecoding.OrdinaryInterpolation
