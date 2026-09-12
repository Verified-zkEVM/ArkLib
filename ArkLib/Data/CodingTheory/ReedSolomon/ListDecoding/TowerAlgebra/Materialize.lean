/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.GeometricSeparation
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.InverseElimination

/-!
# Materializing rational coefficients in a finite tower

After fiber preprocessing, chart coefficients are still represented as numerators over one common
denominator. This file computes its inverse by elimination in the finite tower algebra, then
reduces every numerator times that inverse into the canonical tower basis. The output is an
ordinary `TowerRepresentation`, so tower agreement recovery can consume it directly.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Replace the coefficient payload of a tower by canonically reduced products with one already
computed inverse.  This helper is deterministic and preserves the base and fiber verbatim. -/
def withMaterializedCoefficients (r : TowerRepresentation (F := F))
    (inverse : CPolynomial (CPolynomial F))
    (numerators : List (CPolynomial (CPolynomial F))) : TowerRepresentation (F := F) :=
  { r with
    coefficients := numerators.map fun numerator ↦
      TowerRepresentation.reduceElement r.modulus r.fiber (numerator * inverse) }

/-- Compute the common denominator inverse and materialize all message slots.  `none` is the
explicit failure result when the denominator is not a unit. The executed backend uses elimination
and verifies its result in the quotient; it never evaluates the Cramer reference determinants. -/
def materializeCoefficients? [DecidableEq F] (r : TowerRepresentation (F := F))
    (denominator : CPolynomial (CPolynomial F))
    (numerators : List (CPolynomial (CPolynomial F))) :
    Option (TowerRepresentation (F := F)) :=
  match inverseElimination? r.modulus r.fiber denominator with
  | none => none
  | some inverse => some (withMaterializedCoefficients r inverse numerators)

/-- Under the canonical hypotheses, the executed backend agrees with reference materialization. -/
theorem materializeCoefficients?_eq_reference [DecidableEq F]
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    (denominator : CPolynomial (CPolynomial F))
    (numerators : List (CPolynomial (CPolynomial F))) :
    materializeCoefficients? r denominator numerators =
      match inverseRepresentative? r.modulus r.fiber denominator with
      | none => none
      | some inverse => some (withMaterializedCoefficients r inverse numerators) := by
  unfold materializeCoefficients?
  rw [inverseElimination?_eq_inverseRepresentative? hr.1 hr.2.2.2.1 hr.2.2.2.2.1]

/-- A unit common denominator guarantees that coefficient materialization succeeds. -/
theorem materializeCoefficients?_exists_of_isTowerUnit [DecidableEq F]
    (r : TowerRepresentation (F := F)) {oldWidth : ℕ} (hr : r.WellFormed oldWidth)
    (denominator : CPolynomial (CPolynomial F))
    (numerators : List (CPolynomial (CPolynomial F)))
    (hunit : IsTowerUnit r.modulus r.fiber denominator) :
    ∃ out, materializeCoefficients? r denominator numerators = some out := by
  obtain ⟨inverse, hinverse⟩ := inverseElimination?_exists_of_isTowerUnit
    hr.1 hr.2.2.2.1 hr.2.2.2.2.1 hunit
  exact ⟨withMaterializedCoefficients r inverse numerators,
    by simp only [materializeCoefficients?, hinverse]⟩

/-- Materialization preserves exactly the supplied number of message slots. -/
@[simp] theorem withMaterializedCoefficients_length
    (r : TowerRepresentation (F := F)) (inverse : CPolynomial (CPolynomial F))
    (numerators : List (CPolynomial (CPolynomial F))) :
    (withMaterializedCoefficients r inverse numerators).coefficients.length =
      numerators.length := by
  simp [withMaterializedCoefficients]

/-- Every materialized coefficient is in the canonical rectangular tower slice. -/
theorem withMaterializedCoefficients_wellFormed
    (r : TowerRepresentation (F := F)) {oldWidth : ℕ} (hr : r.WellFormed oldWidth)
    (inverse : CPolynomial (CPolynomial F))
    (numerators : List (CPolynomial (CPolynomial F))) :
    (withMaterializedCoefficients r inverse numerators).WellFormed numerators.length := by
  rcases hr with ⟨hG, hGfree, hGpos, hh, hhpos, hbase, hfiber, _hwidth, _hcoefficients⟩
  refine ⟨hG, hGfree, hGpos, hh, hhpos, hbase, hfiber, ?_, ?_⟩
  · simp [withMaterializedCoefficients]
  · intro coefficient hcoefficient
    simp only [withMaterializedCoefficients, List.mem_map] at hcoefficient
    obtain ⟨numerator, _hnumerator, rfl⟩ := hcoefficient
    exact TowerRepresentation.elementReduced_reduceElement hG hh hhpos (numerator * inverse)

/-- A successful materialization is immediately a well-formed tower packet of the requested
width, suitable for the existing tower agreement-recovery consumer. -/
theorem materializeCoefficients?_wellFormed [DecidableEq F]
    (r : TowerRepresentation (F := F)) {oldWidth : ℕ} (hr : r.WellFormed oldWidth)
    (denominator : CPolynomial (CPolynomial F))
    (numerators : List (CPolynomial (CPolynomial F)))
    (out : TowerRepresentation (F := F))
    (hout : materializeCoefficients? r denominator numerators = some out) :
    out.WellFormed numerators.length := by
  rw [materializeCoefficients?_eq_reference r hr] at hout
  cases hinverse : inverseRepresentative? r.modulus r.fiber denominator with
  | none => simp [hinverse] at hout
  | some inverse =>
      simp only [hinverse, Option.some.injEq] at hout
      subst out
      exact withMaterializedCoefficients_wellFormed r hr inverse numerators

/-- Unit denominators produce a well-formed packet with exactly the requested width. -/
theorem materializeCoefficients?_exists_wellFormed [DecidableEq F]
    (r : TowerRepresentation (F := F)) {oldWidth : ℕ} (hr : r.WellFormed oldWidth)
    (denominator : CPolynomial (CPolynomial F))
    (numerators : List (CPolynomial (CPolynomial F)))
    (hunit : IsTowerUnit r.modulus r.fiber denominator) :
    ∃ out, materializeCoefficients? r denominator numerators = some out ∧
      out.WellFormed numerators.length := by
  obtain ⟨out, hout⟩ := materializeCoefficients?_exists_of_isTowerUnit r hr denominator
    numerators hunit
  exact ⟨out, hout, materializeCoefficients?_wellFormed r hr denominator numerators out hout⟩

theorem evalNested_mul
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (a b : CPolynomial (CPolynomial F)) :
    TowerRepresentation.evalNested (a * b) phi u v =
      TowerRepresentation.evalNested a phi u v * TowerRepresentation.evalNested b phi u v := by
  simp [TowerRepresentation.evalNested,
    FirstOrderNormDecoder.D5.specializeFiberCPolynomial, CPolynomial.toPoly_mul]

theorem evalNested_one
    {K : Type*} [Field K] (phi : F →+* K) (u v : K) :
    TowerRepresentation.evalNested (1 : CPolynomial (CPolynomial F)) phi u v = 1 := by
  simp [TowerRepresentation.evalNested,
    FirstOrderNormDecoder.D5.specializeFiberCPolynomial, CPolynomial.toPoly_one]

/-- Quotient unitness implies nonvanishing at every geometric point of a well-formed tower. -/
theorem isTowerUnit_nonvanishing
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    (denominator : CPolynomial (CPolynomial F))
    (hunit : IsTowerUnit r.modulus r.fiber denominator)
    {K : Type*} [Field K] (phi : F →+* K) (u v : K) (hpoint : r.Point phi u v) :
    TowerRepresentation.evalNested denominator phi u v ≠ 0 := by
  obtain ⟨inverse, hleft, _hright⟩ := hunit
  have heval := congrArg (fun p : CPolynomial (CPolynomial F) ↦
    TowerRepresentation.evalNested p phi u v) hleft
  rw [TowerRepresentation.evalNested_reduceElement phi u v hr.1 hpoint.1
      hr.2.2.2.1 hpoint.2 (denominator * inverse),
    TowerRepresentation.evalNested_reduceElement phi u v hr.1 hpoint.1
      hr.2.2.2.1 hpoint.2 (1 : CPolynomial (CPolynomial F)),
    evalNested_mul, evalNested_one] at heval
  intro hzero
  rw [hzero, zero_mul] at heval
  exact zero_ne_one heval

/-- Successful inversion certifies denominator nonvanishing at every geometric tower point. -/
theorem inverseRepresentative?_nonvanishing
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    (denominator inverse : CPolynomial (CPolynomial F))
    (hinverse : inverseRepresentative? r.modulus r.fiber denominator = some inverse)
    {K : Type*} [Field K] (phi : F →+* K) (u v : K) (hpoint : r.Point phi u v) :
    TowerRepresentation.evalNested denominator phi u v ≠ 0 := by
  exact isTowerUnit_nonvanishing r hr denominator
    (isTowerUnit_of_inverseRepresentative?_eq_some r.modulus r.fiber denominator inverse hinverse)
    phi u v hpoint

/-- At a retained geometric point, a materialized numerator satisfies the defining rational
identity: denominator times materialized coefficient equals the original numerator. -/
theorem evalNested_materializedCoefficient_mul_denominator
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    (denominator inverse numerator : CPolynomial (CPolynomial F))
    (hinverse : inverseRepresentative? r.modulus r.fiber denominator = some inverse)
    {K : Type*} [Field K] (phi : F →+* K) (u v : K) (hpoint : r.Point phi u v) :
    TowerRepresentation.evalNested denominator phi u v *
        TowerRepresentation.evalNested
          (TowerRepresentation.reduceElement r.modulus r.fiber (numerator * inverse)) phi u v =
      TowerRepresentation.evalNested numerator phi u v := by
  have hred := inverseRepresentative?_mul_eq_one r.modulus r.fiber denominator inverse hinverse
  have heval := congrArg (fun p : CPolynomial (CPolynomial F) ↦
    TowerRepresentation.evalNested p phi u v) hred
  rw [TowerRepresentation.evalNested_reduceElement phi u v hr.1 hpoint.1
      hr.2.2.2.1 hpoint.2 (denominator * inverse),
    TowerRepresentation.evalNested_reduceElement phi u v hr.1 hpoint.1
      hr.2.2.2.1 hpoint.2 (1 : CPolynomial (CPolynomial F)),
    evalNested_mul, evalNested_one] at heval
  rw [TowerRepresentation.evalNested_reduceElement phi u v hr.1 hpoint.1
    hr.2.2.2.1 hpoint.2 (numerator * inverse), evalNested_mul]
  calc
    TowerRepresentation.evalNested denominator phi u v *
          (TowerRepresentation.evalNested numerator phi u v *
            TowerRepresentation.evalNested inverse phi u v) =
        TowerRepresentation.evalNested numerator phi u v *
          (TowerRepresentation.evalNested denominator phi u v *
            TowerRepresentation.evalNested inverse phi u v) := by ring
    _ = TowerRepresentation.evalNested numerator phi u v * 1 := by rw [heval]
    _ = TowerRepresentation.evalNested numerator phi u v := mul_one _

/-- Equivalently, each materialized coefficient evaluates to the original rational coefficient. -/
theorem evalNested_materializedCoefficient_eq_div
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    (denominator inverse numerator : CPolynomial (CPolynomial F))
    (hinverse : inverseRepresentative? r.modulus r.fiber denominator = some inverse)
    {K : Type*} [Field K] (phi : F →+* K) (u v : K) (hpoint : r.Point phi u v) :
    TowerRepresentation.evalNested
        (TowerRepresentation.reduceElement r.modulus r.fiber (numerator * inverse)) phi u v =
      TowerRepresentation.evalNested numerator phi u v /
        TowerRepresentation.evalNested denominator phi u v := by
  have hden := inverseRepresentative?_nonvanishing r hr denominator inverse hinverse phi u v hpoint
  apply (eq_div_iff hden).2
  simpa [mul_comm] using
    evalNested_materializedCoefficient_mul_denominator r hr denominator inverse numerator hinverse
      phi u v hpoint

/-- Specializing a successfully materialized tower gives exactly the polynomial assembled from
the original rational coefficient values, in the original numerator order. -/
theorem materializeCoefficients?_specialize [DecidableEq F]
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    (denominator : CPolynomial (CPolynomial F))
    (numerators : List (CPolynomial (CPolynomial F)))
    (out : TowerRepresentation (F := F))
    (hout : materializeCoefficients? r denominator numerators = some out)
    {K : Type*} [Field K] (phi : F →+* K) (u v : K) (hpoint : r.Point phi u v) :
    out.specialize phi u v =
      Polynomial.JetHornerMachine.coefficientPolynomial
        (numerators.map fun numerator ↦
          TowerRepresentation.evalNested numerator phi u v /
            TowerRepresentation.evalNested denominator phi u v) := by
  rw [materializeCoefficients?_eq_reference r hr] at hout
  cases hinverse : inverseRepresentative? r.modulus r.fiber denominator with
  | none => simp [hinverse] at hout
  | some inverse =>
      simp only [hinverse, Option.some.injEq] at hout
      subst out
      apply congrArg Polynomial.JetHornerMachine.coefficientPolynomial
      simp only [withMaterializedCoefficients, List.map_map]
      apply List.map_congr_left
      intro numerator _hnumerator
      simp only [Function.comp_apply]
      exact evalNested_materializedCoefficient_eq_div r hr denominator inverse numerator hinverse
        phi u v hpoint

/-- Unit denominators are exactly those nonvanishing on all geometric points. -/
theorem isTowerUnit_iff_geometric_nonvanishing {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    (denominator : CPolynomial (CPolynomial F)) :
    IsTowerUnit r.modulus r.fiber denominator ↔
      ∀ x y : AlgebraicClosure F, r.Point (algebraMap F (AlgebraicClosure F)) x y →
        TowerRepresentation.evalNested denominator
          (algebraMap F (AlgebraicClosure F)) x y ≠ 0 := by
  constructor
  · intro hunit x y hp
    exact isTowerUnit_nonvanishing r hr denominator hunit _ x y hp
  · intro hnonzero
    obtain ⟨inverse, hinverse⟩ :=
      inverseRepresentative?_exists_of_geometric_nonvanishing r hr denominator hnonzero
    exact isTowerUnit_of_inverseRepresentative?_eq_some _ _ _ _ hinverse

/-- Geometric nonvanishing after fiber preprocessing suffices for actual materialization. -/
theorem materializeCoefficients?_exists_of_geometric_nonvanishing
    {F : Type} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    (denominator : CPolynomial (CPolynomial F))
    (numerators : List (CPolynomial (CPolynomial F)))
    (hnonzero : ∀ x y : AlgebraicClosure F,
      r.Point (algebraMap F (AlgebraicClosure F)) x y →
        TowerRepresentation.evalNested denominator
          (algebraMap F (AlgebraicClosure F)) x y ≠ 0) :
    ∃ out, materializeCoefficients? r denominator numerators = some out ∧
      out.WellFormed numerators.length := by
  exact materializeCoefficients?_exists_wellFormed r hr denominator numerators
    ((isTowerUnit_iff_geometric_nonvanishing r hr denominator).mpr hnonzero)

end ReedSolomon.ListDecoding.TowerAlgebra
