/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.UnivariateRepresentation.Postprocess

/-!
# Undoing an affine chart in a rational univariate map

If translated coordinates satisfy `yᵢ = Nᵢ / B` and the affine chart was
`yᵢ = xᵢ - c`, then the original coordinates satisfy
`xᵢ = (Nᵢ + c B) / B`.  This file performs that numerator update without
changing the eliminant or denominator.
-/

@[expose] public section

namespace ArkLib.UnivariateRepresentation

open CompPoly CompPoly.CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Undo the simultaneous scalar translation `yᵢ = xᵢ - c` in every
rational coordinate numerator. -/
def inverseTranslateMapData (c : F) (input : MapData (F := F)) : MapData (F := F) :=
  {
    modulus := input.modulus
    denominator := input.denominator
    numerators := input.numerators.map fun numerator ↦
      numerator + C c * input.denominator }

@[simp]
theorem inverseTranslateMapData_modulus (c : F) (input : MapData (F := F)) :
    (inverseTranslateMapData c input).modulus = input.modulus := rfl

@[simp]
theorem inverseTranslateMapData_denominator (c : F) (input : MapData (F := F)) :
    (inverseTranslateMapData c input).denominator = input.denominator := rfl

@[simp]
theorem inverseTranslateMapData_numerators (c : F) (input : MapData (F := F)) :
    (inverseTranslateMapData c input).numerators =
      input.numerators.map fun numerator ↦ numerator + C c * input.denominator := rfl

theorem eval₂_inverseTranslateNumerator
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    (c : F) (denominator numerator : CPolynomial F)
    (hdenominator : denominator.toPoly.eval₂ ι θ ≠ 0) :
    (numerator + C c * denominator).toPoly.eval₂ ι θ /
        denominator.toPoly.eval₂ ι θ =
      numerator.toPoly.eval₂ ι θ / denominator.toPoly.eval₂ ι θ + ι c := by
  simp only [toPoly_add, toPoly_mul, toPoly_C, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C]
  rw [add_div, mul_div_cancel_right₀ _ hdenominator]

/-- Specialization of every inverse-translated rational coordinate. -/
theorem inverseTranslateMapData_specializes
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    (c : F) (input : MapData (F := F))
    (hdenominator : input.denominator.toPoly.eval₂ ι θ ≠ 0) :
    List.Forall₂
      (fun numerator original ↦
        numerator.toPoly.eval₂ ι θ / input.denominator.toPoly.eval₂ ι θ =
          original.toPoly.eval₂ ι θ / input.denominator.toPoly.eval₂ ι θ + ι c)
      (inverseTranslateMapData c input).numerators input.numerators := by
  simp only [inverseTranslateMapData_numerators]
  induction input.numerators with
  | nil => exact .nil
  | cons numerator numerators ih =>
      exact .cons (eval₂_inverseTranslateNumerator ι θ c input.denominator numerator
        hdenominator) ih

/-- Interpret a postprocessed coordinate list for the inverse-translated map
against the original translated-coordinate numerators. -/
theorem coordinatesSpecializeAt_inverseTranslateMapData
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    (c : F) (input : MapData (F := F)) (coordinates : List (CPolynomial F))
    (hdenominator : input.denominator.toPoly.eval₂ ι θ ≠ 0)
    (hspecializes :
      CoordinatesSpecializeAt ι θ (inverseTranslateMapData c input).denominator
        (inverseTranslateMapData c input).numerators coordinates) :
    List.Forall₂
      (fun numerator coordinate ↦
        coordinate.toPoly.eval₂ ι θ =
          numerator.toPoly.eval₂ ι θ / input.denominator.toPoly.eval₂ ι θ + ι c)
      input.numerators coordinates := by
  simp only [inverseTranslateMapData_denominator,
    inverseTranslateMapData_numerators] at hspecializes
  generalize input.numerators = numerators at hspecializes ⊢
  induction numerators generalizing coordinates with
  | nil =>
      cases hspecializes
      exact .nil
  | cons numerator numerators ih =>
      cases hspecializes with
      | cons hcoordinate htail =>
          apply List.Forall₂.cons
          · rw [hcoordinate,
              eval₂_inverseTranslateNumerator ι θ c input.denominator numerator
                hdenominator]
          · exact ih _ htail

end ArkLib.UnivariateRepresentation
