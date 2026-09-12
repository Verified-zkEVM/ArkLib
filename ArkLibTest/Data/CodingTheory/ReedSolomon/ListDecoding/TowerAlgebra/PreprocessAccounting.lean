/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PreprocessAccounting
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Separable

/-! Executable accounting checks for ramified fiber preprocessing and empty retained loci. -/

namespace ArkLibTest.PreprocessAccounting

open CompPoly Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.TowerAlgebra

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev F := ZMod 5

private def base : CPolynomial F := CPolynomial.X

/-- A degree-three fiber with a double root at zero and a simple root at one. -/
private def ramifiedFiber : CPolynomial (CPolynomial F) :=
  CPolynomial.X ^ 2 * (CPolynomial.X - CPolynomial.C 1)

private def ramifiedTower : TowerRepresentation (F := F) where
  modulus := base
  fiber := ramifiedFiber
  coefficients := []

private theorem ramifiedTower_preprocessable : Preprocessable ramifiedTower := by
  refine ⟨?_, ?_, ?_⟩
  · apply (CPolynomial.monic_toPoly_iff base).mpr
    simp only [base, CPolynomial.X_toPoly]
    exact Polynomial.monic_X
  · simpa [ramifiedTower, base, CPolynomial.X_toPoly] using
      (Polynomial.separable_X (R := F)).squarefree
  · apply (CPolynomial.monic_toPoly_iff ramifiedFiber).mpr
    simp only [ramifiedFiber, CPolynomial.toPoly_mul, CPolynomial.toPoly_pow,
      CPolynomial.toPoly_sub, CPolynomial.X_toPoly, CPolynomial.C_toPoly]
    exact (Polynomial.monic_X.pow 2).mul (Polynomial.monic_X_sub_C 1)

/-- The field characteristic exceeds the input fiber degree, as required by point correctness. -/
private theorem ramifiedTower_degree_lt_char : ramifiedTower.fiber.natDegree < 5 := by
  decide +kernel

private def separant : CPolynomial (CPolynomial F) := ramifiedFiber.derivative

private theorem regularInputPoint :
    ramifiedTower.Point (RingHom.id F) 0 1 := by
  simp [TowerRepresentation.Point, TowerRepresentation.evalNested, ramifiedTower, base,
    ramifiedFiber, FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.toPoly_pow, CPolynomial.toPoly_sub]

private theorem separant_nonzero_at_regular_point :
    TowerRepresentation.evalNested separant (RingHom.id F) 0 1 ≠ 0 := by
  simp [TowerRepresentation.evalNested, separant, ramifiedFiber,
    FirstOrderNormDecoder.D5.specializeFiberCPolynomial, CPolynomial.derivative_toPoly,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.toPoly_pow, CPolynomial.toPoly_sub]

/-- The simple root at one survives preprocessing even though the input fiber is ramified. -/
private theorem regular_point_retained :
    ∃ out ∈ preprocessFiber ramifiedTower separant ramifiedTower_preprocessable,
      out.Point (RingHom.id F) 0 1 :=
  (preprocessFiber_correct 5 ramifiedTower separant ramifiedTower_preprocessable
    ramifiedTower_degree_lt_char (RingHom.id F) 0 1).mpr
      ⟨regularInputPoint, separant_nonzero_at_regular_point⟩

private def regularOutput :=
  preprocessFiber ramifiedTower separant ramifiedTower_preprocessable

private def emptyOutput :=
  preprocessFiber ramifiedTower 0 ramifiedTower_preprocessable

/-- Executed by the decoder runtime suite. -/
def run : IO Unit := do
  unless regularOutput.length == 1 do
    throw (IO.userError "preprocess accounting check 1 failed: retained component count")
  unless regularOutput.map TowerRepresentation.dimension == [1] do
    throw (IO.userError "preprocess accounting check 2 failed: retained dimension")
  unless regularOutput.map (fun out => out.fiber) ==
      [CPolynomial.X - CPolynomial.C 1] do
    throw (IO.userError "preprocess accounting check 3 failed: retained regular fiber")
  unless emptyOutput.isEmpty do
    throw (IO.userError "preprocess accounting check 4 failed: zero separant locus")
  unless (regularOutput.map TowerRepresentation.dimension).sum ≤ ramifiedTower.dimension do
    throw (IO.userError "preprocess accounting check 5 failed: dimension bound")

end ArkLibTest.PreprocessAccounting
