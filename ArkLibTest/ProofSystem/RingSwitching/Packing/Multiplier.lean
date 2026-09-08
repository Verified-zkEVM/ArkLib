/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Multiplier
import ArkLibTest.ProofSystem.RingSwitching.Packing.Algebra
import ArkLibTest.ProofSystem.RingSwitching.Packing.SeparateFields

/-!
# Public multiplier acceptance and regression cases

These clients exercise three independent algebra ranks over a base with zero divisors, and an
opening field with no embedding into the challenge field. A concrete nonmultiplicative coordinate
observation rules out replacing the matrix computation by a product of observed factors.
-/

noncomputable section

namespace RingSwitching.Packing.MultiplierTests

open Module MvPolynomial Matrix

/-- The production evaluator accepts unrelated product algebras of ranks two, three, and four. -/
theorem unequalRanks (r : Fin 3 → Tests.productData.E)
    (weight : Fin 3 → Fin 4 → ZMod 6) (z : Fin 3 → Fin 4 → ZMod 6) :
    Tests.productData.evaluateMultiplier r weight z =
      (Tests.productData.multiplier r weight).val.eval z :=
  Tests.productData.evaluateMultiplier_eq r weight z

/-- The challenge field need not contain the opening field. -/
theorem noOpeningToChallengeHom :
    ¬ Nonempty (GaloisField 2 3 →ₐ[ZMod 2] GaloisField 2 4) := by
  rw [FiniteField.nonempty_algHom_iff_finrank_dvd]
  simp only [GaloisField.finrank (p := 2) (n := 3) (by decide),
    GaloisField.finrank (p := 2) (n := 4) (by decide)]
  decide

/-- Incompatible opening and challenge fields instantiate the evaluator identity. -/
theorem separateChallenge (r : Fin 2 → GaloisField 2 3)
    (weight : Fin 3 → GaloisField 2 4) (z : Fin 2 → GaloisField 2 4) :
    Tests.separateFields.evaluateMultiplier r weight z =
      (Tests.separateFields.multiplier r weight).val.eval z :=
  Tests.separateFields.evaluateMultiplier_eq r weight z

/-- A rank-one packed algebra and a rank-two opening algebra for explicit arithmetic. -/
abbrev diagonalData : PackingData (ZMod 5) where
  P := ZMod 5
  E := Fin 2 → ZMod 5
  ιP := Unit
  ιE := Fin 2
  packBasis := Basis.singleton Unit (ZMod 5)
  openBasis := Pi.basisFun _ _

/-- Observing with two unit weights sums the two opening coordinates. -/
theorem bridge_sum (a : diagonalData.E) :
    diagonalData.bridge (fun _ => (1 : ZMod 5)) a = a 0 + a 1 := by
  rw [diagonalData.bridge_apply]
  simp [diagonalData, Fin.sum_univ_two]

/-- The bridge is genuinely nonmultiplicative, even on the two nonzero basis vectors. -/
theorem bridge_not_multiplicative :
    diagonalData.bridge (fun _ => (1 : ZMod 5)) ((![1, 0]) * (![0, 1])) ≠
      diagonalData.bridge (fun _ => (1 : ZMod 5)) (![1, 0]) *
      diagonalData.bridge (fun _ => (1 : ZMod 5)) (![0, 1]) := by
  rw [bridge_sum, bridge_sum, bridge_sum]
  decide

/-- Multiplication matrices for the concrete product basis are diagonal. -/
theorem challengeMulMatrix_eq_diagonal (a : diagonalData.E) :
    diagonalData.challengeMulMatrix (C := ZMod 5) a = diagonal a := by
  ext i j
  simp [PackingData.challengeMulMatrix, diagonalData, Algebra.leftMulMatrix_eq_repr_mul,
    Pi.basisFun_apply, Pi.single_apply, diagonal_apply]

/-- Transport through the base algebra leaves the concrete coordinates unchanged. -/
theorem challengeCoordinates_eq (a : diagonalData.E) :
    diagonalData.challengeCoordinates (C := ZMod 5) a = a := by
  ext i
  simp [PackingData.challengeCoordinates, diagonalData]

/-- The concrete interpolated layer uses the two coordinatewise equality factors. -/
theorem interpolate_eq_diagonal (a : diagonalData.E) (z : ZMod 5) :
    ReadOnce.interpolate
      (fun b => diagonalData.challengeMulMatrix (diagonalData.equalityFactor a b)) z =
      diagonal (fun u => (1 - z) * (1 - a u) + z * a u) := by
  simp only [ReadOnce.interpolate, challengeMulMatrix_eq_diagonal, PackingData.equalityFactor,
    Fin.isValue,
    ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide]
  ext i j
  by_cases h : i = j
  · subst j
    simp only [diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  · simp [h]

/-- Direct matrix execution gives the sum of the two coordinatewise kernel products. -/
theorem evaluateMultiplier_eq_sum (r : Fin 2 → diagonalData.E) (z : Fin 2 → ZMod 5) :
    diagonalData.evaluateMultiplier r (fun _ => (1 : ZMod 5)) z =
      ∑ u : Fin 2, ((1 - z 1) * (1 - r 1 u) + z 1 * r 1 u) *
        ((1 - z 0) * (1 - r 0 u) + z 0 * r 0 u) := by
  rw [PackingData.evaluateMultiplier]
  change dotProductBilin (ZMod 5) (ZMod 5) (fun _ => 1)
    (ReadOnce.run (fun i : Fin 2 => ReadOnce.interpolate
      (fun b => diagonalData.challengeMulMatrix (diagonalData.equalityFactor (r i) b)) (z i))
      (diagonalData.challengeCoordinates 1)) = _
  have hLayer (i : Fin 2) : ReadOnce.interpolate
      (fun b => diagonalData.challengeMulMatrix (diagonalData.equalityFactor (r i) b)) (z i) =
      diagonal (fun u => (1 - z i) * (1 - r i u) + z i * r i u) :=
    interpolate_eq_diagonal _ _
  simp only [hLayer]
  simp only [challengeCoordinates_eq, ReadOnce.run_succ, ReadOnce.run_zero]
  change (∑ u : Fin 2, (1 : ZMod 5) * _) = _
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [mulVec_diagonal, one_mul]
  change _ * (_ * 1) = _
  rw [mul_one]
  rfl

/-- The online matrix evaluator is nonzero at a non-Boolean challenge point. -/
theorem evaluateMultiplier_eq_three :
    diagonalData.evaluateMultiplier (![(![1, 0]), (![0, 1])]) (fun _ => (1 : ZMod 5))
      (fun _ => 3) = 3 := by
  rw [evaluateMultiplier_eq_sum]
  decide

/-- The same online matrix evaluator vanishes at zero, so the example is nonconstant. -/
theorem evaluateMultiplier_eq_zero :
    diagonalData.evaluateMultiplier (![(![1, 0]), (![0, 1])]) (fun _ => (1 : ZMod 5))
      (fun _ => 0) = 0 := by
  rw [evaluateMultiplier_eq_sum]
  decide

/-- Multiplying the separately observed factors gives the wrong value at the same point. -/
theorem evaluateMultiplier_ne_prod_bridge :
    diagonalData.evaluateMultiplier (![(![1, 0]), (![0, 1])]) (fun _ => (1 : ZMod 5))
      (fun _ => 3) ≠
      diagonalData.bridge (fun _ => (1 : ZMod 5))
        ((1 - (3 : ZMod 5)) • (1 - (![1, 0])) + (3 : ZMod 5) • (![1, 0])) *
      diagonalData.bridge (fun _ => (1 : ZMod 5))
        ((1 - (3 : ZMod 5)) • (1 - (![0, 1])) + (3 : ZMod 5) • (![0, 1])) := by
  rw [evaluateMultiplier_eq_three, bridge_sum, bridge_sum]
  decide

/-- With no retained variables, the evaluator performs only the observation of one. -/
theorem evaluateMultiplier_zero_variables (weight : Fin 2 → ZMod 5) :
    diagonalData.evaluateMultiplier (fun i : Fin 0 => i.elim0) weight
      (fun i : Fin 0 => i.elim0) = weight 0 + weight 1 := by
  simp only [PackingData.evaluateMultiplier, challengeCoordinates_eq, ReadOnce.run_zero]
  change (∑ u : Fin 2, weight u * 1) = weight 0 + weight 1
  simp [Fin.sum_univ_two]

/-- The instrumented evaluator also covers the zero-variable boundary. -/
theorem runCounted_zero_variables :
    (ReadOnce.runCounted
      (fun i : Fin 0 => ReadOnce.interpolate
        (diagonalData.multiplierLayers (C := ZMod 5) (fun j : Fin 0 => j.elim0) i) 0)
      (diagonalData.challengeCoordinates 1)).2 = 0 :=
  diagonalData.evaluateMultiplier_actions (fun i : Fin 0 => i.elim0) (fun _ => (0 : ZMod 5))

end RingSwitching.Packing.MultiplierTests

end
