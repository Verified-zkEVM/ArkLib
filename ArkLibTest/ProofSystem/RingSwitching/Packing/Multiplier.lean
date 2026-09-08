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

/-- Incompatible opening and challenge fields instantiate the actual evaluator identity. -/
theorem separateChallenge (r : Fin 2 → GaloisField 2 3)
    (weight : Fin 3 → GaloisField 2 4) (z : Fin 2 → GaloisField 2 4) :
    Tests.separateFields.evaluateMultiplier r weight z =
      (Tests.separateFields.multiplier r weight).val.eval z :=
  Tests.separateFields.evaluateMultiplier_eq r weight z

/-- A rank-one packed algebra and a rank-two opening algebra for explicit arithmetic. -/
abbrev counterData : PackingData (ZMod 5) where
  P := ZMod 5
  E := Fin 2 → ZMod 5
  ιP := Unit
  ιE := Fin 2
  packBasis := Basis.singleton Unit (ZMod 5)
  openBasis := Pi.basisFun _ _

/-- Observing with two unit weights sums the two opening coordinates. -/
theorem bridge_sum (a : counterData.E) :
    counterData.bridge (fun _ => (1 : ZMod 5)) a = a 0 + a 1 := by
  rw [counterData.bridge_apply]
  simp [counterData, Fin.sum_univ_two]

/-- The bridge is genuinely nonmultiplicative, even on the two nonzero basis vectors. -/
theorem bridge_not_multiplicative :
    counterData.bridge (fun _ => (1 : ZMod 5)) ((![1, 0]) * (![0, 1])) ≠
      counterData.bridge (fun _ => (1 : ZMod 5)) (![1, 0]) *
      counterData.bridge (fun _ => (1 : ZMod 5)) (![0, 1]) := by
  rw [bridge_sum, bridge_sum, bridge_sum]
  decide

/-- Multiplication matrices for the concrete product basis are diagonal. -/
theorem counterMatrix (a : counterData.E) :
    counterData.challengeMulMatrix (C := ZMod 5) a = diagonal a := by
  ext i j
  simp [PackingData.challengeMulMatrix, counterData, Algebra.leftMulMatrix_eq_repr_mul,
    Pi.basisFun_apply, Pi.single_apply, diagonal_apply]

/-- Transport through the base algebra leaves the concrete coordinates unchanged. -/
theorem counterCoordinates (a : counterData.E) :
    counterData.challengeCoordinates (C := ZMod 5) a = a := by
  ext i
  simp [PackingData.challengeCoordinates, counterData]

/-- The concrete interpolated layer uses the two coordinatewise equality factors. -/
theorem counterLayer (a : counterData.E) (z : ZMod 5) :
    ReadOnce.interpolate
      (fun b => counterData.challengeMulMatrix (counterData.equalityFactor a b)) z =
      diagonal (fun u => (1 - z) * (1 - a u) + z * a u) := by
  simp only [ReadOnce.interpolate, counterMatrix, PackingData.equalityFactor, Fin.isValue,
    ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide]
  ext i j
  by_cases h : i = j
  · subst j
    simp only [diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  · simp [h]

/-- Direct matrix execution gives the sum of the two coordinatewise kernel products. -/
theorem counter_evaluator_formula (r : Fin 2 → counterData.E) (z : Fin 2 → ZMod 5) :
    counterData.evaluateMultiplier r (fun _ => (1 : ZMod 5)) z =
      ∑ u : Fin 2, ((1 - z 1) * (1 - r 1 u) + z 1 * r 1 u) *
        ((1 - z 0) * (1 - r 0 u) + z 0 * r 0 u) := by
  rw [PackingData.evaluateMultiplier]
  change dotProductBilin (ZMod 5) (ZMod 5) (fun _ => 1)
    (ReadOnce.run (fun i : Fin 2 => ReadOnce.interpolate
      (fun b => counterData.challengeMulMatrix (counterData.equalityFactor (r i) b)) (z i))
      (counterData.challengeCoordinates 1)) = _
  have hLayer (i : Fin 2) : ReadOnce.interpolate
      (fun b => counterData.challengeMulMatrix (counterData.equalityFactor (r i) b)) (z i) =
      diagonal (fun u => (1 - z i) * (1 - r i u) + z i * r i u) :=
    counterLayer _ _
  simp only [hLayer]
  simp only [counterCoordinates, ReadOnce.run_succ, ReadOnce.run_zero]
  change (∑ u : Fin 2, (1 : ZMod 5) * _) = _
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [mulVec_diagonal, one_mul]
  change _ * (_ * 1) = _
  rw [mul_one]
  rfl

/-- The online matrix evaluator is nonzero at a non-Boolean challenge point. -/
theorem counter_evaluator_value :
    counterData.evaluateMultiplier (![(![1, 0]), (![0, 1])]) (fun _ => (1 : ZMod 5))
      (fun _ => 3) = 3 := by
  rw [counter_evaluator_formula]
  decide

/-- The same online matrix evaluator vanishes at zero, so the example is nonconstant. -/
theorem counter_evaluator_zero :
    counterData.evaluateMultiplier (![(![1, 0]), (![0, 1])]) (fun _ => (1 : ZMod 5))
      (fun _ => 0) = 0 := by
  rw [counter_evaluator_formula]
  decide

/-- Multiplying the separately observed factors gives the wrong value at that same point. -/
theorem factorwise_observation_is_wrong :
    counterData.evaluateMultiplier (![(![1, 0]), (![0, 1])]) (fun _ => (1 : ZMod 5))
      (fun _ => 3) ≠
      counterData.bridge (fun _ => (1 : ZMod 5))
        ((1 - (3 : ZMod 5)) • (1 - (![1, 0])) + (3 : ZMod 5) • (![1, 0])) *
      counterData.bridge (fun _ => (1 : ZMod 5))
        ((1 - (3 : ZMod 5)) • (1 - (![0, 1])) + (3 : ZMod 5) • (![0, 1])) := by
  rw [counter_evaluator_value, bridge_sum, bridge_sum]
  decide

/-- With no retained variables, the evaluator performs only the observation of one. -/
theorem noVariables (weight : Fin 2 → ZMod 5) :
    counterData.evaluateMultiplier (fun i : Fin 0 => i.elim0) weight
      (fun i : Fin 0 => i.elim0) = weight 0 + weight 1 := by
  simp only [PackingData.evaluateMultiplier, counterCoordinates, ReadOnce.run_zero]
  change (∑ u : Fin 2, weight u * 1) = weight 0 + weight 1
  simp [Fin.sum_univ_two]

/-- The instrumented evaluator also covers the zero-variable boundary. -/
theorem noVariableActions :
    (ReadOnce.runCounted
      (fun i : Fin 0 => ReadOnce.interpolate
        (counterData.multiplierLayers (C := ZMod 5) (fun j : Fin 0 => j.elim0) i) 0)
      (counterData.challengeCoordinates 1)).2 = 0 :=
  counterData.evaluateMultiplier_actions (fun i : Fin 0 => i.elim0) (fun _ => (0 : ZMod 5))

end RingSwitching.Packing.MultiplierTests

end
