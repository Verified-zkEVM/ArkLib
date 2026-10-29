/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Plonk.Accumulator.Computable
import Mathlib.Algebra.Field.ZMod

/-! # Executable cyclic accumulator checks over a small prime field -/

namespace ArkLibTest.PlonkAccumulator

open Plonk
open scoped BigOperators

private abbrev F := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem primitive : IsPrimitiveRoot (6 : F) 2 := by
  apply (IsPrimitiveRoot.iff (by decide)).mpr
  constructor
  · decide
  · intro l hl hlt
    have h : l = 1 := by omega
    subst l
    decide

private def domain : EvaluationDomain F 2 := EvaluationDomain.primitiveRoot 6 primitive

private def cosets : CosetLabels domain where
  k₁ := 2
  k₂ := 3
  k₁_ne_zero := by decide
  k₂_ne_zero := by decide
  disjoint_left_right := Set.disjoint_range_iff.mpr (by decide)
  disjoint_left_output := Set.disjoint_range_iff.mpr (by decide)
  disjoint_right_output := Set.disjoint_range_iff.mpr (by decide)

private def circuit : ConstraintSystem F 1 2 := ![Gate.add 0 0 0, Gate.add 0 0 0]

private def wires : Fin 3 → CompPoly.CPolynomial F :=
  Computable.wirePolynomials domain (fun _ => 1)

private def permutation : Fin 3 → CompPoly.CPolynomial F :=
  Computable.permutationPolynomials domain circuit cosets.label

private def numerator : CompPoly.CPolynomial F :=
  Computable.accumulatorNumerator wires cosets.multiplier 1 6

private def denominator : CompPoly.CPolynomial F :=
  Computable.accumulatorDenominator wires permutation 1 6

private def accumulator : CompPoly.CPolynomial F :=
  Computable.honestAccumulator 6 primitive numerator denominator

example : circuit.CopyConstraintsSatisfied (fun _ => (1 : F)) := by
  intro p q _
  rfl

example : numerator.toPoly = Plonk.accumulatorNumerator
    (Plonk.wirePolynomials domain (fun _ => 1)) cosets.multiplier 1 6 :=
  Computable.accumulatorNumerator_toPoly wires _
    (Computable.wirePolynomials_toPoly domain (fun _ => 1)) _ _ _

private theorem numerator_eval (i : Fin 2) :
    numerator.eval (domain.node i) =
      ∏ c : Fin 3, (1 + cosets.multiplier c * domain.node i + 6) := by
  simp [numerator, Computable.accumulatorNumerator, CompPoly.CPolynomial.eval_toPoly,
    wires, Polynomial.eval_prod]

private theorem denominator_eval (i : Fin 2) :
    denominator.eval (domain.node i) =
      ∏ c : Fin 3, (1 + cosets.label (circuit.perm (finProdFinEquiv (c, i))) + 6) := by
  simp [denominator, Computable.accumulatorDenominator, CompPoly.CPolynomial.eval_toPoly,
    wires, permutation, Polynomial.eval_prod]

example : (∏ i : Fin 2, numerator.eval (domain.node i)) =
    ∏ i : Fin 2, denominator.eval (domain.node i) := by
  simp only [numerator_eval, denominator_eval]
  decide

example : ∀ i : Fin 2, denominator.eval (domain.node i) ≠ 0 := by
  simp only [denominator_eval]
  decide

example : AccumulatorRelation domain 6 numerator.toPoly denominator.toPoly
    accumulator.toPoly := by
  rw [accumulator, Computable.honestAccumulator_toPoly]
  apply honestAccumulator_relation 6 primitive (by decide)
  · intro i
    rw [← CompPoly.CPolynomial.eval_toPoly]
    change denominator.eval (domain.node i) ≠ 0
    rw [denominator_eval]
    exact (by decide : ∀ i : Fin 2,
      (∏ c : Fin 3, (1 + cosets.label (circuit.perm (finProdFinEquiv (c, i))) + 6)) ≠ 0) i
  · simp only [← CompPoly.CPolynomial.eval_toPoly]
    change (∏ i : Fin 2, numerator.eval (domain.node i)) =
      ∏ i : Fin 2, denominator.eval (domain.node i)
    simp only [numerator_eval, denominator_eval]
    decide

-- Equal products can have an impossible first recurrence when denominator factors vanish.
example : (∏ i : Fin 2, (![1, 0] : Fin 2 → F) i) =
    ∏ i : Fin 2, (![0, 1] : Fin 2 → F) i := by
  decide

example : ¬ ∃ z : Fin 2 → F, z 0 = 1 ∧
    ∀ i : Fin 2, z (i + 1) * (![0, 1] : Fin 2 → F) i =
      z i * (![1, 0] : Fin 2 → F) i := by
  rintro ⟨z, hzero, hstep⟩
  have h := hstep 0
  simp [hzero] at h

private def accumulatorRuntimeChecks : IO Unit := do
  unless (List.ofFn (fun i => numerator.eval (domain.node i)) = [6, 1]) do
    throw (IO.userError "Unexpected numerator values")
  unless (List.ofFn (fun i => denominator.eval (domain.node i)) = [1, 6]) do
    throw (IO.userError "Unexpected denominator values")
  unless (List.ofFn (fun i => accumulator.eval (domain.node i)) = [1, 6]) do
    throw (IO.userError "Unexpected accumulator values")
  unless (accumulator.eval 1 = 1) do
    throw (IO.userError "Unexpected accumulator normalization")
  unless (∀ i, accumulator.eval (6 * domain.node i) * denominator.eval (domain.node i) =
    accumulator.eval (domain.node i) * numerator.eval (domain.node i)) do
    throw (IO.userError "Unexpected cyclic recurrence")
  unless (∀ i, (Computable.boundaryResidual domain (by decide) accumulator).eval
    (domain.node i) = 0) do
    throw (IO.userError "Unexpected boundary residual")
  unless (∀ i, (Computable.recurrenceResidual 6 numerator denominator accumulator).eval
    (domain.node i) = 0) do
    throw (IO.userError "Unexpected recurrence residual")
  unless ((![1, 0] : Fin 2 → F) 0 * (![1, 0] : Fin 2 → F) 1 =
    (![0, 1] : Fin 2 → F) 0 * (![0, 1] : Fin 2 → F) 1) do
    throw (IO.userError "Unexpected zero-factor products")
  IO.println "Plonk accumulator runtime checks passed."

/-- info: Plonk accumulator runtime checks passed. -/
#guard_msgs in
#eval accumulatorRuntimeChecks

end ArkLibTest.PlonkAccumulator
