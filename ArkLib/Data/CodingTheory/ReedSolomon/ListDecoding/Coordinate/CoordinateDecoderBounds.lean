/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateDecoderMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticDecoderBounds
/-!
# Order-dependent bounds for the same executed coordinate decoder

The coordinate refinement factor and actual alphabet materialization costs are absorbed into
coefficients. The powers of the field size are unchanged. At order zero the coefficient is
universal even for growing multiplicity; at positive order it depends only on order and
multiplicity. These bounds concern primitive work of the literal coordinate run, not bit cost.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CoordinateDecoderMachine

open HiddenDerivative QuadraticAlgebra PolynomialDifferential
open SeparateSampleFieldExecution (ExactOutput)

/-- The exact numerical majorant returned by the executed coordinate decoder theorem. -/
def totalBudget (k d m A n q e : ℕ) : ℕ :=
  InterpolationDispatch.budget k d m A n + SetupMachine.budget q (m * A) +
    CoordinateDecoderCore.fuel d m q e + 45 * q ^ 2 + 16 * q + 168

/-- Only the two fixed algorithm parameters occur in the positive-order coefficient. -/
def fixedCoefficient (d m : ℕ) : ℕ :=
  17179869184 * (NonzeroInterpolationMachine.attemptBudget d m 1 1 +
    SeparateSampleDecoder.sizePolynomial (SeparateSampleDecoder.fixedSizeCoefficient d m) +
    90 * m + 911) + 101

/-- A universal order-zero coefficient, independent of multiplicity and all input sizes. -/
def zeroCoefficient : ℕ :=
  17179869184 * (SeparateSampleDecoder.sizePolynomial 26 + 294227) + 101

/-- Coordinate overhead adds no new field-size exponent. -/
theorem totalBudget_le_scaled (k d m A n q e : ℕ) :
    totalBudget k d m A n q e ≤
      17179869184 * QuadraticDecoderMachine.totalBudget k d m A n q e + 45 * q ^ 2 + 56 := by
  unfold totalBudget QuadraticDecoderMachine.totalBudget CoordinateDecoderCore.fuel
  omega

private theorem absorb (total original coefficient power square : ℕ)
    (hscale : total ≤ 17179869184 * original + 45 * square + 56)
    (hmain : original ≤ coefficient * power) (h2 : square ≤ power) (h1 : 1 ≤ power) :
    total ≤ (17179869184 * coefficient + 101) * power := by
  have hextra : 45 * square + 56 ≤ 101 * power := by omega
  calc
    total ≤ 17179869184 * original + (45 * square + 56) := by omega
    _ ≤ 17179869184 * (coefficient * power) + 101 * power :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hmain) hextra
    _ = (17179869184 * coefficient + 101) * power := by ring

/-- Positive-order work has exactly the original exponent, uniformly in k and e. -/
theorem budget_fixed (k d m A n q e : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hA : A ≤ n) (hn : n ≤ q) :
    totalBudget k d m A n q e ≤ fixedCoefficient d m * q ^ (e * (d + 2) + 10) := by
  have h2 : q ^ 2 ≤ q ^ (e * (d + 2) + 10) := Nat.pow_le_pow_right hq (by omega)
  have h1 : 1 ≤ q ^ (e * (d + 2) + 10) := Nat.one_le_pow _ _ hq
  exact absorb _ _ _ _ _ (totalBudget_le_scaled k d m A n q e)
    (QuadraticDecoderMachine.budget_fixed k d m A n q e hd hq hA hn) h2 h1

/-- Order-zero work retains the universal exponents 27 and 29 for the two center regimes. -/
theorem budget_zero (k m A n q e : ℕ) (hq : 0 < q) (hm : m ≤ n)
    (hA : A ≤ n) (hn : n ≤ q) :
    totalBudget k 0 m A n q e ≤ zeroCoefficient * q ^ (2 * e + 25) := by
  have h2 : q ^ 2 ≤ q ^ (2 * e + 25) := Nat.pow_le_pow_right hq (by omega)
  have h1 : 1 ≤ q ^ (2 * e + 25) := Nat.one_le_pow _ _ hq
  exact absorb _ _ _ _ _ (totalBudget_le_scaled k 0 m A n q e)
    (QuadraticDecoderMachine.budget_zero k m A n q e hq hm hA hn) h2 h1

/-- Select the constant coefficient without introducing size dependence at order zero. -/
def workCoefficient (d m : ℕ) : ℕ := if d = 0 then zeroCoefficient else fixedCoefficient d m

/-- The same field-size exponents as the original primitive-work decoder. -/
def workExponent (d e : ℕ) : ℕ := if d = 0 then 2 * e + 25 else e * (d + 2) + 10

/-- One numerical API covers both zero and positive orders. -/
theorem budget_le (k d m A n q e : ℕ) (hq : 0 < q) (hm : m ≤ n)
    (hA : A ≤ n) (hn : n ≤ q) :
    totalBudget k d m A n q e ≤ workCoefficient d m * q ^ workExponent d e := by
  by_cases hd : d = 0
  · subst d
    simpa [workCoefficient, workExponent] using budget_zero k m A n q e hq hm hA hn
  · simpa [workCoefficient, workExponent, hd] using
      budget_fixed k d m A n q e (by omega) hq hA hn

variable {q : ℕ} [Fact q.Prime]

/-- The same literal interpolation/setup/coordinate execution has an order-dependent polynomial
work bound and exactly the required decoding list. No bit-cost realization is assumed. -/
theorem run_exact_bound (k d m A : ℕ) {n : ℕ}
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hodd : q ≠ 2) (hL : m * A ≤ q ^ 2)
    (found : AmbientSearchMachine.Output (ZMod q))
    (hi : (InterpolationDispatch.run k d m A
      (List.ofFn (fun i ↦ (domain i, received i)))).1 = some found)
    (hdepth : d ≤ found.degree) (hk : k ≤ found.degree + 1)
    (hD : found.degree ≤ n) (hnq : n ≤ q) (hA : A ≤ n) (hm : m ≤ n)
    (hchar : IsBelowCharacteristic found.degree
      (NonzeroInterpolationMachine.sourceOutput (d := d) found.degree m A found.interpolant))
    (hweight : differentialWeightedDegree found.degree
      (NonzeroInterpolationMachine.sourceOutput (d := d)
        found.degree m A found.interpolant) < m * A) :
    ∃ out cost, run k d m A (List.ofFn (fun i ↦ (domain i, received i))) hodd hL =
      (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ workCoefficient d m * q ^ workExponent d
        (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) := by
  obtain ⟨out, cost, hr, ho, hb⟩ := run_exact_of_interpolation k d m A domain received
    hodd hL found hi hdepth hk hD hnq hA hm hchar hweight
  have hn := budget_le k d m A n q
    (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2)
    (Fact.out : q.Prime).pos hm hA hnq
  exact ⟨out, cost, hr, ho, hb.trans hn⟩

end ReedSolomon.ListDecoding.CoordinateDecoderMachine
