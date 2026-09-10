/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.BudgetedExecution
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.RateEligibility
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.AutomaticCertificate
/-!
# Executing the automatic first-order certificate

The automatic numerical recipe supplies an actual nonzero candidate to the existing decoder with
independent strict jet cutoff `J = mu + 1`. For fixed real parameters, one explicit constant
length threshold discharges the decoder's stronger size guards whenever the prime field has size
at least the block length. The result records the existing primitive-work ledger; it introduces
no new cost model.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CapacityDecoderMachine

open HiddenDerivative PolynomialDifferential
open SeparateSampleFieldExecution (ExactOutput)

noncomputable section

set_option autoImplicit false

/-- A fixed-parameter length threshold that dominates the automatic multiplicity, the strict
jet cutoff `mu+1`, and the decoder's non-small-block boundary. -/
def automaticFirstOrderExecutionLength (rho a : ℝ) : ℕ :=
  max 3 (max (automaticMultiplicity rho a) (automaticJetDegree rho a + 1))

/-- Above the fixed execution threshold, the block length is strictly larger than the automatic
total jet cap. -/
theorem automaticJetDegree_lt_of_executionLength_le (rho a : ℝ) {n : ℕ}
    (hn : automaticFirstOrderExecutionLength rho a ≤ n) :
    automaticJetDegree rho a < n := by
  unfold automaticFirstOrderExecutionLength at hn
  omega

/-- If the prime field has at least `n` elements, the eventual length bound also gives the
decoder's stronger characteristic inequality `q > mu`. -/
theorem automaticJetDegree_lt_prime_of_executionLength_le (rho a : ℝ) {n q : ℕ}
    (hn : automaticFirstOrderExecutionLength rho a ≤ n) (hnq : n ≤ q) :
    automaticJetDegree rho a < q :=
  (automaticJetDegree_lt_of_executionLength_le rho a hn).trans_le hnq

/-- The same threshold supplies all three length-only guards needed by the budgeted decoder. -/
theorem automaticExecution_length_guards (rho a : ℝ) {n : ℕ}
    (hn : automaticFirstOrderExecutionLength rho a ≤ n) :
    3 ≤ n ∧ automaticMultiplicity rho a ≤ n ∧ automaticJetDegree rho a + 1 ≤ n := by
  unfold automaticFirstOrderExecutionLength at hn
  omega

/-- For prime `q ≥ n`, the literal automatic certificate is submitted to the existing budgeted
decoder at order one and strict cutoff `mu+1`. The returned physical coefficient lists are
exactly the degree-`<k` polynomials with at least `A` agreements. -/
theorem automaticFirstOrder_run_exact
    {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    {q n k A : ℕ} [Fact q.Prime]
    (hn : automaticFirstOrderExecutionLength rho a ≤ n)
    (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (haA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) (hnq : n ≤ q) :
    let m := automaticMultiplicity rho a
    let J := automaticJetDegree rho a + 1
    ∃ (out : List (List (ZMod q))) (cost : ℕ)
      (found : AmbientSearchMachine.Output (ZMod q)),
      runWithBudget n k 1 m J A (List.ofFn (fun i ↦ (domain i, received i))) =
        (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ InterpolationDispatch.budgetWithBudget k 1 m J A n +
        QuadraticAlgebra.SetupMachine.budget q (m * A) +
        QuadraticDecoderMachine.decoderFuelWithBudget 1 m J q
          (if 2 * (m * A + 1 - (found.degree + 1)) ≤ q then 1 else 2) +
        16 * q + 152 := by
  let m := automaticMultiplicity rho a
  let mu := automaticJetDegree rho a
  let J := mu + 1
  let D := k - 1
  obtain ⟨hn3, hmn, hJn⟩ := automaticExecution_length_guards rho a hn
  have hnpos : 0 < n := by omega
  obtain ⟨cert⟩ := exists_automaticFirstOrder_symbolicCertificate
    (F := ZMod q) hrho hrhoOne ha haOne hnpos rfl hk hkRate haA
      domain received (fun _ ↦ 0)
  obtain ⟨Q, hQ, heligible, hlocal⟩ := cert.exists_executableSpecialization 0
  have hlocal' : ∀ row ∈ List.ofFn (fun i ↦ (domain i, received i)),
      localConstraintAt m row.1 row.2 Q = 0 := by
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    simpa only [m, zero_mul, add_zero, SatisfiesLocalConstraints] using hlocal i
  have hJq : J ≤ q := hJn.trans hnq
  have hmA : m * A ≤ q ^ 2 := by
    calc
      m * A ≤ n * n := Nat.mul_le_mul hmn hAn
      _ ≤ q * q := Nat.mul_le_mul hnq hnq
      _ = q ^ 2 := by ring
  have hkn : k < n := by
    have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hrhon : rho * (n : ℝ) < n := by
      calc
        rho * (n : ℝ) < 1 * n := mul_lt_mul_of_pos_right hrhoOne hnreal
        _ = n := one_mul _
    exact_mod_cast hkRate.trans_lt hrhon
  have hDlow : max (k - 1) 1 ≤ D := by
    dsimp [D]
    omega
  have hDhigh : D < n := by
    dsimp [D]
    omega
  exact runWithBudget_exact_of_candidate domain received (by omega) hn3 hAn hnq hmA hJq
    hDlow hDhigh Q hQ heligible hlocal'

end

end ReedSolomon.ListDecoding.CapacityDecoderMachine
