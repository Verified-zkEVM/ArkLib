/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticDecoderParameters
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticDecoderBounds
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderZero.DecoderCertificate
/-!
# Executed quadratic decoding for gaps at least one quarter

The literal order-zero interpolation dispatch, quadratic setup, and decoding driver return the
same exact list with a universal polynomial primitive-work bound. Multiplicity is allowed to
grow with the block length. Blocks of length at most two are handled separately by direct
decoding. This result does not assert the unfinished bit-RAM refinement.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed-Solomon List Decoding up to Capacity at Every
  Rate*][DKTZ26], the large-gap branch of uniform capacity decoding.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticDecoderMachine

open HiddenDerivative ReedSolomon QuadraticAlgebra PolynomialDifferential
open SeparateSampleFieldExecution (ExactOutput)

variable {q : ℕ} [Fact q.Prime]

/-- A quarter gap supplies actual interpolation success and an exact, polynomial-work execution.
The same program handles every feasible message dimension, including dimension one. -/
theorem quarter_gap_run_exact (delta : ℝ) (hquarter : (1 / 4 : ℝ) ≤ delta)
    (n k A : ℕ) (hn : 3 ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hA : agreementThreshold delta n k ≤ A) (hAn : A ≤ n) (hnq : n ≤ q)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    ∃ (hodd : q ≠ 2) (hL : (n / 2) * A ≤ q ^ 2)
      (out : List (List (ZMod q))) (cost : ℕ),
      run k 0 (n / 2) A (List.ofFn (fun i ↦ (domain i, received i))) hodd hL =
        (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ (SeparateSampleDecoder.sizePolynomial 26 + 294227) * q ^ 29 := by
  have hodd : q ≠ 2 := by omega
  have hL : (n / 2) * A ≤ q ^ 2 := by
    simpa only [pow_two] using
      Nat.mul_le_mul ((Nat.div_le_self n 2).trans hnq) (hAn.trans hnq)
  obtain ⟨interp, ic, hi, _hcert, _hic, _hne, _helig, _hjet, hweight, hchar, _hlocal⟩ :=
    OrderZeroDecoderCertificate.quarter_attempt_characteristic delta hquarter n k A hn hk hA
      (by simpa only [ringChar.eq (ZMod q) q] using hnq) domain received
  let found : AmbientSearchMachine.Output (ZMod q) := ⟨k - 1, interp⟩
  have hdispatch : (InterpolationDispatch.run k 0 (n / 2) A
      (List.ofFn (fun i ↦ (domain i, received i)))).1 = some found := by
    simp only [InterpolationDispatch.run, if_true, hi, Option.map_some, found]
  have hbelow : IsBelowCharacteristic (k - 1)
      (NonzeroInterpolationMachine.sourceOutput (d := 0) (k - 1) (n / 2) A interp) := by
    refine ⟨?_, hchar⟩
    rw [ringChar.eq (ZMod q) q]
    omega
  obtain ⟨out, cost, hr, ho, hb⟩ := run_exact_of_interpolation k 0 (n / 2) A domain received
    hodd hL found hdispatch (Nat.zero_le _) (by dsimp [found]; omega)
    (by dsimp [found]; omega) hnq hAn (Nat.div_le_self n 2) hbelow hweight
  refine ⟨hodd, hL, out, cost, hr, ho, ?_⟩
  have hmono := decoderFuel_one_le_two 0 (n / 2) q (Fact.out : q.Prime).pos
  have hcost : cost ≤ totalBudget k 0 (n / 2) A n q 2 := by
    unfold totalBudget
    split at hb <;> omega
  exact hcost.trans (budget_zero k (n / 2) A n q 2 (Fact.out : q.Prime).pos
    (Nat.div_le_self n 2) hAn hnq)

end ReedSolomon.ListDecoding.QuadraticDecoderMachine
