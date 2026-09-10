/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.CapacityDecoderMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticDecoderLargeGap
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SmallBlock.SmallBlockDecoderProof
/-!
# Exact capacity decoding with an observed primitive-work bound

The integer-input program returns the physical list described by the agreement specification.
All rates, both field-size regimes, oversized thresholds, and the binary exceptional case are
covered. The gap determines only fixed program parameters and the coefficient. This is a
primitive-work theorem for this same execution, not the unfinished bit-RAM complexity theorem.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed-Solomon List Decoding up to Capacity at Every
  Rate*][DKTZ26], uniform capacity decoding and its reduced larger-field condition.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CapacityDecoderMachine

open HiddenDerivative PolynomialDifferential ReedSolomon
open SeparateSampleFieldExecution (ExactOutput)

/-- A gap-dependent coefficient covering positive-order, order-zero and exceptional executions. -/
def workCoefficient (d m : ℕ) : ℕ :=
  NonzeroInterpolationMachine.attemptBudget d m 1 1 +
    SeparateSampleDecoder.sizePolynomial (SeparateSampleDecoder.fixedSizeCoefficient d m) +
    90 * m + 911 + (SeparateSampleDecoder.sizePolynomial 26 + 294227) + 74

private theorem constant_bound (d m q e : ℕ) (hq : 0 < q) :
    74 ≤ workCoefficient d m * q ^ e := by
  have h1 : 1 ≤ q ^ e := Nat.one_le_pow _ _ hq
  have hc : 74 ≤ workCoefficient d m := by unfold workCoefficient; omega
  exact hc.trans (Nat.le_mul_of_pos_right _ h1)

variable {q : ℕ} [Fact q.Prime]

/-- A successful independently budgeted interpolation gives exact physical capacity output on
the nonexceptional positive-order branch. -/
theorem runWithBudget_exact_of_interpolation {n k d m J A : ℕ}
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hd : 0 < d) (hA : A ≤ n) (hn : 3 ≤ n) (hnq : n ≤ q)
    (hodd : q ≠ 2) (hL : m * A ≤ q ^ 2)
    (found : AmbientSearchMachine.Output (ZMod q))
    (hi : (InterpolationDispatch.runWithBudget k d m J A
      (List.ofFn (fun i ↦ (domain i, received i)))).1 = some found)
    (hdepth : d ≤ found.degree) (hk : k ≤ found.degree + 1)
    (hD : found.degree ≤ n)
    (hchar : IsBelowCharacteristic found.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d)
        found.degree m J A found.interpolant))
    (hweight : differentialWeightedDegree found.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d)
        found.degree m J A found.interpolant) < m * A) :
    ∃ out cost,
      runWithBudget n k d m J A (List.ofFn (fun i ↦ (domain i, received i))) =
        (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ InterpolationDispatch.budgetWithBudget k d m J A n +
        QuadraticAlgebra.SetupMachine.budget q (m * A) +
        QuadraticDecoderMachine.decoderFuelWithBudget d m J q
          (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) +
        16 * q + 152 := by
  obtain ⟨out, c, hr, he, hc⟩ :=
    QuadraticDecoderMachine.runWithBudget_exact_of_interpolation k d m J A domain received
      hodd hL found hi hdepth hk hD hnq hA hchar hweight
  have hmul : multiplicity n d m = m := by simp only [multiplicity, if_neg (by omega : d ≠ 0)]
  have hr' := runWithBudget_of_quadratic n k d m J A
    (List.ofFn (fun i ↦ (domain i, received i))) hA hn hodd
    (by simpa only [hmul] using hL) out c (by simpa only [hmul] using hr)
  exact ⟨out, c + 40, hr', he, by omega⟩

/-- Exactness of the executed exceptional branch, using the same physical coefficient lists. -/
theorem run_exact_of_small {n k A : ℕ} (d m : ℕ)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hsmall : n < A ∨ n ≤ 2)
    (hs : SmallBlockDecoderProof.CertifiedRun domain received k A) :
    ∃ out cost, run n k d m A (List.ofFn (fun i ↦ (domain i, received i))) =
      (some out, cost) ∧ ExactOutput domain received k A out ∧ cost ≤ 74 := by
  obtain ⟨out, c, steps, hr, _ht, _hsteps, hc, hn, hp, hpoly, hvec⟩ := hs
  exact ⟨out, c + 40, run_of_small n k d m A _ hsmall out c hr,
    ⟨hp, hn, hpoly, hvec⟩, by omega⟩

/-- The integer decoder succeeds at the paper's gap-only parameters, with the same observed
output and primitive cost satisfying both field-size regimes. This does not assert bit cost. -/
theorem run_exact (delta : ℝ) (hdelta : 0 < delta) (n k A : ℕ)
    (hblock : (if (1 / 4 : ℝ) ≤ delta then 1 else 8 * weightedSupportMultiplicity delta) ≤ n)
    (hk : 0 < k) (hkn : k ≤ n) (hnq : n ≤ q)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    let d := capacityDerivativeOrder delta
    let m := weightedSupportMultiplicity delta
    ∃ out cost, run n k d m A (List.ofFn (fun i ↦ (domain i, received i))) =
      (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ workCoefficient d m * q ^ (2 * d + 29) ∧
      (delta < (1 / 4 : ℝ) →
        2 * (m * A + d - weightedSupportAmbientDimension delta n k) ≤ q →
        cost ≤ workCoefficient d m * q ^ (d + 29)) := by
  let d := capacityDerivativeOrder delta
  let m := weightedSupportMultiplicity delta
  have hq : 0 < q := (Fact.out : q.Prime).pos
  by_cases hos : n < A
  · obtain ⟨out, cost, hr, he, hc⟩ := run_exact_of_small d m domain received (Or.inl hos)
      (SmallBlockDecoderProof.oversized_exact domain received hos)
    exact ⟨out, cost, hr, he, hc.trans (constant_bound d m q _ hq),
      fun _ _ ↦ hc.trans (constant_bound d m q _ hq)⟩
  have hAn : A ≤ n := by omega
  by_cases hquarter : (1 / 4 : ℝ) ≤ delta
  · have hd : d = 0 := capacityDerivativeOrder_eq_zero hquarter
    by_cases hsmall : n ≤ 2
    · have hs : SmallBlockDecoderProof.CertifiedRun domain received k A := by
        have hn : n = 1 ∨ n = 2 := by omega
        rcases hn with rfl | rfl
        · exact SmallBlockDecoderProof.one_exact delta hdelta k A hk hA domain received
        · exact SmallBlockDecoderProof.two_quarter_exact delta hquarter k A hk hA domain received
      obtain ⟨out, cost, hr, he, hc⟩ := run_exact_of_small d m domain received (Or.inr hsmall) hs
      exact ⟨out, cost, hr, he, hc.trans (constant_bound d m q _ hq),
        fun h _ ↦ (not_lt_of_ge hquarter h).elim⟩
    · obtain ⟨hodd, hL, out, c, hr, he, hc⟩ := QuadraticDecoderMachine.quarter_gap_run_exact
        delta hquarter n k A (by omega) hk hkn hA hAn hnq domain received
      have hmul : multiplicity n d m = n / 2 := by simp only [multiplicity, hd, if_true]
      have hr' := run_of_quadratic n k d m A
        (List.ofFn (fun i ↦ (domain i, received i))) hAn (by omega) hodd
        (by simpa only [hmul] using hL) out c
        (by simpa only [hd, multiplicity, if_true] using hr)
      refine ⟨out, c + 40, hr', he, ?_, fun h _ ↦ (not_lt_of_ge hquarter h).elim⟩
      have h1 : 1 ≤ q ^ 29 := Nat.one_le_pow _ _ hq
      change c + 40 ≤ workCoefficient d m * q ^ (2 * d + 29)
      simp only [hd, Nat.mul_zero, Nat.zero_add]
      unfold workCoefficient
      nlinarith only [hc, h1]
  · have hsmall : delta < (1 / 4 : ℝ) := lt_of_not_ge hquarter
    have hd : 0 < d := by
      dsimp only [d]
      rw [capacityDerivativeOrder_eq_ceil hsmall]
      exact Nat.ceil_pos.mpr (Real.exp_pos _)
    have hm : 0 < m := weightedSupportMultiplicity_pos hdelta hsmall
    have hn : 8 * m ≤ n := by simpa only [if_neg hquarter] using hblock
    obtain ⟨hodd, hL, out, c, hr, he, hc, hlarge⟩ :=
      QuadraticDecoderMachine.small_gap_run_exact delta hdelta hsmall n k A hn hk hkn
        hA hAn hnq domain received
    have hmul : multiplicity n d m = m := by simp only [multiplicity, if_neg (by omega : d ≠ 0)]
    have hr' := run_of_quadratic n k d m A
      (List.ofFn (fun i ↦ (domain i, received i))) hAn (by omega) hodd
      (by simpa only [hmul] using hL) out c (by simpa only [hmul] using hr)
    have hcost (e : ℕ) (he2 : e ≤ 2)
        (hc' : c ≤ QuadraticDecoderMachine.totalBudget k d m A n q e) :
        c + 40 ≤ workCoefficient d m * q ^ (e * d + 29) := by
      have hb := hc'.trans (QuadraticDecoderMachine.budget_fixed k d m A n q e hd hq hAn hnq)
      have he : q ^ (e * (d + 2) + 10) ≤ q ^ (e * d + 29) := by
        apply Nat.pow_le_pow_right hq
        nlinarith
      have hb' := hb.trans (Nat.mul_le_mul_left _ he)
      have h1 : 1 ≤ q ^ (e * d + 29) := Nat.one_le_pow _ _ hq
      unfold workCoefficient
      nlinarith only [hb', h1]
    refine ⟨out, c + 40, hr', he, hcost 2 le_rfl hc, ?_⟩
    intro _hsmall hfield
    simpa only [one_mul] using hcost 1 (by decide) (hlarge hfield)

end ReedSolomon.ListDecoding.CapacityDecoderMachine
