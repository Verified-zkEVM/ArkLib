/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybrid
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Bounds
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.AutomaticBounds

/-!
# First-order rate, slack, and finite-field probability bounds

Write `a₁(ρ)` for the first-order rate threshold and set `a = a₁(ρ) + η₁`. For a fixed physical
rate `0 < ρ < 1` and positive slack `η₁`, the automatic recipe gives a complete-list envelope
`C_Λ(ρ) n / η₁³` and an exact line-agreement exception envelope `C_E(ρ) n² / η₁⁵`.

The rate theorem fixes `ρ`, `η₁`, the code parameters, and the evaluation domain before the
received word or received line. Its list conclusion is uniform over every received word. For each
received line it chooses one exceptional set before quantifying over challenges and candidate
polynomials, and the recovered pair may depend on both.

Over a finite field with a uniform affine-line challenge, dividing the exception count by `|F|`
and capping at one bounds the mutual correlated agreement error.

## Main statements

* `ReedSolomon.automaticFirstOrder_rate_bounds`: the cubic list envelope and the quintic
  exception envelope over an arbitrary field.
* `ReedSolomon.automaticFirstOrder_rate_mcaError_le`: the line MCA error over a finite field.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode

open Classical in
/-- Complete lists and exact line agreement at agreement `a = a₁(ρ) + η₁`.

The constants depend only on `ρ`. The list quantifier ranges over every received word after all
parameters and the field are fixed. The agreement quantifiers then range over received lines;
each line has one exceptional set that works for every nonexceptional challenge and qualifying
polynomial. -/
theorem automaticFirstOrder_rate_bounds
    (rho eta : ℝ) (n k A : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    /-

    The dimension and integer agreement threshold enforce the fixed physical rate
    and the requested agreement fraction.
    -/
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    /-

    Distinct evaluation points turn agreement into a count of distinct polynomial roots.
    -/
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨ max (k - 1)
      (automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)) < ringChar F) :
    -- The cubic slack loss controls the complete list for every received word.
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          automaticListBoundConstant rho * n / eta ^ 3) ∧
      /-

      The quintic slack loss controls one uniform exceptional set per received line.
      -/
      ∀ f g : Fin n → F, ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤ automaticExceptionBoundConstant rho * n ^ 2 / eta ^ 5 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have ha : firstOrderRateThreshold rho < firstOrderRateThreshold rho + eta :=
    lt_add_of_pos_right _ heta
  obtain ⟨hlistBound, hexceptionBound⟩ := automaticClosedListAndExceptionBounds
    hrho hrhoOne heta haOne (by omega : 1 ≤ n) rfl hkRate hA
  refine ⟨fun received ↦ ?_, fun f g ↦ ?_⟩
  · obtain ⟨hfinite, -, -, hclosed⟩ := automaticFirstOrder_closePolynomialSet_finite_and_card_le
      hrho hrhoOne ha haOne hn rfl hk hkRate hA hAn domain received hchar
    exact ⟨hfinite, hclosed.trans hlistBound⟩
  · obtain ⟨-, -, -, -, -, -, exceptional, -, -, hclosed, hgood⟩ :=
      exists_automaticFirstOrder_hybridEquation_base hrho hrhoOne ha haOne hn rfl hk hkRate hA
        hAn hchar domain f g
    exact ⟨exceptional, hclosed.trans hexceptionBound, hgood⟩

/-- The quintic exception envelope controls a uniform finite-field affine-line challenge.

The code and field are fixed before the affine-line generator samples its challenge. The integer
threshold is `A = ⌈(a₁(ρ) + η₁) n⌉₊`. For each received line, the agreement theorem gives one
exceptional set of size at most `C_E(ρ) n² / η₁⁵`. Uniform sampling turns this count into the
ratio over `|F|`, and `min 1` records that a probability cannot exceed one. -/
theorem automaticFirstOrder_rate_mcaError_le
    (rho eta : ℝ) (n k : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    /-

    The dimension and the rate guard enforce the fixed physical rate.
    -/
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    /-

    Distinct evaluation points turn agreement into a count of distinct polynomial roots.
    -/
    {F : Type} [Field F] [Fintype F] [SampleableType F] (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨ max (k - 1)
      (automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)) < ringChar F) :
    mcaError (AffineLineGenerator F) (code domain k)
        (1 - (firstOrderRateThreshold rho + eta)) ≤
      min 1 (ENNReal.ofReal
        ((automaticExceptionBoundConstant rho * n ^ 2 / eta ^ 5) / Fintype.card F)) := by
  classical
  have hA : (firstOrderRateThreshold rho + eta) * n ≤
      (⌈(firstOrderRateThreshold rho + eta) * n⌉₊ : ℝ) := Nat.le_ceil _
  have hAn : ⌈(firstOrderRateThreshold rho + eta) * n⌉₊ ≤ n :=
    Nat.ceil_le.mpr (mul_le_of_le_one_left (Nat.cast_nonneg n) haOne.le)
  have hthreshold : ⌈(firstOrderRateThreshold rho + eta) * n⌉₊ ≤
      ⌈(Fintype.card (Fin n) : ℝ) * (1 - (1 - (firstOrderRateThreshold rho + eta)))⌉₊ := by
    rw [Fintype.card_fin, sub_sub_cancel, mul_comm]
  exact mcaError_affineLine_le_min_one_of_exactAgreement domain _
    (lineExactAgreementBound_of_exactCorrelatedPair domain _
      (automaticFirstOrder_rate_bounds rho eta n k _ hrho hrhoOne heta haOne hn hk hkRate hA hAn
        domain hchar).2) _ hthreshold

end ReedSolomon
