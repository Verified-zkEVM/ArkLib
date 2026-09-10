/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Bounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.AutomaticBounds
/-!
# First-order rate, slack, and finite-field probability bounds

Write `a₁(ρ)` for the first-order rate curve and set `a = a₁(ρ) + η₁`. For fixed physical
rate `0 < ρ < 1` and positive slack `η₁`, the automatic recipe gives a complete-list envelope
`C_Λ(ρ)n / η₁³` and an exact line-MCA exception envelope `C_E(ρ)n² / η₁⁵`.

The rate theorem chooses `ρ`, `η₁`, the code parameters, and the evaluation domain before the
received word or received line. Its list conclusion is uniform over every received word. For each
received line it chooses one exceptional set before quantifying over challenges and candidate
polynomials, and the recovered pair may depend on both.

The final theorem specializes to a finite field and a uniform affine-line challenge. Dividing the
exception count by `|F|` and capping at one gives the displayed MCA failure probability. The
complete-list and exact-agreement statements themselves remain valid over arbitrary fields.
-/

@[expose] public section

namespace ReedSolomon
open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

open Classical in
/-- Complete lists and exact line MCA at agreement `a = a₁(ρ) + η₁`.

The constants depend only on `ρ`. The list quantifier ranges over every received word after all
parameters and the field are fixed. The MCA quantifiers then range over received lines; each line
has one exceptional set that works for every nonexceptional challenge and qualifying polynomial.
-/
theorem automaticFirstOrder_rate_bounds
    (rho eta : ℝ) (n k A : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    /-

    The dimension and integer agreement threshold enforce the fixed physical rate
    and the requested agreement fraction.
    -/
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    /-

    Distinct evaluation points turn agreement into a count of distinct polynomial roots.
    -/
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨ max (k - 1)
      (automaticDerivativeCap rho (automaticFirstOrderThreshold rho + eta)) < ringChar F) :
    -- The cubic slack loss controls the complete list for every received word.
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          automaticLambdaBoundConstant rho * n / eta ^ 3) ∧
      /-

      The quintic slack loss controls one uniform exceptional set per received line.
      -/
      ∀ f g : Fin n → F, ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤ automaticExceptionBoundConstant rho * n ^ 2 / eta ^ 5 ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have ha : automaticFirstOrderThreshold rho < automaticFirstOrderThreshold rho + eta :=
    lt_add_of_pos_right _ heta
  obtain ⟨hlistBound, hexceptionBound⟩ := automaticHybridClosedBounds
    hrho hrhoOne heta haOne (by omega : 1 ≤ n) rfl hkRate hA
  obtain ⟨hlist, hmca⟩ := automaticFirstOrder_list_and_lineMCA rho
    (automaticFirstOrderThreshold rho + eta) n k A hrho hrhoOne ha haOne hn hk hkRate
    hA hAn domain hchar
  constructor
  · intro received
    obtain ⟨hf, hraw, hceil, hclosed⟩ := hlist received
    exact ⟨hf, hclosed.trans hlistBound⟩
  · intro f g
    obtain ⟨ex, hraw, hceil, hclosed, hgood⟩ := hmca f g
    exact ⟨ex, hclosed.trans hexceptionBound, hgood⟩

/-- Both rate-only constants are positive, so the cubic and quintic envelopes are nonvacuous. -/
theorem automaticFirstOrder_rate_constants_pos (rho : ℝ) :
    0 < automaticLambdaBoundConstant rho ∧ 0 < automaticExceptionBoundConstant rho := by
  have hC : 0 < automaticHybridEnvelopeConstant rho :=
    lt_of_lt_of_le zero_lt_one (one_le_automaticHybridEnvelopeConstant rho)
  unfold automaticLambdaBoundConstant automaticExceptionBoundConstant
  constructor <;> positivity

open Classical in
/-- The quintic exception envelope controls a uniform finite-field affine-line challenge.

The code and field are fixed before the affine-line generator samples its challenge. The exact
integer threshold is `A = ceil((a₁(ρ)+η₁)n)`. For each received line, the agreement theorem
gives one exceptional set of size at most `C_E(ρ)n²/η₁⁵`. Uniform sampling turns this count
into the ratio over `|F|`, and `min 1` records that a probability cannot exceed one. -/
theorem automaticFirstOrder_rate_mcaError_le
    (rho eta : ℝ) (n k : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    /-

    The dimension and integer agreement threshold enforce the fixed physical rate
    and the requested agreement fraction.
    -/
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    /-

    Distinct evaluation points turn agreement into a count of distinct polynomial roots.
    -/
    {F : Type} [Field F] [Fintype F] (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨ max (k - 1)
      (automaticDerivativeCap rho (automaticFirstOrderThreshold rho + eta)) < ringChar F) :
    mcaError (AffineLineGenerator F) (code domain k)
        (1 - (automaticFirstOrderThreshold rho + eta)) ≤
      min 1 (ENNReal.ofReal
        ((automaticExceptionBoundConstant rho * n ^ 2 / eta ^ 5) /
          (Fintype.card F : ℝ))) := by
  let a := automaticFirstOrderThreshold rho + eta
  let A := Nat.ceil (a * n)
  have hA : a * (n : ℝ) ≤ A := Nat.le_ceil _
  have hAn : A ≤ n := Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg n (α := ℝ)])
  have hline : LineExactAgreementBound domain k A
      (automaticExceptionBoundConstant rho * n ^ 2 / eta ^ 5) := by
    intro f g
    obtain ⟨ex, hcard, hgood⟩ := (automaticFirstOrder_rate_bounds rho eta n k A
      hrho hrhoOne heta haOne hn hk hkRate hA hAn domain hchar).2 f g
    refine ⟨ex, hcard, ?_⟩
    intro z hz P hP hagree
    obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP hagree
    refine ⟨pair.1, pair.2, hp0, hp1, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using heq
    · simpa [mappedDomain] using hset
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  have heq : (n : ℝ) * (1 - (1 - (automaticFirstOrderThreshold rho + eta))) =
      a * n := by dsimp only [a]; ring
  rw [heq]
end ReedSolomon
