/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.FiniteRateParameters
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RoundedCounts
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Symbolic
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveCertificate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.SymbolicRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ColumnHeight
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# First-order rate certificates

A finite first-order rate choice with strict source surplus gives a symbolic interpolation
certificate over every field. Its challenge degree is fixed by the finite rate choice and does not
depend on the block length, ambient degree, agreement threshold, or received line.

## Main statements

* `FirstOrderFiniteRateParameters.rankCount_mul_lt_dimensionCount` transfers strict finite rate
  surplus to a strict surplus over the first-order interpolation dimension.
* `FirstOrderFiniteRateParameters.kernelHeight_le_challengeDegree` bounds the scaled kernel height
  by the challenge degree selected by the finite rate choice.
* `exists_firstOrderRate_symbolicCertificate` constructs a first-order symbolic certificate from
  rate-compatible block parameters.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {rate agreement : ℝ} (p : FirstOrderFiniteRateParameters rate agreement)

/-- A strict finite rate surplus remains strict after scaling by every positive block length and
is bounded above by the corresponding first-order interpolation dimension. -/
theorem FirstOrderFiniteRateParameters.rankCount_mul_lt_dimensionCount
    {n D A : ℕ} (hn : 0 < n)
    (hD : (D : ℝ) ≤ rate * n) (hA : agreement * n ≤ A) :
    n * p.rankCount <
      firstOrderDimensionCount D A p.multiplicity p.derivativeCap p.jetDegree := by
  have hlower := firstOrderSourceCount_mul_le_firstOrderDimensionCount
    (rate := rate) (agreement := agreement) (m := p.multiplicity)
    (M := p.derivativeCap) (mu := p.jetDegree) hD hA
  have hstrict : ((n * p.rankCount : ℕ) : ℝ) < n * p.sourceCount := by
    push_cast
    exact mul_lt_mul_of_pos_left p.sourceCount_gt_rankCount (Nat.cast_pos.mpr hn)
  exact_mod_cast hstrict.trans_le hlower

/-- The block-dependent kernel-height quotient is bounded by the challenge degree of the finite
rate choice. -/
theorem FirstOrderFiniteRateParameters.kernelHeight_le_challengeDegree
    {n D A : ℕ} (hD : (D : ℝ) ≤ rate * n) (hA : agreement * n ≤ A) :
    let N := firstOrderDimensionCount D A p.multiplicity p.derivativeCap p.jetDegree
    n * p.rankCount * p.jetDegree / (N - n * p.rankCount) ≤ p.challengeDegree := by
  dsimp only
  have hlower := firstOrderSourceCount_mul_le_firstOrderDimensionCount
    (rate := rate) (agreement := agreement) (m := p.multiplicity)
    (M := p.derivativeCap) (mu := p.jetDegree) hD hA
  have hheight := scaledKernelHeight_le_floor
    (n := n) (N := firstOrderDimensionCount D A p.multiplicity p.derivativeCap p.jetDegree)
    (r := p.rankCount) (mu := p.jetDegree) (N₀ := p.sourceCount)
    p.sourceCount_gt_rankCount hlower
  simpa [FirstOrderFiniteRateParameters.challengeDegree, firstOrderRateChallengeDegree,
    FirstOrderFiniteRateParameters.rankCount, FirstOrderFiniteRateParameters.sourceCount,
    FirstOrderFiniteRateParameters.derivativeCap, FirstOrderFiniteRateParameters.jetDegree]
    using hheight.trans (Nat.le_max_right 1 _)

/-- A finite first-order rate choice constructs, over every field, a primitive symbolic
interpolant with bounded support and coefficient degree at most its fixed challenge degree. -/
theorem exists_firstOrderRate_symbolicCertificate
    {F : Type*} [Field F] {n D A k : ℕ}
    (hn : 0 < n) (hD : 0 < D) (hbudget : 0 < p.multiplicity * A)
    (hkD : k ≤ D + 1) (hDrate : (D : ℝ) ≤ rate * n)
    (hArate : agreement * n ≤ A)
    (centers : Fin n ↪ F) (f g : Fin n → F) :
    Nonempty (FirstOrderSymbolicCertificate (F := F)
      D A p.multiplicity p.derivativeCap p.jetDegree k p.challengeDegree centers f g
      (firstOrderColumns (D := D) (A := A) (m := p.multiplicity)
        (M := p.derivativeCap) (μ := p.jetDegree))) := by
  let m := p.multiplicity
  let M := p.derivativeCap
  let μ := p.jetDegree
  let h := p.challengeDegree
  let N := (firstOrderExponents D A m M μ).card
  let r := n * p.rankCount
  let columns := firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)
  let w : Fin n → F[X] := fun i ↦ receivedLine (f i) (g i)
  have hN : N = firstOrderDimensionCount D A m M μ := by
    simpa [N] using (card_firstOrderExponents (D := D) (A := A) (m := m)
      (M := M) (μ := μ) hD)
  have hrN : r < N := by
    rw [hN]
    exact p.rankCount_mul_lt_dimensionCount hn hDrate hArate
  have hy₀ : ∀ j, (columns j).y₀ ≤ μ := by
    intro j
    rw [← SourceColumn.exponent_zero]
    exact firstOrder_y₀_le_μ (firstOrderColumns_eligible
      (D := D) (A := A) (m := m) (M := M) (μ := μ) j)
  have hw : ∀ i, (w i).natDegree ≤ 1 := fun i ↦ natDegree_receivedLine_le (f i) (g i)
  have hrank :
      ((localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w columns).map
        (algebraMap F[X] (RatFunc F))).rank ≤ r := by
    calc
      _ ≤ n * certifiedEnlargedRankBound 1 m M 0 := by
        simpa only [Fintype.card_fin] using
          rank_firstOrderLocalConstraintMatrix_le (D := D) (A := A) (m := m) (M := M)
            (μ := μ) (fun i ↦ centers i) w columns
            (fun j ↦ firstOrderColumns_eligible
              (D := D) (A := A) (m := m) (M := M) (μ := μ) j)
      _ = r := by
        rw [certifiedEnlargedRankBound_one_eq_firstOrderRankCount]
        rfl
  have hrN' : r < Fintype.card (Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) := by
    simpa [N, Fintype.card_coe] using hrN
  obtain ⟨v, _hv, hvdegree, hprimitive, hnonzero, hconstraints⟩ :=
    exists_primitive_interpolant_of_rank_le m 1 μ (fun i ↦ centers i) w hw columns
      firstOrderColumns_injective hy₀ (algebraMap F[X] (RatFunc F))
      (IsFractionRing.injective F[X] (RatFunc F)) hrank hrN'
  let Q : DifferentialPolynomial F[X] 1 := SourceColumn.interpolant columns v
  have hheight : r * μ / (N - r) ≤ h := by
    rw [hN]
    exact p.kernelHeight_le_challengeDegree hDrate hArate
  have hvheight : ∀ j, (v j).natDegree ≤ h := by
    intro j
    apply (hvdegree j).trans
    simpa [N] using hheight
  have hQsupport : Q ∈ firstOrderSpace F[X] D A m M μ :=
    interpolant_mem_firstOrderSpace columns firstOrderColumns_eligible v
  have hfirstJet : ∀ u ∈ Q.support, firstJetExponent u ≤ M := by
    intro u hu
    exact (mem_firstOrderSpace_iff.mp hQsupport u hu).1
  have htotalJet : ∀ u ∈ Q.support, totalJetDegree u ≤ μ := by
    intro u hu
    exact (mem_firstOrderSpace_iff.mp hQsupport u hu).2.1
  refine ⟨⟨v, Q, rfl, hprimitive,
    SourceColumn.coeff_interpolant_natDegree_le columns firstOrderColumns_injective v hvheight,
    hQsupport, hfirstJet, htotalJet, hconstraints, ?_⟩⟩
  intro E _ ι z
  refine ⟨hnonzero (Polynomial.eval₂RingHom ι z), ?_⟩
  intro indices P hPdegree hcard hagreements
  have hagreeCurve : ∀ i ∈ indices,
      P.eval (ι (centers i)) = (w i).eval₂ ι z := by
    intro i hi
    rw [hagreements i hi]
    simp [w, receivedLine]
    ring
  exact differentialSpecialization_eq_zero_of_firstOrderSpace
    hkD hbudget centers w Q hQsupport hconstraints ι z indices P hPdegree hcard hagreeCurve

end

end ReedSolomon.HiddenDerivative
