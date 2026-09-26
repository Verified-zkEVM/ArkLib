/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveCertificate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Capacity
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupportCertificate
import ArkLib.Data.Polynomial.Differential.WitnessCount

/-!
# Prescribed parameters for correlated-agreement charts

The prescribed weighted-support construction gives a symbolic received-curve certificate and
size bounds for its Taylor parameters. A characteristic bound by the block length supplies all
binomial pivots below the block length.

## Main statements

* `ReedSolomon.exists_prescribed_correlated_parameters`: a certificate and its parameter bounds.

## References

* [DKT26]
-/

@[expose] public section

open ReedSolomon.HiddenDerivative.WeightedSupportParameters

namespace ReedSolomon

open HiddenDerivative

universe u

private theorem binomial_pivots_below_of_characteristic {F : Type*} [Field F]
    {n : ℕ} (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∀ r i, r < i → i < n → (i.choose r : F) ≠ 0 := by
  intro r i hri hi
  have hn : 0 < n := by omega
  have hchar' : ringChar F = 0 ∨ n - 1 < ringChar F := by
    rcases hchar with hzero | hpos
    · exact Or.inl hzero
    · exact Or.inr (by omega)
  have hk : 0 < i - r := by omega
  have hs : i - r + r ≤ n - 1 := by omega
  have hchoose := PolynomialDifferential.natCast_choose_ne_zero_of_ringChar
    (F := F) (D := n - 1) (s := r) hchar' (i - r) hk hs
  simpa [Nat.sub_add_cancel hri.le] using hchoose

/-- Prescribed interpolation parameters give a certificate and the associated size bounds. -/
theorem exists_prescribed_correlated_parameters {F : Type u} [Field F]
    (δ : ℝ) (n k : ℕ) (centers : Fin n ↪ F) (f g : Fin n → F)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n)
    (hA : capacityAgreementThreshold δ n k ≤ n)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    let A := capacityAgreementThreshold δ n k
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let ν := 2 * m - 1
    Nonempty (SymbolicReceivedCurve.Certificate A k 1 ν d (12 * ν - 1) centers
      (fun i : Fin n => receivedLine (f i) (g i))) ∧
      0 < n ∧ 0 < ν ∧ ν < n ∧ d < n ∧ k ≤ n ∧ k ≤ A ∧
      (k : ℝ) + δ * n ≤ A ∧
      ∀ r i, r < i → i < n → (i.choose r : F) ≠ 0 := by
  dsimp only
  obtain ⟨hn, _hm, hν, _hνm, hνn, hdK, hkK, hKn, hkA, hgap⟩ :=
    prescribed_geometric_parameters δ n k hδ hδ' hblock hA
  exact ⟨exists_prescribed_symbolic_weightedSupport_certificate δ n k centers f g
      hδ hδ' hblock hA,
    hn, hν, hνn, hdK.trans_le hKn, hkK.trans hKn, hkA, hgap,
    binomial_pivots_below_of_characteristic hchar⟩

end ReedSolomon
