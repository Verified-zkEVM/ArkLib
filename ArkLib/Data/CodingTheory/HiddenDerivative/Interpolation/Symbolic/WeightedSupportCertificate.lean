/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveCertificate
public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveSupportCertificate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Margin
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Block
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.DimensionInputs
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold

/-!
# Weighted-support certificate constructions

This module constructs certificates for received lines using the symbolic curve certificate API.
The weighted-support interpolation construction imposes local constraints at every received point;
a strict dimension surplus yields challenge-degree and jet-degree bounds, and prescribed rate
parameters provide the surplus for the certificate construction.

## Main statements

* `exists_weightedSupport_certificate_of_fixed_margin`: construction from a weighted-support
  dimension surplus.
* `exists_weightedSupport_certificate_of_rate` and
  `exists_prescribed_symbolic_weightedSupport_certificate`: the rate-parameter constructions.

## References

* [DKTZ26], Section 5.1, Corollary 5.3
-/

@[expose] public section

open Polynomial PolynomialDifferential
open MvPolynomial
open ReedSolomon.HiddenDerivative.WeightedSupportParameters
open scoped BigOperators

noncomputable section

namespace ReedSolomon.HiddenDerivative

/-- A strict weighted-support surplus constructs a certificate for any received line. -/
theorem exists_weightedSupport_certificate_of_fixed_margin {F : Type*} [Field F]
    {D d W m : ℕ} {ι : Type*} [Fintype ι] {A k : ℕ} {g₀ : ℝ}
    (hD : 0 < D) (hg₁ : g₀ ≤ 1) (hm : 0 < m)
    (hL : (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    (hkD : k ≤ D + 1) (centers : ι ↪ F) (f g : ι → F)
    (hmargin : (543 / 500 : ℝ) * Fintype.card ι * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := (D : ℝ) * m * (1 + g₀)) m hD 0 0)) <
      Module.finrank F
        (weightedSupportSpace F D d W ((D : ℝ) * m * (1 + g₀)) hD)) :
    Nonempty (SymbolicReceivedCurve.Certificate A k 1 (2 * m - 1) d
      (12 * (2 * m - 1) - 1) centers (fun i => receivedLine (f i) (g i))) := by
  simpa only [Nat.one_mul] using
    (SymbolicReceivedCurve.exists_certificate_of_fixed_margin
      (d := d) (D := D) (m := m) (W := W) (A := A) (k := k) (ℓ := 1)
      hD hg₁ hm (by norm_num) hL hbudget hkD centers
      (fun i => receivedLine (f i) (g i))
      (fun i => natDegree_receivedLine_le (f i) (g i)) hmargin)

/-- The prescribed rate interval constructs a certificate with challenge degree below
`12 (2 m - 1)` and total jet degree at most `2 m - 1`. -/
theorem exists_weightedSupport_certificate_of_rate {F : Type*} [Field F]
    (δ : ℝ) (n D A k : ℕ) (centers : Fin n ↪ F) (f g : Fin n → F)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hn : 0 < n) (hD : 0 < D)
    (hρlo : δ / 3 ≤ (D : ℝ) / n) (hρhi : (D : ℝ) / n ≤ 1 - δ)
    (hkD : k ≤ D + 1)
    (hslack : (D : ℝ) * (1 + rateGap δ ((D : ℝ) / n)) ≤ A) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    Nonempty (SymbolicReceivedCurve.Certificate A k 1 (2 * m - 1) d
      (12 * (2 * m - 1) - 1) centers (fun i => receivedLine (f i) (g i))) := by
  simpa only [Nat.one_mul] using
    (SymbolicReceivedCurve.exists_weightedSupport_certificate_of_rate (F := F)
      δ n D A k 1 centers (fun i => receivedLine (f i) (g i))
      (fun i => natDegree_receivedLine_le (f i) (g i)) (by norm_num) hδ hδmax hn hD
      hρlo hρhi hkD hslack)

/-- The prescribed block threshold constructs a uniformly nonvanishing line certificate. -/
theorem exists_prescribed_symbolic_weightedSupport_certificate {F : Type*} [Field F]
    (δ : ℝ) (n k : ℕ) (centers : Fin n ↪ F) (f g : Fin n → F)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n)
    (hA : ReedSolomon.agreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    Nonempty (SymbolicReceivedCurve.Certificate (ReedSolomon.agreementThreshold δ n k) k 1
      (2 * m - 1) d (12 * (2 * m - 1) - 1) centers
      (fun i => receivedLine (f i) (g i))) := by
  simpa only [Nat.one_mul] using
    (SymbolicReceivedCurve.exists_prescribed_certificate (F := F) δ n k 1 centers
      (fun i => receivedLine (f i) (g i))
      (fun i => natDegree_receivedLine_le (f i) (g i)) (by norm_num) hδ hδmax hblock hA)

end ReedSolomon.HiddenDerivative
