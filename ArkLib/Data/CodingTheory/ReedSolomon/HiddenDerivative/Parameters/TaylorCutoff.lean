/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.SupportCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Block
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Harmonic
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TotalJetDegreeRootCount
/-! # Prescribed weighted-support parameters for the geometric list count -/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon
open HiddenDerivative

/-- The prescribed weighted-support parameters admit a Taylor cutoff at most n and a total
jet degree strictly below n, exactly as required by geometric counting. -/
theorem prescribed_geometric_parameters
    (δ : ℝ) (n k : ℕ) (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((27 / 10) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((27 / 10) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) :
    let A := agreementThreshold δ n k
    let d := Nat.ceil (Real.exp ((27 / 10) / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
    let ν := 2 * m - 1
    let K := max k (Nat.floor (δ * n / 2))
    0 < n ∧ 0 < m ∧ 0 < ν ∧ ν ≤ 2 * m ∧ ν < n ∧
      d < K ∧ k ≤ K ∧ K ≤ n ∧ k ≤ A ∧ (k : ℝ) + δ * n ≤ A := by
  let d := Nat.ceil (Real.exp ((27 / 10) / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let K := max k (Nat.floor (δ * n / 2))
  have hb := WeightedSupportParameters.prescribedBlockBounds δ n k hδ hδ' hk
    (by simpa only [WeightedSupportParameters.xi, harmonicNumber_eq_harmonic] using hblock)
    hA
  obtain ⟨hn, hD, hdD, _, _, hKn, _⟩ := hb
  have ho := WeightedSupportParameters.prescribed_order_lower δ hδ hδ'.le
  have hH : 0 < harmonicNumber (d - 1) := by
    rw [harmonicNumber_eq_harmonic]
    exact (div_pos (show (0 : ℝ) < 27 / 10 by norm_num) hδ).trans_le ho.2.2
  have hd : 0 < d := by
    have hh := ho.1
    change 48000 ≤ d at hh
    omega
  have hmR : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) (Nat.le_ceil _)
  have hm : 0 < m := Nat.cast_pos.mp hmR
  have hdK : d < K := by
    have hh : d < K - 1 := hdD
    omega
  have hkK : k ≤ K := Nat.le_max_left _ _
  have hkA : k ≤ agreementThreshold δ n k := Nat.le_add_right _ _
  have hgap : (k : ℝ) + δ * n ≤ agreementThreshold δ n k :=
    (agreementThreshold_le_iff_real hδ.le n k _).mp le_rfl
  have hblock' : 8 * m ≤ n := hblock
  have hν : 0 < 2 * m - 1 := by omega
  have hνn : 2 * m - 1 < n := by omega
  exact ⟨hn, hm, hν, Nat.sub_le _ _, hνn, hdK, hkK, hKn, hkA, hgap⟩

/-- The exact characteristic threshold for the prescribed geometric argument supplies its two
independent uses: the total jet cap for separant descent and every binomial pivot below `K`.
Characteristic zero remains an explicit branch. -/
theorem geometric_characteristic_components {F : Type*} [Field F] {K ν : ℕ}
    (hK : 0 < K) (hchar : ringChar F = 0 ∨ max (K - 1) ν < ringChar F) :
    (ringChar F = 0 ∨ ν < ringChar F) ∧
      (ringChar F = 0 ∨ K ≤ ringChar F) := by
  constructor
  · exact hchar.imp_right (fun hc ↦ (Nat.le_max_right (K - 1) ν).trans_lt hc)
  · apply hchar.imp_right
    intro hc
    have hpred : K - 1 < ringChar F := (Nat.le_max_left (K - 1) ν).trans_lt hc
    omega

/-- The positive-characteristic contract follows from the prescribed total jet
cap and a field characteristic at least n. -/
theorem geometric_below_characteristic {F : Type*} [Field F] {d n k ν : ℕ}
    (Q : DifferentialPolynomial F d) (hk : 0 < k) (hkn : k ≤ n)
    (hνn : ν < n) (hdegree : jetTotalDegree Q ≤ ν) (hchar : n ≤ ringChar F) :
    IsBelowCharacteristic (k - 1) Q := by
  refine ⟨by omega, ?_⟩
  intro j
  exact (jetDegree_le_total Q j).trans_lt
    (hdegree.trans_lt (hνn.trans_le hchar))

end ReedSolomon
