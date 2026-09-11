/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Certificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.RateHeight
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Bound
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.SupportGuards
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.FiniteParameters

/-! # Rate-dependent curve certificates from the strict partition gate -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open Polynomial PolynomialDifferential

universe u

/-- The actual finite ratio constructs a curve equation with any certified independent jet cap. -/
theorem exists_ratePartitionFinite_certificate {F : Type u} [Field F]
    {R a γ : ℝ} {D d m n k A ℓ ν : ℕ}
    (hD : 0 < D) (hd : 500 ≤ d) (hm : 0 < m) (hn : 0 < n)
    (hR : 0 < R) (ha : 0 < a) (hW : 0 < ratePartitionWeight R a d m)
    (hkD : k ≤ D + 1) (hDn : (D : ℝ) ≤ R * n) (haA : a * n ≤ A)
    (domain : Fin n ↪ F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (hdegree : ∀ u, RatePartitionEligible D d (ratePartitionWeight R a d m)
      (m * A : ℕ) u → totalJetDegree u ≤ ν)
    (hγ : 1 < γ) (hγle : γ ≤ ratePartitionFiniteRatio R a d m) :
    Nonempty (SymbolicReceivedCurve.Certificate.{u, u} F A k ℓ ν d
      (ℓ * ratePartitionHeight ν γ) domain w) := by
  let W := ratePartitionWeight R a d m
  let r := n * ratePartitionRankBound d m W
  let N := (ratePartitionExponents D d W (m * A : ℕ) hD).card
  have hA : 0 < A := by
    have h : (0 : ℝ) < A := (mul_pos ha (by exact_mod_cast hn)).trans_le haA
    exact_mod_cast h
  have hs := ratePartition_dimension_gt_finiteRatio hD hd hm hn hR ha hW hDn haA
  have hs' : ratePartitionFiniteRatio R a d m * r < N := by
    simpa only [r, N, W, Nat.cast_mul, mul_assoc] using hs
  have hmargin : γ * r < N :=
    (mul_le_mul_of_nonneg_right hγle (Nat.cast_nonneg r)).trans_lt hs'
  have hsurplus : r < N := by
    have : (r : ℝ) < N := by nlinarith [Nat.cast_nonneg r (α := ℝ)]
    exact_mod_cast this
  obtain ⟨cert⟩ := SymbolicReceivedCurve.exists_ratePartition_certificate.{u, u}
    (k := k) hD (le_refl ((m * A : ℕ) : ℝ)) (mul_pos hm hA)
    hkD domain w hw hdegree hsurplus
  have hheight := SymbolicReceivedCurve.kernel_height_le_ratePartitionHeight
    (ℓ := ℓ) (ν := ν) hγ hmargin
  exact ⟨{ cert with challengeDegree_le := fun u ↦ (cert.challengeDegree_le u).trans hheight }⟩

/-- Rate parameters construct a curve certificate before any characteristic restriction. -/
theorem exists_ratePartitionRate_certificate {F : Type u} [Field F]
    {R a : ℝ} {d n k A ℓ : ℕ} (p : RatePartitionFiniteParameters R a d)
    (hR : 0 < R) (hRone : R < 1) (ha : 0 < a) (hd : 500 ≤ d)
    (hn : ratePartitionLength R d p.multiplicity ≤ n)
    (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ) :
    Nonempty (SymbolicReceivedCurve.Certificate.{u, u} F A k ℓ
      (ratePartitionJetBound R p.multiplicity) d
      (ℓ * ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
        (ratePartitionFiniteRatio R a d p.multiplicity)) domain w) := by
  obtain ⟨hdD, hDlower, hkD, hDn, hνn, hmn, hceil, hn2⟩ :=
    ratePartition_length_guards hR hRone hn hkR haA
  have hD : 0 < ⌊R * n⌋₊ := by omega
  exact exists_ratePartitionFinite_certificate hD hd p.multiplicity_pos (by omega)
    hR ha p.weight_pos (hkD.trans (Nat.le_succ _)) (Nat.floor_le (by positivity)) haA
    domain w hw (fun _ hu ↦ ratePartition_totalJetDegree_le hD hR hDlower hAn hu)
    p.ratio_gt_one le_rfl

/-- The mathematical rate threshold constructs the same certificate without changing the
conservative length recipe used by the executable decoder. -/
theorem exists_ratePartitionMathematical_certificate {F : Type u} [Field F]
    {R a : ℝ} {d n k A ℓ : ℕ} (p : RatePartitionFiniteParameters R a d)
    (hR : 0 < R) (hRone : R < 1) (ha : 0 < a) (hd : 500 ≤ d)
    (hn : ratePartitionMathematicalLength R d p.multiplicity ≤ n)
    (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ) :
    Nonempty (SymbolicReceivedCurve.Certificate.{u, u} F A k ℓ
      (ratePartitionJetBound R p.multiplicity) d
      (ℓ * ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
        (ratePartitionFiniteRatio R a d p.multiplicity)) domain w) := by
  obtain ⟨hdD, hDlower, hkD, hDn, hνn, hmn, hceil, hn2⟩ :=
    ratePartition_mathematical_length_guards hR hRone (by omega) hn hkR haA
  have hD : 0 < ⌊R * n⌋₊ := by omega
  exact exists_ratePartitionFinite_certificate hD hd p.multiplicity_pos (by omega)
    hR ha p.weight_pos (hkD.trans (Nat.le_succ _)) (Nat.floor_le (by positivity)) haA
    domain w hw (fun _ hu ↦ ratePartition_totalJetDegree_le hD hR hDlower hAn hu)
    p.ratio_gt_one le_rfl

end ReedSolomon.HiddenDerivative
