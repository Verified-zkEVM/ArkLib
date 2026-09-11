/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.UniformRate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.GuardedUniform

/-!
# Archived guarded `1.489` uniform Reed--Solomon list bound

This library-only comparison replaces the headline derivative order by the minimum of the
headline `1.5` order and the guarded `1.489` order. The canonical manuscript no longer includes
this optional refinement. It retains the mathematical 300-based multiplicity and makes no claim
about the separately retained executable selector.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- The archived guarded parameters bound the complete close-polynomial set over any field whose
positive characteristic is at least the block length. -/
theorem guardedUniformRatePartition_close_list_bound {F : Type u} [Field F]
    {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ)
    (hδsmall : δ < 6 / 25)
    (hn : guardedRatePartitionLength δ ≤ n)
    (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n)
    (domain : Fin n ↪ F)
    (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (guardedRatePartitionJetBound δ : ℝ) ^ 2 *
          (2 * guardedRatePartitionJetBound δ / δ) ^ guardedRatePartitionOrder δ *
          n ^ guardedRatePartitionOrder δ := by
  obtain ⟨e⟩ := exists_guardedRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  have hd := guardedRatePartitionOrder_ge_519 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hm : 0 < guardedRatePartitionMultiplicity δ :=
    lt_of_lt_of_le (by omega) (ratePartitionMathematicalMultiplicity_ge_guardedOrder hδ hδsmall)
  obtain ⟨_hsize, _hmn, hν, hνn⟩ :=
    guardedRatePartition_integer_guards hδ hδone hm hn
  obtain ⟨cert⟩ := e.exists_curve_certificate hδ hδsmall hn hAn domain
    (fun i ↦ Polynomial.C (received i)) (fun _ ↦ by simp)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast h
  have hchar' : ringChar F = 0 ∨
      max (e.ambientDegree + 1 - 1) (guardedRatePartitionJetBound δ) < ringChar F := by
    apply hchar.imp_right
    intro hc
    have hD := e.ambient_le
    exact (max_lt (by omega) hνn).trans_le hc
  exact close_list_bound_of_curve_certificate_of_jetCharacteristic
    domain received cert hk e.message_le (by have := e.order_le; omega) e.ambient_le hkA hAn
    hν hδ hgap hchar'

open Classical in
/-- **Archived guarded refinement of the uniform capacity list bound.**

For `d = min (ceil(exp(1.5/delta))) (max 1000 (ceil(exp(1.489/delta))))`, the complete
degree-`< k` list has size at most `C*n^d`, where the displayed `C` depends only on `delta`.
The statement is semantic and does not alter the reference capacity executor. -/
theorem uniform_capacity_list_bound_1489_guarded
    (δ : ℝ)
    (hδ : 0 < δ)
    (hδsmall : δ < 6 / 25)
    (n k A : ℕ)
    (hn : guardedRatePartitionLength δ ≤ n)
    (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n)
    {F : Type*} [Field F]
    (domain : Fin n ↪ F)
    (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    let d := guardedRatePartitionOrder δ
    let ν := guardedRatePartitionJetBound δ
    let C : ℝ := (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤ C * n ^ d := by
  exact guardedUniformRatePartition_close_list_bound hδ hδsmall hn hk hgap hAn
    domain received hchar

end ReedSolomon
