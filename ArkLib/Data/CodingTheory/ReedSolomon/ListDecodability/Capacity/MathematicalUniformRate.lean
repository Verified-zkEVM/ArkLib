/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.UniformRate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.MathematicalUniform

/-!
# Revised uniform Reed–Solomon list bounds near capacity

For a capacity gap `delta`, this mathematical construction chooses

* `d = ceil(exp(3/(2*delta)))`, the derivative order;
* `m = ceil(300*d²*log(6*d))`, the interpolation multiplicity;
* `nu = ceil(m/delta²)-1`, the total jet-degree bound; and
* `Ndelta = ceil(2*m/delta²)`, a sufficient block-length threshold.

The complete list has size at most `C*n^d`, where
`C = nu²*(2*nu/delta)^d`. The retained complete reference executor deliberately continues to use
its separately verified 1000-based parameter recipe. This file proves a mathematical list-size
statement and makes no decoder-runtime or bit-complexity claim.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- The 300-based mathematical theorem in expanded parameter form.

The gap uses the actual message dimension `k`, so codewords have degree strictly below `k`,
including the zero polynomial. Finiteness and the cardinality bound concern the complete list. -/
theorem mathematicalUniformRatePartition_close_list_bound {F : Type u} [Field F]
    {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ)
    (hδsmall : δ < 6 / 25)
    /-

    The explicit threshold gives the finite interpolation and characteristic guards.
    -/
    (hn : uniformRatePartitionMathematicalLength δ ≤ n)
    (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n)
    /-

    Distinct evaluation points turn agreement into a count of distinct polynomial roots.
    -/
    (domain : Fin n ↪ F)
    (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    /-

    Both conclusions concern the complete list, even over infinite fields.
    -/
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
          (2 * uniformRatePartitionMathematicalJetBound δ / δ) ^
            uniformRatePartitionOrder δ *
          n ^ uniformRatePartitionOrder δ := by
  obtain ⟨e⟩ := exists_mathematicalRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  have hd := uniformRatePartitionOrder_ge_519 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hm : 0 < uniformRatePartitionMathematicalMultiplicity δ :=
    lt_of_lt_of_le (by omega) (ratePartitionMathematicalMultiplicity_ge_order hd)
  obtain ⟨_hsize, _hmn, hν, hνn⟩ :=
    uniformRatePartitionMathematical_integer_guards hδ hδone hm hn
  obtain ⟨cert⟩ := e.exists_curve_certificate hδ hδone hd hn hAn domain
    (fun i ↦ Polynomial.C (received i)) (fun _ ↦ by simp)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast h
  have hchar' : ringChar F = 0 ∨
      max (e.ambientDegree + 1 - 1)
        (uniformRatePartitionMathematicalJetBound δ) < ringChar F := by
    apply hchar.imp_right
    intro hc
    have hD := e.ambient_le
    exact (max_lt (by omega) hνn).trans_le hc
  exact close_list_bound_of_curve_certificate_of_jetCharacteristic
    domain received cert hk e.message_le
    (by have := e.order_le; omega) e.ambient_le hkA hAn hν hδ hgap hchar'

open Classical in
/-- **Uniform list bound with the revised 300-based mathematical multiplicity.**

For any distinct evaluation points and received word, the complete set of polynomials of degree
`< k` agreeing in at least `A` positions is finite and has size at most `C*n^d`. The field may be
infinite; in positive characteristic its characteristic must be at least `n`.

Here `d = ceil(exp(3/(2*delta)))`, `nu = ceil(m/delta²)-1`, and
`m = ceil(300*d²*log(6*d))`. Thus `C = nu²*(2*nu/delta)^d` depends only on `delta`.
This is the revised mathematical headline; it does not change the retained executable selector. -/
theorem uniform_capacity_list_bound_300
    /-

    Fix the capacity gap and its small-gap regime.
    -/
    (δ : ℝ)
    (hδ : 0 < δ)
    (hδsmall : δ < 6 / 25)
    /-

    The sufficient length depends only on delta, not on the field or received word.
    -/
    (n k A : ℕ)
    (hn : uniformRatePartitionMathematicalLength δ ≤ n)
    (hk : 0 < k)
    /-

    Agreement is measured in positions, and message degree is strictly below k.
    -/
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n)
    /-

    An embedding records that all n evaluation points are distinct.
    -/
    {F : Type*} [Field F]
    (domain : Fin n ↪ F)
    (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    let d := uniformRatePartitionOrder δ
    let ν := uniformRatePartitionMathematicalJetBound δ
    let C : ℝ := (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d
    /-

    Both conclusions concern the complete list, not a selected sublist.
    -/
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤ C * n ^ d := by
  exact mathematicalUniformRatePartition_close_list_bound hδ hδsmall hn hk hgap hAn
    domain received hchar

end ReedSolomon
