/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CurveCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.UniformRateCertificate

/-!
# Uniform Reed–Solomon list bounds near capacity

For a capacity gap `delta`, the construction chooses

* `d = ceil(exp(3/(2*delta)))`, the derivative order;
* `m = ceil(1000*d²*log(6*d))`, the interpolation multiplicity;
* `nu = ceil(m/delta²)-1`, the total jet-degree bound; and
* `Ndelta = ceil(2*m/delta²)`, a sufficient block-length threshold.

The strict interpolation-support inequality permits the subtraction of one in `nu`. Requiring
`Ndelta ≤ n` then ensures `nu < n`, which supplies both the characteristic guard and the
root-family degree estimate. With

`C = nu² * (2*nu/delta)^d`,

the complete set of degree-`< k` polynomials agreeing with an arbitrary received word in at least
`A` positions is finite and has size at most `C*n^d`. The field may be infinite; in positive
characteristic the theorem requires `n ≤ ringChar F`.

The proof constructs the uniform partition certificate, converts its integer guards into the
characteristic condition required by the root theorem, and applies the complete-list bound. This
is a mathematical list-size statement and makes no decoder-runtime or bit-complexity claim.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- The underlying uniform small-gap theorem in expanded parameter form.

The gap hypothesis uses the actual message dimension `k`, so codewords have degree strictly below
`k`, including the zero polynomial. The conclusion concerns the complete list and separately
asserts its finiteness. -/
theorem uniformRatePartition_close_list_bound {F : Type u} [Field F]
    {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ)
    (hδsmall : δ < 6 / 25)
    /-

    The explicit length threshold ensures the chosen jet degree is strictly below n.
    -/
    (hn : uniformRatePartitionLength δ ≤ n)
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

    Finiteness and the cardinality bound concern the complete list, even over infinite fields.
    -/
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (uniformRatePartitionJetBound δ : ℝ) ^ 2 *
          (2 * uniformRatePartitionJetBound δ / δ) ^ uniformRatePartitionOrder δ *
          n ^ uniformRatePartitionOrder δ := by
  obtain ⟨e⟩ := exists_uniformRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  have hd := uniformRatePartitionOrder_ge_500 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hm : 0 < uniformRatePartitionMultiplicity δ :=
    lt_of_lt_of_le (by omega) (ratePartitionClosedMultiplicity_ge_order hd)
  obtain ⟨hsize, hmn, hν, hνn⟩ := uniformRatePartition_integer_guards hδ hδone hm hn
  obtain ⟨cert⟩ := e.exists_curve_certificate hδ hδone hd hn hAn domain
    (fun i ↦ Polynomial.C (received i)) (fun _ ↦ by simp)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast h
  have hchar' : ringChar F = 0 ∨
      max (e.ambientDegree + 1 - 1) (uniformRatePartitionJetBound δ) < ringChar F := by
    apply hchar.imp_right
    intro hc
    have hD := e.ambient_le
    exact (max_lt (by omega) hνn).trans_le hc
  exact close_list_bound_of_curve_certificate_of_jetCharacteristic
    domain received cert hk e.message_le
    (by have := e.order_le; omega) e.ambient_le hkA hAn hν hδ hgap hchar'

open Classical in
/-- **Uniform list bound with order `⌈exp(3 / (2 * δ))⌉₊`.**

For any distinct evaluation points and any received word, the complete set of polynomials
of degree `< k` agreeing in at least `A` positions is finite and has size at most `C * n ^ d`.
The zero polynomial is included whenever it meets the agreement threshold.

The constants `d`, `ν`, and `C` depend only on `δ`. The explicit sufficient block length is
`uniformRatePartitionLength δ`. The field may be infinite; in positive characteristic its
characteristic must be at least `n`. A bound on field cardinality alone is not this condition.

Finiteness is stated explicitly because `Set.ncard` alone would not certify a finite list.
This is a mathematical list-size theorem; it makes no execution or bit-complexity claim.
-/
theorem uniform_capacity_list_bound
    /-

    Fix the capacity gap and its small-gap regime.
    -/
    (δ : ℝ)
    (hδ : 0 < δ)
    (hδsmall : δ < 6 / 25)
    /-

    The sufficient length depends only on δ, not on the field or received word.
    -/
    (n k A : ℕ)
    (hn : uniformRatePartitionLength δ ≤ n)
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
    /-

    d = ceil(exp(3/(2δ))) is the derivative order in the uniform construction.
    The partition dimension/rank estimate proves that this order suffices
    uniformly over the physical code rate once n exceeds the stated threshold.
    -/
    let d := uniformRatePartitionOrder δ
    /-

    With m = ceil(1000 d² log(6d)), the construction gives
    ν = ceil(m/δ²) - 1 as a uniform bound on total jet degree.
    The strict support inequality justifies the subtraction of one.
    The length bound n ≥ ceil(2m/δ²) ensures ν < n.
    -/
    let ν := uniformRatePartitionJetBound δ
    /-

    C = ν²(2ν/δ)^d is the degree/incidence prefactor in the list bound.
    Both ν and d depend only on δ, so C is independent of n, k, and the field.
    -/
    let C : ℝ := (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d
    /-

    Both conclusions concern the complete list, not a selected sublist.
    -/
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤ C * n ^ d := by
  exact uniformRatePartition_close_list_bound hδ hδsmall hn hk hgap hAn
    domain received hchar

end ReedSolomon
