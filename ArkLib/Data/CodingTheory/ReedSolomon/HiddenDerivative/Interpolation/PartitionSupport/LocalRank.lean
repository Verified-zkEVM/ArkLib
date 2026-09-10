/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.PartitionSupport.Basic

/-!
# Local rank for derivative-order partition support

After backward Taylor substitution a reachable monomial `T^i E^h Y^b` satisfies
`h ≤ i`, `Σ j*b_j ≤ W+i-h`, and `i+d*h < m`. Grouping by `s=i-h` gives
`Σ s<m, ceil((m-s)/(d+1)) * p_d(W+s)` possible coordinates.
This is an upper bound on the actual linear-map rank, not an independence claim.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential MvPolynomial
open scoped BigOperators

/-- The derivative-order weight of the visible local jets. -/
def localDerivativeWeight {d : ℕ} (exponent : LocalVariable d →₀ ℕ) : ℕ :=
  ∑ index : Fin d, (index.val + 1) * exponent (localY index)

private theorem source_derivative_weight {d : ℕ} (exponent : JetVariable d →₀ ℕ) :
    Finsupp.weight (sourceWeight 0 0 (fun index : Fin d ↦ (index.val : ℤ) + 1)) exponent =
      (fullDerivativeWeight exponent : ℤ) := by
  simp only [Finsupp.weight_eq_sum, fullDerivativeWeight, Fintype.sum_option,
    sourceWeight, nsmul_eq_mul, mul_zero, zero_add]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [mul_comm]

private theorem local_derivative_weight {d : ℕ} (exponent : LocalVariable d →₀ ℕ) :
    Finsupp.weight (localWeight (-1) 1 (fun index : Fin d ↦ (index.val : ℤ) + 1)) exponent =
      (localDerivativeWeight exponent : ℤ) + exponent (localE d) - exponent (localT d) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, localWeight, localDerivativeWeight,
    localY, localE, localAux, localT, Nat.cast_sum, Nat.cast_mul,
    mul_comm, add_comm, add_left_comm]
  ring

/-- The new derivative-order weight gains at most the displacement minus error exponent. -/
theorem unscaledLocal_derivative_weight_le {R : Type*} [CommRing R] {d W : ℕ}
    (center received : R) {equation : DifferentialPolynomial R d}
    (hweight : ∀ exponent ∈ equation.support, fullDerivativeWeight exponent ≤ W)
    {exponent : LocalVariable d →₀ ℕ}
    (hexponent : exponent ∈ (unscaledLocalSubstitution d center received equation).support) :
    localDerivativeWeight exponent ≤ W + (exponent (localT d) - exponent (localE d)) := by
  have hbound := unscaled_support_weight_le (-1) 1 0 0
    (fun index : Fin d ↦ (index.val : ℤ) + 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun index ↦ by simp) center received (cap := W)
    (fun source hsource ↦ by
      rw [source_derivative_weight]
      exact_mod_cast hweight source hsource) hexponent
  rw [local_derivative_weight] at hbound
  have hbalance := unscaledLocal_error_le_t center received equation hexponent
  omega

/-- The actual local map has precisely the three support bounds used in the rank estimate. -/
theorem partitionSupport_localConstraint_support {R : Type*} [CommRing R]
    {d D m W : ℕ} {cutoff : ℝ} (hD : 0 < D) (center received : R)
    {equation : DifferentialPolynomial R d}
    (hequation : equation ∈ partitionSupportSpace R D d W cutoff hD)
    {exponent : LocalVariable d →₀ ℕ}
    (hexponent : exponent ∈ (localConstraintAt m center received equation).support) :
    exponent (localE d) ≤ exponent (localT d) ∧
      localDerivativeWeight exponent ≤ W + (exponent (localT d) - exponent (localE d)) ∧
      localContactOrder d exponent < m := by
  have hproject : localContactOrder d exponent < m ∧
      exponent ∈ (unscaledLocalSubstitution d center received equation).support := by
    rw [MvPolynomial.mem_support_iff, localConstraintAt, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, projectLowContact, coeff_filterLocalMonomials] at hexponent
    split_ifs at hexponent with hcontact
    · exact ⟨hcontact, MvPolynomial.mem_support_iff.mpr hexponent⟩
    · exact (hexponent rfl).elim
  exact ⟨unscaledLocal_error_le_t center received equation hproject.2,
    unscaledLocal_derivative_weight_le center received
      (fun source hsource ↦ (mem_partitionSupportSpace_iff.mp hequation source hsource).1)
      hproject.2, hproject.1⟩

/-- The finite local-coordinate count, with all `d` derivative coordinates weighted. -/
def partitionLocalRankBound (d m W : ℕ) : ℕ :=
  ∑ shift ∈ Finset.range m,
    ((m - shift) ⌈/⌉ (d + 1)) * weightedHigherJetCount (d + 1) (W + shift)

/-- Coordinate indices split by displacement minus error. -/
abbrev PartitionLocalIndex (d m W : ℕ) :=
  Σ shift : Fin m,
    Fin ((m - shift.val) ⌈/⌉ (d + 1)) × ↥(weightedHigherJetTuples (d + 1) (W + shift.val))

/-- The dependent coordinate index has the displayed ceiling-sum cardinality. -/
theorem card_partitionLocalIndex (d m W : ℕ) :
    Fintype.card (PartitionLocalIndex d m W) = partitionLocalRankBound d m W := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  exact Fin.sum_univ_eq_sum_range
    (fun shift ↦ ((m - shift) ⌈/⌉ (d + 1)) * weightedHigherJetCount (d + 1) (W + shift)) m

/-- Recover the local monomial represented by a partition-coordinate index. -/
def partitionLocalExponent {d m W : ℕ} (index : PartitionLocalIndex d m W) :
    LocalVariable d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun slot ↦
    match slot with
    | none => index.1.val + index.2.1.val
    | some none => index.2.1.val
    | some (some jet) => index.2.2.val jet

/-- A finite set containing the support of every local output. -/
def partitionLocalExponents (d m W : ℕ) : Finset (LocalVariable d →₀ ℕ) :=
  Finset.univ.image (partitionLocalExponent (d := d) (m := m) (W := W))

/-- Each index emits one monomial, so the image has at most the rank-budget cardinality. -/
theorem card_partitionLocalExponents_le (d m W : ℕ) :
    (partitionLocalExponents d m W).card ≤ partitionLocalRankBound d m W := by
  exact Finset.card_image_le.trans (by rw [Finset.card_univ, card_partitionLocalIndex])

/-- The three backward-Taylor inequalities place a monomial in the finite coordinate set. -/
theorem mem_partitionLocalExponents_of_bounds {d m W : ℕ}
    {exponent : LocalVariable d →₀ ℕ}
    (hbalance : exponent (localE d) ≤ exponent (localT d))
    (hweight : localDerivativeWeight exponent ≤
      W + (exponent (localT d) - exponent (localE d)))
    (hcontact : localContactOrder d exponent < m) :
    exponent ∈ partitionLocalExponents d m W := by
  have hcontact' : exponent (localT d) + d * exponent (localE d) < m := by
    simpa [localContactOrder, Finsupp.weight_eq_sum, Fintype.sum_option,
      localContactWeight, localT, localE, localAux, mul_comm] using hcontact
  let shift := exponent (localT d) - exponent (localE d)
  have hshift : shift < m := by dsimp [shift]; omega
  have herror : exponent (localE d) < (m - shift) ⌈/⌉ (d + 1) := by
    apply lt_of_not_ge
    intro hbound
    have hmul := (ceilDiv_le_iff_le_mul (Nat.succ_pos d)).mp hbound
    rw [Nat.succ_mul] at hmul
    dsimp [shift] at hmul
    omega
  have hjets : (fun jet : Fin d ↦ exponent (localY jet)) ∈
      weightedHigherJetTuples (d + 1) (W + shift) :=
    mem_weightedHigherJetTuples.mpr hweight
  let index : PartitionLocalIndex d m W :=
    ⟨⟨shift, hshift⟩, ⟨⟨exponent (localE d), herror⟩, ⟨_, hjets⟩⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨index, Finset.mem_univ _, ?_⟩
  ext slot
  rcases slot with _ | (_ | jet)
  · change exponent (localT d) - exponent (localE d) + exponent (localE d) =
      exponent (localT d)
    exact Nat.sub_add_cancel hbalance
  · simp [partitionLocalExponent, index, localE, localAux]
  · simp [partitionLocalExponent, index, localY]

/-- The actual local constraint map on the new partition support. -/
def partitionSupportLocalConstraint {R : Type*} [CommRing R]
    {d D W : ℕ} {cutoff : ℝ} (m : ℕ) (hD : 0 < D) (center received : R) :
    partitionSupportSpace R D d W cutoff hD →ₗ[R] LocalPolynomial R d :=
  (localConstraintAt m center received).domRestrict _

/-- Counting the reachable coordinates bounds the actual local rank over every field. -/
theorem finrank_partitionSupportLocalConstraint_le {F : Type*} [Field F]
    {d D m W : ℕ} {cutoff : ℝ} (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (partitionSupportLocalConstraint (d := d) (W := W) (cutoff := cutoff)
        m hD center received)) ≤ partitionLocalRankBound d m W := by
  let coordinates := partitionLocalExponents d m W
  let target := MvPolynomial.restrictSupport F (coordinates : Set (LocalVariable d →₀ ℕ))
  let basis := MvPolynomial.basisRestrictSupport (R := F)
    (coordinates : Set (LocalVariable d →₀ ℕ))
  let _ : Module.Finite F target := Module.Finite.of_basis basis
  have hdimension : Module.finrank F target = coordinates.card := by
    rw [← Fintype.card_coe]
    exact Module.finrank_eq_card_basis basis
  have hrange : LinearMap.range
      (partitionSupportLocalConstraint (d := d) (W := W) (cutoff := cutoff)
        m hD center received) ≤ target := by
    rintro _ ⟨equation, rfl⟩
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro exponent hexponent
    obtain ⟨hbalance, hweight, hcontact⟩ :=
      partitionSupport_localConstraint_support hD center received equation.2 hexponent
    exact mem_partitionLocalExponents_of_bounds hbalance hweight hcontact
  exact (Submodule.finrank_mono hrange).trans
    (hdimension.le.trans (card_partitionLocalExponents_le d m W))

end ReedSolomon.HiddenDerivative
