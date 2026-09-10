/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Basic

/-!
# Counting local coordinates for the rate-partition support

A reachable monomial has displacement `i`, error exponent `h ≤ i`, and visible
derivative weight at most `W+i-h`. Writing `s=i-h`, the contact condition is
`s+(d+1)h<m`. Thus each `s<m` allows `ceil((m-s)/(d+1))` error exponents
and `p_d(W+s)` derivative tuples. Counting these coordinates bounds the local
rank without assuming they are linearly independent.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open scoped BigOperators

/-- Integer derivative tuples with weights `1,...,d`; the shifted argument reuses the
existing finite anisotropic-simplex enumerator. -/
def ratePartitionTupleCount (d B : ℕ) : ℕ := weightedHigherJetCount (d + 1) B

/-- The finite local rank budget, including the exact rounded contact multiplicity. -/
def ratePartitionRankBound (d m W : ℕ) : ℕ :=
  ∑ s ∈ Finset.range m, ((m - s) ⌈/⌉ (d + 1)) * ratePartitionTupleCount d (W + s)

/-- Each index specifies displacement minus error, error exponent, and all visible jets. -/
abbrev RatePartitionLocalIndex (d m W : ℕ) :=
  Σ s : Fin m, Fin ((m - s.val) ⌈/⌉ (d + 1)) ×
    ↥(weightedHigherJetTuples (d + 1) (W + s.val))

/-- The coordinate index has precisely the displayed finite rank budget. -/
theorem card_ratePartitionLocalIndex (d m W : ℕ) :
    Fintype.card (RatePartitionLocalIndex d m W) = ratePartitionRankBound d m W := by
  simp only [RatePartitionLocalIndex, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_coe, ratePartitionRankBound, ratePartitionTupleCount,
    weightedHigherJetCount]
  exact Fin.sum_univ_eq_sum_range
    (fun s ↦ ((m - s) ⌈/⌉ (d + 1)) *
      (weightedHigherJetTuples (d + 1) (W + s)).card) m

/-- Reconstruct a local exponent from its contact and derivative-tuple coordinates. -/
def ratePartitionLocalExponent {d m W : ℕ} (p : RatePartitionLocalIndex d m W) :
    LocalVariable d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v ↦ match v with
    | none => p.1.val + p.2.1.val
    | some none => p.2.1.val
    | some (some j) => p.2.2.val j

/-- All potentially reachable local monomials. -/
def ratePartitionLocalExponents (d m W : ℕ) : Finset (LocalVariable d →₀ ℕ) :=
  Finset.univ.image (ratePartitionLocalExponent (d := d) (m := m) (W := W))

/-- Different coordinate indices can only decrease the count when mapped to monomials. -/
theorem card_ratePartitionLocalExponents_le (d m W : ℕ) :
    (ratePartitionLocalExponents d m W).card ≤ ratePartitionRankBound d m W :=
  Finset.card_image_le.trans (by rw [Finset.card_univ, card_ratePartitionLocalIndex])

/-- The visible derivative weight is the anisotropic tuple weight with all d derivatives. -/
theorem localDerivativeJetWeight_eq_tuple {d : ℕ} (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (localDerivativeJetWeight d) e =
      higherJetTupleWeight (d := d + 1) (fun j ↦ e (localY j)) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, localDerivativeJetWeight,
    higherJetTupleWeight, localY, Nat.mul_comm]

/-- Contact order is displacement plus d times the error exponent, also at order zero. -/
theorem localContactOrder_eq_t_add_error {d : ℕ} (e : LocalVariable d →₀ ℕ) :
    localContactOrder d e = e (localT d) + d * e (localE d) := by
  simp [localContactOrder, Finsupp.weight_eq_sum, Fintype.sum_option,
    localContactWeight, localT, localE, localAux, Nat.mul_comm]

/-- Every local exponent satisfying the three support bounds is enumerated. -/
theorem mem_ratePartitionLocalExponents_of_bounds {d m W : ℕ}
    {e : LocalVariable d →₀ ℕ} (hbalance : e (localE d) ≤ e (localT d))
    (hweight : Finsupp.weight (localDerivativeJetWeight d) e ≤
      W + (e (localT d) - e (localE d)))
    (hcontact : localContactOrder d e < m) :
    e ∈ ratePartitionLocalExponents d m W := by
  rw [localContactOrder_eq_t_add_error] at hcontact
  have hs : e (localT d) - e (localE d) < m := by omega
  have hh : e (localE d) < (m - (e (localT d) - e (localE d))) ⌈/⌉ (d + 1) := by
    apply lt_of_not_ge
    intro h
    have hmul := (ceilDiv_le_iff_le_mul (Nat.succ_pos d)).mp h
    rw [Nat.succ_mul] at hmul
    omega
  have hz : (fun j ↦ e (localY j)) ∈
      weightedHigherJetTuples (d + 1) (W + (e (localT d) - e (localE d))) := by
    apply mem_weightedHigherJetTuples.mpr
    exact (localDerivativeJetWeight_eq_tuple e).symm.le.trans hweight
  let p : RatePartitionLocalIndex d m W :=
    ⟨⟨e (localT d) - e (localE d), hs⟩, ⟨⟨e (localE d), hh⟩, ⟨_, hz⟩⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨p, Finset.mem_univ _, ?_⟩
  ext v
  rcases v with _ | (_ | j)
  · simpa [ratePartitionLocalExponent, p, localT] using Nat.sub_add_cancel hbalance
  · simp [ratePartitionLocalExponent, p, localE, localAux]
  · simp [ratePartitionLocalExponent, p, localY]

/-- The actual local map restricted to the derivative-order partition support. -/
def ratePartitionLocalConstraint {F : Type*} [CommRing F]
    {D d W : ℕ} {L : ℝ} (m : ℕ) (hD : 0 < D) (center received : F) :
    ratePartitionSpace F D d W L hD →ₗ[F] LocalPolynomial F d :=
  (localConstraintAt m center received).domRestrict _

/-- The local rank is bounded by the finite partition/contact count over every field. -/
theorem finrank_ratePartitionLocalConstraint_le {F : Type*} [Field F]
    {D d m W : ℕ} {L : ℝ} (hD : 0 < D) (center received : F) :
    Module.finrank F (LinearMap.range
      (ratePartitionLocalConstraint (d := d) (W := W) (L := L) m hD center received)) ≤
      ratePartitionRankBound d m W := by
  let s := ratePartitionLocalExponents d m W
  let V := MvPolynomial.restrictSupport F (s : Set (LocalVariable d →₀ ℕ))
  let b := MvPolynomial.basisRestrictSupport (R := F) (s : Set (LocalVariable d →₀ ℕ))
  let _ : Module.Finite F V := Module.Finite.of_basis b
  have hdim : Module.finrank F V = s.card := by
    rw [← Fintype.card_coe]
    exact Module.finrank_eq_card_basis b
  have hsubset : LinearMap.range
      (ratePartitionLocalConstraint (d := d) (W := W) (L := L) m hD center received) ≤ V := by
    rintro _ ⟨Q, rfl⟩
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro e he
    obtain ⟨hb, hw, hc⟩ := ratePartition_localConstraint_support center received Q.2 he
    exact mem_ratePartitionLocalExponents_of_bounds hb hw hc
  exact (Submodule.finrank_mono hsubset).trans
    (hdim.le.trans (card_ratePartitionLocalExponents_le d m W))

end ReedSolomon.HiddenDerivative
