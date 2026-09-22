/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Index
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Space
public import ArkLib.Data.MvPolynomial.WeightAtMost
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The weighted interpolation support without degree bands

An exponent `u` of `X^a Y₀^(b₀) ⋯ Y_d^(b_d)` is *weighted-support eligible* for parameters
`D`, `W` and a real cutoff `L` when its higher-jet weight `∑_{j ≥ 2} (j - 1) b_j` is at most `W`
and its coarse specialization weight `a + D · ∑_j b_j` is strictly below `L`. The weighted support
space is the space of differential polynomials whose support consists of eligible exponents.

Only the coarse cutoff bounds the degree of each monomial, so every higher-jet degree, including
zero, is allowed. For `0 < D` the coarse cutoff bounds the total degree by `⌈L⌉₊`, so the set of
eligible exponents is finite and the dimension of the space is its cardinality. The same cutoff
bounds the total jet degree by `L / D`, which is what the local rank count of
`WeightedSupport/LocalRank.lean` uses, and it bounds the exact specialization weight
`a + ∑_j (D - j) b_j`, which gives the decoder's degree bounds and the inclusion into the exact
interpolation space.

In the capacity construction the cutoff is `L = m D (1 + g)`.

## Main statements

* `WeightedSupportEligible`, `weightedSupportEligible_finite`, `weightedSupportExponents`.
* `weightedSupportSpace`, `mem_weightedSupportSpace_iff`, `finrank_weightedSupportSpace_eq_card`.
* `totalJetDegree_lt_of_weightedSupportEligible`: the total jet degree is below `L / D`.
* `weightedSupportSpace_le_exactInterpolationSpace`: the inclusion into the exact interpolation
  space.
* `differentialWeightedDegree_lt_of_mem_weightedSupportSpace` and
  `jetTotalDegree_lt_of_mem_weightedSupportSpace`: the decoder's degree bounds.

## References

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/Basic.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `WeightedSupportEligible`, `weightedSupportEligible_finite`, `weightedSupportExponents`,
  `mem_weightedSupportExponents`, `mem_weightedSupportSpace_iff`,
  `totalJetDegree_lt_of_weightedSupportEligible`, `finrank_weightedSupportSpace_eq_card`,
  `weightedSupportSpace_le_exactInterpolationSpace`,
  `differentialWeightedDegree_lt_of_mem_weightedSupportSpace` and
  `jetTotalDegree_lt_of_mem_weightedSupportSpace` keep their statements, except as follows.
* `weightedSupportSpace` no longer takes the proof `hD : 0 < D`: it is `restrictSupport` of the
  set of eligible exponents, which is a submodule for every `D`. Positivity of `D` is needed only
  for finiteness, the dimension, and the total-jet-degree bound, which take `hD`.
* `degree_lt_ceil_of_weightedSupportEligible` keeps its statement, with the source's
  `exponentDegree_eq_x_add_totalJetDegree` replaced by the existing `degree_eq_add_totalJetDegree`.
* `exactInterpolationMonomialWeight_lt_of_weightedSupportEligible` is
  `weight_differentialWeight_lt_of_weightedSupportEligible`, since the exact monomial weight is
  `Finsupp.weight (differentialWeight D)`; the coarse comparison
  `exactInterpolationMonomialWeight_le_coarse` is the existing `weight_differentialWeight_le` of
  `Interpolation/Space.lean` at `K = D + 1`.
* `totalJetDegree_le_pred_of_weightedSupportEligible` is stated in the strict form
  `totalJetDegree_lt_of_weightedSupportEligible_of_le`.
* `weightedSupportBasis` is `MvPolynomial.basisRestrictSupport` and is not restated, and
  `decoder_bounds_of_mem_weightedSupportSpace`, the conjunction of the two degree bounds, is
  derived in the matching `ArkLibTest` file.

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Section 3.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} {d D W : ℕ} {L : ℝ}

/-- An exponent is weighted-support eligible when its higher-jet weight is at most `W` and its
coarse specialization weight `a + D · ∑_j b_j` is strictly below the real cutoff `L`. -/
def WeightedSupportEligible (D d W : ℕ) (L : ℝ) (u : JetVariable d →₀ ℕ) : Prop :=
  fullHigherJetWeight u ≤ W ∧ (u none + D * totalJetDegree u : ℕ) < L

/-- For `0 < D` the coarse cutoff bounds the total degree of an eligible exponent by `⌈L⌉₊`,
even when some jet has weight zero in the higher-jet weight. -/
theorem degree_lt_ceil_of_weightedSupportEligible (hD : 0 < D)
    {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible D d W L u) :
    u.degree < ⌈L⌉₊ := by
  rw [degree_eq_add_totalJetDegree]
  have hmul : totalJetDegree u ≤ D * totalJetDegree u := Nat.le_mul_of_pos_left _ hD
  exact (Nat.add_le_add_left hmul _).trans_lt (Nat.lt_ceil.mpr hu.2)

/-- For `0 < D` there are finitely many eligible exponents. The hypothesis is needed: for
`D = 0` and `0 < L`, every power of `Y₀` is eligible. -/
theorem weightedSupportEligible_finite (hD : 0 < D) :
    {u : JetVariable d →₀ ℕ | WeightedSupportEligible D d W L u}.Finite :=
  (Finsupp.finite_of_degree_le ⌈L⌉₊).subset fun _ hu =>
    (degree_lt_ceil_of_weightedSupportEligible hD hu).le

/-- The finite set of eligible exponents, for `0 < D`. -/
def weightedSupportExponents (D d W : ℕ) (L : ℝ) (hD : 0 < D) : Finset (JetVariable d →₀ ℕ) :=
  (weightedSupportEligible_finite (d := d) (W := W) (L := L) hD).toFinset

@[simp]
theorem mem_weightedSupportExponents {hD : 0 < D} {u : JetVariable d →₀ ℕ} :
    u ∈ weightedSupportExponents D d W L hD ↔ WeightedSupportEligible D d W L u := by
  simp [weightedSupportExponents]

/-- The weighted support space: differential polynomials whose support consists of eligible
exponents. -/
def weightedSupportSpace (F : Type*) [CommSemiring F] (D d W : ℕ) (L : ℝ) :
    Submodule F (DifferentialPolynomial F d) :=
  MvPolynomial.restrictSupport F {u | WeightedSupportEligible D d W L u}

/-- A polynomial lies in the weighted support space exactly when every exponent of its support is
eligible. -/
theorem mem_weightedSupportSpace_iff [CommSemiring F] {Q : DifferentialPolynomial F d} :
    Q ∈ weightedSupportSpace F D d W L ↔ ∀ u ∈ Q.support, WeightedSupportEligible D d W L u := by
  rw [weightedSupportSpace, MvPolynomial.mem_restrictSupport_iff]
  rfl

/-- The weighted support space is spanned by the eligible monomials, so its dimension over a
field is the number of eligible exponents. -/
theorem finrank_weightedSupportSpace_eq_card [Field F] (hD : 0 < D) :
    Module.finrank F (weightedSupportSpace F D d W L) =
      (weightedSupportExponents D d W L hD).card := by
  have hs : {u : JetVariable d →₀ ℕ | WeightedSupportEligible D d W L u} =
      ↑(weightedSupportExponents D d W L hD) := by
    ext u
    simp
  rw [weightedSupportSpace, hs, MvPolynomial.finrank_restrictSupport_finset]

/-- The total jet degree of an eligible exponent is strictly below `L / D`, since
`D · totalJetDegree u ≤ a + D · totalJetDegree u < L`. -/
theorem totalJetDegree_lt_of_weightedSupportEligible (hD : 0 < D)
    {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible D d W L u) :
    (totalJetDegree u : ℝ) < L / D := by
  rw [lt_div_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)]
  have hx : (0 : ℝ) ≤ u none := Nat.cast_nonneg _
  have h := hu.2
  push_cast at h
  linarith

/-- If `L ≤ D t`, an eligible exponent has total jet degree strictly below `t`. For capacity
`t = 2 m`. -/
theorem totalJetDegree_lt_of_weightedSupportEligible_of_le (hD : 0 < D) {t : ℕ}
    (hL : L ≤ (D : ℝ) * t) {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible D d W L u) :
    totalJetDegree u < t := by
  have ht := totalJetDegree_lt_of_weightedSupportEligible hD hu
  have hquot : L / D ≤ t :=
    (div_le_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr (by linarith)
  exact_mod_cast ht.trans_le hquot

/-- If `L ≤ B`, an eligible exponent has exact specialization weight below `B`. -/
theorem weight_differentialWeight_lt_of_weightedSupportEligible {B : ℕ} (hL : L ≤ B)
    {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible D d W L u) :
    Finsupp.weight (differentialWeight D) u < B := by
  have hcoarse : u none + D * totalJetDegree u < B := by exact_mod_cast hu.2.trans_le hL
  have h := weight_differentialWeight_le (D.lt_add_one) u
  rw [Nat.add_sub_cancel] at h
  exact h.trans_lt hcoarse

/-- For `d < D`, `L ≤ m A` and `L ≤ D M`, the weighted support space lies in the exact
interpolation space with first-jet cap `M`. The cap `L ≤ D M` bounds the exponent of `Y₁` by the
total jet degree, which is below `L / D ≤ M`; this is an inclusion, not a restriction of the
weighted support. -/
theorem weightedSupportSpace_le_exactInterpolationSpace [CommSemiring F] {A m M : ℕ}
    (hD : 0 < D) (hdD : d < D) (hL : L ≤ (m * A : ℕ)) (hcap : L ≤ (D : ℝ) * M) :
    weightedSupportSpace F D d W L ≤ exactInterpolationSpace F D A d m M W hdD := by
  intro Q hQ
  rw [mem_exactInterpolationSpace_iff]
  intro u hu
  have he := mem_weightedSupportSpace_iff.mp hQ u hu
  exact ⟨(firstJetExponent_le_totalJetDegree u).trans
      (totalJetDegree_lt_of_weightedSupportEligible_of_le hD hcap he).le,
    he.1, weight_differentialWeight_lt_of_weightedSupportEligible hL he⟩

/-- If `0 < B` and `L ≤ B`, every polynomial of the weighted support space has differential
weighted degree below `B`. The hypothesis `0 < B` covers the zero polynomial, whose degree is
`0`. -/
theorem differentialWeightedDegree_lt_of_mem_weightedSupportSpace [CommSemiring F] {B : ℕ}
    (hB : 0 < B) (hL : L ≤ B) {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ weightedSupportSpace F D d W L) :
    differentialWeightedDegree D Q < B := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_lt_iff hB]
  exact fun u hu => weight_differentialWeight_lt_of_weightedSupportEligible hL
    (mem_weightedSupportSpace_iff.mp hQ u hu)

/-- If `0 < D`, `0 < t` and `L ≤ D t`, every polynomial of the weighted support space has total
jet degree below `t`. The hypothesis `0 < t` covers the zero polynomial. -/
theorem jetTotalDegree_lt_of_mem_weightedSupportSpace [CommSemiring F] (hD : 0 < D) {t : ℕ}
    (ht : 0 < t) (hL : L ≤ (D : ℝ) * t) {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ weightedSupportSpace F D d W L) :
    jetTotalDegree Q < t := by
  have hb : jetTotalDegree Q ≤ t - 1 := (jetTotalDegree_le_iff Q _).mpr fun u hu =>
    Nat.le_sub_one_of_lt (totalJetDegree_lt_of_weightedSupportEligible_of_le hD hL
      (mem_weightedSupportSpace_iff.mp hQ u hu))
  omega

end ReedSolomon.HiddenDerivative
