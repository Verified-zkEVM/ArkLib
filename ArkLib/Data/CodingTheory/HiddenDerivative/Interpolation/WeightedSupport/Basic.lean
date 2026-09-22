/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Space
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The weighted interpolation support

For a positive weight `D`, a higher-jet budget `W : ℕ` and a real cutoff `L`, an exponent
`X^a Y₀^b₀ ⋯ Y_d^b_d` is *weighted-support eligible* when

```text
sum_{j=2}^d (j - 1) b_j ≤ W,
a + D (b₀ + ⋯ + b_d) < L.
```

The first inequality is the higher-jet budget of the exact interpolation space of
`Interpolation/Index.lean`. The second is a strict cutoff on the coarse weight
`a + D * totalJetDegree u`. Unlike the exact space there is no cap on the exponent of `Y₁` and no
lower bound on any jet degree; the cutoff alone makes the support finite once `0 < D`, since then
the ordinary degree `a + totalJetDegree u` is at most the coarse weight. The weighted support
space is the space of differential polynomials whose monomials are all eligible.

In the capacity construction the cutoff is `L = m * D * (1 + g)`. Dividing by `D` bounds the total
jet degree by `L / D`, and the coarse weight dominates the specialization weight
`Finsupp.weight (differentialWeight D)`, so members of the space satisfy the decoder's degree
budgets directly.

## Main statements

* `WeightedSupportEligible`, `weightedSupportExponents`, `weightedSupportSpace` and
  `weightedSupportSpaceBasis`, with `weightedSupportEligible_finite` and
  `finrank_weightedSupportSpace_eq_card`.
* `totalJetDegree_lt_of_weightedSupportEligible` and
  `totalJetDegree_le_pred_of_weightedSupportEligible`: the cutoff bounds the total jet degree by
  `L / D`.
* `weightedSupportSpace_le_exactInterpolationSpace`: the weighted support space lies in the exact
  interpolation space when `L ≤ m * A` and `L ≤ D * M`.
* `differentialWeightedDegree_lt_of_mem_weightedSupportSpace`,
  `jetTotalDegree_lt_of_mem_weightedSupportSpace` and
  `decoder_bounds_of_mem_weightedSupportSpace`: degree budgets of members of the space.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`Basic.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d:
`WeightedSupportEligible`, `degree_lt_ceil_of_weightedSupportEligible`,
`weightedSupportEligible_finite`, `weightedSupportExponents`, `mem_weightedSupportExponents`,
`weightedSupportSpace`, `mem_weightedSupportSpace_iff`,
`totalJetDegree_lt_of_weightedSupportEligible`, `finrank_weightedSupportSpace_eq_card`,
`weightedSupportSpace_le_exactInterpolationSpace`,
`totalJetDegree_le_pred_of_weightedSupportEligible`,
`differentialWeightedDegree_lt_of_mem_weightedSupportSpace`,
`jetTotalDegree_lt_of_mem_weightedSupportSpace` and `decoder_bounds_of_mem_weightedSupportSpace`,
with the same statements up to the following changes. The source's `weightedSupportBasis` is
`weightedSupportSpaceBasis`, indexed by the exponent `Finset` like
`exactInterpolationSpaceBasis`. The source's `exactInterpolationMonomialWeight_lt_of_…` is
`weight_differentialWeight_lt_of_weightedSupportEligible`, stated through
`Finsupp.weight (differentialWeight D)`, and its coarse comparison is
`weight_le_add_mul_totalJetDegree` of `Interpolation/Index.lean`. The source imported
`RootFinding/Counting/TotalJetDegreeRootCount.lean` only for `jetTotalDegree` and
`jetTotalDegree_le_iff`, which are now `PolynomialDifferential.jetTotalDegree` and
`PolynomialDifferential.jetTotalDegree_le_iff`; accordingly `[Field F]` is weakened to
`[CommSemiring F]` in `jetTotalDegree_lt_of_mem_weightedSupportSpace` and
`decoder_bounds_of_mem_weightedSupportSpace`. The coordinate description and the dimension lower
bound are in `WeightedSupport/Dimension.lean`.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} {d D W : ℕ} {L : ℝ}

/-! ### Eligible exponents -/

/-- An exponent `u` is weighted-support eligible when its higher-jet weight
`∑_{j ≥ 2} (j - 1) u(Y_j)` is at most `W` and its coarse weight `u X + D * totalJetDegree u` is
strictly below the real cutoff `L`. -/
def WeightedSupportEligible (D d W : ℕ) (L : ℝ) (u : JetVariable d →₀ ℕ) : Prop :=
  fullHigherJetWeight u ≤ W ∧ ((u none + D * totalJetDegree u : ℕ) : ℝ) < L

/-- If `0 < D`, an eligible exponent has ordinary degree below `⌈L⌉₊`: the degree
`u X + totalJetDegree u` is at most the coarse weight. The hypothesis is needed, since for
`D = 0` every power of `Y₀` is eligible when `0 < L`. -/
theorem degree_lt_ceil_of_weightedSupportEligible (hD : 0 < D) {u : JetVariable d →₀ ℕ}
    (hu : WeightedSupportEligible D d W L u) : u.degree < ⌈L⌉₊ := by
  rw [degree_eq_add_totalJetDegree]
  have hmul : totalJetDegree u ≤ D * totalJetDegree u := Nat.le_mul_of_pos_left _ hD
  exact (Nat.add_le_add_left hmul _).trans_lt (Nat.lt_ceil.mpr hu.2)

/-- If `0 < D`, there are finitely many eligible exponents. See
`degree_lt_ceil_of_weightedSupportEligible` for why `0 < D` is needed. -/
theorem weightedSupportEligible_finite (hD : 0 < D) :
    {u : JetVariable d →₀ ℕ | WeightedSupportEligible D d W L u}.Finite :=
  (Finsupp.finite_of_degree_le ⌈L⌉₊).subset fun _ hu =>
    (degree_lt_ceil_of_weightedSupportEligible hD hu).le

/-- The finite set of weighted-support eligible exponents. It is specified through
`Set.Finite.toFinset`, so it is not an executable enumeration. -/
def weightedSupportExponents (D d W : ℕ) (L : ℝ) (hD : 0 < D) : Finset (JetVariable d →₀ ℕ) :=
  (weightedSupportEligible_finite (d := d) (W := W) (L := L) hD).toFinset

@[simp]
theorem mem_weightedSupportExponents {hD : 0 < D} {u : JetVariable d →₀ ℕ} :
    u ∈ weightedSupportExponents D d W L hD ↔ WeightedSupportEligible D d W L u := by
  simp [weightedSupportExponents]

/-! ### The space and its dimension -/

/-- The differential polynomials whose monomials are all weighted-support eligible. -/
def weightedSupportSpace (F : Type*) [CommSemiring F] (D d W : ℕ) (L : ℝ) (hD : 0 < D) :
    Submodule F (DifferentialPolynomial F d) :=
  MvPolynomial.restrictSupport F
    (↑(weightedSupportExponents D d W L hD) : Set (JetVariable d →₀ ℕ))

/-- Membership in the weighted support space is eligibility of every support exponent. -/
theorem mem_weightedSupportSpace_iff [CommSemiring F] {hD : 0 < D}
    {Q : DifferentialPolynomial F d} :
    Q ∈ weightedSupportSpace F D d W L hD ↔ ∀ u ∈ Q.support, WeightedSupportEligible D d W L u := by
  rw [weightedSupportSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_weightedSupportExponents]

/-- The monomial basis of the weighted support space, indexed by the eligible exponents. -/
def weightedSupportSpaceBasis (F : Type*) [CommSemiring F] (D d W : ℕ) (L : ℝ) (hD : 0 < D) :
    Module.Basis ↥(weightedSupportExponents D d W L hD) F (weightedSupportSpace F D d W L hD) :=
  MvPolynomial.basisRestrictSupport (R := F)
    (↑(weightedSupportExponents D d W L hD) : Set (JetVariable d →₀ ℕ))

/-- Over a field, the dimension of the weighted support space is the number of eligible
exponents. -/
theorem finrank_weightedSupportSpace_eq_card [Field F] (hD : 0 < D) :
    Module.finrank F (weightedSupportSpace F D d W L hD) =
      (weightedSupportExponents D d W L hD).card := by
  rw [Module.finrank_eq_card_basis (weightedSupportSpaceBasis F D d W L hD)]
  exact Fintype.card_coe _

/-! ### Degree bounds -/

/-- An eligible exponent has total jet degree strictly below `L / D`, since
`D * totalJetDegree u ≤ u X + D * totalJetDegree u < L`. The hypothesis `0 < D` makes the
division meaningful. -/
theorem totalJetDegree_lt_of_weightedSupportEligible (hD : 0 < D) {u : JetVariable d →₀ ℕ}
    (hu : WeightedSupportEligible D d W L u) : (totalJetDegree u : ℝ) < L / D := by
  rw [lt_div_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)]
  have hx : (0 : ℝ) ≤ u none := Nat.cast_nonneg _
  have hweight := hu.2
  push_cast at hweight
  linarith

/-- If `L ≤ D * t`, an eligible exponent has total jet degree at most `t - 1`: the strict cutoff
survives the passage to natural numbers. In the capacity construction `t = 2 * m`. -/
theorem totalJetDegree_le_pred_of_weightedSupportEligible (hD : 0 < D) {t : ℕ}
    (hL : L ≤ (D : ℝ) * t) {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible D d W L u) :
    totalJetDegree u ≤ t - 1 := by
  have ht := totalJetDegree_lt_of_weightedSupportEligible hD hu
  have hquot : L / D ≤ t :=
    (div_le_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr (by linarith)
  have : totalJetDegree u < t := by exact_mod_cast ht.trans_le hquot
  omega

/-- If `L ≤ B`, an eligible exponent has specialization weight below `B`, since the
specialization weight is at most the coarse weight (`weight_le_add_mul_totalJetDegree`). -/
theorem weight_differentialWeight_lt_of_weightedSupportEligible {B : ℕ} (hL : L ≤ B)
    {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible D d W L u) :
    Finsupp.weight (differentialWeight D) u < B :=
  (weight_le_add_mul_totalJetDegree D u).trans_lt (by exact_mod_cast hu.2.trans_le hL)

/-- If `L ≤ m * A` and `L ≤ D * M`, the weighted support space lies in the exact interpolation
space of `Interpolation/Index.lean`. The first hypothesis gives the specialization-weight bound;
the second bounds the `Y₁` exponent, which is at most the total jet degree `< L / D ≤ M`. This is
an inclusion into a search space, not a further restriction of the support. -/
theorem weightedSupportSpace_le_exactInterpolationSpace [CommSemiring F] {A m M : ℕ}
    (hD : 0 < D) (hdD : d < D) (hL : L ≤ (m * A : ℕ)) (hcap : L ≤ (D : ℝ) * M) :
    weightedSupportSpace F D d W L hD ≤ exactInterpolationSpace F D A d m M W hdD := by
  intro Q hQ
  rw [mem_exactInterpolationSpace_iff]
  intro u hu
  have he := mem_weightedSupportSpace_iff.mp hQ u hu
  refine ⟨?_, he.1, weight_differentialWeight_lt_of_weightedSupportEligible hL he⟩
  have ht := totalJetDegree_lt_of_weightedSupportEligible hD he
  have hquot : L / D ≤ M :=
    (div_le_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr (by linarith)
  have htotal : totalJetDegree u ≤ M := by exact_mod_cast ht.le.trans hquot
  exact (firstJetExponent_le_totalJetDegree u).trans htotal

/-- If `L ≤ B`, every member of the weighted support space has specialization-weighted degree
below `B`. The hypothesis `0 < B` covers the zero polynomial, whose weighted degree is `0`. -/
theorem differentialWeightedDegree_lt_of_mem_weightedSupportSpace [CommSemiring F] {B : ℕ}
    {hD : 0 < D} (hB : 0 < B) (hL : L ≤ B) {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ weightedSupportSpace F D d W L hD) : differentialWeightedDegree D Q < B := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_lt_iff hB]
  exact fun u hu => weight_differentialWeight_lt_of_weightedSupportEligible hL
    (mem_weightedSupportSpace_iff.mp hQ u hu)

/-- If `L ≤ D * t`, every member of the weighted support space has total jet degree below `t`.
The hypothesis `0 < t` covers the zero polynomial. No cap on the `Y₁` exponent is used. -/
theorem jetTotalDegree_lt_of_mem_weightedSupportSpace [CommSemiring F] {t : ℕ} {hD : 0 < D}
    (ht : 0 < t) (hL : L ≤ (D : ℝ) * t) {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ weightedSupportSpace F D d W L hD) : jetTotalDegree Q < t := by
  have hb : jetTotalDegree Q ≤ t - 1 := (jetTotalDegree_le_iff Q _).mpr fun u hu =>
    totalJetDegree_le_pred_of_weightedSupportEligible hD hL
      (mem_weightedSupportSpace_iff.mp hQ u hu)
  omega

/-- The two decoder budgets: if `L ≤ D * (2 m)` and `L ≤ m * A` with `0 < m` and `0 < A`, every
member of the weighted support space has total jet degree below `2 m` and
specialization-weighted degree below `m A`. -/
theorem decoder_bounds_of_mem_weightedSupportSpace [CommSemiring F] {m A : ℕ} {hD : 0 < D}
    (hm : 0 < m) (hA : 0 < A) (hjet : L ≤ (D : ℝ) * (2 * m)) (hweight : L ≤ (m * A : ℕ))
    {Q : DifferentialPolynomial F d} (hQ : Q ∈ weightedSupportSpace F D d W L hD) :
    jetTotalDegree Q < 2 * m ∧ differentialWeightedDegree D Q < m * A :=
  ⟨jetTotalDegree_lt_of_mem_weightedSupportSpace (by omega) (by exact_mod_cast hjet) hQ,
    differentialWeightedDegree_lt_of_mem_weightedSupportSpace (Nat.mul_pos hm hA) hweight hQ⟩

end

end ReedSolomon.HiddenDerivative
