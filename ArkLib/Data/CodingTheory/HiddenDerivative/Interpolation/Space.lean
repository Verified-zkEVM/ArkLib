/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Counting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Index
public import ArkLib.ToMathlib.Finsupp.Weight

/-!
# The support-first interpolation space

This file defines the rectangular interpolation space of the hidden-derivative argument and the
higher-jet exponent sets used to count it. The variables are `X` and the jets `Y₀, ..., Y_d`. An
exponent `u` is eligible for the parameters `d m A K B W C` when

```text
b₁ ≤ m,   ∑_j b_j ≤ B,   a + (K - 1) ∑_j b_j < m A,
∑_{j ≥ 2} (j - 1) b_j ≤ W,   ∑_{j ≥ 2} b_j ≤ C,
```

where `a` is the exponent of `X` and `b_j` that of `Y_j`. The space is finite for all parameters,
because the second and third clauses bound the total degree even though several of the weights
vanish on some variables.

For `d < D < K` every eligible exponent is eligible for the exact interpolation space of
`Interpolation/Index.lean` with `M = m`, since the specialization weight `a + ∑_j (D - j) b_j`
is at most `a + (K - 1) ∑_j b_j`. The rectangular space is used for lower bounds
on the dimension, and this comparison transfers them to the exact space.

The file also adds the derivative-order weight `fullDerivativeJetWeight`, which charges `Y_j`
weight `j` and so also counts `Y₁`, and the ordinary higher-jet degree `fullHigherJetDegree`.

## Main statements

* `goodHigherExponentSet_finite` and `card_goodHigherExponents_of_le`: for `W ≤ C` the degree
  bound is implied by the weight bound, and the eligible higher-jet exponents are counted by
  `weightedHigherJetCount d W`.
* `globalEligibleExponentSet_finite`, `interpolationSpace`, `mem_interpolationSpace_iff`,
  `interpolationSpaceBasis`, and `finrank_interpolationSpace_eq_card`.
* `GlobalEligibleExponent.toExactInterpolationEligibleExponent`,
  `interpolationSpace_le_exactInterpolationSpace`, and
  `finrank_interpolationSpace_le_exactInterpolationSpace`: the comparison with the exact space,
  for every `K > D`.
* `fullHigherJetWeight_le_fullDerivativeJetWeight` and `firstJetExponent_le_totalJetDegree`.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Space.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d (adapted there from Kai Zhe Zheng's
`rs-ld-mca` formalization): `HigherJetExponent`, `higherJetWeight`, `higherJetDegree`,
`GoodHigherExponent`, `goodHigherExponentSet`, `goodHigherExponentSet_finite`,
`goodHigherExponents`, `mem_goodHigherExponents`, `firstJetExponent_le_totalJetDegree`,
`fullDerivativeJetWeight`, `fullHigherJetWeight_le_fullDerivativeJetWeight`,
`fullHigherJetDegree`, `GlobalEligibleExponent`, `globalEligibleExponentSet`,
`globalEligibleExponentSet_finite`, `globalEligibleExponents`, `mem_globalEligibleExponents`,
`interpolationSpace`, `mem_interpolationSpace_iff`, `monomial_mem_interpolationSpace`, and
`interpolationSpaceBasis`. `firstJetExponent`, `totalJetDegree`, `fullHigherJetWeight`, and
`exponentDegree_eq_x_add_totalJetDegree` (here `degree_eq_add_totalJetDegree`) are already in
`Interpolation/Index.lean` and `PolynomialDifferential`. As there, `fullDerivativeJetWeight` and
`fullHigherJetDegree` are `Finsupp.weight` of the pointwise weights `jetDerivativeWeight` and
`jetHigherDegreeWeight`.

From the source's `Interpolation/Index.lean`:
`GlobalEligibleExponent.toExactInterpolationEligibleExponent`,
`interpolationSpace_le_exactInterpolationSpace`, and
`finrank_interpolationSpace_le_exactInterpolationSpace`. The source fixed `K = D + 1`; here any
`K` with `D < K` is allowed. The finrank comparison is proved from the inclusion of the exponent
sets, which also gives `globalEligibleExponents_subset_exactInterpolationExponents`.

From the source's `Interpolation/Counting.lean`: `goodHigherExponents_self_eq_weighted_count`,
here `card_goodHigherExponents_of_le` for every `C ≥ W`, with the source statement at `C = W`
recovered in the tests.

Deferred: the shell and staircase counts, `exactInterpolationDimensionCount`, and the lower
bound `finrank_interpolationSpace_lowerBound` of the source's dimension files.

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Section 3.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {d : ℕ}

/-! ### Higher-jet exponents -/

/-- Exponent vectors of the higher jets `Y₂, ..., Y_d`; coordinate `i : Fin (d - 1)` is the
exponent of `Y_(i+2)`. For `d ≤ 1` the type has exactly one element. -/
abbrev HigherJetExponent (d : ℕ) := Fin (d - 1) →₀ ℕ

/-- The anisotropic weight `∑_i (i + 1) c_i` of a higher-jet exponent, which gives `Y_j` weight
`j - 1`. -/
def higherJetWeight (c : HigherJetExponent d) : ℕ :=
  c.weight fun i : Fin (d - 1) => i.val + 1

/-- The ordinary degree `∑_i c_i` of a higher-jet exponent. -/
def higherJetDegree (c : HigherJetExponent d) : ℕ :=
  c.degree

/-- Every weight in `higherJetWeight` is at least one, so the degree is at most the weight. -/
theorem higherJetDegree_le_higherJetWeight (c : HigherJetExponent d) :
    higherJetDegree c ≤ higherJetWeight c := by
  rw [higherJetDegree, higherJetWeight, Finsupp.degree_eq_weight_one]
  exact Finsupp.weight_le_weight (fun i => by simp) c

/-- A higher-jet exponent is good for `W, C` if its weight is at most `W` and its degree at most
`C`. -/
def GoodHigherExponent (d W C : ℕ) (c : HigherJetExponent d) : Prop :=
  higherJetWeight c ≤ W ∧ higherJetDegree c ≤ C

/-- The set of good higher-jet exponents. -/
def goodHigherExponentSet (d W C : ℕ) : Set (HigherJetExponent d) :=
  {c | GoodHigherExponent d W C c}

/-- The good higher-jet exponents form a finite set, by the weight bound alone. -/
theorem goodHigherExponentSet_finite (d W C : ℕ) : (goodHigherExponentSet d W C).Finite :=
  (Finsupp.finite_of_nat_weight_le (fun i : Fin (d - 1) => i.val + 1) (fun _ => by omega)
    W).subset fun _ hc => hc.1

/-- The finite set of good higher-jet exponents. -/
def goodHigherExponents (d W C : ℕ) : Finset (HigherJetExponent d) :=
  (goodHigherExponentSet_finite d W C).toFinset

/-- Membership in `goodHigherExponents` is the predicate `GoodHigherExponent`. -/
@[simp]
theorem mem_goodHigherExponents {W C : ℕ} {c : HigherJetExponent d} :
    c ∈ goodHigherExponents d W C ↔ GoodHigherExponent d W C c := by
  simp [goodHigherExponents, goodHigherExponentSet]

/-- If `W ≤ C` the degree bound follows from the weight bound, and the good exponents are
counted by the weighted simplex: there are `weightedHigherJetCount d W` of them. For `C < W` the
degree bound can remove exponents: at `d = 3`, `W = 2`, `C = 1` the exponent `Y₂²` is excluded. -/
theorem card_goodHigherExponents_of_le {W C : ℕ} (hWC : W ≤ C) :
    (goodHigherExponents d W C).card = weightedHigherJetCount d W := by
  classical
  have hw : ∀ i : Fin (d - 1), i.val + 1 ≠ 0 := fun i => Nat.add_one_ne_zero i.val
  rw [weightedHigherJetCount,
    ← Finset.card_finsupp_weight_le_eq_card_natWeightedSimplex _ hw W,
    ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  rw [mem_goodHigherExponents, GoodHigherExponent]
  exact ⟨fun h => h.1, fun h => ⟨h, (higherJetDegree_le_higherJetWeight c).trans (h.trans hWC)⟩⟩

/-! ### Further jet weights -/

/-- The derivative-order weight: `X` has weight zero and `Y_j` has weight `j`. -/
def jetDerivativeWeight : JetVariable d → ℕ
  | none => 0
  | some j => j.val

/-- The ordinary-degree weight of the higher jets: `Y_j` has weight one for `j ≥ 2` and every
other variable has weight zero. -/
def jetHigherDegreeWeight : JetVariable d → ℕ
  | none => 0
  | some j => if 2 ≤ j.val then 1 else 0

/-- The derivative-order weight `∑_j j b_j` of an exponent. Unlike `fullHigherJetWeight`, it also
counts `Y₁`. -/
def fullDerivativeJetWeight (u : JetVariable d →₀ ℕ) : ℕ :=
  u.weight jetDerivativeWeight

/-- The ordinary degree `∑_{j ≥ 2} b_j` of an exponent in the higher jets. -/
def fullHigherJetDegree (u : JetVariable d →₀ ℕ) : ℕ :=
  u.weight jetHigherDegreeWeight

/-- The exponent of `Y₁` is at most the total jet degree. -/
theorem firstJetExponent_le_totalJetDegree (u : JetVariable d →₀ ℕ) :
    firstJetExponent u ≤ totalJetDegree u :=
  Finsupp.weight_le_weight (fun v => by
    rcases v with _ | j
    · exact le_rfl
    · simp only [jetFirstWeight, jetDegreeWeight]; split_ifs <;> omega) u

/-- The higher-jet weight is at most the derivative-order weight, since `j - 1 ≤ j`. -/
theorem fullHigherJetWeight_le_fullDerivativeJetWeight (u : JetVariable d →₀ ℕ) :
    fullHigherJetWeight u ≤ fullDerivativeJetWeight u :=
  Finsupp.weight_le_weight (fun v => by
    rcases v with _ | j
    · exact le_rfl
    · exact Nat.sub_le _ _) u

/-! ### The global eligible exponents -/

/-- Eligibility for the rectangular space: at most `m` copies of `Y₁`, total jet degree at most
`B`, `a + (K - 1) ∑_j b_j < m A`, higher-jet weight at most `W`, and higher-jet degree at most
`C`. -/
def GlobalEligibleExponent (d m A K B W C : ℕ) (u : JetVariable d →₀ ℕ) : Prop :=
  firstJetExponent u ≤ m ∧
    totalJetDegree u ≤ B ∧
    u none + (K - 1) * totalJetDegree u < m * A ∧
    fullHigherJetWeight u ≤ W ∧
    fullHigherJetDegree u ≤ C

/-- The set of globally eligible exponents. -/
def globalEligibleExponentSet (d m A K B W C : ℕ) : Set (JetVariable d →₀ ℕ) :=
  {u | GlobalEligibleExponent d m A K B W C u}

/-- The globally eligible exponents form a finite set for all parameters: the `X` exponent is
below `m A` and the total jet degree is at most `B`. -/
theorem globalEligibleExponentSet_finite (d m A K B W C : ℕ) :
    (globalEligibleExponentSet d m A K B W C).Finite := by
  refine (Finsupp.finite_of_degree_le (m * A + B)).subset fun u hu => ?_
  have hx : u none < m * A := lt_of_le_of_lt (Nat.le_add_right _ _) hu.2.2.1
  change u.degree ≤ m * A + B
  rw [degree_eq_add_totalJetDegree]
  exact Nat.add_le_add hx.le hu.2.1

/-- The finite set of globally eligible exponents. -/
def globalEligibleExponents (d m A K B W C : ℕ) : Finset (JetVariable d →₀ ℕ) :=
  (globalEligibleExponentSet_finite d m A K B W C).toFinset

/-- Membership in `globalEligibleExponents` is the predicate `GlobalEligibleExponent`. -/
@[simp]
theorem mem_globalEligibleExponents {m A K B W C : ℕ} {u : JetVariable d →₀ ℕ} :
    u ∈ globalEligibleExponents d m A K B W C ↔ GlobalEligibleExponent d m A K B W C u := by
  simp [globalEligibleExponents, globalEligibleExponentSet]

/-! ### The rectangular space -/

/-- The polynomials supported on globally eligible exponents. -/
def interpolationSpace (R : Type*) [CommSemiring R] (d m A K B W C : ℕ) :
    Submodule R (DifferentialPolynomial R d) :=
  MvPolynomial.restrictSupport R (globalEligibleExponents d m A K B W C : Set _)

/-- A polynomial lies in the rectangular space exactly when every exponent in its support is
globally eligible. -/
theorem mem_interpolationSpace_iff {R : Type*} [CommSemiring R] {m A K B W C : ℕ}
    {Q : DifferentialPolynomial R d} :
    Q ∈ interpolationSpace R d m A K B W C ↔
      ∀ u ∈ Q.support, GlobalEligibleExponent d m A K B W C u := by
  rw [interpolationSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_globalEligibleExponents]

/-- A monomial lies in the space exactly when its exponent is eligible or its coefficient is
zero. -/
@[simp]
theorem monomial_mem_interpolationSpace {R : Type*} [CommSemiring R] {m A K B W C : ℕ}
    {u : JetVariable d →₀ ℕ} {a : R} :
    MvPolynomial.monomial u a ∈ interpolationSpace R d m A K B W C ↔
      GlobalEligibleExponent d m A K B W C u ∨ a = 0 := by
  simp [interpolationSpace]

/-- The monomial basis of the rectangular space. -/
def interpolationSpaceBasis (R : Type*) [CommSemiring R] (d m A K B W C : ℕ) :
    Module.Basis (globalEligibleExponents d m A K B W C) R (interpolationSpace R d m A K B W C) :=
  MvPolynomial.basisRestrictSupport (R := R)
    (↑(globalEligibleExponents d m A K B W C) : Set (JetVariable d →₀ ℕ))

/-- The dimension of the rectangular space over a field is the number of eligible exponents. -/
theorem finrank_interpolationSpace_eq_card (R : Type*) [Field R] (d m A K B W C : ℕ) :
    Module.finrank R (interpolationSpace R d m A K B W C) =
      (globalEligibleExponents d m A K B W C).card := by
  rw [Module.finrank_eq_card_basis (interpolationSpaceBasis R d m A K B W C)]
  exact Fintype.card_coe _

/-! ### Comparison with the exact space -/

/-- For `D < K` the specialization weight of an exponent is at most `a + (K - 1) ∑_j b_j`, since
every jet variable has specialization weight `D - j ≤ D ≤ K - 1`. -/
theorem weight_differentialWeight_le {D K : ℕ} (hDK : D < K) (u : JetVariable d →₀ ℕ) :
    u.weight (differentialWeight D) ≤ u none + (K - 1) * totalJetDegree u := by
  rw [weight_differentialWeight_eq, totalJetDegree_eq_sum, Finset.mul_sum]
  refine Nat.add_le_add_left (Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ ?_) _
  omega

/-- A globally eligible exponent with `D < K` is eligible for the exact space with `M = m`. The
hypothesis `D < K` is needed: for `K ≤ D` the third clause of global eligibility no longer bounds
the specialization weight (at `d = 0`, `K = 1`, `D = 1`, `m = A = 1` the exponent `Y₀` is
globally eligible but has specialization weight `1 = m A`). -/
theorem GlobalEligibleExponent.toExactInterpolationEligibleExponent {D m A K B W C : ℕ}
    (hDK : D < K) {u : JetVariable d →₀ ℕ} (hu : GlobalEligibleExponent d m A K B W C u) :
    ExactInterpolationEligibleExponent D A d m m W u :=
  ⟨hu.1, hu.2.2.2.1, (weight_differentialWeight_le hDK u).trans_lt hu.2.2.1⟩

/-- The eligible exponents of the rectangular space form a subset of those of the exact space. -/
theorem globalEligibleExponents_subset_exactInterpolationExponents {D m A K B W C : ℕ}
    (hdD : d < D) (hDK : D < K) :
    globalEligibleExponents d m A K B W C ⊆ exactInterpolationExponents D A d m m W hdD :=
  fun _ hu => mem_exactInterpolationExponents.mpr
    ((mem_globalEligibleExponents.mp hu).toExactInterpolationEligibleExponent hDK)

/-- For `d < D < K` the rectangular space is contained in the exact space with `M = m`. -/
theorem interpolationSpace_le_exactInterpolationSpace {R : Type*} [CommSemiring R]
    {D m A K B W C : ℕ} (hdD : d < D) (hDK : D < K) :
    interpolationSpace R d m A K B W C ≤ exactInterpolationSpace R D A d m m W hdD :=
  MvPolynomial.restrictSupport_mono R
    (Finset.coe_subset.mpr (globalEligibleExponents_subset_exactInterpolationExponents hdD hDK))

/-- For `d < D < K` the rectangular space has dimension at most that of the exact space with
`M = m`. -/
theorem finrank_interpolationSpace_le_exactInterpolationSpace (R : Type*) [Field R]
    {D m A K B W C : ℕ} (hdD : d < D) (hDK : D < K) :
    Module.finrank R (interpolationSpace R d m A K B W C) ≤
      Module.finrank R (exactInterpolationSpace R D A d m m W hdD) := by
  rw [finrank_interpolationSpace_eq_card, finrank_exactInterpolationSpace_eq_card]
  exact Finset.card_le_card (globalEligibleExponents_subset_exactInterpolationExponents hdD hDK)

end

end ReedSolomon.HiddenDerivative
