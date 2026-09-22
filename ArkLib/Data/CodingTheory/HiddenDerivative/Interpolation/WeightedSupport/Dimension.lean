/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Dimension
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Basic
public import ArkLib.ToMathlib.Combinatorics.CubicStaircase

/-!
# A lower bound on the dimension of the weighted support space

Write an exponent on `X, Y₀, ..., Y_d` (for `d > 0`) in the coordinates `(x, b₀, b₁, c)` of
`jetExponentCoordinatesEquiv`, where `c : Fin (d - 1) → ℕ` holds the exponents of
`Y₂, ..., Y_d`. The weighted support conditions of `WeightedSupport/Basic.lean` become

```text
sum_i (i + 1) c_i ≤ W,
x + D (b₀ + b₁ + sum_i c_i) < L.
```

The first condition only involves `c`, and says that `c` lies in the lattice simplex
`Finset.natWeightedSimplex (fun i ↦ i + 1) W`. Fix such a `c`. The second condition is then
`x + D (b₀ + b₁) < D * (L / D - ∑ i, c i)`, whose solutions `(x, b₀, b₁)` contain the images of the
slots `CubicStaircase.Slot D (L / D - ∑ i, c i)`. Different pairs `(c, slot)` give different
exponents. Hence the number of eligible exponents, and so the dimension of the weighted support
space, is at least

```text
sum_{c ∈ natWeightedSimplex (i + 1) W} CubicStaircase.count D (L / D - ∑ i, c i)
  ≥ sum_c D * (max (L / D - ∑ i, c i) 0) ^ 3 / 6.
```

## Main statements

* `weightedSupportEligible_coordinates_iff`: weighted-support eligibility in coordinates.
* `weightedSupportSlotExponent`, `weightedSupportSlotExponent_eligible` and
  `weightedSupportSlotExponent_injective`: the exponent represented by a higher-jet tuple and a
  cubic staircase slot.
* `sum_count_le_card_weightedSupportExponents` and `sum_count_le_finrank_weightedSupportSpace`:
  the exact staircase sum bounds the number of eligible exponents and the dimension.
* `weightedSupport_dimension_ge_cubic_sum`: the cubic lower bound on the dimension.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`Dimension.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source's
coordinates `exactExponentCoordinatesEquiv` are `jetExponentCoordinatesEquiv` of
`Interpolation/Dimension.lean`, its `weightedHigherJetTuples d W` is
`Finset.natWeightedSimplex (fun i : Fin (d - 1) ↦ i.val + 1) W` and its `higherJetTupleDegree c`
is `∑ i, c i`. The source's dependent type `WeightedSupportSlot` and its `Fintype` instance are
replaced by the `Finset.sigma` of the lattice simplex with the slot types; accordingly
`weightedSupportSlotExponent` takes the tuple `c` and the slot as separate arguments,
`weightedSupportSlotExponent_eligible` assumes `c` lies in the simplex, and
`card_weightedSupportSlot_le` with `card_weightedSupportSlot_eq` become
`sum_count_le_card_weightedSupportExponents`. The source's
`weightedSupport_dimension_ge_cubic_sum` keeps its statement. The coordinate lemma
`weightedSupportEligible_coordinates_iff` and the intermediate
`sum_count_le_finrank_weightedSupportSpace` are new. The integral and probability forms of the
bound are in `WeightedSupport/Estimate.lean`.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential Finset

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {d D W : ℕ} {L : ℝ}

/-- Weighted-support eligibility of the exponent `X^x Y₀^b₀ Y₁^b₁ Y₂^c₀ ⋯ Y_d^c_(d-2)`: the
higher-jet weight `∑_i (i + 1) c_i` is at most `W` and the coarse weight
`x + D (b₀ + b₁ + ∑_i c_i)` is below `L`. -/
theorem weightedSupportEligible_coordinates_iff (hd : 0 < d) (x b₀ b₁ : ℕ)
    (c : Fin (d - 1) → ℕ) :
    WeightedSupportEligible D d W L ((jetExponentCoordinatesEquiv hd).symm (x, b₀, b₁, c)) ↔
      ∑ i : Fin (d - 1), (i.val + 1) * c i ≤ W ∧
        ((x + D * (b₀ + b₁ + ∑ i, c i) : ℕ) : ℝ) < L := by
  set u := (jetExponentCoordinatesEquiv hd).symm (x, b₀, b₁, c)
  have hu : jetExponentCoordinatesEquiv hd u = (x, b₀, b₁, c) := Equiv.apply_symm_apply _ _
  have hx : u none = x := congrArg Prod.fst hu
  rw [WeightedSupportEligible, fullHigherJetWeight_eq_coordinates hd,
    totalJetDegree_eq_coordinates hd, hu, hx]

/-- The exponent `X^x Y₀^b₀ Y₁^b₁ Y^c`, where `(x, b₀, b₁)` are the exponents
`CubicStaircase.Slot.exponents` of the slot `a` and `c` holds the exponents of `Y₂, ..., Y_d`. -/
def weightedSupportSlotExponent (hd : 0 < d) (c : Fin (d - 1) → ℕ) {L' : ℝ}
    (a : CubicStaircase.Slot D L') : JetVariable d →₀ ℕ :=
  (jetExponentCoordinatesEquiv hd).symm (a.exponents.1, a.exponents.2.1, a.exponents.2.2, c)

/-- If `c` lies in the higher-jet lattice simplex of budget `W` and `0 < D`, every slot of the
cubic staircase at the remaining cutoff `L / D - ∑ i, c i` gives an eligible exponent. The slot
satisfies `x + D (b₀ + b₁) < D * (L / D - ∑ i, c i) = L - D * ∑ i, c i`; the hypothesis `0 < D`
is used to cancel `D` against `L / D`. -/
theorem weightedSupportSlotExponent_eligible (hd : 0 < d) (hD : 0 < D) {c : Fin (d - 1) → ℕ}
    (hc : c ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W)
    (a : CubicStaircase.Slot D (L / D - ((∑ i, c i : ℕ) : ℝ))) :
    WeightedSupportEligible D d W L (weightedSupportSlotExponent hd c a) := by
  rw [weightedSupportSlotExponent, weightedSupportEligible_coordinates_iff]
  refine ⟨(mem_natWeightedSimplex fun i => Nat.succ_ne_zero _).mp hc, ?_⟩
  have hslot := a.weighted_degree_lt
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hcancel : (D : ℝ) * (L / D - ((∑ i, c i : ℕ) : ℝ)) = L - D * ((∑ i, c i : ℕ) : ℝ) := by
    field_simp
  rw [hcancel] at hslot
  push_cast at hslot ⊢
  linarith

/-- Different pairs of a higher-jet tuple and a slot give different exponents: the tuple is read
off the coordinates, and slots are determined by their exponents
(`CubicStaircase.Slot.exponents_injective`). -/
theorem weightedSupportSlotExponent_injective (hd : 0 < d) {c c' : Fin (d - 1) → ℕ} {L₁ L₂ : ℝ}
    {a : CubicStaircase.Slot D L₁} {a' : CubicStaircase.Slot D L₂}
    (h : weightedSupportSlotExponent hd c a = weightedSupportSlotExponent hd c' a') :
    c = c' ∧ a.exponents = a'.exponents := by
  have h' := (jetExponentCoordinatesEquiv hd).symm.injective h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨hx, hb₀, hb₁, hc⟩ := h'
  exact ⟨hc, Prod.ext hx (Prod.ext hb₀ hb₁)⟩

/-- For `0 < d` and `0 < D`, the number of weighted-support eligible exponents is at least the
sum over the higher-jet lattice simplex of the cubic staircase counts at the remaining cutoffs
`L / D - ∑ i, c i`. The hypothesis `0 < d` provides the `Y₁` coordinate; `0 < D` is needed for
the support to be finite. -/
theorem sum_count_le_card_weightedSupportExponents (hd : 0 < d) (hD : 0 < D) :
    ∑ c ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W,
        CubicStaircase.count D (L / D - ((∑ i, c i : ℕ) : ℝ)) ≤
      #(weightedSupportExponents D d W L hD) := by
  classical
  let s := (natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W).sigma fun c =>
    (univ : Finset (CubicStaircase.Slot D (L / D - ((∑ i, c i : ℕ) : ℝ))))
  have hs : #s = ∑ c ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W,
      CubicStaircase.count D (L / D - ((∑ i, c i : ℕ) : ℝ)) := by
    simp only [s, card_sigma, card_univ, CubicStaircase.card_slot]
  rw [← hs]
  refine card_le_card_of_injOn (fun p => weightedSupportSlotExponent hd p.1 p.2) ?_ ?_
  · rintro ⟨c, a⟩ hp
    rw [coe_sigma, Set.mem_sigma_iff] at hp
    exact mem_coe.mpr (mem_weightedSupportExponents.mpr
      (weightedSupportSlotExponent_eligible hd hD hp.1 a))
  · rintro ⟨c, a⟩ - ⟨c', a'⟩ - h
    obtain ⟨rfl, ha⟩ := weightedSupportSlotExponent_injective hd h
    dsimp only at ha ⊢
    rw [CubicStaircase.Slot.exponents_injective _ _ ha]

/-- Over a field, the dimension of the weighted support space is at least the staircase sum of
`sum_count_le_card_weightedSupportExponents`. -/
theorem sum_count_le_finrank_weightedSupportSpace (F : Type*) [Field F] (hd : 0 < d)
    (hD : 0 < D) :
    ∑ c ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W,
        CubicStaircase.count D (L / D - ((∑ i, c i : ℕ) : ℝ)) ≤
      Module.finrank F (weightedSupportSpace F D d W L hD) := by
  rw [finrank_weightedSupportSpace_eq_card]
  exact sum_count_le_card_weightedSupportExponents hd hD

/-- The cubic lower bound on the dimension of the weighted support space: for `0 < d` and
`0 < D`, the sum over the higher-jet lattice simplex of `D * (max (L / D - ∑ i, c i) 0) ^ 3 / 6`
is at most the dimension. Each term bounds one staircase count from below
(`CubicStaircase.count_ge_cubic`), for every real cutoff. -/
theorem weightedSupport_dimension_ge_cubic_sum (F : Type*) [Field F] (hd : 0 < d) (hD : 0 < D) :
    ∑ c ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W,
        (D : ℝ) * (max (L / D - ((∑ i, c i : ℕ) : ℝ)) 0) ^ 3 / 6 ≤
      (Module.finrank F (weightedSupportSpace F D d W L hD) : ℝ) :=
  (sum_le_sum fun c _ => CubicStaircase.count_ge_cubic _ _).trans <| by
    rw [← Nat.cast_sum]
    exact_mod_cast sum_count_le_finrank_weightedSupportSpace F hd hD

end

end ReedSolomon.HiddenDerivative
