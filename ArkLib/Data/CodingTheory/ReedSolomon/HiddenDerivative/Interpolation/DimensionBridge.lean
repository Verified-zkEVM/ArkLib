/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Counting
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Index
public import Mathlib.Algebra.BigOperators.Finsupp.Fin


/-!
# Exact interpolation dimension bridge

This file identifies the proof-facing monomial index from `InterpolationIndex.lean` with the
executable nested index from `Counting.lean`.  The equivalence splits a full exponent into the
four groups used by the exact dimension sum:

```text
X exponent, Y₀ exponent, Y₁ exponent, exponents of Y₂,...,Y_d.
```

Both inequalities `0 < d < D` are structural.  The first makes `Y₁` an actual coordinate;
the second makes all derivative weights positive, so the cap-free exact support is finite.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26].
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

open scoped BigOperators

variable {F : Type*} {D A d m M W : ℕ}

/-! ### Splitting full exponent coordinates -/

/-- Split `Y₀,...,Y_d` into the first two jets and the higher jets. -/
def jetIndexSplitEquiv (hd : 0 < d) :
    Fin (d + 1) ≃ Fin 2 ⊕ Fin (d - 1) :=
  (finCongr (by omega : d + 1 = 2 + (d - 1))).trans finSumFinEquiv.symm

/-- Coordinates `(x, ((b₀,b₁),c))` of a differential monomial exponent. -/
abbrev ExactExponentCoordinates (d : ℕ) :=
  ℕ × ((ℕ × ℕ) × HigherJetTuple d)

/-- Every exponent on `X,Y₀,...,Y_d` is equivalent to its four coordinate groups. -/
def exactExponentCoordinatesEquiv (hd : 0 < d) :
    (JetVariable d →₀ ℕ) ≃ ExactExponentCoordinates d :=
  Finsupp.optionEquiv.trans <|
    Equiv.prodCongr (Equiv.refl ℕ) <|
      (Finsupp.domCongr (jetIndexSplitEquiv hd)).toEquiv.trans <|
        Finsupp.sumFinsuppEquivProdFinsupp.trans <|
          Equiv.prodCongr (finTwoArrowEquiv' ℕ) Finsupp.equivFunOnFinite

@[simp]
theorem exactExponentCoordinatesEquiv_x (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    (exactExponentCoordinatesEquiv hd u).1 = u none :=
  rfl

@[simp]
theorem exactExponentCoordinatesEquiv_y₀ (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    (exactExponentCoordinatesEquiv hd u).2.1.1 = u (some ⟨0, by omega⟩) := by
  simp only [exactExponentCoordinatesEquiv, jetIndexSplitEquiv, AddEquiv.toEquiv_eq_coe,
    Equiv.trans_apply, Finsupp.optionEquiv_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Equiv.coe_trans, EquivLike.coe_coe, Prod.map_apply, id_eq, Function.comp_apply,
    Finsupp.domCongr_apply, Finsupp.sumFinsuppEquivProdFinsupp_apply,
    finTwoArrowEquiv'_apply, Fin.isValue, Finsupp.comapDomain_apply,
    Finsupp.equivMapDomain_apply, Equiv.symm_trans, Equiv.symm_symm, finCongr_symm,
    finSumFinEquiv_apply_left, finCongr_apply, Finsupp.some_apply]
  congr 2

@[simp]
theorem exactExponentCoordinatesEquiv_y₁ (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    (exactExponentCoordinatesEquiv hd u).2.1.2 = u (some ⟨1, by omega⟩) := by
  simp only [exactExponentCoordinatesEquiv, jetIndexSplitEquiv, AddEquiv.toEquiv_eq_coe,
    Equiv.trans_apply, Finsupp.optionEquiv_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Equiv.coe_trans, EquivLike.coe_coe, Prod.map_apply, id_eq, Function.comp_apply,
    Finsupp.domCongr_apply, Finsupp.sumFinsuppEquivProdFinsupp_apply,
    finTwoArrowEquiv'_apply, Fin.isValue, Finsupp.comapDomain_apply,
    Finsupp.equivMapDomain_apply, Equiv.symm_trans, Equiv.symm_symm, finCongr_symm,
    finSumFinEquiv_apply_left, finCongr_apply, Finsupp.some_apply]
  congr 2

@[simp]
theorem exactExponentCoordinatesEquiv_higher (hd : 0 < d) (u : JetVariable d →₀ ℕ)
    (i : Fin (d - 1)) :
    (exactExponentCoordinatesEquiv hd u).2.2 i =
      u (some ⟨i.val + 2, by omega⟩) := by
  simp only [exactExponentCoordinatesEquiv, jetIndexSplitEquiv, AddEquiv.toEquiv_eq_coe,
    Equiv.trans_apply, Finsupp.optionEquiv_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Equiv.coe_trans, EquivLike.coe_coe, Prod.map_apply, id_eq, Function.comp_apply,
    Finsupp.domCongr_apply, Finsupp.sumFinsuppEquivProdFinsupp_apply,
    finTwoArrowEquiv'_apply, Fin.isValue, Finsupp.comapDomain_apply,
    Finsupp.equivMapDomain_apply, Equiv.symm_trans, Equiv.symm_symm, finCongr_symm,
    finSumFinEquiv_apply_left, finCongr_apply, Finsupp.some_apply,
    Finsupp.equivFunOnFinite_apply, finSumFinEquiv_apply_right]
  congr 2
  apply Fin.ext
  simp [Nat.add_comm]

/-- Split a sum over the jet indices into `Y₀`, `Y₁`, and `Y₂,...,Y_d`. -/
theorem sum_jet_eq_y₀_add_y₁_add_higher (hd : 0 < d) (f : Fin (d + 1) → ℕ) :
    (∑ j, f j) = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ +
      ∑ i : Fin (d - 1), f ⟨i.val + 2, by omega⟩ := by
  calc
    (∑ j, f j) =
        ∑ z : Fin 2 ⊕ Fin (d - 1), f ((jetIndexSplitEquiv hd).symm z) := by
      symm
      exact Equiv.sum_comp (jetIndexSplitEquiv hd).symm f
    _ = (∑ i : Fin 2, f ((jetIndexSplitEquiv hd).symm (Sum.inl i))) +
          ∑ i : Fin (d - 1), f ((jetIndexSplitEquiv hd).symm (Sum.inr i)) := by
      rw [Fintype.sum_sum_type]
    _ = _ := by
      rw [Fin.sum_univ_two]
      apply congrArg₂ (· + ·)
      · apply congrArg₂ (· + ·) <;> congr 2
      · apply Finset.sum_congr rfl
        intro i hi
        congr 2
        apply Fin.ext
        simp [jetIndexSplitEquiv, Nat.add_comm]

/-- The abstract first-jet statistic is the `Y₁` coordinate of the split exponent. -/
theorem firstJetExponent_eq_coordinate (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    firstJetExponent u = (exactExponentCoordinatesEquiv hd u).2.1.2 := by
  rw [firstJetExponent, Finsupp.weight_eq_sum]
  rw [sum_jet_eq_y₀_add_y₁_add_higher hd]
  simp

/-- The full high-jet statistic is the anisotropic weight of the split higher tuple. -/
theorem fullHigherJetWeight_eq_coordinate (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    fullHigherJetWeight u =
      higherJetTupleWeight (exactExponentCoordinatesEquiv hd u).2.2 := by
  rw [fullHigherJetWeight, Finsupp.weight_eq_sum, higherJetTupleWeight]
  rw [sum_jet_eq_y₀_add_y₁_add_higher hd]
  simp [exactExponentCoordinatesEquiv_higher, mul_comm]

/-- The exact differential weight is the staircase cost plus the fixed higher-jet cost. -/
theorem exactInterpolationMonomialWeight_eq_coordinates (hd : 0 < d)
    (u : JetVariable d →₀ ℕ) :
    exactInterpolationMonomialWeight D u =
      (exactExponentCoordinatesEquiv hd u).1 +
      D * (exactExponentCoordinatesEquiv hd u).2.1.1 +
      (D - 1) * (exactExponentCoordinatesEquiv hd u).2.1.2 +
      higherJetTupleSpecializationCost D (exactExponentCoordinatesEquiv hd u).2.2 := by
  rw [exactInterpolationMonomialWeight_eq,
    Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  rw [sum_jet_eq_y₀_add_y₁_add_higher hd]
  simp only [Nat.sub_zero, nsmul_eq_mul, exactExponentCoordinatesEquiv_x,
    exactExponentCoordinatesEquiv_y₀, exactExponentCoordinatesEquiv_y₁,
    higherJetTupleSpecializationCost]
  simp_rw [exactExponentCoordinatesEquiv_higher hd]
  simp only [mul_comm, Nat.add_assoc]
  congr 3

/-! ### Eligible exponents and the nested counting index -/

/-- Coordinate form of exact interpolation eligibility.  The residual inequality is precisely
the staircase predicate used by `ExactDimensionIndex`. -/
def ExactDimensionCoordinatesEligible (D A d m M W : ℕ)
    (p : ExactExponentCoordinates d) : Prop :=
  p.2.1.2 ≤ M ∧
    higherJetTupleWeight p.2.2 ≤ W ∧
    p.1 + D * p.2.1.1 < exactDimensionResidual D m A p.2.1.2 p.2.2

/-- Exact support eligibility is equivalent to the nested count's coordinate predicate. -/
theorem exactInterpolationEligibleExponent_iff_coordinates (hd : 0 < d)
    (u : JetVariable d →₀ ℕ) :
    ExactInterpolationEligibleExponent D A d m M W u ↔
      ExactDimensionCoordinatesEligible D A d m M W (exactExponentCoordinatesEquiv hd u) := by
  rw [ExactInterpolationEligibleExponent, ExactDimensionCoordinatesEligible,
    firstJetExponent_eq_coordinate hd, fullHigherJetWeight_eq_coordinate hd,
    exactInterpolationMonomialWeight_eq_coordinates hd, exactDimensionResidual,
    Nat.lt_sub_iff_add_lt]
  simp only [Nat.add_assoc]

/-- The proof-facing eligible-exponent subtype in split coordinates. -/
def exactEligibleExponentCoordinateEquiv (hd : 0 < d) :
    {u : JetVariable d →₀ ℕ // ExactInterpolationEligibleExponent D A d m M W u} ≃
      {p : ExactExponentCoordinates d // ExactDimensionCoordinatesEligible D A d m M W p} :=
  Equiv.subtypeEquiv (exactExponentCoordinatesEquiv hd) fun u ↦
    exactInterpolationEligibleExponent_iff_coordinates hd u

/-- Split eligible coordinates into the higher-jet simplex, `Y₁` cap, and staircase index.
This coordinate-level equivalence only needs a positive staircase weight `D`; the stronger
`d < D` boundary enters through the proof-facing `ExactInterpolationIndex` API. -/
def exactCoordinateDimensionIndexEquiv (hD : 0 < D) :
    {p : ExactExponentCoordinates d // ExactDimensionCoordinatesEligible D A d m M W p} ≃
      ExactDimensionIndex D A d m M W where
  toFun p :=
    ⟨⟨p.1.2.2, mem_weightedHigherJetTuples.mpr p.2.2.1⟩,
      ⟨⟨p.1.2.1.2, Nat.lt_succ_of_le p.2.1⟩,
        (staircaseIndexEquiv D
          (exactDimensionResidual D m A p.1.2.1.2 p.1.2.2) hD).symm
            ⟨(p.1.1, p.1.2.1.1), p.2.2.2⟩⟩⟩
  invFun p :=
    let q := staircaseIndexEquiv D
      (exactDimensionResidual D m A p.2.1.val p.1.1) hD p.2.2
    ⟨(q.1.1, ((q.1.2, p.2.1.val), p.1.1)),
      ⟨Nat.le_of_lt_succ p.2.1.isLt, mem_weightedHigherJetTuples.mp p.1.2, q.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    simp [staircaseIndexEquiv]
  right_inv p := by
    rcases p with ⟨c, b₁, q⟩
    simp [staircaseIndexEquiv]

/-- Replace membership in the proof-facing finite set by its exact support predicate. -/
def exactInterpolationIndexEligibleEquiv (hdD : d < D) :
    ExactInterpolationIndex D A d m M W hdD ≃
      {u : JetVariable d →₀ ℕ // ExactInterpolationEligibleExponent D A d m M W u} :=
  Equiv.subtypeEquiv (Equiv.refl _) fun _ ↦ mem_exactInterpolationExponents

/-- Canonical equivalence between the exact monomial columns and the executable nested
dimension index.  These are the ambient hypotheses carried by the exact interpolation API:
`d > 0` supplies `Y₁`, while `d < D` supplies its cap-free finiteness proof. -/
def exactInterpolationIndexEquivExactDimensionIndex (hd : 0 < d) (hdD : d < D) :
    ExactInterpolationIndex D A d m M W hdD ≃ ExactDimensionIndex D A d m M W :=
    (exactInterpolationIndexEligibleEquiv hdD).trans <|
    (exactEligibleExponentCoordinateEquiv hd).trans <|
      exactCoordinateDimensionIndexEquiv (by omega)

/-- The proof-facing exact exponent set has exactly the paper's finite dimension sum. -/
theorem card_exactInterpolationExponents_eq_exactInterpolationDimensionCount
    (hd : 0 < d) (hdD : d < D) :
    (exactInterpolationExponents D A d m M W hdD).card =
      exactInterpolationDimensionCount D A d m M W := by
  rw [← Fintype.card_coe]
  exact (Fintype.card_congr
    (exactInterpolationIndexEquivExactDimensionIndex hd hdD)).trans
      (card_exactDimensionIndex D A d m M W)

/-- The exact interpolation space has the exact derivative-weighted dimension count. -/
theorem finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount [Field F]
    (hd : 0 < d) (hdD : d < D) :
    Module.finrank F (exactInterpolationSpace F D A d m M W hdD) =
      exactInterpolationDimensionCount D A d m M W := by
  rw [finrank_exactInterpolationSpace_eq_card hdD,
    card_exactInterpolationExponents_eq_exactInterpolationDimensionCount hd hdD]

/-- Total jet degree in the four coordinate groups. -/
theorem totalJetDegree_eq_coordinates (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    totalJetDegree u = (exactExponentCoordinatesEquiv hd u).2.1.1 +
      (exactExponentCoordinatesEquiv hd u).2.1.2 +
        higherJetTupleDegree (exactExponentCoordinatesEquiv hd u).2.2 := by
  rw [totalJetDegree, Finsupp.degree_eq_sum, sum_jet_eq_y₀_add_y₁_add_higher hd]
  simp [higherJetTupleDegree]

/-- Higher-jet degree in the existing coordinate split. -/
theorem fullHigherJetDegree_eq_coordinates (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    fullHigherJetDegree u =
      higherJetTupleDegree (exactExponentCoordinatesEquiv hd u).2.2 := by
  rw [fullHigherJetDegree, Finsupp.weight_eq_sum, sum_jet_eq_y₀_add_y₁_add_higher hd]
  simp [higherJetTupleDegree]

end
end HiddenDerivative
end ReedSolomon
