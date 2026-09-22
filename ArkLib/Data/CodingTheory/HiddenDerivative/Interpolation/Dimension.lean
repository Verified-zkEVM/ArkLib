/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Space

/-!
# Dimensions of the interpolation spaces

This file computes the dimension of the exact interpolation space of `Interpolation/Index.lean`
and bounds the dimension of the rectangular interpolation space of `Interpolation/Space.lean`
from below. Both arguments read an exponent on `X, Y₀, ..., Y_d` in four coordinates: the
exponent `x` of `X`, the exponents `b₀` and `b₁` of `Y₀` and `Y₁`, and the tuple `c` of
exponents of `Y₂, ..., Y_d`. This needs `d > 0`, so that `Y₁` exists.

* In coordinates, an exponent is eligible for the exact space exactly when `b₁ ≤ M`, `c` lies in
  the higher-jet weighted simplex of weight `W`, and `(x, b₀)` lies in the staircase of slope `D`
  and length `m A - ((D - 1) b₁ + ∑_i (D - (i + 2)) c_i)`. Hence the exact space has dimension
  `exactInterpolationDimensionCount D A d m M W` of `Interpolation/Counting.lean`.
* For every good higher-jet exponent `c`, `x < N`, `b₀ < H₀`, and `b₁ < H₁`, the exponent with
  these coordinates is globally eligible once `H₁ ≤ m`, `C + H₀ + H₁ ≤ B`, and
  `N + (K - 1)(C + H₀ + H₁) ≤ m A`. These exponents are distinct, which bounds the dimension of
  the rectangular space below by `#(goodHigherExponents d W C) * N * H₀ * H₁`.

## Main statements

* `jetExponentCoordinatesEquiv`: exponents on `X, Y₀, ..., Y_d` are equivalent to coordinate
  tuples `(x, b₀, b₁, c)` when `d > 0`.
* `weight_eq_coordinates`, `firstJetExponent_eq_coordinates`,
  `fullHigherJetWeight_eq_coordinates`, `fullHigherJetDegree_eq_coordinates`,
  `totalJetDegree_eq_coordinates`, and `weight_differentialWeight_eq_coordinates`: the jet weights
  in coordinates.
* `exactInterpolationEligibleExponent_iff_coordinates` and
  `globalEligibleExponent_iff_coordinates`: both eligibility conditions in coordinates.
* `card_exactInterpolationExponents` and
  `finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount`: for `0 < d < D` the exact
  space has dimension `exactInterpolationDimensionCount D A d m M W`.
* `card_mul_le_card_globalEligibleExponents` and `le_finrank_interpolationSpace`: the
  rectangular lower bound with independent side lengths `N`, `H₀`, `H₁`.
* `finrank_interpolationSpace_lowerBound`: the case `N = (K - 1) H` and `H₀ = H₁ = H`.
* `card_goodHigherExponents_mul_le_finrank_exactInterpolationSpace`: the same lower bound for the
  exact space with `M = m`, for every `D` with `d < D < K`.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], Section 3.
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential Finset

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {d : ℕ}

/-! ### Exponent coordinates -/

private theorem sum_jet_eq {M : Type*} [AddCommMonoid M] (hd : 0 < d) (f : Fin (d + 1) → M) :
    ∑ j, f j = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ +
      ∑ i : Fin (d - 1), f ⟨i.val + 2, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  exact (add_assoc _ _ _).symm

/-- For `d > 0`, an exponent on `X, Y₀, ..., Y_d` is determined by the exponents `x` of `X`,
`b₀` of `Y₀`, `b₁` of `Y₁`, and the tuple `c` of exponents of `Y₂, ..., Y_d`, where coordinate
`i : Fin (d - 1)` of `c` is the exponent of `Y_(i+2)`. The hypothesis `0 < d` provides `Y₁`; for
`d = 0` there is no `Y₁` and the fourth component would be spurious. -/
def jetExponentCoordinatesEquiv (hd : 0 < d) :
    (JetVariable d →₀ ℕ) ≃ ℕ × ℕ × ℕ × (Fin (d - 1) → ℕ) where
  toFun u := (u none, u (some ⟨0, by omega⟩), u (some ⟨1, by omega⟩),
    fun i => u (some ⟨i.val + 2, by omega⟩))
  invFun p := Finsupp.equivFunOnFinite.symm fun
    | none => p.1
    | some j =>
      if h₀ : j.val = 0 then p.2.1
      else if h₁ : j.val = 1 then p.2.2.1
      else p.2.2.2 ⟨j.val - 2, by have := j.isLt; omega⟩
  left_inv u := by
    ext v
    rcases v with _ | ⟨j, hj⟩
    · rfl
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
      split_ifs with h0 h1
      · subst h0; rfl
      · subst h1; rfl
      · congr 2
        ext
        simp only
        omega
  right_inv p := by
    obtain ⟨x, b₀, b₁, c⟩ := p
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (funext fun i => ?_)))
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    split_ifs <;> first | omega | contradiction | rfl

/-- The coordinates of an exponent `u` are `u X`, `u Y₀`, `u Y₁`, and `i ↦ u Y_(i+2)`. -/
@[simp]
theorem jetExponentCoordinatesEquiv_apply (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    jetExponentCoordinatesEquiv hd u = (u none, u (some ⟨0, by omega⟩),
      u (some ⟨1, by omega⟩), fun i => u (some ⟨i.val + 2, by omega⟩)) :=
  rfl

/-- The weight of an exponent for any weight function `w` on the variables, in coordinates:
`w X · x + w Y₀ · b₀ + w Y₁ · b₁ + ∑_i w Y_(i+2) · c_i`. -/
theorem weight_eq_coordinates (hd : 0 < d) (w : JetVariable d → ℕ) (u : JetVariable d →₀ ℕ) :
    u.weight w = w none * (jetExponentCoordinatesEquiv hd u).1 +
      w (some ⟨0, by omega⟩) * (jetExponentCoordinatesEquiv hd u).2.1 +
      w (some ⟨1, by omega⟩) * (jetExponentCoordinatesEquiv hd u).2.2.1 +
      ∑ i : Fin (d - 1), w (some ⟨i.val + 2, by omega⟩) *
        (jetExponentCoordinatesEquiv hd u).2.2.2 i := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_option,
    sum_jet_eq hd]
  simp only [smul_eq_mul, jetExponentCoordinatesEquiv_apply, mul_comm, add_assoc]

/-- The `Y₁` exponent is the third coordinate. -/
theorem firstJetExponent_eq_coordinates (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    firstJetExponent u = (jetExponentCoordinatesEquiv hd u).2.2.1 := by
  rw [firstJetExponent, weight_eq_coordinates hd]
  simp [jetFirstWeight]

/-- The higher-jet weight is `∑_i (i + 1) c_i`. -/
theorem fullHigherJetWeight_eq_coordinates (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    fullHigherJetWeight u =
      ∑ i : Fin (d - 1), (i.val + 1) * (jetExponentCoordinatesEquiv hd u).2.2.2 i := by
  rw [fullHigherJetWeight, weight_eq_coordinates hd]
  simp [jetHigherWeight]

/-- The higher-jet degree is `∑_i c_i`. -/
theorem fullHigherJetDegree_eq_coordinates (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    fullHigherJetDegree u = ∑ i : Fin (d - 1), (jetExponentCoordinatesEquiv hd u).2.2.2 i := by
  rw [fullHigherJetDegree, weight_eq_coordinates hd]
  simp [jetHigherDegreeWeight]

/-- The total jet degree is `b₀ + b₁ + ∑_i c_i`. -/
theorem totalJetDegree_eq_coordinates (hd : 0 < d) (u : JetVariable d →₀ ℕ) :
    totalJetDegree u = (jetExponentCoordinatesEquiv hd u).2.1 +
      (jetExponentCoordinatesEquiv hd u).2.2.1 +
      ∑ i : Fin (d - 1), (jetExponentCoordinatesEquiv hd u).2.2.2 i := by
  rw [totalJetDegree, weight_eq_coordinates hd]
  simp [jetDegreeWeight]

/-- The specialization weight is `x + D b₀ + (D - 1) b₁ + ∑_i (D - (i + 2)) c_i`. -/
theorem weight_differentialWeight_eq_coordinates (hd : 0 < d) (D : ℕ) (u : JetVariable d →₀ ℕ) :
    u.weight (differentialWeight D) = (jetExponentCoordinatesEquiv hd u).1 +
      D * (jetExponentCoordinatesEquiv hd u).2.1 +
      (D - 1) * (jetExponentCoordinatesEquiv hd u).2.2.1 +
      higherJetTupleSpecializationCost D (jetExponentCoordinatesEquiv hd u).2.2.2 := by
  rw [weight_eq_coordinates hd, higherJetTupleSpecializationCost]
  simp

/-! ### The exact dimension -/

/-- Exact eligibility in coordinates: `b₁ ≤ M`, `∑_i (i + 1) c_i ≤ W`, and
`x + D b₀ < m A - ((D - 1) b₁ + ∑_i (D - (i + 2)) c_i)`. The last condition is the staircase
condition of `exactInterpolationDimensionCount`. -/
theorem exactInterpolationEligibleExponent_iff_coordinates (hd : 0 < d) {D A m M W : ℕ}
    (u : JetVariable d →₀ ℕ) :
    ExactInterpolationEligibleExponent D A d m M W u ↔
      (jetExponentCoordinatesEquiv hd u).2.2.1 ≤ M ∧
      ∑ i : Fin (d - 1), (i.val + 1) * (jetExponentCoordinatesEquiv hd u).2.2.2 i ≤ W ∧
      (jetExponentCoordinatesEquiv hd u).1 + D * (jetExponentCoordinatesEquiv hd u).2.1 <
        exactDimensionResidual D m A (jetExponentCoordinatesEquiv hd u).2.2.1
          (jetExponentCoordinatesEquiv hd u).2.2.2 := by
  rw [ExactInterpolationEligibleExponent, firstJetExponent_eq_coordinates hd,
    fullHigherJetWeight_eq_coordinates hd, weight_differentialWeight_eq_coordinates hd,
    exactDimensionResidual]
  omega

/-- Reorder coordinates `(x, b₀, b₁, c)` as `⟨(c, b₁), (x, b₀)⟩`. -/
private def coordinatesSigmaEquiv :
    ℕ × ℕ × ℕ × (Fin (d - 1) → ℕ) ≃ Σ _ : (Fin (d - 1) → ℕ) × ℕ, ℕ × ℕ where
  toFun p := ⟨(p.2.2.2, p.2.2.1), (p.1, p.2.1)⟩
  invFun q := (q.2.1, q.2.2, q.1.2, q.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- For `0 < d < D` the exact interpolation space has `exactInterpolationDimensionCount` eligible
exponents. The hypothesis `d < D` makes the exponent set finite and is part of its definition.
The hypothesis `0 < d` is needed: for `d = 0` there is no `Y₁`, but the count still sums over
`M + 1` values of `b₁`. -/
theorem card_exactInterpolationExponents (hd : 0 < d) {D A m M W : ℕ} (hdD : d < D) :
    #(exactInterpolationExponents D A d m M W hdD) =
      exactInterpolationDimensionCount D A d m M W := by
  rw [← card_exactDimensionCoordinates]
  refine card_equiv ((jetExponentCoordinatesEquiv hd).trans coordinatesSigmaEquiv) fun u => ?_
  have hw : ∀ i : Fin (d - 1), i.val + 1 ≠ 0 := fun i => Nat.add_one_ne_zero _
  rw [mem_exactInterpolationExponents, exactInterpolationEligibleExponent_iff_coordinates hd,
    Equiv.trans_apply, exactDimensionCoordinates, mem_sigma, mem_product, mem_range,
    mem_natWeightedSimplex hw, mem_staircase_of_pos (by omega)]
  simp only [coordinatesSigmaEquiv, Equiv.coe_fn_mk]
  omega

/-- For `0 < d < D` the exact interpolation space has dimension
`exactInterpolationDimensionCount D A d m M W`. See `card_exactInterpolationExponents` for the
role of the hypotheses. -/
theorem finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount (R : Type*) [Field R]
    (hd : 0 < d) {D A m M W : ℕ} (hdD : d < D) :
    Module.finrank R (exactInterpolationSpace R D A d m M W hdD) =
      exactInterpolationDimensionCount D A d m M W := by
  rw [finrank_exactInterpolationSpace_eq_card, card_exactInterpolationExponents hd]

/-! ### The rectangular lower bound -/

/-- Global eligibility in coordinates: `b₁ ≤ m`, `b₀ + b₁ + ∑_i c_i ≤ B`,
`x + (K - 1)(b₀ + b₁ + ∑_i c_i) < m A`, `∑_i (i + 1) c_i ≤ W`, and `∑_i c_i ≤ C`. -/
theorem globalEligibleExponent_iff_coordinates (hd : 0 < d) {m A K B W C : ℕ}
    (u : JetVariable d →₀ ℕ) :
    GlobalEligibleExponent d m A K B W C u ↔
      (jetExponentCoordinatesEquiv hd u).2.2.1 ≤ m ∧
      (jetExponentCoordinatesEquiv hd u).2.1 + (jetExponentCoordinatesEquiv hd u).2.2.1 +
          ∑ i : Fin (d - 1), (jetExponentCoordinatesEquiv hd u).2.2.2 i ≤ B ∧
      (jetExponentCoordinatesEquiv hd u).1 + (K - 1) *
          ((jetExponentCoordinatesEquiv hd u).2.1 + (jetExponentCoordinatesEquiv hd u).2.2.1 +
            ∑ i : Fin (d - 1), (jetExponentCoordinatesEquiv hd u).2.2.2 i) < m * A ∧
      ∑ i : Fin (d - 1), (i.val + 1) * (jetExponentCoordinatesEquiv hd u).2.2.2 i ≤ W ∧
      ∑ i : Fin (d - 1), (jetExponentCoordinatesEquiv hd u).2.2.2 i ≤ C := by
  rw [GlobalEligibleExponent, firstJetExponent_eq_coordinates hd,
    totalJetDegree_eq_coordinates hd, fullHigherJetWeight_eq_coordinates hd,
    fullHigherJetDegree_eq_coordinates hd]
  simp only [jetExponentCoordinatesEquiv_apply]

/-- The rectangular lower bound on the number of globally eligible exponents. For every good
higher-jet exponent `c`, every `x < N`, `b₀ < H₀`, and `b₁ < H₁`, the exponent
`X^x Y₀^b₀ Y₁^b₁ Y^c` is globally eligible, and distinct choices give distinct exponents.

The hypotheses are the eligibility conditions at the largest coordinates, with some slack:
`H₁ ≤ m` bounds `b₁`; `C + H₀ + H₁ ≤ B` bounds the total jet degree `b₀ + b₁ + ∑_i c_i`, which
is below `C + H₀ + H₁`; and `N + (K - 1)(C + H₀ + H₁) ≤ m A` bounds
`x + (K - 1)(b₀ + b₁ + ∑_i c_i)`. The hypothesis `0 < d` provides the `Y₁` direction; without
it the bound fails, as the tests show at `d = 0`. -/
theorem card_mul_le_card_globalEligibleExponents (hd : 0 < d) {m A K B W C N H₀ H₁ : ℕ}
    (hH₁ : H₁ ≤ m) (hB : C + H₀ + H₁ ≤ B) (hA : N + (K - 1) * (C + H₀ + H₁) ≤ m * A) :
    #(goodHigherExponents d W C) * N * H₀ * H₁ ≤ #(globalEligibleExponents d m A K B W C) := by
  classical
  have hcard : #(goodHigherExponents d W C ×ˢ range N ×ˢ range H₀ ×ˢ range H₁) =
      #(goodHigherExponents d W C) * N * H₀ * H₁ := by
    simp [card_product, mul_assoc]
  rw [← hcard]
  refine card_le_card_of_injOn
    (fun q => (jetExponentCoordinatesEquiv hd).symm (q.2.1, q.2.2.1, q.2.2.2, ⇑q.1)) ?_ ?_
  · rintro ⟨c, x, b₀, b₁⟩ hq
    simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hq
    obtain ⟨hc, hx, hb₀, hb₁⟩ := hq
    obtain ⟨hcW, hcC⟩ := mem_goodHigherExponents.mp hc
    have hweight : ∑ i : Fin (d - 1), (i.val + 1) * c i = higherJetWeight c := by
      rw [higherJetWeight, ← weightedSum_equivFunOnFinite]
      rfl
    have hdegree : ∑ i : Fin (d - 1), c i = higherJetDegree c := by
      rw [higherJetDegree, Finsupp.degree_eq_sum]
    rw [mem_coe, mem_globalEligibleExponents, globalEligibleExponent_iff_coordinates hd,
      Equiv.apply_symm_apply]
    simp only [hweight, hdegree]
    have hmul : (K - 1) * (b₀ + b₁ + higherJetDegree c) ≤ (K - 1) * (C + H₀ + H₁) :=
      Nat.mul_le_mul_left _ (by omega)
    refine ⟨by omega, by omega, by omega, hcW, hcC⟩
  · rintro ⟨c, x, b₀, b₁⟩ _ ⟨c', x', b₀', b₁'⟩ _ h
    have h := (jetExponentCoordinatesEquiv hd).symm.injective h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, hc⟩ := h
    rw [DFunLike.coe_injective hc]

/-- The rectangular lower bound on the dimension of the rectangular interpolation space, with
independent side lengths `N` for `X`, `H₀` for `Y₀`, and `H₁` for `Y₁`. See
`card_mul_le_card_globalEligibleExponents` for the hypotheses. -/
theorem le_finrank_interpolationSpace (R : Type*) [Field R] (hd : 0 < d)
    {m A K B W C N H₀ H₁ : ℕ} (hH₁ : H₁ ≤ m) (hB : C + H₀ + H₁ ≤ B)
    (hA : N + (K - 1) * (C + H₀ + H₁) ≤ m * A) :
    #(goodHigherExponents d W C) * N * H₀ * H₁ ≤
      Module.finrank R (interpolationSpace R d m A K B W C) := by
  rw [finrank_interpolationSpace_eq_card]
  exact card_mul_le_card_globalEligibleExponents hd hH₁ hB hA

/-- The rectangular lower bound with one side length `H`:
`#(goodHigherExponents d W C) (K - 1) H³` is at most the dimension of the rectangular space when
`H ≤ m`, `C + 2H ≤ B`, and `(K - 1)(C + 3H) ≤ m A`. This is `le_finrank_interpolationSpace` with
`N = (K - 1) H` and `H₀ = H₁ = H`; the three hypotheses expose all rounding loss. -/
theorem finrank_interpolationSpace_lowerBound (R : Type*) [Field R] (hd : 0 < d)
    {m A K B W C H : ℕ} (hH : H ≤ m) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ m * A) :
    #(goodHigherExponents d W C) * (K - 1) * H ^ 3 ≤
      Module.finrank R (interpolationSpace R d m A K B W C) := by
  have hA : (K - 1) * H + (K - 1) * (C + H + H) ≤ m * A :=
    calc (K - 1) * H + (K - 1) * (C + H + H) = (K - 1) * (C + 3 * H) := by ring
      _ ≤ m * A := hweighted
  calc #(goodHigherExponents d W C) * (K - 1) * H ^ 3 =
        #(goodHigherExponents d W C) * ((K - 1) * H) * H * H := by ring
    _ ≤ _ := le_finrank_interpolationSpace R hd (B := B) hH (by omega) hA

/-- The rectangular lower bound transferred to the exact interpolation space with `M = m`: for
`0 < d < D < K`, `H ≤ m`, and `(K - 1)(C + 3H) ≤ m A`,
`#(goodHigherExponents d W C) (K - 1) H³` is at most the dimension of the exact space. This is
`finrank_interpolationSpace_lowerBound` at the jet-degree budget `B = C + 2H`, followed by
`finrank_interpolationSpace_le_exactInterpolationSpace`; the exact space has no jet-degree budget,
so `B` does not appear. -/
theorem card_goodHigherExponents_mul_le_finrank_exactInterpolationSpace (R : Type*) [Field R]
    (hd : 0 < d) {D m A K W C H : ℕ} (hdD : d < D) (hDK : D < K) (hH : H ≤ m)
    (hweighted : (K - 1) * (C + 3 * H) ≤ m * A) :
    #(goodHigherExponents d W C) * (K - 1) * H ^ 3 ≤
      Module.finrank R (exactInterpolationSpace R D A d m m W hdD) :=
  (finrank_interpolationSpace_lowerBound R hd (B := C + 2 * H) (W := W) hH le_rfl hweighted).trans
    (finrank_interpolationSpace_le_exactInterpolationSpace R hdD hDK)

end

end ReedSolomon.HiddenDerivative
