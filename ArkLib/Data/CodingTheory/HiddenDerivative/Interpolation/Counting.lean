/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.Finset.Staircase
public import ArkLib.Data.Finset.WeightedSimplex
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.Floor.Div

/-!
# Counts for the certified local rank bound

This file contains the arithmetic behind the certified bound on the rank of the local
constraint map. The local intermediate space has, at each `T`-degree `r < m`, one block of
`(r + 1) (M + 1)` exponents of `U` and `Y₁` for every higher-jet exponent of weight at most
`W + r`. The exhibited kernel removes a rectangle of `(r + 1 - h) (M + 1 - h)` of these, where
`h = ⌈(m - r) / d⌉` is the least power of the hidden error that reaches contact order `m`.

* `weightedHigherJetCount d W` is the number of exponent vectors `(c₂, ..., c_d)` of `Y₂, ..., Y_d`
  with `∑ (j - 1) c_j ≤ W`, counted as a weighted simplex.
* `contactThreshold d m r = ⌈(m - r) / d⌉`.
* `certifiedEnlargedRankBound d m M W` is the sum over `r < m` of the higher-jet count times the
  residual `(r + 1)(M + 1) - (r + 1 - h)(M + 1 - h)`.
* `localResidualCoordinateBudget d m W B` and `localCoordinateBudget d m W B` count the local
  coordinates of `Interpolation/Local/Coordinates.lean`, with a jet-degree cutoff `B`;
  `localDerivativeCoordinateBudget d m W` counts them under a derivative-order weight bound, with
  no cutoff.
* `exactInterpolationDimensionCount D A d m M W` is the dimension of the exact interpolation space
  of `Interpolation/Index.lean`: a sum over the higher-jet exponents `c` of weight at most `W` and
  the `Y₁` exponents `b₁ ≤ M` of the staircase count `Nat.staircaseCount D` at the residual budget
  `m A - ((D - 1) b₁ + ∑_i (D - (i + 2)) c_i)` left for the `X` and `Y₀` exponents.

## Main statements

* `multiplicity_le_add_mul_contactThreshold`: `m ≤ r + d h` when `d > 0`.
* `add_mul_lt_multiplicity_of_lt_contactThreshold`: every `b < h` has `r + d b < m`.
* `ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound`: the ambient count minus the
  exhibited-kernel count is the certified bound.
* `certifiedEnlargedRankBound_le_of_le_mul`: if `m ≤ d k`, the certified bound is at most
  `m k (m + M + 1) Λ_d(W + m)`, from `contactThreshold_le_of_le_mul`,
  `exhibitedKernelResidualCount_le`, and `weightedHigherJetCount_mono`.
* `localResidualCoordinateBudget_le_localCoordinateBudget`.
* `card_exactDimensionCoordinates`: `exactInterpolationDimensionCount` is the number of
  coordinate tuples `(c, b₁, x, b₀)` it counts, for every `D`.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], Section 3
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open Finset

/-- The number of exponent vectors of the higher jets `Y₂, ..., Y_d` of anisotropic weight
`∑_{j ≥ 2} (j - 1) c_j` at most `W`, as a weighted simplex over `Fin (d - 1)` with weights
`1, 2, ..., d - 1`. For `d ≤ 1` there are no higher jets and the count is `1`. -/
def weightedHigherJetCount (d W : ℕ) : ℕ :=
  (natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W).card

/-- For `d = n + 1` the higher jets are indexed by `Fin n`. -/
theorem weightedHigherJetCount_succ (n W : ℕ) :
    weightedHigherJetCount (n + 1) W =
      (natWeightedSimplex (fun i : Fin n => i.val + 1) W).card :=
  rfl

/-- The least power of the hidden error that reaches contact order `m` from `T`-degree `r`:
`⌈(m - r) / d⌉`. It is zero when `r ≥ m`, and also when `d = 0`. -/
def contactThreshold (d m r : ℕ) : ℕ :=
  (m - r) ⌈/⌉ d

/-- At the threshold the contact order `r + d h` reaches `m`. The hypothesis `0 < d` is needed:
for `d = 0` the threshold is `0`, and `m ≤ r` fails whenever `r < m`. -/
theorem multiplicity_le_add_mul_contactThreshold {d : ℕ} (hd : 0 < d) (m r : ℕ) :
    m ≤ r + d * contactThreshold d m r := by
  have hcover : m - r ≤ d * contactThreshold d m r := le_smul_ceilDiv hd
  omega

/-- Below the threshold the contact order stays below `m`. No hypothesis is needed: if
`d = 0` or `r ≥ m`, the threshold is `0` and there is no `b` below it. -/
theorem add_mul_lt_multiplicity_of_lt_contactThreshold {d m r b : ℕ}
    (hb : b < contactThreshold d m r) : r + d * b < m := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [contactThreshold] at hb
  have hnot : ¬m - r ≤ d * b := fun h =>
    absurd ((ceilDiv_le_iff_le_mul hd).mpr h) (Nat.not_le.mpr hb)
  omega

/-- The number of `(U, Y₁)` exponents `(a, b)` with `a ≤ r` and `b ≤ M`. -/
def ambientContactCount (r M : ℕ) : ℕ :=
  (r + 1) * (M + 1)

/-- The number of `(U, Y₁)` exponents `(a, b)` with `a + h ≤ r` and `b + h ≤ M`. Each factor is
written `r + 1 - h` rather than `r - h + 1`, which would be wrong in `ℕ` when `h > r`. -/
def exhibitedKernelContactCount (r M h : ℕ) : ℕ :=
  (r + 1 - h) * (M + 1 - h)

/-- The ambient count minus the exhibited-kernel count. -/
def exhibitedKernelResidualCount (r M h : ℕ) : ℕ :=
  ambientContactCount r M - exhibitedKernelContactCount r M h

/-- The exhibited rectangle is never larger than the ambient one. -/
theorem exhibitedKernelContactCount_le_ambientContactCount (r M h : ℕ) :
    exhibitedKernelContactCount r M h ≤ ambientContactCount r M :=
  Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)

/-- The residual count at `T`-degree `r` with the threshold `contactThreshold d m r`. -/
def certifiedContactRankBudget (d m M r : ℕ) : ℕ :=
  exhibitedKernelResidualCount r M (contactThreshold d m r)

/-- The certified bound on the rank of the enlarged local constraint map:
`∑_{r < m} Λ_d(W + r) ((r + 1)(M + 1) - (r + 1 - h_r)(M + 1 - h_r))`, where `Λ_d` is
`weightedHigherJetCount d` and `h_r = contactThreshold d m r`. It is an upper bound obtained from
an exhibited part of the kernel, not the exact rank. -/
def certifiedEnlargedRankBound (d m M W : ℕ) : ℕ :=
  ∑ r ∈ range m, weightedHigherJetCount d (W + r) * certifiedContactRankBudget d m M r

/-- The ambient count minus the exhibited-kernel count is the certified bound. Truncated
subtraction commutes with the sum because the exhibited count is termwise at most the ambient
count. -/
theorem ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound (d m M W : ℕ) :
    (∑ r ∈ range m, weightedHigherJetCount d (W + r) * ambientContactCount r M) -
        ∑ r ∈ range m,
          weightedHigherJetCount d (W + r) *
            exhibitedKernelContactCount r M (contactThreshold d m r) =
      certifiedEnlargedRankBound d m M W := by
  rw [← sum_tsub_distrib]
  · simp only [certifiedEnlargedRankBound, certifiedContactRankBudget,
      exhibitedKernelResidualCount, Nat.mul_sub]
  · exact fun r _ => Nat.mul_le_mul_left _
      (exhibitedKernelContactCount_le_ambientContactCount r M (contactThreshold d m r))

/-- The higher-jet count is monotone in the weight budget, since the weighted simplex is. -/
theorem weightedHigherJetCount_mono (d : ℕ) {W W' : ℕ} (hWW' : W ≤ W') :
    weightedHigherJetCount d W ≤ weightedHigherJetCount d W' :=
  card_le_card (natWeightedSimplex_mono _ hWW')

/-- If `m ≤ d k`, the contact threshold is at most `k` at every `T`-degree `r`, because `k`
powers of the hidden error already reach contact order `m` from `r = 0`. No hypothesis on `d` is
needed: for `d = 0` the threshold is `0`. -/
theorem contactThreshold_le_of_le_mul {d m k : ℕ} (h : m ≤ d * k) (r : ℕ) :
    contactThreshold d m r ≤ k := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [contactThreshold]
  · rw [contactThreshold, ceilDiv_le_iff_le_mul hd]
    omega

/-- Removing the exhibited `(r + 1 - h) × (M + 1 - h)` rectangle from the ambient
`(r + 1) × (M + 1)` rectangle leaves at most the two boundary strips of width `h`, of total size
`h ((r + 1) + (M + 1))`. This holds for every `h`, including `h > r + 1` or `h > M + 1`, where a
side of the exhibited rectangle is empty. -/
theorem exhibitedKernelResidualCount_le (r M h : ℕ) :
    exhibitedKernelResidualCount r M h ≤ h * (r + 1 + (M + 1)) := by
  rw [exhibitedKernelResidualCount, ambientContactCount, exhibitedKernelContactCount,
    Nat.sub_le_iff_le_add]
  generalize r + 1 = a
  generalize M + 1 = b
  rcases le_or_gt h a with ha | ha
  · rcases le_or_gt h b with hb | hb
    · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ha
      obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
      simp only [Nat.add_sub_cancel_left]
      have e : h * (h + a + (h + b)) + a * b = (h + a) * (h + b) + h * h := by ring
      omega
    · calc a * b ≤ a * h := Nat.mul_le_mul_left a hb.le
        _ = h * a := Nat.mul_comm a h
        _ ≤ h * (a + b) := Nat.mul_le_mul_left h (Nat.le_add_right a b)
        _ ≤ h * (a + b) + (a - h) * (b - h) := Nat.le_add_right _ _
  · calc a * b ≤ h * b := Nat.mul_le_mul_right b ha.le
      _ ≤ h * (a + b) := Nat.mul_le_mul_left h (Nat.le_add_left b a)
      _ ≤ h * (a + b) + (a - h) * (b - h) := Nat.le_add_right _ _

/-- A closed-form upper bound on the certified bound. If `m ≤ d k`, every contact threshold is
at most `k` (`contactThreshold_le_of_le_mul`), every residual at `T`-degree `r < m` is at most
`k (m + M + 1)` (`exhibitedKernelResidualCount_le`), and every higher-jet count is at most
`Λ_d(W + m)` (`weightedHigherJetCount_mono`), so
`certifiedEnlargedRankBound d m M W ≤ m k (m + M + 1) Λ_d(W + m)`. -/
theorem certifiedEnlargedRankBound_le_of_le_mul {d m M W k : ℕ} (h : m ≤ d * k) :
    certifiedEnlargedRankBound d m M W ≤
      m * (k * (m + M + 1)) * weightedHigherJetCount d (W + m) := by
  rw [certifiedEnlargedRankBound]
  calc ∑ r ∈ range m, weightedHigherJetCount d (W + r) * certifiedContactRankBudget d m M r
      ≤ ∑ _r ∈ range m, weightedHigherJetCount d (W + m) * (k * (m + M + 1)) := by
        refine sum_le_sum fun r hr => ?_
        have hr := mem_range.mp hr
        refine Nat.mul_le_mul (weightedHigherJetCount_mono d (by omega)) ?_
        calc certifiedContactRankBudget d m M r ≤
              contactThreshold d m r * (r + 1 + (M + 1)) :=
            exhibitedKernelResidualCount_le _ _ _
          _ ≤ k * (m + M + 1) := Nat.mul_le_mul (contactThreshold_le_of_le_mul h r) (by omega)
    _ = m * (k * (m + M + 1)) * weightedHigherJetCount d (W + m) := by
        rw [sum_const, card_range, smul_eq_mul]
        ring

/-- The count of local residual coordinates of `Interpolation/Local/Coordinates.lean`. For each
residual `r = t - h < m` of the `T`-degree `t` by the `E`-degree `h`, there are
`contactThreshold (d + 1) m r` values of `h`, and for each higher-jet exponent `z` of weight at most
`W + r` there are `B - ∑ z` values of the `Y₁`-degree, which keep the jet degree below `B`. -/
def localResidualCoordinateBudget (d m W B : ℕ) : ℕ :=
  ∑ r ∈ range m, contactThreshold (d + 1) m r *
    ∑ z ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) (W + r), (B - ∑ i, z i)

/-- The coarser local coordinate budget, which allows `B` values of the `Y₁`-degree for every
higher-jet exponent. -/
def localCoordinateBudget (d m W B : ℕ) : ℕ :=
  B * ∑ r ∈ range m, contactThreshold (d + 1) m r * weightedHigherJetCount d (W + r)

/-- The derivative-order coordinate budget
`∑_{r < m} ⌈(m - r)/(d + 1)⌉ · #{c : Fin d → ℕ | ∑_j (j + 1) c_j ≤ W + r}`. The factor
`⌈(m - r)/(d + 1)⌉` counts the error exponents `h` of contact order `r + (d + 1) h < m`, and the
second factor counts the exponents of `Y₁, ..., Y_d` of derivative-order weight at most `W + r`.
It counts the local coordinates of `localDerivativeExponents` in
`Interpolation/Local/Coordinates.lean`. Unlike `localResidualCoordinateBudget`, it needs no
jet-degree cutoff, because the derivative-order weight charges `Y₁`. -/
def localDerivativeCoordinateBudget (d m W : ℕ) : ℕ :=
  ∑ r ∈ range m, contactThreshold (d + 1) m r * weightedHigherJetCount (d + 1) (W + r)

/-- The residual budget is at most the coarse budget, for any cutoffs `B ≤ B'`. -/
theorem localResidualCoordinateBudget_le_localCoordinateBudget {d m W B B' : ℕ} (hB : B ≤ B') :
    localResidualCoordinateBudget d m W B ≤ localCoordinateBudget d m W B' := by
  rw [localCoordinateBudget, mul_sum]
  refine sum_le_sum fun r _ => ?_
  rw [mul_left_comm, weightedHigherJetCount, mul_comm B', ← smul_eq_mul (#_) B', ← sum_const]
  exact Nat.mul_le_mul_left _ (sum_le_sum fun z _ => (Nat.sub_le _ _).trans hB)

/-! ### The exact interpolation dimension -/

/-- The part `∑_i (D - (i + 2)) c_i` of the specialization weight carried by the higher jets
`Y₂, ..., Y_d`, whose exponents are `c`: coordinate `i` is the exponent of `Y_(i+2)`, which has
specialization weight `D - (i + 2)`. -/
def higherJetTupleSpecializationCost {d : ℕ} (D : ℕ) (c : Fin (d - 1) → ℕ) : ℕ :=
  ∑ i, (D - (i.val + 2)) * c i

/-- The budget `m A - ((D - 1) b₁ + ∑_i (D - (i + 2)) c_i)` left for `x + D b₀` once the `Y₁`
exponent `b₁` and the higher-jet exponents `c` are fixed. It is `0` when those exponents already
use up `m A`. -/
def exactDimensionResidual {d : ℕ} (D m A b₁ : ℕ) (c : Fin (d - 1) → ℕ) : ℕ :=
  m * A - ((D - 1) * b₁ + higherJetTupleSpecializationCost D c)

/-- The number of exponents `X^x Y₀^b₀ Y₁^b₁ Y₂^c₀ ⋯ Y_d^c_(d-2)` with `b₁ ≤ M`,
`∑_i (i + 1) c_i ≤ W`, and specialization weight
`x + D b₀ + (D - 1) b₁ + ∑_i (D - (i + 2)) c_i < m A`. For each `c` and `b₁` the pairs
`(x, b₀)` form a staircase of slope `D` and length `exactDimensionResidual D m A b₁ c`.

This counts the exponents of the exact interpolation space when `0 < d < D`; see
`finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount`. The expression is defined
for all parameters. -/
def exactInterpolationDimensionCount (D A d m M W : ℕ) : ℕ :=
  ∑ c ∈ natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W,
    ∑ b₁ ∈ range (M + 1), Nat.staircaseCount D (exactDimensionResidual D m A b₁ c)

/-- The coordinate tuples `⟨(c, b₁), (x, b₀)⟩` counted by `exactInterpolationDimensionCount`:
`c` in the higher-jet weighted simplex of weight `W`, `b₁ ≤ M`, and `(x, b₀)` in the staircase
of slope `D` and length `exactDimensionResidual D m A b₁ c`. -/
def exactDimensionCoordinates (D A d m M W : ℕ) :
    Finset (Σ _ : (Fin (d - 1) → ℕ) × ℕ, ℕ × ℕ) :=
  (natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W ×ˢ range (M + 1)).sigma
    fun p => staircase D (exactDimensionResidual D m A p.2 p.1)

/-- `exactInterpolationDimensionCount` is the number of coordinate tuples it describes. No
hypothesis on the parameters is needed. -/
theorem card_exactDimensionCoordinates (D A d m M W : ℕ) :
    #(exactDimensionCoordinates D A d m M W) = exactInterpolationDimensionCount D A d m M W := by
  rw [exactDimensionCoordinates, card_sigma, sum_product, exactInterpolationDimensionCount]
  simp only [card_staircase]

end ReedSolomon.HiddenDerivative
