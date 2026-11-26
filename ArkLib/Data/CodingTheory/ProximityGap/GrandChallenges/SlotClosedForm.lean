/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges.SlotArithmetic

/-!
# Closed forms for the slot counts

`SlotArithmetic` restates the two sides of the first-order slot inequality
`firstOrderCurveShiftedRowSlotBound … < firstOrderCurveShiftedHeightSlotCount …` as nested
`sumRange` sums. Their inner sums have closed forms, so both counts can be evaluated with one term
per outer index `t`. This file defines the closed forms and proves that they agree with the library
definitions for all parameters. After rewriting with these equalities, the kernel work for a
concrete slot inequality grows with `μ` rather than with the number of inner terms. Whether a single
`decide +kernel` call suffices for a given instance still depends on the kernel's time and memory
for its `μ + 1` terms.

* Height: for fixed `t`, the inner sum `∑_{b ≤ min t M} (m * A + b - D * t)` is a difference of
  two triangular numbers (`sumRange_add_sub_eq`), including the cases where the truncated
  subtraction is zero.
* Row: for fixed `t`, the summand `min (m - s) (gradedSourceCount D A m M s t)` of
  `gradedRankBound` is zero, increasing, constant or decreasing on six intervals of `s` whose ends
  are explicit (`gradedRankBound_eq_pieces`).

## Main results

* `heightSlotCountClosed_eq`, `rowSlotBoundClosed_eq`: the closed forms equal the
  `SlotArithmetic` restatements.
* `firstOrderCurveShiftedHeightSlotCount_eq_closed`, `firstOrderCurveShiftedRowSlotBound_eq_closed`:
  the library counts equal the closed forms.
-/

@[expose] public section

open ReedSolomon.HiddenDerivative

namespace ProximityGap.GrandChallenges.SlotArithmetic

/-! ### Triangular numbers and range sums -/

/-- The triangular number `triangle x = 0 + 1 + ⋯ + (x - 1)`. It equals `Nat.choose x 2`; this form
evaluates with one multiplication and one division, while `Nat.choose` unfolds its recursion. -/
def triangle (x : Nat) : Nat := x * (x - 1) / 2

/-- `triangle x` is the range sum `∑_{i < x} i`. -/
private theorem triangle_eq_sum (x : Nat) : triangle x = ∑ i ∈ Finset.range x, i :=
  (Finset.sum_range_id x).symm

/-- `triangle (y + 1) = triangle y + y`. -/
private theorem triangle_succ (y : Nat) : triangle (y + 1) = triangle y + y := by
  exact Nat.triangle_succ y

/-- `triangle` is monotone. -/
theorem triangle_mono : Monotone triangle := by
  intro x y hxy
  rw [triangle_eq_sum, triangle_eq_sum]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hxy)

/-- A range sum of truncated differences in closed form:
`∑_{b < n} (c + b - d) = triangle (n + c - d) - triangle (c - d)`, for all `c`, `d`, `n`. -/
theorem sumRange_add_sub_eq (c d : Nat) :
    ∀ n, sumRange n (fun b ↦ c + b - d) = triangle (n + c - d) - triangle (c - d)
  | 0 => by simp [sumRange]
  | n + 1 => by
    rw [show sumRange (n + 1) (fun b ↦ c + b - d) =
        sumRange n (fun b ↦ c + b - d) + (c + n - d) from rfl, sumRange_add_sub_eq c d n]
    by_cases hd : d ≤ n + c
    · rw [show n + 1 + c - d = (n + c - d) + 1 by omega, triangle_succ]
      have := triangle_mono (show c - d ≤ n + c - d by omega)
      omega
    · rw [show n + 1 + c - d = 0 by omega, show n + c - d = 0 by omega,
        show c - d = 0 by omega, show c + n - d = 0 by omega]
      omega

/-- A constant factor comes out of `sumRange`. -/
private theorem sumRange_mul_const (k : Nat) (f : Nat → Nat) (n : Nat) :
    sumRange n (fun b ↦ f b * k) = sumRange n f * k := by
  simp only [sumRange_eq, Finset.sum_mul]

/-- `sumRange n f` depends only on the values of `f` below `n`. -/
private theorem sumRange_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i = g i) :
    sumRange n f = sumRange n g := by
  simp only [sumRange_eq]
  apply Finset.sum_congr rfl
  intro i hi
  exact h i (Finset.mem_range.mp hi)

/-- `∑_{i < n} (a - i) = triangle (a + 1) - triangle (a + 1 - n)`. -/
theorem sumRange_sub_eq (a : Nat) :
    ∀ n, sumRange n (fun i ↦ a - i) = triangle (a + 1) - triangle (a + 1 - n)
  | 0 => by simp [sumRange]
  | n + 1 => by
    change sumRange n (fun i ↦ a - i) + (a - n) = triangle (a + 1) - triangle (a + 1 - (n + 1))
    rw [sumRange_sub_eq a n]
    by_cases hn : n ≤ a
    · rw [show a + 1 - n = (a - n) + 1 by omega,
        triangle_succ (a - n), show a + 1 - (n + 1) = a - n by omega]
      have hm := triangle_mono (show a - n + 1 ≤ a + 1 by omega)
      rw [triangle_succ (a - n)] at hm
      omega
    · have h₁ : a - n = 0 := by omega
      have h₂ : a + 1 - n = 0 := by omega
      have h₃ : a + 1 - (n + 1) = 0 := by omega
      rw [h₁, h₂, h₃]
      simp

/-! ### Height count -/

/-- `heightSlotCount` with the inner sum in closed form: one term per `t ≤ μ`. -/
def heightSlotCountClosed (D A m M μ ℓ h : Nat) : Nat :=
  sumRange (μ + 1) fun t ↦
    (triangle (min t M + 1 + m * A - D * t) - triangle (m * A - D * t)) * (h + 1 - ℓ * t)

/-- The closed height count equals `heightSlotCount`, for all parameters. -/
theorem heightSlotCountClosed_eq (D A m M μ ℓ h : Nat) :
    heightSlotCountClosed D A m M μ ℓ h = heightSlotCount D A m M μ ℓ h := by
  unfold heightSlotCountClosed heightSlotCount
  congr 1
  funext t
  rw [sumRange_mul_const, sumRange_add_sub_eq]

/-- The library height count equals its closed form, for all parameters. -/
theorem firstOrderCurveShiftedHeightSlotCount_eq_closed (D A m M μ ℓ h : Nat) :
    firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h = heightSlotCountClosed D A m M μ ℓ h := by
  rw [firstOrderCurveShiftedHeightSlotCount_eq, heightSlotCountClosed_eq]

/-! ### Sums over intervals -/

/-- The sum of `f` over the interval `[lo, hi)`. -/
private def sumIco (lo hi : Nat) (f : Nat → Nat) : Nat := sumRange (hi - lo) fun i ↦ f (lo + i)

/-- The kernel-reducible interval sum agrees with the finite-set sum. -/
private theorem sumIco_eq_sum (lo hi : Nat) (f : Nat → Nat) :
    sumIco lo hi f = ∑ i ∈ Finset.Ico lo hi, f i := by
  rw [sumIco, sumRange_eq, Finset.sum_Ico_eq_sum_range]

/-- `sumIco lo hi f` depends only on the values of `f` on `[lo, hi)`. -/
private theorem sumIco_congr {lo hi : Nat} {f g : Nat → Nat}
    (h : ∀ s, lo ≤ s → s < hi → f s = g s) :
    sumIco lo hi f = sumIco lo hi g := by
  rw [sumIco_eq_sum, sumIco_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact h i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2

/-- Splitting `[lo, hi)` at `mid`. -/
private theorem sumIco_split (f : Nat → Nat) {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    sumIco lo hi f = sumIco lo mid f + sumIco mid hi f := by
  rw [sumIco_eq_sum, sumIco_eq_sum, sumIco_eq_sum]
  exact (Finset.sum_Ico_consecutive f h1 h2).symm

/-- The sum of a constant over `[lo, hi)`. -/
private theorem sumIco_const (lo hi c : Nat) : sumIco lo hi (fun _ ↦ c) = (hi - lo) * c := by
  rw [sumIco_eq_sum]
  simp [Nat.card_Ico]

/-- `∑_{s ∈ [lo, hi)} (s + 1 - q)` in closed form. -/
private theorem sumIco_add_one_sub (lo hi q : Nat) :
    sumIco lo hi (fun s ↦ s + 1 - q) = triangle (hi + 1 - q) - triangle (lo + 1 - q) := by
  by_cases h : lo ≤ hi
  · unfold sumIco
    dsimp only
    have key := sumRange_add_sub_eq (lo + 1) q (hi - lo)
    rw [show hi - lo + (lo + 1) - q = hi + 1 - q by omega] at key
    rw [← key]
    apply sumRange_congr
    intro i _
    omega
  · have hs : hi - lo = 0 := by omega
    have ht : triangle (hi + 1 - q) ≤ triangle (lo + 1 - q) := triangle_mono (by omega)
    simp [sumIco, hs, sumRange, Nat.sub_eq_zero_of_le ht]

/-- `∑_{s ∈ [lo, hi)} (m - s)` in closed form. -/
private theorem sumIco_sub (lo hi m : Nat) :
    sumIco lo hi (fun s ↦ m - s) = triangle (m - lo + 1) - triangle (m - hi + 1) := by
  by_cases h1 : lo ≤ hi
  · unfold sumIco
    dsimp only
    rw [show (fun i ↦ m - (lo + i)) = (fun i ↦ (m - lo) - i) from funext fun i ↦ by omega,
      sumRange_sub_eq (m - lo) (hi - lo)]
    by_cases h2 : hi ≤ m
    · rw [show m - lo + 1 - (hi - lo) = m - hi + 1 by omega]
    · have hu : m - lo + 1 - (hi - lo) ≤ 1 := by omega
      have hv : m - hi + 1 ≤ 1 := by omega
      have hu0 : triangle (m - lo + 1 - (hi - lo)) = 0 := by
        generalize m - lo + 1 - (hi - lo) = x at hu ⊢
        interval_cases x <;> norm_num [triangle]
      have hv0 : triangle (m - hi + 1) = 0 := by
        generalize m - hi + 1 = x at hv ⊢
        interval_cases x <;> norm_num [triangle]
      rw [hu0, hv0]
  · have hs : hi - lo = 0 := by omega
    have ht : triangle (m - lo + 1) ≤ triangle (m - hi + 1) := triangle_mono (by omega)
    simp [sumIco, hs, sumRange, Nat.sub_eq_zero_of_le ht]

/-! ### Row count -/

/-- The summand of `gradedRankBound D A m M t` at `s`. -/
private def gradedRankTerm (D A m M t s : Nat) : Nat := min (m - s) (gradedSourceCount D A m M s t)

/-- `gradedRankBound` as a sum of `gradedRankTerm` over `[0, m)`. -/
private theorem gradedRankBound_eq_sumIco (D A m M t : Nat) :
    gradedRankBound D A m M t = sumIco 0 m (gradedRankTerm D A m M t) := by
  unfold gradedRankBound sumIco gradedRankTerm
  simp only [Nat.sub_zero, Nat.zero_add]

/-- `gradedRankBound` as a sum over six intervals of `s`, each in closed form:
`[0, lo)` and `[N, m)` contribute `0`, `[lo, b1)` the increasing side `s + 1 - q`, `[n1, b2)` the
constant side `c2`, and `[b1, n1)`, `[b2, N)` the decreasing side `m - s`. The interval ends are
named by hypotheses; their `min`/`max` definitions are first turned into linear facts, and each
`omega` call sees only the facts it needs. -/
private theorem gradedRankBound_eq_pieces (D A m M t N q c2 n1 lo b1 b2 : Nat)
    (hN : N = min m (m * A - (D - 1) * t)) (hq : q = t - M) (hc2 : c2 = t + 1 - q)
    (hn1 : n1 = min N t) (hlo : lo = min q n1) (hb1 : b1 = min n1 (max lo ((m + q + 1) / 2)))
    (hb2 : b2 = min N (max n1 (m + 1 - c2))) :
    gradedRankBound D A m M t =
      (triangle (b1 + 1 - q) - triangle (lo + 1 - q)) +
        (triangle (m - b1 + 1) - triangle (m - n1 + 1)) +
        ((b2 - n1) * c2 + (triangle (m - b2 + 1) - triangle (m - N + 1))) := by
  have hNm : N ≤ m := by clear * - hN; omega
  have hNLK : N ≤ m * A - (D - 1) * t := by clear * - hN; omega
  have hNc : N = m ∨ N = m * A - (D - 1) * t := by clear * - hN; omega
  have hn1N : n1 ≤ N := by clear * - hn1; omega
  have hn1t : n1 ≤ t := by clear * - hn1; omega
  have hn1c : n1 = N ∨ n1 = t := by clear * - hn1; omega
  have hlon1 : lo ≤ n1 := by clear * - hlo; omega
  have hloq : lo ≤ q := by clear * - hlo; omega
  have hloc : lo = q ∨ lo = n1 := by clear * - hlo; omega
  have hb1n : b1 ≤ n1 := by clear * - hb1; omega
  have hlob1 : lo ≤ b1 := by clear * - hb1 hlon1; omega
  have hb1X : b1 ≤ lo ∨ b1 ≤ (m + q + 1) / 2 := by clear * - hb1; omega
  have hb1lt : b1 < n1 → (m + q + 1) / 2 ≤ b1 := by clear * - hb1; omega
  have hb2N : b2 ≤ N := by clear * - hb2; omega
  have hn1b2 : n1 ≤ b2 := by clear * - hb2 hn1N; omega
  have hb2Y : b2 ≤ n1 ∨ b2 ≤ m + 1 - c2 := by clear * - hb2; omega
  have hb2lt : b2 < N → m + 1 - c2 ≤ b2 := by clear * - hb2; omega
  clear hN hn1 hlo hb1 hb2
  rw [gradedRankBound_eq_sumIco, sumIco_split _ (Nat.zero_le N) hNm,
    sumIco_split _ (Nat.zero_le n1) hn1N, sumIco_split _ (Nat.zero_le lo) hlon1,
    sumIco_split _ hlob1 hb1n, sumIco_split _ hn1b2 hb2N]
  -- `N ≤ s < m`: the branch condition of `gradedSourceCount` fails.
  have e0 : ∀ s, N ≤ s → s < m → gradedRankTerm D A m M t s = (fun _ ↦ 0) s := by
    intro s h1 h2
    clear * - h1 h2 hNc
    unfold gradedRankTerm gradedSourceCount
    beta_reduce
    split <;> omega
  -- `s < lo`: `s < q`, so `min t s + 1 - (t - M) = 0`.
  have e1 : ∀ s, 0 ≤ s → s < lo → gradedRankTerm D A m M t s = (fun _ ↦ 0) s := by
    intro s _ h2
    clear * - h2 hNLK hlon1 hn1N hn1t hloq hq
    unfold gradedRankTerm gradedSourceCount
    beta_reduce
    split <;> omega
  -- `lo ≤ s < b1`: the increasing side `s + 1 - q`.
  have e2 : ∀ s, lo ≤ s → s < b1 → gradedRankTerm D A m M t s = (fun s ↦ s + 1 - q) s := by
    intro s h1 h2
    clear * - h1 h2 hb1n hn1N hNLK hn1t hloc hb1X hq
    unfold gradedRankTerm gradedSourceCount
    beta_reduce
    split <;> omega
  -- `b1 ≤ s < n1`: the decreasing side `m - s`.
  have e3 : ∀ s, b1 ≤ s → s < n1 → gradedRankTerm D A m M t s = (fun s ↦ m - s) s := by
    intro s h1 h2
    clear * - h1 h2 hn1N hNLK hn1t hloc hlob1 hb1lt hNm hq
    unfold gradedRankTerm gradedSourceCount
    beta_reduce
    split <;> omega
  -- `n1 ≤ s < b2`: the constant side `c2 = min t M + 1`.
  have e4 : ∀ s, n1 ≤ s → s < b2 → gradedRankTerm D A m M t s = (fun _ ↦ c2) s := by
    intro s h1 h2
    clear * - h1 h2 hb2N hNLK hn1c hb2Y hc2 hq
    unfold gradedRankTerm gradedSourceCount
    beta_reduce
    split <;> omega
  -- `b2 ≤ s < N`: the decreasing side `m - s`.
  have e5 : ∀ s, b2 ≤ s → s < N → gradedRankTerm D A m M t s = (fun s ↦ m - s) s := by
    intro s h1 h2
    clear * - h1 h2 hNLK hn1c hn1b2 hb2lt hNm hc2 hq
    unfold gradedRankTerm gradedSourceCount
    beta_reduce
    split <;> omega
  rw [sumIco_congr e0, sumIco_congr e1, sumIco_congr e2, sumIco_congr e3, sumIco_congr e4,
    sumIco_congr e5, sumIco_const, sumIco_const, sumIco_add_one_sub lo b1 q,
    sumIco_sub b1 n1 m, sumIco_const, sumIco_sub b2 N m]
  clear * -
  omega

/-- `gradedRankBound` in closed form: a bounded number of operations for every `t`. -/
def gradedRankBoundClosed (D A m M t : Nat) : Nat :=
  let N := min m (m * A - (D - 1) * t)
  let q := t - M
  let c2 := t + 1 - q
  let n1 := min N t
  let lo := min q n1
  let b1 := min n1 (max lo ((m + q + 1) / 2))
  let b2 := min N (max n1 (m + 1 - c2))
  (triangle (b1 + 1 - q) - triangle (lo + 1 - q)) +
    (triangle (m - b1 + 1) - triangle (m - n1 + 1)) +
    ((b2 - n1) * c2 + (triangle (m - b2 + 1) - triangle (m - N + 1)))

/-- The closed form equals `gradedRankBound`, for all parameters. -/
theorem gradedRankBoundClosed_eq (D A m M t : Nat) :
    gradedRankBoundClosed D A m M t = gradedRankBound D A m M t :=
  (gradedRankBound_eq_pieces D A m M t _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl).symm

/-- `rowSlotBound` with `gradedRankBound` in closed form: one term per `t ≤ μ`. -/
def rowSlotBoundClosed (D A m M μ n ℓ h : Nat) : Nat :=
  sumRange (μ + 1) fun t ↦ n * gradedRankBoundClosed D A m M t * (h + 1 - ℓ * t)

/-- The closed row bound equals `rowSlotBound`, for all parameters. -/
theorem rowSlotBoundClosed_eq (D A m M μ n ℓ h : Nat) :
    rowSlotBoundClosed D A m M μ n ℓ h = rowSlotBound D A m M μ n ℓ h := by
  unfold rowSlotBoundClosed rowSlotBound
  simp only [gradedRankBoundClosed_eq]

/-- The library row bound equals its closed form, for all parameters. -/
theorem firstOrderCurveShiftedRowSlotBound_eq_closed (D A m M μ n ℓ h : Nat) :
    firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h = rowSlotBoundClosed D A m M μ n ℓ h := by
  rw [firstOrderCurveShiftedRowSlotBound_eq, rowSlotBoundClosed_eq]

end ProximityGap.GrandChallenges.SlotArithmetic
