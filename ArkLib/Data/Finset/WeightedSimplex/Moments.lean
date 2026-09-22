/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Finset.WeightedSimplex
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Exact moments of the unit-weight discrete simplex

Let `σ` be a finite index type with `n = Fintype.card σ` and let `Δ S` be the unit-weight
simplex `natWeightedSimplex (fun _ : σ ↦ 1) S` of natural vectors with total at most `S`. Its
cardinality is `C = (S + n).choose n` (`card_natWeightedSimplex_one`). This file computes the
first and second coordinate moments of `Δ S` as exact counting identities, without division:

* `(n + 1) * ∑ c ∈ Δ S, c i = S * C`;
* `(n + 1) * (n + 2) * ∑ c ∈ Δ S, c i * (c i - 1) = 2 * S * (S - 1) * C`;
* `(n + 1) * (n + 2) * ∑ c ∈ Δ S, c i * c j = S * (S - 1) * C` for `i ≠ j`.

The factor `n + 1` counts the `n` coordinates together with the unused budget, which behaves like
one more coordinate. All three identities hold at `S = 0` and `S = 1` and need no lower bound on
`S`. The proof marks one of the units in coordinate `i` of a vector with total at most `S + 1`,
and splits that coordinate at the mark. The units before the mark become a new coordinate, and the
mark itself is removed. This is a bijection onto `Δ S` over `Option σ`, with the new coordinate at
`none`, so a coordinate sum over `Δ (S + 1)` becomes a cardinality or first moment one dimension
higher.

The second half casts the identities to an arbitrary commutative ring and assembles the weighted
statistic `∑ i, w i * c i`: its sum and its sum of squares over `Δ S` have closed forms. The
normalized mean and variance are in `ArkLib.Data.Finset.WeightedSimplex.Variance`.

## Main statements

* `le_of_mem_natWeightedSimplex`, `zero_mem_natWeightedSimplex`,
  `natWeightedSimplex_nonempty`: the coordinate box and nonemptiness, for arbitrary weights.
* `natSimplexSplit`, `sum_natWeightedSimplex_one_sum_range_split`: the marked-unit splitting
  bijection, stated as a reindexing of sums with values in any additive commutative monoid.
* `sum_natWeightedSimplex_one_apply_succ`: the first moment at budget `S + 1` is the cardinality of
  the simplex over `Option σ` at budget `S`.
* `card_add_one_mul_sum_natWeightedSimplex_one_apply`: the first moment.
* `card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_pred`: the second
  falling-factorial moment.
* `card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_of_ne`: the mixed moment.
* `card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_cast_mul`: the full second-moment
  matrix in a commutative ring.
* `card_add_one_mul_sum_natWeightedSimplex_one_weighted` and
  `card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_weighted_sq`: the weighted first
  and second moments in a commutative ring.
-/

@[expose] public section

namespace Finset

open scoped BigOperators

section Basic

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Every coordinate of a vector in the finite box is at most the budget. This holds for arbitrary
weights, including zero weights, because the box is part of the definition. -/
theorem le_of_mem_natWeightedSimplex {w : σ → ℕ} {W : ℕ} {c : σ → ℕ}
    (hc : c ∈ natWeightedSimplex w W) (i : σ) : c i ≤ W := by
  have hbox := (mem_filter.mp hc).1
  rw [Fintype.mem_piFinset] at hbox
  exact Nat.le_of_lt_succ (mem_range.mp (hbox i))

/-- The zero vector lies in every weighted simplex, including at budget zero and at an empty
index type. -/
theorem zero_mem_natWeightedSimplex (w : σ → ℕ) (W : ℕ) : 0 ∈ natWeightedSimplex w W := by
  refine mem_filter.mpr ⟨?_, by simp⟩
  rw [Fintype.mem_piFinset]
  intro i
  simp

/-- Every weighted simplex is nonempty, so averages over it are well defined. -/
theorem natWeightedSimplex_nonempty (w : σ → ℕ) (W : ℕ) : (natWeightedSimplex w W).Nonempty :=
  ⟨0, zero_mem_natWeightedSimplex w W⟩

/-- Unit-weight membership is the total-degree budget. -/
private theorem mem_natWeightedSimplex_one {τ : Type*} [Fintype τ] [DecidableEq τ] {W : ℕ}
    {c : τ → ℕ} : c ∈ natWeightedSimplex (fun _ : τ ↦ 1) W ↔ ∑ i, c i ≤ W := by
  rw [mem_natWeightedSimplex (fun _ ↦ one_ne_zero)]
  simp only [one_mul]

end Basic

section Split

variable {σ : Type*} [DecidableEq σ]

private theorem sum_update_add_apply [Fintype σ] (c : σ → ℕ) (i : σ) (b : ℕ) :
    (∑ j, Function.update c i b j) + c i = (∑ j, c j) + b := by
  rw [sum_update_of_mem (mem_univ i), sdiff_singleton_eq_erase]
  have h := sum_erase_add univ c (mem_univ i)
  omega

/-- Split coordinate `i` of `c` at the marked unit `m < c i`. The new coordinate `none` records
the `m` units before the mark, coordinate `some i` keeps the `c i - (m + 1)` units after it, and
the other coordinates are unchanged. The mark itself is removed, so the total drops by one. -/
def natSimplexSplit (i : σ) (c : σ → ℕ) (m : ℕ) : Option σ → ℕ :=
  fun k ↦ k.elim m (Function.update c i (c i - (m + 1)))

/-- Inverse of `natSimplexSplit`: merge the coordinates `none` and `some i` and restore the mark. -/
private def natSimplexMerge (i : σ) (v : Option σ → ℕ) : σ → ℕ :=
  Function.update (fun k ↦ v (some k)) i (v (some i) + v none + 1)

/-- The new coordinate of a split records the units before the mark. -/
@[simp] theorem natSimplexSplit_none (i : σ) (c : σ → ℕ) (m : ℕ) :
    natSimplexSplit i c m none = m := rfl

/-- The split coordinate keeps the units after the mark. -/
@[simp] theorem natSimplexSplit_some_self (i : σ) (c : σ → ℕ) (m : ℕ) :
    natSimplexSplit i c m (some i) = c i - (m + 1) := by
  simp [natSimplexSplit]

/-- Splitting coordinate `i` leaves every other coordinate unchanged. -/
theorem natSimplexSplit_some_of_ne {i j : σ} (hij : i ≠ j) (c : σ → ℕ) (m : ℕ) :
    natSimplexSplit i c m (some j) = c j := by
  simp [natSimplexSplit, Ne.symm hij]

/-- Marked-unit splitting as a reindexing of sums. Pairs `(c, m)` with `c` of total at most
`S + 1` and `m < c i` correspond bijectively to vectors over `Option σ` of total at most `S`, via
`natSimplexSplit i`. Values lie in any additive commutative monoid. -/
theorem sum_natWeightedSimplex_one_sum_range_split [Fintype σ] {M : Type*} [AddCommMonoid M] (i : σ)
    (S : ℕ) (g : (Option σ → ℕ) → M) :
    ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) (S + 1), ∑ m ∈ range (c i),
        g (natSimplexSplit i c m) =
      ∑ v ∈ natWeightedSimplex (fun _ : Option σ ↦ 1) S, g v := by
  rw [sum_sigma']
  refine sum_bij' (fun x _ ↦ natSimplexSplit i x.1 x.2)
    (fun v _ ↦ (⟨natSimplexMerge i v, v none⟩ : Σ _ : σ → ℕ, ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨c, m⟩ hx
    simp only [mem_sigma, mem_natWeightedSimplex_one, mem_range] at hx
    rw [mem_natWeightedSimplex_one, Fintype.sum_option]
    have hsum := sum_update_add_apply c i (c i - (m + 1))
    simp only [natSimplexSplit, Option.elim_none, Option.elim_some]
    omega
  · intro v hv
    rw [mem_natWeightedSimplex_one, Fintype.sum_option] at hv
    rw [mem_sigma, mem_natWeightedSimplex_one, mem_range]
    have hsum := sum_update_add_apply (fun k ↦ v (some k)) i (v (some i) + v none + 1)
    simp only [natSimplexMerge, Function.update_self]
    omega
  · rintro ⟨c, m⟩ hx
    rw [mem_sigma, mem_range] at hx
    have hm : m < c i := hx.2
    refine Sigma.ext ?_ (heq_of_eq rfl)
    funext k
    by_cases hk : k = i
    · subst k
      simp only [natSimplexMerge, natSimplexSplit, Function.update_self, Option.elim_some,
        Option.elim_none]
      omega
    · simp [natSimplexMerge, natSimplexSplit, hk]
  · intro v _
    funext k
    cases k with
    | none => rfl
    | some k =>
      by_cases hk : k = i
      · subst k
        simp [natSimplexMerge, natSimplexSplit]
      · simp [natSimplexMerge, natSimplexSplit]
  · intro _ _
    rfl

end Split

section NatMoments

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- At budget `S + 1`, the unnormalized first moment of a coordinate counts the marked units,
which is the number of vectors over `Option σ` of total at most `S`. -/
theorem sum_natWeightedSimplex_one_apply_succ (i : σ) (S : ℕ) :
    ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) (S + 1), c i =
      (natWeightedSimplex (fun _ : Option σ ↦ 1) S).card := by
  have h := sum_natWeightedSimplex_one_sum_range_split i S (fun _ ↦ (1 : ℕ))
  simpa using h

/-- After splitting coordinate `i`, a different coordinate `j` is unchanged, so the mixed moment
at budget `S + 1` is a first moment over `Option σ` at budget `S`. -/
theorem sum_natWeightedSimplex_one_mul_succ_of_ne {i j : σ} (hij : i ≠ j) (S : ℕ) :
    ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) (S + 1), c i * c j =
      ∑ v ∈ natWeightedSimplex (fun _ : Option σ ↦ 1) S, v (some j) := by
  rw [← sum_natWeightedSimplex_one_sum_range_split i S (fun v ↦ v (some j))]
  apply sum_congr rfl
  intro c _
  simp [natSimplexSplit_some_of_ne hij]

/-- Splitting coordinate `i` at a marked unit leaves `c i - 1` units in the two resulting
coordinates, so the falling-factorial moment at budget `S + 1` is a sum of two first moments over
`Option σ` at budget `S`. -/
theorem sum_natWeightedSimplex_one_mul_pred_succ (i : σ) (S : ℕ) :
    ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) (S + 1), c i * (c i - 1) =
      ∑ v ∈ natWeightedSimplex (fun _ : Option σ ↦ 1) S, (v (some i) + v none) := by
  rw [← sum_natWeightedSimplex_one_sum_range_split i S (fun v ↦ v (some i) + v none)]
  apply sum_congr rfl
  intro c _
  rw [sum_congr rfl (g := fun _ ↦ c i - 1)]
  · simp
  · intro m hm
    have := mem_range.mp hm
    simp only [natSimplexSplit_some_self, natSimplexSplit_none]
    omega

private theorem apply_eq_zero_of_mem_zero {c : σ → ℕ}
    (hc : c ∈ natWeightedSimplex (fun _ : σ ↦ 1) 0) (i : σ) : c i = 0 :=
  Nat.le_zero.mp (le_of_mem_natWeightedSimplex hc i)

/-- The first moment of the unit-weight simplex, without division: with `n = Fintype.card σ`,
`(n + 1) * ∑ c ∈ Δ S, c i = S * #(Δ S)`. After normalization each coordinate has mean
`S / (n + 1)`: the budget is shared evenly among the `n` coordinates and the unused slack. -/
theorem card_add_one_mul_sum_natWeightedSimplex_one_apply (i : σ) (S : ℕ) :
    (Fintype.card σ + 1) * ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, c i =
      S * (natWeightedSimplex (fun _ : σ ↦ 1) S).card := by
  cases S with
  | zero => rw [sum_eq_zero fun c hc ↦ by simp [apply_eq_zero_of_mem_zero hc i]]; simp
  | succ S =>
    rw [sum_natWeightedSimplex_one_apply_succ, card_natWeightedSimplex_one,
      card_natWeightedSimplex_one, Fintype.card_option]
    have h := Nat.choose_succ_right_eq (S + 1 + Fintype.card σ) (Fintype.card σ)
    rw [show S + (Fintype.card σ + 1) = S + 1 + Fintype.card σ by omega,
      show S + 1 + Fintype.card σ - Fintype.card σ = S + 1 by omega] at *
    rw [Nat.mul_comm, h, Nat.mul_comm]

/-- The mixed second moment at distinct coordinates, without division: with
`n = Fintype.card σ`, `(n + 1) * (n + 2) * ∑ c ∈ Δ S, c i * c j = S * (S - 1) * #(Δ S)`.
The natural subtraction is harmless because both sides vanish at `S = 0`. The hypothesis
`i ≠ j` is necessary: at `i = j` the sum is the second moment of one coordinate, given by
`card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_pred`. -/
theorem card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_of_ne {i j : σ}
    (hij : i ≠ j) (S : ℕ) :
    (Fintype.card σ + 1) * (Fintype.card σ + 2) *
        ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, c i * c j =
      S * (S - 1) * (natWeightedSimplex (fun _ : σ ↦ 1) S).card := by
  cases S with
  | zero => rw [sum_eq_zero fun c hc ↦ by simp [apply_eq_zero_of_mem_zero hc i]]; simp
  | succ S =>
    have hMass := card_add_one_mul_sum_natWeightedSimplex_one_apply i (S + 1)
    rw [sum_natWeightedSimplex_one_apply_succ] at hMass
    have hMoment := card_add_one_mul_sum_natWeightedSimplex_one_apply (some j) S
    rw [Fintype.card_option] at hMoment
    rw [sum_natWeightedSimplex_one_mul_succ_of_ne hij, Nat.add_sub_cancel]
    calc
      (Fintype.card σ + 1) * (Fintype.card σ + 2) *
          ∑ v ∈ natWeightedSimplex (fun _ : Option σ ↦ 1) S, v (some j) =
          (Fintype.card σ + 1) * ((Fintype.card σ + 1 + 1) *
            ∑ v ∈ natWeightedSimplex (fun _ : Option σ ↦ 1) S, v (some j)) := by ring
      _ = S * ((Fintype.card σ + 1) *
            (natWeightedSimplex (fun _ : Option σ ↦ 1) S).card) := by rw [hMoment]; ring
      _ = (S + 1) * S * (natWeightedSimplex (fun _ : σ ↦ 1) (S + 1)).card := by
        rw [hMass]; ring

/-- The second falling-factorial moment of one coordinate, without division: with
`n = Fintype.card σ`, `(n + 1) * (n + 2) * ∑ c ∈ Δ S, c i * (c i - 1) =
2 * S * (S - 1) * #(Δ S)`. It is twice the mixed moment, which is the difference between repeated
and distinct coordinates. It holds at `S = 0` and `S = 1`, where both sides vanish. -/
theorem card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_pred (i : σ) (S : ℕ) :
    (Fintype.card σ + 1) * (Fintype.card σ + 2) *
        ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, c i * (c i - 1) =
      2 * S * (S - 1) * (natWeightedSimplex (fun _ : σ ↦ 1) S).card := by
  cases S with
  | zero => rw [sum_eq_zero fun c hc ↦ by simp [apply_eq_zero_of_mem_zero hc i]]; simp
  | succ S =>
    have hMass := card_add_one_mul_sum_natWeightedSimplex_one_apply i (S + 1)
    rw [sum_natWeightedSimplex_one_apply_succ] at hMass
    have hMoment := card_add_one_mul_sum_natWeightedSimplex_one_apply (some i) S
    have hLast := card_add_one_mul_sum_natWeightedSimplex_one_apply (none : Option σ) S
    rw [Fintype.card_option] at hMoment hLast
    rw [sum_natWeightedSimplex_one_mul_pred_succ, Nat.add_sub_cancel, sum_add_distrib]
    calc
      (Fintype.card σ + 1) * (Fintype.card σ + 2) *
          ((∑ v ∈ natWeightedSimplex (fun _ : Option σ ↦ 1) S, v (some i)) +
            ∑ v ∈ natWeightedSimplex (fun _ : Option σ ↦ 1) S, v none) =
          (Fintype.card σ + 1) * ((Fintype.card σ + 1 + 1) *
            (∑ v ∈ natWeightedSimplex (fun _ : Option σ ↦ 1) S, v (some i)) +
            (Fintype.card σ + 1 + 1) *
              ∑ v ∈ natWeightedSimplex (fun _ : Option σ ↦ 1) S, v none) := by ring
      _ = 2 * S * ((Fintype.card σ + 1) *
            (natWeightedSimplex (fun _ : Option σ ↦ 1) S).card) := by
        rw [hMoment, hLast]; ring
      _ = 2 * (S + 1) * S * (natWeightedSimplex (fun _ : σ ↦ 1) (S + 1)).card := by
        rw [hMass]; ring

end NatMoments

section RingMoments

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*}

/-- The first moment cast to a commutative semiring. -/
theorem card_add_one_mul_sum_natWeightedSimplex_one_cast [CommSemiring R] (i : σ) (S : ℕ) :
    ((Fintype.card σ : R) + 1) * ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, (c i : R) =
      (S : R) * (natWeightedSimplex (fun _ : σ ↦ 1) S).card := by
  have h := congrArg (Nat.cast : ℕ → R) (card_add_one_mul_sum_natWeightedSimplex_one_apply i S)
  push_cast at h
  exact h

/-- The second-moment matrix of the unit-weight simplex in a commutative ring. With
`n = Fintype.card σ` and `C = #(Δ S)`,
`(n + 1) * (n + 2) * ∑ c ∈ Δ S, c i * c j = (S * (S - 1) + [i = j] * S * (S + n + 1)) * C`.
The diagonal correction `S * (S + n + 1)` combines the falling-factorial moment with the first
moment. Ring subtraction makes the formula valid at `S = 0` without a case split. -/
theorem card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_cast_mul [CommRing R]
    (i j : σ) (S : ℕ) :
    ((Fintype.card σ : R) + 1) * ((Fintype.card σ : R) + 2) *
        ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, (c i : R) * (c j : R) =
      ((S : R) * ((S : R) - 1) +
        if i = j then (S : R) * ((S : R) + ((Fintype.card σ : R) + 1)) else 0) *
          (natWeightedSimplex (fun _ : σ ↦ 1) S).card := by
  have hPred (a : ℕ) : ((a * (a - 1) : ℕ) : R) = (a : R) * ((a : R) - 1) := by
    cases a <;> simp
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte]
    have hFirst := card_add_one_mul_sum_natWeightedSimplex_one_cast (R := R) i S
    have hFactorial := congrArg (fun a : ℕ ↦ (a : R))
      (card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_pred i S)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_sum] at hFactorial
    rw [mul_assoc 2 (S : R), ← Nat.cast_mul S (S - 1), hPred] at hFactorial
    simp only [← Nat.cast_mul, hPred] at hFactorial
    have hSquare : ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, (c i : R) * (c i : R) =
        ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, (c i : R) * ((c i : R) - 1) +
          ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, (c i : R) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun _ _ ↦ by ring
    rw [hSquare, mul_add, hFactorial]
    linear_combination ((Fintype.card σ : R) + 2) * hFirst
  · simp only [hij, ↓reduceIte, add_zero]
    have h := congrArg (fun a : ℕ ↦ (a : R))
      (card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_of_ne hij S)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_sum] at h
    rw [← Nat.cast_mul S (S - 1), hPred] at h
    exact h

/-- The weighted first moment in a commutative semiring. With `n = Fintype.card σ`,
`(n + 1) * ∑ c ∈ Δ S, ∑ i, w i * c i = S * #(Δ S) * ∑ i, w i`. -/
theorem card_add_one_mul_sum_natWeightedSimplex_one_weighted [CommSemiring R] (w : σ → R)
    (S : ℕ) :
    ((Fintype.card σ : R) + 1) *
        ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, ∑ i, w i * (c i : R) =
      (S : R) * (natWeightedSimplex (fun _ : σ ↦ 1) S).card * ∑ i, w i := by
  rw [sum_comm, mul_sum, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← mul_sum, mul_left_comm, card_add_one_mul_sum_natWeightedSimplex_one_cast]
  ring

/-- Expanding the square of a weighted statistic and applying the second-moment matrix. -/
private theorem sum_weighted_matrix [CommRing R] (w : σ → R) (a b c : R) :
    ∑ i, ∑ j, w i * w j * ((a + if i = j then b else 0) * c) =
      (a * (∑ i, w i) ^ 2 + b * ∑ i, w i ^ 2) * c := by
  have hTerm (i j : σ) : w i * w j * ((a + if i = j then b else 0) * c) =
      a * c * (w i * w j) + if j = i then b * c * w i ^ 2 else 0 := by
    by_cases h : i = j
    · subst j
      simp only [↓reduceIte]
      ring
    · simp only [h, Ne.symm h, ↓reduceIte, add_zero]
      ring
  simp_rw [hTerm, sum_add_distrib, sum_ite_eq']
  simp only [mem_univ, ↓reduceIte]
  simp_rw [← mul_sum]
  rw [← sum_mul]
  ring

/-- The weighted second moment in a commutative ring. With `n = Fintype.card σ` and
`C = #(Δ S)`, `(n + 1) * (n + 2) * ∑ c ∈ Δ S, (∑ i, w i * c i) ^ 2` equals
`(S * (S - 1) * (∑ i, w i) ^ 2 + S * (S + n + 1) * ∑ i, w i ^ 2) * C`. The weights are arbitrary
ring elements and the slack coordinate carries weight zero. -/
theorem card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_weighted_sq [CommRing R]
    (w : σ → R) (S : ℕ) :
    ((Fintype.card σ : R) + 1) * ((Fintype.card σ : R) + 2) *
        ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, (∑ i, w i * (c i : R)) ^ 2 =
      ((S : R) * ((S : R) - 1) * (∑ i, w i) ^ 2 +
        (S : R) * ((S : R) + ((Fintype.card σ : R) + 1)) * ∑ i, w i ^ 2) *
          (natWeightedSimplex (fun _ : σ ↦ 1) S).card := by
  have hExpand : ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, (∑ i, w i * (c i : R)) ^ 2 =
      ∑ i, ∑ j, w i * w j *
        ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, (c i : R) * (c j : R) := by
    calc
      ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, (∑ i, w i * (c i : R)) ^ 2 =
          ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S, ∑ i, ∑ j,
            w i * w j * ((c i : R) * (c j : R)) :=
        sum_congr rfl fun c _ ↦ by
          rw [sq, sum_mul_sum]
          exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
      _ = ∑ i, ∑ j, ∑ c ∈ natWeightedSimplex (fun _ : σ ↦ 1) S,
            w i * w j * ((c i : R) * (c j : R)) := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ ↦ sum_comm
      _ = _ := sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ (mul_sum _ _ _).symm
  rw [hExpand, mul_sum, ← sum_weighted_matrix]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [mul_left_comm,
    card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_cast_mul]

end RingMoments

end Finset
