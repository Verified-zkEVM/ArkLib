/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Dense common intersections of tuples of large sets

Let `T x` be a subset of an `n`-element ambient type, for each `x` in a finite type `β` of size `N`,
with every `T x` of size at least `μ`. If the sets are large enough, some `k`-tuple of distinct
indices `ys` has a common intersection `⋂ T (ys i)` meeting many of the sets `T x` densely.

The proof is the averaging argument behind list-decoding bounds for generators. Summing
`|⋂ T (ys i) ∩ T x|` over all `ys : κ → β` and `x : β` gives `∑ j, d j ^ (k + 1)`, where
`d j = #{x | j ∈ T x}` (`sum_sum_card_inf_inter_eq`). Jensen's inequality bounds this below by
`(∑ j, d j) ^ (k + 1) / n ^ k`, and `∑ j, d j = ∑ x, |T x| ≥ N · μ`. The non-injective tuples
number at most `k.choose 2 · N ^ (k - 1)` (`pow_succ_le_choose_two_mul_pow_add_mul_descFactorial`),
too few to carry the sum, so some injective tuple carries it.

Everything is stated without division and with no coding-theory hypotheses.

## Main statements

* `Finset.sum_sum_card_inf_inter_eq` — the incidence identity `∑ ys, ∑ x, |⋂ T (ys i) ∩ T x| =
  ∑ j, d j ^ (k + 1)`.
* `Nat.pow_succ_le_choose_two_mul_pow_add_mul_descFactorial` — the birthday bound
  `N ^ (k + 1) ≤ k.choose 2 · N ^ k + N · N.descFactorial k`.
* `Finset.exists_injective_two_mul_card_filter_lt_card_inf_inter` — the main statement.
-/

@[expose] public section

namespace Nat

/-- **Birthday bound.** At most `k.choose 2 · N ^ (k - 1)` of the `N ^ k` maps from a `k`-element
type to an `N`-element type fail to be injective, since `N.descFactorial k` of them are injective.
Stated multiplied through by `N`, so that no subtraction is needed. -/
theorem pow_succ_le_choose_two_mul_pow_add_mul_descFactorial (N k : ℕ) :
    N ^ (k + 1) ≤ k.choose 2 * N ^ k + N * N.descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : N * N.descFactorial k ≤ N.descFactorial (k + 1) + k * N.descFactorial k := by
      rw [Nat.descFactorial_succ, ← Nat.add_mul]
      exact Nat.mul_le_mul_right _ (le_tsub_add : N ≤ N - k + k)
    have hD : N.descFactorial k ≤ N ^ k := Nat.descFactorial_le_pow N k
    calc N ^ (k + 1 + 1) = N * N ^ (k + 1) := by ring
      _ ≤ N * (k.choose 2 * N ^ k + N * N.descFactorial k) := Nat.mul_le_mul_left _ ih
      _ = k.choose 2 * N ^ (k + 1) + N * (N * N.descFactorial k) := by ring
      _ ≤ k.choose 2 * N ^ (k + 1) + N * (N.descFactorial (k + 1) + k * N.descFactorial k) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ hstep) _
      _ = k.choose 2 * N ^ (k + 1) + k * (N * N.descFactorial k)
            + N * N.descFactorial (k + 1) := by ring
      _ ≤ k.choose 2 * N ^ (k + 1) + k * N ^ (k + 1) + N * N.descFactorial (k + 1) := by
          gcongr
          calc N * N.descFactorial k ≤ N * N ^ k := Nat.mul_le_mul_left _ hD
            _ = N ^ (k + 1) := by ring
      _ = (k + 1).choose 2 * N ^ (k + 1) + N * N.descFactorial (k + 1) := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring

end Nat

namespace Finset

variable {β κ ι : Type*} [Fintype β] [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- **The incidence identity.** Summing the size of `⋂ T (ys i) ∩ T x` over every tuple
`ys : κ → β` and every `x : β` counts each point `j` exactly `d j ^ (|κ| + 1)` times, where
`d j = #{x | j ∈ T x}`: a point lies in the intersection exactly when it lies in all `|κ| + 1`
chosen sets, and the choices are independent. -/
theorem sum_sum_card_inf_inter_eq (T : β → Finset ι) :
    ∑ ys : κ → β, ∑ x : β, #((univ.inf fun i => T (ys i)) ∩ T x)
      = ∑ j : ι, #(univ.filter fun x => j ∈ T x) ^ (Fintype.card κ + 1) := by
  classical
  have hcard : ∀ (ys : κ → β) (x : β), #((univ.inf fun i => T (ys i)) ∩ T x)
      = ∑ j : ι, (∏ i, if j ∈ T (ys i) then 1 else 0) * (if j ∈ T x then 1 else 0) := by
    intro ys x
    simp only [Fintype.prod_boole, ite_zero_mul_ite_zero, mul_one, Finset.sum_boole, Nat.cast_id]
    congr 1
    ext j
    simp [Finset.mem_inf]
  have hrow : ∀ j : ι, ∑ ys : κ → β, (∏ i, if j ∈ T (ys i) then 1 else 0)
      = #(univ.filter fun x => j ∈ T x) ^ Fintype.card κ := by
    intro j
    rw [← Fintype.prod_sum (fun (_ : κ) (b : β) => if j ∈ T b then 1 else 0)]
    simp [Finset.sum_boole]
  calc ∑ ys : κ → β, ∑ x : β, #((univ.inf fun i => T (ys i)) ∩ T x)
      = ∑ ys : κ → β, ∑ j : ι, ∑ x : β,
          (∏ i, if j ∈ T (ys i) then 1 else 0) * (if j ∈ T x then 1 else 0) := by
        refine Finset.sum_congr rfl fun ys _ => ?_
        simp_rw [hcard ys]
        exact Finset.sum_comm
    _ = ∑ j : ι, ∑ ys : κ → β, ∑ x : β,
          (∏ i, if j ∈ T (ys i) then 1 else 0) * (if j ∈ T x then 1 else 0) := Finset.sum_comm
    _ = ∑ j : ι, (∑ ys : κ → β, ∏ i, if j ∈ T (ys i) then 1 else 0)
          * (∑ x : β, if j ∈ T x then 1 else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul_sum]
    _ = ∑ j : ι, #(univ.filter fun x => j ∈ T x) ^ (Fintype.card κ + 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hrow j, Finset.sum_boole, Nat.cast_id, pow_succ]

omit [DecidableEq κ] in
/-- **Some injective tuple has a dense intersection with many sets.** Let `T x`, for `x` in a
finite type `β` of size `N`, be subsets of an `n`-element type, each of size at least `μ`, and let
`k = |κ|`. If

* `n ^ k · (θ + n · η) ≤ μ ^ (k + 1)` (the sets are large enough that an average
  `(k + 1)`-wise intersection exceeds `θ + n · η`), and
* `2 · k.choose 2 < N · η` (there are enough sets that repeated indices are rare),

then some injective `ys : κ → β` has `⋂ T (ys i)` meeting at least `N · η / 2` of the sets `T x`
in more than `θ` points. Stated division-free as `N · η ≤ 2 · #{x | θ < |⋂ T (ys i) ∩ T x|}`.

The average of `|⋂ T (ys i) ∩ T x|` over all `(ys, x)` is at least `θ + n · η`, by
`sum_sum_card_inf_inter_eq` and Jensen's inequality; each term is at most `n`, so at least an
`η`-fraction of the pairs exceed `θ`. The non-injective `ys` are too few to carry that fraction
(`Nat.pow_succ_le_choose_two_mul_pow_add_mul_descFactorial`), so some injective `ys` carries half of
it.

`ι` must be nonempty: with `n = 0` no intersection exceeds `θ ≥ 0`. -/
theorem exists_injective_two_mul_card_filter_lt_card_inf_inter [Nonempty ι]
    (T : β → Finset ι) {μ θ η : ℝ} (hμ : 0 ≤ μ) (hθ : 0 ≤ θ)
    (hT : ∀ x, μ ≤ #(T x))
    (hpow : (Fintype.card ι : ℝ) ^ Fintype.card κ * (θ + Fintype.card ι * η)
      ≤ μ ^ (Fintype.card κ + 1))
    (hN : (2 * (Fintype.card κ).choose 2 : ℝ) < Fintype.card β * η) :
    ∃ ys : κ → β, Function.Injective ys ∧
      (Fintype.card β : ℝ) * η
        ≤ 2 * #(univ.filter fun x => θ < (#((univ.inf fun i => T (ys i)) ∩ T x) : ℝ)) := by
  classical
  set n := Fintype.card ι with hn_def
  set N := Fintype.card β with hN_def
  set k := Fintype.card κ with hk_def
  set c : (κ → β) → β → ℕ := fun ys x => #((univ.inf fun i => T (ys i)) ∩ T x) with hc_def
  set G : (κ → β) → ℕ := fun ys => #(univ.filter fun x => θ < (c ys x : ℝ)) with hG_def
  set d : ι → ℕ := fun j => #(univ.filter fun x => j ∈ T x) with hd_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hC0 : (0 : ℝ) ≤ 2 * (k.choose 2 : ℝ) := by positivity
  have hNη : 0 < (N : ℝ) * η := hC0.trans_lt hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero fun h => by simp [h] at hNη
  have hP : (0 : ℝ) < (N : ℝ) ^ k := by positivity
  -- the incidence identity, the degree sum, and Jensen
  have hfub : ∑ ys : κ → β, ∑ x : β, (c ys x : ℝ) = ∑ j : ι, (d j : ℝ) ^ (k + 1) := by
    exact_mod_cast sum_sum_card_inf_inter_eq (κ := κ) T
  have hsumd : ∑ j : ι, (d j : ℝ) = ∑ x : β, (#(T x) : ℝ) := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (univ : Finset β)) (t := (univ : Finset ι)) (fun x j => j ∈ T x)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow, Finset.filter_univ_mem] at h
    exact_mod_cast h.symm
  have hjensen : (∑ j : ι, (d j : ℝ)) ^ (k + 1) ≤ (n : ℝ) ^ k * ∑ j : ι, (d j : ℝ) ^ (k + 1) := by
    have h := _root_.pow_sum_div_card_le_sum_pow (s := (univ : Finset ι))
      (f := fun j => (d j : ℝ)) (fun j _ => Nat.cast_nonneg _) k
    rw [Finset.card_univ, div_le_iff₀ (by positivity)] at h
    linarith
  have hlow : (N : ℝ) * μ ≤ ∑ j : ι, (d j : ℝ) := by
    rw [hsumd]
    calc (N : ℝ) * μ = ∑ _x : β, μ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ x : β, (#(T x) : ℝ) := Finset.sum_le_sum fun x _ => hT x
  -- the average intersection exceeds `θ + n · η`
  have hbelow : (N : ℝ) ^ (k + 1) * (θ + n * η) ≤ ∑ ys : κ → β, ∑ x : β, (c ys x : ℝ) := by
    have hchain : (n : ℝ) ^ k * ((N : ℝ) ^ (k + 1) * (θ + n * η))
        ≤ (n : ℝ) ^ k * ∑ ys : κ → β, ∑ x : β, (c ys x : ℝ) := by
      calc (n : ℝ) ^ k * ((N : ℝ) ^ (k + 1) * (θ + n * η))
          = (N : ℝ) ^ (k + 1) * ((n : ℝ) ^ k * (θ + n * η)) := by ring
        _ ≤ (N : ℝ) ^ (k + 1) * μ ^ (k + 1) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ((N : ℝ) * μ) ^ (k + 1) := (mul_pow _ _ _).symm
        _ ≤ (∑ j : ι, (d j : ℝ)) ^ (k + 1) := pow_le_pow_left₀ (by positivity) hlow _
        _ ≤ (n : ℝ) ^ k * ∑ j : ι, (d j : ℝ) ^ (k + 1) := hjensen
        _ = (n : ℝ) ^ k * ∑ ys : κ → β, ∑ x : β, (c ys x : ℝ) := by rw [hfub]
    exact le_of_mul_le_mul_left hchain (by positivity)
  -- each tuple contributes at most `n · G ys + N · θ`
  have hupper : ∀ ys : κ → β, ∑ x : β, (c ys x : ℝ) ≤ n * (G ys : ℝ) + N * θ := by
    intro ys
    have hpt : ∀ x : β, (c ys x : ℝ) ≤ n * (if θ < (c ys x : ℝ) then 1 else 0) + θ := by
      intro x
      split_ifs with h
      · have : (c ys x : ℝ) ≤ n := by exact_mod_cast Finset.card_le_univ _
        linarith
      · linarith [not_lt.mp h]
    calc ∑ x : β, (c ys x : ℝ) ≤ ∑ x : β, (n * (if θ < (c ys x : ℝ) then 1 else 0) + θ) :=
          Finset.sum_le_sum fun x _ => hpt x
      _ = n * (G ys : ℝ) + N * θ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
  -- so the good pairs number at least `η · N ^ (k + 1)`
  have hsumG : (N : ℝ) ^ k * N * η ≤ ∑ ys : κ → β, (G ys : ℝ) := by
    have hcardfun : (Fintype.card (κ → β) : ℝ) = (N : ℝ) ^ k := by
      rw [Fintype.card_fun]; push_cast; rfl
    have h := hbelow.trans (Finset.sum_le_sum fun ys _ => hupper ys)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hcardfun] at h
    have h' : (n : ℝ) * ((N : ℝ) ^ k * N * η) ≤ n * ∑ ys : κ → β, (G ys : ℝ) := by
      have hpow1 : (N : ℝ) ^ (k + 1) = (N : ℝ) ^ k * N := pow_succ _ _
      rw [hpow1] at h
      nlinarith
    exact le_of_mul_le_mul_left h' hnR
  -- split off the non-injective tuples, which the birthday bound makes few
  have hInjcard : (#((univ : Finset (κ → β)).filter Function.Injective) : ℝ)
      = (N.descFactorial k : ℝ) := by
    rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding κ β),
      Fintype.card_embedding_eq]
  have hsplit : (#((univ : Finset (κ → β)).filter Function.Injective) : ℝ)
      + (#((univ : Finset (κ → β)).filter fun ys => ¬ Function.Injective ys) : ℝ)
      = (N : ℝ) ^ k := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (κ → β))) Function.Injective
    rw [Finset.card_univ, Fintype.card_fun] at h
    exact_mod_cast h
  have hbirthday : ((N.descFactorial k : ℕ) : ℝ) * N
      + (#((univ : Finset (κ → β)).filter fun ys => ¬ Function.Injective ys) : ℝ) * N
      ≤ (k.choose 2 : ℝ) * (N : ℝ) ^ k + N * (N.descFactorial k : ℝ) := by
    have hb := Nat.pow_succ_le_choose_two_mul_pow_add_mul_descFactorial N k
    have hbR : (N : ℝ) ^ (k + 1)
        ≤ (k.choose 2 : ℝ) * (N : ℝ) ^ k + N * (N.descFactorial k : ℝ) := by
      exact_mod_cast hb
    have hsum : ((N.descFactorial k : ℕ) : ℝ)
        + (#((univ : Finset (κ → β)).filter fun ys => ¬ Function.Injective ys) : ℝ)
        = (N : ℝ) ^ k := by rw [← hInjcard]; exact hsplit
    calc ((N.descFactorial k : ℕ) : ℝ) * N
          + (#((univ : Finset (κ → β)).filter fun ys => ¬ Function.Injective ys) : ℝ) * N
        = (((N.descFactorial k : ℕ) : ℝ)
            + (#((univ : Finset (κ → β)).filter fun ys => ¬ Function.Injective ys) : ℝ)) * N := by
          ring
      _ = (N : ℝ) ^ (k + 1) := by rw [hsum, pow_succ]
      _ ≤ (k.choose 2 : ℝ) * (N : ℝ) ^ k + N * (N.descFactorial k : ℝ) := hbR
  have hnonInj : ∑ ys ∈ (univ : Finset (κ → β)).filter (fun ys => ¬ Function.Injective ys),
      (G ys : ℝ) ≤ (k.choose 2 : ℝ) * (N : ℝ) ^ k := by
    have hle : ∀ ys ∈ (univ : Finset (κ → β)).filter (fun ys => ¬ Function.Injective ys),
        (G ys : ℝ) ≤ N := fun ys _ => by
      exact_mod_cast (Finset.card_filter_le _ _).trans_eq Finset.card_univ
    have := Finset.sum_le_card_nsmul _ _ _ hle
    rw [nsmul_eq_mul] at this
    linarith
  -- if every injective tuple carried less than half, the total would be too small
  by_contra! hcon
  have hinj : 2 * ∑ ys ∈ (univ : Finset (κ → β)).filter Function.Injective, (G ys : ℝ)
      ≤ (N : ℝ) ^ k * (N * η) := by
    have hle : ∀ ys ∈ (univ : Finset (κ → β)).filter Function.Injective,
        2 * (G ys : ℝ) ≤ N * η := fun ys hys =>
      (hcon ys (Finset.mem_filter.mp hys).2).le
    have h := Finset.sum_le_card_nsmul _ _ _ hle
    rw [nsmul_eq_mul, ← Finset.mul_sum, hInjcard] at h
    have hD : ((N.descFactorial k : ℕ) : ℝ) ≤ (N : ℝ) ^ k := by
      exact_mod_cast Nat.descFactorial_le_pow N k
    nlinarith
  have htot := Finset.sum_filter_add_sum_filter_not (univ : Finset (κ → β))
    Function.Injective (fun ys => (G ys : ℝ))
  nlinarith [mul_pos hP (sub_pos.mpr hN)]

end Finset
