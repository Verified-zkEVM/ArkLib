/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.BigOperators.Fin
import ArkLib.Data.Fin.Basic
import ArkLib.Data.Fin.Fold
import ArkLib.Data.Fin.Tuple.Lemmas

/-!
# Fin Sigma Equivalences

We re-define big-operators sum and product over `Fin` to have good definitional equalities.
-/

universe u v

open Finset

namespace Fin

section BigOperators

variable {α : Type*} [CommMonoid α]

/-- Version of multiplying over `Fin` vectors with good definitional equalities, using `dfoldl'`.

The definitional equality we want is that:
`vprod a = a ⟨n,⬝⟩ * a ⟨n-1,⬝⟩ * ... * a ⟨0,⬝⟩ * 1`
-/
-- @[to_additive
-- "Version of summing over `Fin` vectors with good definitional equalities, using `dfoldl'`.

-- The definitional equality we want is that: `vsum a = a 0 + a 1 + ... + a (n-1) + 0`.

-- When `x + 0 = x` definitionally in `α`, we have the following definitional equalities:
-- - `vsum !v[] = 0`
-- - `vsum !v[a] = a`
-- - `vsum !v[a, b] = a + b`
-- - `vsum !v[a, b, c] = (a + b) + c`
-- - and so on
-- "]
def vprod {n : ℕ} (a : Fin n → α) : α :=
  match n with
    | 0 => 1
    | 1 => a 0
    | n + 1 => vprod (a ∘ Fin.castSucc) * a (Fin.last n)

-- Can't use `to_additive` attribute for some reason
def vsum {n : ℕ} (a : Fin n → ℕ) : ℕ := match n with
  | 0 => 0
  | 1 => a 0
  | n + 1 => vsum (a ∘ Fin.castSucc) + a (Fin.last n)

variable {n : ℕ}

@[simp]
lemma vprod_zero {a : Fin 0 → α} : vprod a = 1 := rfl

@[simp]
lemma vprod_one {a : Fin 1 → α} : vprod a = a 0 := rfl

@[simp]
lemma vprod_succ {a : Fin (n + 2) → α} : vprod a = vprod (a ∘ Fin.castSucc) * a (Fin.last _) := rfl

@[simp]
lemma vprod_two {a : Fin 2 → α} : vprod a = a 0 * a 1 := rfl

@[simp]
lemma vprod_three {a : Fin 3 → α} : vprod a = a 0 * a 1 * a 2 := rfl

/-- `vprod a` is equivalent to the standard `Finset`-based definition, `∏ i, a i`. -/
lemma vprod_eq_univ_prod {a : Fin n → α} : vprod a = ∏ i, a i := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 => simp [ih2, Fin.prod_univ_castSucc]

@[simp]
lemma vsum_zero {a : Fin 0 → ℕ} : vsum a = 0 := rfl

@[simp]
lemma vsum_one {a : Fin 1 → ℕ} : vsum a = a 0 := rfl

@[simp]
lemma vsum_succ {a : Fin (n + 2) → ℕ} : vsum a = vsum (a ∘ Fin.castSucc) + a (Fin.last _) := rfl

@[simp]
lemma vsum_two {a : Fin 2 → ℕ} : vsum a = a 0 + a 1 := rfl

@[simp]
lemma vsum_three {a : Fin 3 → ℕ} : vsum a = a 0 + a 1 + a 2 := rfl

/-- `vsum a` is equivalent to the standard `Finset`-based definition, `∑ i, a i`. -/
lemma vsum_eq_univ_sum {a : Fin n → ℕ} : vsum a = ∑ i, a i := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 => simp [ih2, Fin.sum_univ_castSucc]

end BigOperators

end Fin

namespace Fin

section Sum

-- #check finSumFinEquiv

-- def finSumFinEquiv' {m n : ℕ} : Fin m ⊕ Fin n ≃ Fin (m + n) := match n with
--   | 0 => Equiv.sumEmpty _ _
--   | n + 1 => by dsimp

end Sum

section Sigma

variable {m : ℕ} {n : Fin m → ℕ}

def injSum' {m : ℕ} {n : Fin m → ℕ} (i : Fin m) (j : Fin (n i)) : Fin (vsum n) := match m with
  | 0 => Fin.elim0 i
  | 1 => match i with | 0 => j
  | m + 2 => by
    by_cases hi : i = Fin.last (m + 1)
    · rw [hi] at j; exact Fin.natAdd _ j
    · letI i' := i.castPred hi
      haveI : i = i'.castSucc := by simp [i']
      rw [this] at j
      exact Fin.castAdd _ (injSum' i' j)

@[simp]
theorem injSum'_zero {n : Fin 0 → ℕ} {i : Fin 0} (j : Fin (n i)) : injSum' i j = Fin.elim0 i := rfl

@[simp]
theorem injSum'_one {n : Fin 1 → ℕ} {i : Fin 1} (j : Fin (n i)) :
    injSum' i j = match i with | 0 => j := rfl

-- @[simp]
-- theorem injSum'_succ {i : Fin (m + 1)} (j : Fin (n i)) :
--     injSum' i j =
-- if i = Fin.last (m + 1) then j else Fin.castAdd (n i) (injSum' i.castPred j) := rfl

def splitSum' {m : ℕ} {n : Fin m → ℕ} (k : Fin (vsum n)) : (i : Fin m) × Fin (n i) := match m with
  | 0 => Fin.elim0 k
  | 1 => ⟨0, k⟩
  | _ + 2 =>
    Fin.addCases
      (fun k => let ⟨i, j⟩ := splitSum' k; ⟨i.castSucc, j⟩)
      (fun k => ⟨Fin.last _, k⟩)
      k
  -- match finSumFinEquiv.symm k with
  --   | Sum.inl k => let ⟨i, j⟩ := splitSum' k; ⟨i.castSucc, j⟩
  --   | Sum.inr k => ⟨Fin.last _, k⟩

@[simp]
theorem splitSum'_zero {n : Fin 0 → ℕ} {k : Fin (vsum n)} : splitSum' k = Fin.elim0 k := rfl

@[simp]
theorem splitSum'_one {n : Fin 1 → ℕ} {k : Fin (vsum n)} : splitSum' k = ⟨0, k⟩ := rfl

@[simp]
theorem splitSum'_succ {n : Fin (m + 2) → ℕ} {k : Fin (vsum n)} :
    splitSum' k = Fin.addCases (fun k => let ⟨i, j⟩ := splitSum' k; ⟨i.castSucc, j⟩)
      (fun k => ⟨Fin.last _, k⟩) k := rfl

def finSum'FinEquiv' {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (vsum n) where
  toFun := fun ⟨i, j⟩ => injSum' i j
  invFun := splitSum'
  left_inv := fun k => by
    induction m using Nat.twoStepInduction with
    | zero => exact Fin.elim0 k.1
    | one => dsimp; aesop
    | more m ih =>
      simp [injSum', splitSum']
      by_cases hi : k.1 = Fin.last (m + 1)
      · obtain ⟨i, j⟩ := k; simp_all only [↓reduceDIte, addCases_right, Sigma.mk.injEq,
        cast_heq, and_self]
      · obtain ⟨i, j⟩ := k
        simp_all only [↓reduceDIte, addCases_left]
        rename_i ih'
        haveI : i = (i.castPred hi).castSucc := by simp
        have := ih' (n := n ∘ Fin.castSucc) ⟨i.castPred hi, j⟩
        simp at this
        rw [this]; simp
  right_inv := fun k => by
    induction m using Nat.twoStepInduction with
    | zero => exact Fin.elim0 k
    | one => simp
    | more m ih => sorry
      -- dsimp at k
      -- refine Fin.addCases ?_ ?_ k
      -- · intro i; simp
      -- simp [injSum', splitSum']
      -- by_cases hi : k = Fin.last (m + 1)
      -- simp_all

end Sigma

end Fin

namespace Fin

variable {α : Sort*}

def vjoin {m : ℕ} {n : Fin m → ℕ} (v : (i : Fin m) → Fin (n i) → α) :
    Fin (vsum n) → α := match m with
  | 0 => !v[]
  | 1 => v 0
  | _ + 2 => vappend (vjoin (fun i => v (castSucc i))) (v (last _))

@[simp]
theorem vjoin_zero {n : Fin 0 → ℕ} {v : (i : Fin 0) → Fin (n i) → α} : vjoin v = !v[] := rfl

@[simp]
theorem vjoin_one {n : Fin 1 → ℕ} {v : (i : Fin 1) → Fin (n i) → α} : vjoin v = v 0 := rfl

@[simp]
theorem vjoin_succ {m : ℕ} {n : Fin (m + 2) → ℕ} {v : (i : Fin (m + 2)) → Fin (n i) → α} :
    vjoin v = vappend (vjoin (fun i => v (castSucc i))) (v (last _)) := rfl

def djoin {m : ℕ} {n : Fin m → ℕ} {α : (i : Fin m) → (j : Fin (n i)) → Sort*}
    (v : (i : Fin m) → (j : Fin (n i)) → α i j) : (k : Fin (vsum n)) → Fin.vjoin α k := match m with
  | 0 => !t[]
  | 1 => v 0
  | _ + 2 => dappend (djoin (fun i => v (castSucc i))) (v (last _))

@[simp]
theorem djoin_zero {n : Fin 0 → ℕ} {α : (i : Fin 0) → (j : Fin (n i)) → Sort*}
    {v : (i : Fin 0) → (j : Fin (n i)) → α i j} : djoin v = !t[] := rfl

@[simp]
theorem djoin_one {n : Fin 1 → ℕ} {α : (i : Fin 1) → (j : Fin (n i)) → Sort*}
    {v : (i : Fin 1) → (j : Fin (n i)) → α i j} : djoin v = v 0 := rfl

@[simp]
theorem djoin_succ {m : ℕ} {n : Fin (m + 2) → ℕ} {α : (i : Fin (m + 2)) → (j : Fin (n i)) → Sort*}
    {v : (i : Fin (m + 2)) → (j : Fin (n i)) → α i j} :
    djoin v = dappend (djoin (fun i => v (castSucc i))) (v (last _)) := rfl

section FinSigmaFinEquiv

variable {n : ℕ}

def map {α β : Fin n → Sort*} (f : (i : Fin n) → α i → β i) (a : (i : Fin n) → α i) :
    (i : Fin n) → β i := fun i => f i (a i)

def range (n : ℕ) : Fin n → ℕ := fun i => i

def ranges {n : ℕ} (a : Fin n → ℕ) : (i : Fin n) → Fin (a i) → ℕ :=
  match n with
  | 0 => fun i => elim0 i
  | n + 1 => fun i => by
    by_cases h : i = 0
    · exact val
    · letI rest := ranges (tail a) (i.pred h)
      simp only [tail, pred, subNat_one_succ] at rest
      exact fun j => rest j + a 0

theorem ranges_eq_ranges_list {a : Fin n → ℕ} :
    List.ofFn (fun i => List.ofFn (ranges a i)) = List.ranges (List.ofFn a) := by
  induction n using Nat.strongRec with
  | ind n IH => sorry

/-- Find the first index `i` such that `k` is smaller than `∑ j < i, a j`, and return `none`
  otherwise.

  This is the dependent version of `Fin.divNat`.
-/
def divSum? {m : ℕ} (n : Fin m → ℕ) (k : ℕ) : Option (Fin m) :=
  find (fun i => k < ∑ j, n (castLE i.isLt j))

theorem divSum?_is_some_iff_lt_sum {m : ℕ} {n : Fin m → ℕ} {k : ℕ} :
    (divSum? n k).isSome ↔ k < ∑ i, n i := by
  constructor
  · intro h
    simp only [divSum?, Nat.succ_eq_add_one, castLE, isSome_find_iff] at h
    obtain ⟨i, hi⟩ := h
    have : i.val + 1 + (m - i.val - 1) = m := by omega
    rw [← Fin.sum_congr' _ this, Fin.sum_univ_add]
    simp only [gt_iff_lt]
    exact Nat.lt_add_right _ hi
  · intro isLt
    have : m ≠ 0 := fun h => by subst h; simp at isLt
    refine Fin.isSome_find_iff.mpr ?_
    have hm : (m - 1) + 1 = m := by omega
    refine ⟨Fin.cast hm (Fin.last (m - 1)), ?_⟩
    simp only [coe_cast, val_last, Nat.succ_eq_add_one, Fin.castLE_of_eq hm,
        Fin.sum_congr' n hm, isLt]

def divSum {m : ℕ} {n : Fin m → ℕ} (k : Fin (∑ j, n j)) : Fin m :=
  (divSum? n k).get (divSum?_is_some_iff_lt_sum.mpr k.isLt)

theorem sum_le_of_divSum?_eq_some {m : ℕ} {n : Fin m → ℕ} {k : Fin (∑ j, n j)} {i : Fin m}
    (hi : divSum? n k = some i) : ∑ j : Fin i, n (castLE i.isLt.le j) ≤ k := by
  by_cases hi' : 0 = i.val
  · rw [← Fin.sum_congr' _ hi']
    simp only [Finset.univ_eq_empty, Finset.sum_empty, _root_.zero_le]
  · have : (i.val - 1) + 1 = i.val := by omega
    rw [← Fin.sum_congr' _ this]
    have := Fin.find_min (Option.mem_def.mp hi) (j := ⟨i.val - 1, by omega⟩) <| Fin.lt_def.mpr
      (by simp only; omega)
    exact not_lt.mp this

def modSum {m : ℕ} {n : Fin m → ℕ} (k : Fin (∑ j, n j)) : Fin (n (divSum k)) :=
  ⟨k - ∑ j, n (Fin.castLE (divSum k).isLt.le j), by
    have divSum_mem : divSum k ∈ divSum? n k := by
      simp only [divSum, divSum?, Option.mem_def, Option.some_get]
    have hk : k < ∑ j, n (Fin.castLE (divSum k).isLt j) := Fin.find_spec _ divSum_mem
    simp only [Fin.sum_univ_succAbove _ (Fin.last (divSum k)), succAbove_last] at hk
    rw [Nat.sub_lt_iff_lt_add' (sum_le_of_divSum?_eq_some divSum_mem)]
    rw [add_comm]
    exact hk⟩

/-- Equivalence between `(i : Fin m) × Fin (n i)` and `Fin (∑ i, n i)`.

Put this as the prime version since it already exists in mathlib (though with a different definition
that's not def'eq to this one). -/
def finSigmaFinEquiv' {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (∑ i, n i) :=
  .ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_sigma, Fintype.card_fin])
    (fun ⟨i, j⟩ => ⟨∑ k, n (Fin.castLE i.isLt.le k) + j, by
      have hi : i.val + 1 + (m - i.val - 1) = m := by omega
      conv_rhs => rw [← Fin.sum_congr' n hi, Fin.sum_univ_add, Fin.sum_univ_add, add_assoc]
      have hk {k : Fin i} : Fin.castLE i.isLt.le k =
            Fin.cast hi (Fin.castAdd (m - i - 1) (Fin.castAdd 1 k)) := by
        simp only [Fin.castLE, Fin.cast, Fin.coe_castAdd]
      simp_rw [hk, Nat.add_lt_add_iff_left, univ_unique, sum_singleton]
      exact Nat.lt_add_right _ (by simp only [Fin.cast, Fin.coe_castAdd, Fin.coe_natAdd,
          Fin.val_eq_zero, add_zero, Fin.is_lt])⟩)
    (fun k => ⟨k.divSum, k.modSum⟩)
    (by
      intro a
      induction n using Fin.consInduction with
      | h0 =>
        simp only [univ_eq_empty, sum_empty] at a
        exact Fin.elim0 a
      | h =>
        ext
        exact Nat.add_sub_cancel' (Fin.sum_le_of_divSum?_eq_some (Option.some_get _).symm))

@[simp]
theorem finSigmaFinEquiv'_apply {m : ℕ} {n : Fin m → ℕ} (k : (i : Fin m) × Fin (n i)) :
    (finSigmaFinEquiv' k : ℕ) = ∑ i : Fin k.1, n (Fin.castLE k.1.isLt.le i) + k.2 := rfl

theorem finSigmaFinEquiv'_pair {m : ℕ} {n : Fin m → ℕ} (i : Fin m) (k : Fin (n i)) :
    (finSigmaFinEquiv' ⟨i, k⟩ : ℕ) = ∑ j, n (Fin.castLE i.isLt.le j) + k := by
  simp only [finSigmaFinEquiv', Equiv.ofRightInverseOfCardLE_apply]

end FinSigmaFinEquiv

#check finSigmaFinEquiv

section Join

variable {n : ℕ} {a : Fin n → ℕ} {α : (i : Fin n) → (j : Fin (a i)) → Sort*}

def join (v : (i : Fin n) → (j : Fin (a i)) → α i j) (k : Fin (∑ i, a i)) : α k.divSum k.modSum :=
  v k.divSum k.modSum

variable {v : (i : Fin n) → (j : Fin (a i)) → α i j}

@[simp]
theorem join_zero {a : Fin 0 → ℕ} {α : (i : Fin 0) → (j : Fin (a i)) → Sort*}
    {v : (i : Fin 0) → (j : Fin (a i)) → α i j} :
    join v = fun i => Fin.elim0 i := by
  funext i; exact Fin.elim0 i

theorem join_addCases : True := sorry

theorem join_eq_addCases : True := sorry

theorem join_eq_join_list : True := sorry

end Join

end Fin
