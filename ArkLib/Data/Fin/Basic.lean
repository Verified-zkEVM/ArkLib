/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fin.Tuple.Take
import Batteries.Data.Fin.Fold
import ArkLib.Data.Classes.DCast

/-!
  # Lemmas on `Fin` and `Fin`-indexed tuples

  We define operations on `Fin` and `Fin`-indexed tuples that are needed for ArkLib.
-/

universe u v w

-- We may need special naming for these objects `FinTuple` and `FinVec`
-- in order to consolidate a pattern that we find in this development
-- i.e. `ProtocolSpec` is a `FinVec`, `(Full)Transcript` is a `FinTuple`, and so on

/-- A `FinVec` is a `FinTuple` with a constant type family, i.e. `Fin n → α`. -/
abbrev FinVec (α : Sort u) (n : ℕ) : Sort _ := Fin n → α

def IndexedByFinVec (α : Sort u) (n : ℕ) := (β : FinVec α n) → Type v

/-- A `FinTuple` of size `n` and type family `α` is a dependent function `(i : Fin n) → α i`. -/
abbrev FinTuple (n : ℕ) (α : FinVec (Sort u) n) : Sort _ := (i : Fin n) → α i

/-- Cast a `FinTuple` across an equality `n' = n` and a family of equalities
  `∀ i, α (Fin.cast h i) = α' i`.

  Since this is a pull-back, we state the equalities in the other direction (i.e. `n' = n` instead
  of `n = n'`) -/
def FinTuple.cast {n n' : ℕ} {α : Fin n → Sort u} {α' : Fin n' → Sort u}
    (h : n' = n) (hα : ∀ i, α (Fin.cast h i) = α' i) (v : FinTuple n α) :
      FinTuple n' α' :=
  fun i => _root_.cast (hα i) (v (Fin.cast h i))

/-- Version of `funext_iff` for dependent functions `f : (x : α) → β x` and
`g : (x : α') → β' x`. -/
theorem funext_heq_iff {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v}
    {f : (x : α) → β x} {g : (x : α') → β' x} (ha : α = α') (hb : ∀ x, β x = β' (cast ha x)) :
      HEq f g ↔ ∀ x, HEq (f x) (g (cast ha x)) := by
  subst ha
  have : β = β' := funext hb
  subst this
  simp [funext_iff]

alias ⟨_, funext_heq⟩ := funext_heq_iff

theorem funext₂_iff {α : Sort u} {β : α → Sort v} {γ : (a : α) → β a → Sort w}
    {f g : (a : α) → (b : β a) → γ a b} : f = g ↔ ∀ a b, f a b = g a b := by
  simp [funext_iff]

/-- Version of `funext₂_iff` for heterogeneous equality. -/
theorem funext₂_heq_iff {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v}
    {γ : (a : α) → β a → Sort w} {γ' : (a : α') → β' a → Sort w}
    {f : (a : α) → (b : β a) → γ a b} {g : (a : α') → (b : β' a) → γ' a b}
    (ha : α = α') (hb : ∀ a, β a = β' (cast ha a))
    (hc : ∀ a b, γ a b = γ' (cast ha a) (cast (hb a) b)) :
      HEq f g ↔ ∀ a b, HEq (f a b) (g (cast ha a) (cast (hb a) b)) := by
  subst ha
  have : β = β' := funext hb
  subst this
  have : γ = γ' := funext₂ hc
  subst this
  simp [funext₂_iff]

alias ⟨_, funext₂_heq⟩ := funext₂_heq_iff

namespace Fin

open Function

/-- Version of `Fin.heq_fun_iff` for dependent functions `f : (i : Fin k) → α i`. -/
protected theorem heq_fun_iff' {k l : ℕ} {α : Fin k → Sort u} {β : Fin l → Sort u} (h : k = l)
    (h' : ∀ i : Fin k, (α i) = (β (Fin.cast h i))) {f : (i : Fin k) → α i} {g : (j : Fin l) → β j} :
    HEq f g ↔ ∀ i : Fin k, HEq (f i) (g (Fin.cast h i)) := by
  subst h
  simp only [cast_eq_self]
  exact funext_heq_iff rfl h'

/-- Casting a `Fin` doesn't change its value. -/
@[simp]
theorem cast_val {m n : ℕ} (h : m = n) (a : Fin m) : (Fin.cast h a).val = a.val := by
  subst h; simp

@[simp]
theorem induction_one {motive : Fin 2 → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin 1, motive i.castSucc → motive i.succ} :
      induction (motive := motive) zero succ (last 1) = succ 0 zero := rfl

/-- Alternate version of `Fin.induction_one` that uses `1 : Fin 2` instead of `last 1`. -/
@[simp]
theorem induction_one' {motive : Fin 2 → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin 1, motive i.castSucc → motive i.succ} :
      induction (motive := motive) zero succ (1 : Fin 2) = succ 0 zero := rfl

@[simp]
theorem induction_two {motive : Fin 3 → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin 2, motive i.castSucc → motive i.succ} :
      induction (motive := motive) zero succ (last 2) = succ 1 (succ 0 zero) := rfl

/-- Alternate version of `Fin.induction_two` that uses `2 : Fin 3` instead of `last 2`. -/
@[simp]
theorem induction_two' {motive : Fin 3 → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin 2, motive i.castSucc → motive i.succ} :
      induction (motive := motive) zero succ (2 : Fin 3) = succ 1 (succ 0 zero) := by rfl

/-- Heterogeneous equality on `Fin.induction` -/
theorem induction_heq {n n' : ℕ} {motive : Fin (n + 1) → Sort u} {motive' : Fin (n' + 1) → Sort u}
    {zero : motive 0} {zero' : motive' 0}
    {succ : ∀ i : Fin n, motive i.castSucc → motive i.succ}
    {succ' : ∀ i : Fin n', motive' i.castSucc → motive' i.succ}
    {i : Fin (n + 1)} {i' : Fin (n' + 1)}
    (hn : n = n') (hmotive : HEq motive motive') (hzero : HEq zero zero')
    (hsucc : HEq succ succ') (hi : HEq i i') :
      HEq (induction (motive := motive) zero succ i)
        (induction (motive := motive') zero' succ' i') := by
  subst hn; subst hmotive; subst hzero; subst hsucc; subst hi; rfl

theorem induction_init {n : ℕ} {motive : Fin (n + 2) → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin (n + 1), motive i.castSucc → motive i.succ} {i : Fin (n + 1)} :
      induction (motive := motive) zero succ i.castSucc =
        induction (motive := Fin.init motive) zero (fun j x => succ j.castSucc x) i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i _ =>
    have : i.succ.castSucc = i.castSucc.succ := rfl
    rw! (castMode := .all) [this]
    simp only [induction_succ]
    congr

theorem induction_tail {n : ℕ} {motive : Fin (n + 2) → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin (n + 1), motive i.castSucc → motive i.succ} {i : Fin (n + 1)} :
      induction (motive := motive) zero succ i.succ =
        induction (motive := Fin.tail motive) (succ 0 zero) (fun j x => succ j.succ x) i := by
  induction i using Fin.induction with
  | zero => simp only [succ_zero_eq_one, induction_zero]; rfl
  | succ i ih =>
    simp
    have : i.succ.castSucc = i.castSucc.succ := rfl
    aesop

/-- `Fin.induction` on `m + n` for `i ≤ m` steps is equivalent to `Fin.induction` on `m` for `i`
  steps. -/
theorem induction_append_left {m n : ℕ} {motive : Fin (m + n + 1) → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin (m + n), motive i.castSucc → motive i.succ} {i : Fin (m + 1)} :
      induction (motive := motive) zero succ ⟨i, by omega⟩ =
        @induction m (fun j => motive ⟨j, by omega⟩) zero (fun j x => succ ⟨j, by omega⟩ x) i := by
  induction i using Fin.induction with
  | zero => simp [induction_zero]; rfl
  | succ i ih =>
    simp at ih ⊢
    have : (⟨i.1 + 1, by omega⟩ : Fin (m + n + 1)) = (⟨i, by omega⟩ : Fin (m + n)).succ := rfl
    rw! (castMode := .all) [this, induction_succ, ih]

/-- `Fin.induction` on `m + n` for `m + i` steps is equivalent to `Fin.induction` on `n` on `i`
  steps on the result of `Fin.induction` on `m`. -/
theorem induction_append_right {m n : ℕ} {motive : Fin (m + n + 1) → Sort*} {zero : motive 0}
  {succ : ∀ i : Fin (m + n), motive i.castSucc → motive i.succ} {i : Fin (n + 1)} :
    induction zero succ (i.natAdd m) =
      @induction n (fun i => motive (i.natAdd m))
        (@induction m (fun j => motive (Fin.cast (by omega) (j.castAdd n)))
          zero (fun j x => succ (j.castAdd n) x) (last m))
        (fun i x => succ (i.natAdd m) x) i := by
  induction i using Fin.induction with
  | zero =>
    simp [castAdd, castLE, last, natAdd, HMod.hMod, Mod.mod, Nat.mod]
    rw [induction_append_left (i := ⟨m, by omega⟩)]
    rfl
  | succ i ih =>
    simp [← ih]
    have : natAdd m i.succ = (natAdd m i).succ := rfl
    rw! (castMode := .all) [this, induction_succ]
    rfl

/-- `Fin.insertNth 0` is equivalent to `Fin.cases`. -/
theorem insertNth_zero_eq_cases {n : ℕ} {α : Fin (n + 1) → Sort u} :
    insertNth 0 = cases (motive := α) := by
  funext x p j
  induction j using Fin.cases with
  | zero => simp only [insertNth, succAboveCases, ↓reduceDIte, cases_zero]
  | succ j =>
    simp only [insertNth, succAboveCases, not_lt_zero, ↓reduceDIte, cases_succ, Fin.succ_ne_zero]
    congr

section Append

variable {m n : ℕ} {α β : Sort*}

theorem append_comp {a : Fin m → α} {b : Fin n → α} (f : α → β) :
    append (f ∘ a) (f ∘ b) = f ∘ append a b := by
  funext i
  simp only [append, addCases, comp_apply, eq_rec_constant]
  by_cases h : i < m <;> simp only [h, ↓reduceDIte]

theorem append_comp' {a : Fin m → α} {b : Fin n → α} (f : α → β)
    (i : Fin (m + n)) : append (f ∘ a) (f ∘ b) i = f (append a b i) := by
  simp only [append_comp, comp_apply]

theorem addCases_left' {motive : Fin (m + n) → Sort*}
    {left : (i : Fin m) → motive (castAdd n i)} {right : (j : Fin n) → motive (natAdd m j)}
    {i : Fin m} (j : Fin (m + n)) (h : j = castAdd n i) :
      addCases (motive := motive) left right j = h ▸ (left i) := by
  subst h
  simp only [addCases_left]

theorem addCases_right' {motive : Fin (m + n) → Sort*}
    {left : (i : Fin m) → motive (castAdd n i)} {right : (j : Fin n) → motive (natAdd m j)}
    {i : Fin n} (j : Fin (m + n)) (h : j = natAdd m i) :
      addCases (motive := motive) left right j = h ▸ (right i) := by
  subst h
  simp only [addCases_right]

-- theorem append_left' {u : Fin m → α} {v : Fin n → α} {i : Fin m}
--     (j : Fin (m + n)) (h : j = castAdd n i) : append u v j = u i := by
--   subst h
  -- simp only [append_left]

theorem append_right' {u : Fin m → α} {v : Fin n → α} {i : Fin n}
    (j : Fin (m + n)) (h : j = natAdd m i) : append u v j = v i := by
  subst h
  simp only [append_right]

theorem append_left_injective (b : Fin n → α) : Function.Injective (@Fin.append m n α · b) := by
  intro a a' h
  simp only at h
  ext i
  have : append a b (castAdd n i) = append a' b (castAdd n i) := by rw [h]
  simp only [append_left] at this
  exact this

theorem append_right_injective (a : Fin m → α) : Function.Injective (@Fin.append m n α a) := by
  intro b b' h
  ext i
  have : append a b (natAdd m i) = append a b' (natAdd m i) := by rw [h]
  simp only [append_right] at this
  exact this

end Append

/-- Version of `Fin.addCases` that splits the motive into two dependent vectors `α` and `β`, and
  the return type is `Fin.append α β`. -/
def addCases' {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u} (left : (i : Fin m) → α i)
    (right : (j : Fin n) → β j) (i : Fin (m + n)) : append α β i := by
  refine addCases ?_ ?_ i <;> intro j <;> simp
  · exact left j
  · exact right j

@[simp]
theorem addCases'_left {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (left : (i : Fin m) → α i) (right : (j : Fin n) → β j) (i : Fin m) :
      addCases' left right (Fin.castAdd n i) = (Fin.append_left α β i) ▸ (left i) := by
  simp [addCases', cast_eq_iff_heq]

@[simp]
theorem addCases'_right {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (left : (i : Fin m) → α i) (right : (j : Fin n) → β j) (i : Fin n) :
      addCases' left right (Fin.natAdd m i) = (Fin.append_right α β i) ▸ (right i) := by
  simp [addCases', cast_eq_iff_heq]

-- theorem addCases'_heq_addCases {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
--     (left : (i : Fin m) → α i) (right : (j : Fin n) → β j) :
--       HEq (addCases' left right) = addCases (motive := append α β) left right := by
--   ext i
--   refine addCasesFn_iff.mpr (fun i => ?_)
--   simp [addCases']

section Sum

-- Append multiple `Fin` tuples?

def castSum (l : List ℕ) {n : ℕ} (h : n ∈ l) : Fin n → Fin l.sum := fun i =>
  match l with
  | [] => by contradiction
  | n' :: l' => by
    simp only [List.sum_cons]
    by_cases hi : n = n'
    · exact castAdd l'.sum (Fin.cast hi i)
    · exact natAdd n' (castSum l' (List.mem_of_ne_of_mem hi h) i)

theorem castSum_castLT {l' : List ℕ} {i : ℕ} (j : Fin i) :
    castSum (i :: l') (by simp) j =
      castLT j (Nat.lt_of_lt_of_le j.isLt (List.le_sum_of_mem (by simp))) := by
  simp [castSum, castAdd, castLE, castLT]

theorem castSum_castAdd {n m : ℕ} (i : Fin n) : castSum [n, m] (by simp) i = castAdd m i := by
  simp [castSum]

def sumCases {l : List ℕ} {motive : Fin l.sum → Sort*}
    (cases : ∀ (n : ℕ) (h : n ∈ l) (i : Fin n), motive (castSum l h i))
    (i : Fin l.sum) : motive i := match l with
  | [] => by simp only [List.sum_nil] at i; exact elim0 i
  | n' :: l' => by
    simp only [List.sum_cons] at i
    by_cases hi : i < n'
    · convert cases n' (by simp) ⟨i.val, hi⟩
      simp [castSum]
    · have hj' : i.val - n' < l'.sum := by sorry
      sorry
      -- refine sumCases (l := l') (motive := motive ∘ natAdd i') ?_ ⟨j.val - i', hj'⟩

end Sum

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

open Finset in
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

-- theorem join_one {a : Fin 1 → ℕ} {α : (i : Fin 1) → (j : Fin (a i)) → Sort*}
--     {v : (i : Fin 1) → (j : Fin (a i)) → α i j} :
--     join v = v 0 := by
--   funext i; exact Fin.elim0 i

theorem join_addCases : True := sorry

theorem join_eq_addCases : True := sorry

theorem join_eq_join_list : True := sorry

end Join

section OptionEquivPrime

-- Experimenting with `Fin n` instead of `Fin (n + 1)`, but it seems we'd need to re-define every
-- existing `Fin` functions, which is bad

variable {n : ℕ}

def finSuccEquivNth' (i : Fin n) : Fin n ≃ Option (Fin (n - 1)) := by
  haveI : n = (n - 1) + 1 := (Nat.sub_eq_iff_eq_add (Nat.zero_lt_of_lt i.isLt)).mp rfl
  exact Equiv.trans (Equiv.cast (congrArg _ this)) (finSuccEquiv' (Fin.cast this i))

end OptionEquivPrime

section Fold

/-- Congruence for `dfoldl` -/
theorem dfoldl_congr {n : ℕ}
    {α α' : Fin (n + 1) → Type u}
    {f : (i : Fin n) → α i.castSucc → α i.succ}
    {f' : (i : Fin n) → α' i.castSucc → α' i.succ}
    {init : α 0} {init' : α' 0}
    (hα : ∀ i, α i = α' i)
    (hf : ∀ i a, f i a = (cast (hα _).symm (f' i (cast (hα _) a))))
    (hinit : init = cast (hα 0).symm init') :
      dfoldl n α f init = cast (hα (last n)).symm (dfoldl n α' f' init') := by
  have hα' : α = α' := funext hα
  subst hα'
  simp_all only [cast_eq]
  have hf' : f = f' := funext₂ hf
  subst hf'
  subst hinit
  rfl

/-- Congruence for `dfoldl` whose type vectors are indexed by `ι` and have a `DCast` instance

Note that we put `cast` (instead of `dcast`) in the theorem statement for easier matching,
but `dcast` inside the hypotheses for downstream proving. -/
theorem dfoldl_congr_dcast {n : ℕ}
    {ι : Type v} {α α' : Fin (n + 1) → ι} {β : ι → Type u} [DCast ι β]
    {f : (i : Fin n) → β (α i.castSucc) → β (α i.succ)}
    {f' : (i : Fin n) → β (α' i.castSucc) → β (α' i.succ)}
    {init : β (α 0)} {init' : β (α' 0)}
    (hα : ∀ i, α i = α' i)
    (hf : ∀ i a, f i a = (dcast (hα _).symm (f' i (dcast (hα _) a))))
    (hinit : init = dcast (hα 0).symm init') :
      dfoldl n (fun i => β (α i)) f init =
        cast (by have := funext hα; subst this; simp) (dfoldl n (fun i => β (α' i)) f' init') := by
  have hα' : α = α' := funext hα
  cases hα'
  simp_all only [dcast_eq, cast_eq]
  simp at hf
  have hf' : f = f' := funext₂ hf
  cases hf'
  cases hinit
  rfl

/-- Distribute `dcast` inside `dfoldl`. Requires the minimal condition of `α = α'` -/
theorem dfoldl_dcast {ι : Type v} {β : ι → Type u} [DCast ι β]
    {n : ℕ} {α α' : Fin (n + 1) → ι}
    {f : (i : Fin n) → β (α i.castSucc) → β (α i.succ)} {init : β (α 0)}
    (hα : ∀ i, α i = α' i) :
      dcast (hα (last n)) (dfoldl n (fun i => β (α i)) f init) =
        dfoldl n (fun i => β (α' i))
          (fun i a => dcast (hα _) (f i (dcast (hα _).symm a))) (dcast (hα 0) init) := by
  have hα' : α = α' := funext hα
  subst hα'
  simp_all only [dcast_eq]

-- theorem dfoldl_dcast₂ {n : ℕ}
--     {ι₁ : Type v} {ι₂ : ι₁ → Type w} {α α' : Fin (n + 1) → (i : ι₁) → ι₂ i}
--     {β : (i : ι₁) → ι₂ i → Type u}
--     {f : (i : Fin n) → β (α i.castSucc) → β (α i.succ) (ι₂ (α i.succ))}
--     {f' : (i : Fin n) → β (α' i.castSucc) → β (α' i.succ)}
--     {init : β (α 0)} {init' : β (α' 0)}
--     (hα : ∀ i, α i = α' i)
--     (hf : ∀ i a, f i a = (cast (congrArg β (hα _)).symm (f' i (cast (congrArg β (hα _)) a))))
--     (hinit : init = cast (congrArg β (hα 0).symm) init') :
--       dfoldl n (β ∘ α) f init =
--         cast (congrArg β (hα (last n)).symm) (dfoldl n (β ∘ α') f' init') := by
--   have hα' : α = α' := funext hα
--   subst hα'
--   simp_all
--   have hf' : f = f' := funext₂ hf
--   subst hf'
--   subst hinit
--   rfl

end Fold

end Fin
