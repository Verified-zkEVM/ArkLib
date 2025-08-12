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
import Mathlib.Tactic.FinCases
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

@[simp]
lemma append_zero_of_succ_left {u : Fin (m + 1) → α} {v : Fin n → α} :
    (append u v) 0 = u 0 := by
  simp [append, addCases, castLT]

@[simp]
lemma append_last_of_succ_right {u : Fin m → α} {v : Fin (n + 1) → α} :
    (append u v) (last (m + n)) = v (last n) := by
  simp [append, addCases, last]

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

section OptionEquivPrime

-- Experimenting with `Fin n` instead of `Fin (n + 1)`, but it seems we'd need to re-define every
-- existing `Fin` functions, which is bad

variable {n : ℕ}

def finSuccEquivNth' (i : Fin n) : Fin n ≃ Option (Fin (n - 1)) := by
  haveI : n = (n - 1) + 1 := (Nat.sub_eq_iff_eq_add (Nat.zero_lt_of_lt i.isLt)).mp rfl
  exact Equiv.trans (Equiv.cast (congrArg _ this)) (finSuccEquiv' (Fin.cast this i))

end OptionEquivPrime

end Fin
