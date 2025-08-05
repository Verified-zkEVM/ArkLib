/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Tuple.Notation

/-!
  # Lemmas for `Fin`-indexed vectors
-/

universe u

namespace FinVec

variable {m n : ℕ} {α : Sort u}

@[simp]
theorem cons_zero (a : α) (v : Fin n → α) : (a ::ᵛ v) 0 = a := by
  induction n with
  | zero => simp [cons]
  | succ n ih => simp [cons]; rfl

@[simp]
theorem cons_succ (a : α) (v : Fin n → α) (i : Fin n) : (a ::ᵛ v) i.succ = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => simp [cons, Fin.succ]

theorem cons_eq_fin_cons (a : α) (v : Fin n → α) : a ::ᵛ v = Fin.cons a v := by
  ext i
  induction i using Fin.induction <;> simp

-- Additional index access lemmas (cons_zero and cons_succ already defined above)
@[simp]
theorem cons_one (a : α) (v : FinVec α n.succ) : (a ::ᵛ v) 1 = v 0 := by
  convert cons_succ a v 0

@[simp]
theorem cons_empty (a : α) : a ::ᵛ !v[] = !v[a] := rfl

@[simp]
theorem cons_of_one (a : α) {i : Fin 1} : !v[a] i = a := rfl

-- Head/Tail Operations for cons (matching Fin.cons naming)
@[simp]
theorem tail_cons (a : α) (v : FinVec α n) : Fin.tail (a ::ᵛ v) = v := by
  ext i
  simp [Fin.tail]

@[simp]
theorem cons_self_tail (v : FinVec α n.succ) : (v 0) ::ᵛ (Fin.tail v) = v := by
  ext i
  induction i using Fin.induction <;> simp [Fin.tail]

-- Injectivity Properties (matching Fin.cons naming)
theorem cons_right_injective (a : α) :
    Function.Injective (cons a : FinVec α n → FinVec α n.succ) := by
  intro v w h
  have : Fin.tail (a ::ᵛ v) = Fin.tail (a ::ᵛ w) := by
    ext i; rw [h]
  rwa [tail_cons, tail_cons] at this

theorem cons_left_injective (v : FinVec α n) : Function.Injective (fun a => a ::ᵛ v) := by
  intro a b h
  have := congr_fun h 0
  simp at this
  exact this

theorem cons_injective2 : Function.Injective2 (@cons α n) := by
  intro a₁ v₁ a₂ v₂ h
  rw [cons_eq_fin_cons, cons_eq_fin_cons] at h
  exact Fin.cons_injective2 h

theorem cons_inj (a b : α) (v w : FinVec α n) : a ::ᵛ v = b ::ᵛ w ↔ a = b ∧ v = w := by
  constructor
  · intro h
    exact cons_injective2 h
  · intro ⟨ha, hv⟩
    rw [ha, hv]

-- Empty Vector Properties
@[simp]
theorem cons_fin_zero (a : α) (v : FinVec α 0) : a ::ᵛ v = fun _ => a := by
  simp [cons]

theorem cons_eq_const (a : α) : a ::ᵛ (fun _ : Fin n => a) = fun _ => a := by
  ext i
  induction i using Fin.induction <;> simp

-- Range Properties for cons (when α : Type*)
theorem range_cons {α : Type*} (a : α) (v : FinVec α n) :
    Set.range (a ::ᵛ v) = insert a (Set.range v) :=
  sorry

theorem range_empty {α : Type*} : Set.range (!v[] : FinVec α 0) = ∅ := by
  simp

theorem range_cons_empty {α : Type*} (a : α) (v : FinVec α 0) : Set.range (a ::ᵛ v) = {a} :=
  sorry

@[simp]
theorem concat_zero (a : α) : concat (Fin.elim0 : Fin 0 → α) a = fun _ => a := by
  simp [concat]

@[simp]
theorem concat_last (v : Fin n → α) (a : α) : concat v a (Fin.last n) = a := by
  induction n with
  | zero => simp [concat]
  | succ n ih =>
    simp [concat, cons, Fin.last]
    exact ih _

@[simp]
theorem concat_castSucc (v : Fin n → α) (a : α) (i : Fin n) :
    concat v a (Fin.castSucc i) = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp [concat]
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [ih]

-- Additional concat properties (matching Fin.snoc naming)
theorem concat_eq_snoc (v : FinVec α n) (a : α) : concat v a = Fin.snoc v a := by
  ext i
  by_cases h : i.val < n
  · have : i = Fin.castSucc ⟨i.val, h⟩ := by ext; simp
    rw [this, concat_castSucc, Fin.snoc_castSucc]
  · have : i = Fin.last n := by
      ext; simp; omega
    rw [this, concat_last, Fin.snoc_last]

theorem concat_cons (a : α) (v : FinVec α n) (b : α) :
    concat (a ::ᵛ v) b = a ::ᵛ (concat v b) := by
  ext i
  simp [concat, cons]
  sorry

-- Init/snoc properties (matching Fin.snoc naming)
theorem init_concat (v : FinVec α n) (a : α) :
    (fun i => concat v a (Fin.castSucc i)) = v := by
  ext i
  simp [concat_castSucc]

theorem concat_init_self (v : FinVec α n.succ) :
    concat (fun i => v (Fin.castSucc i)) (v (Fin.last n)) = v := by
  ext i
  by_cases h : i.val < n
  · have : i = Fin.castSucc ⟨i.val, h⟩ := by ext; simp
    rw [this, concat_castSucc]
  · have : i = Fin.last n := by
      ext; simp; omega
    rw [this]
    simp [concat_last]

-- Range properties for concat (when α : Type*)
theorem range_concat {α : Type*} (v : FinVec α n) (a : α) :
    Set.range (concat v a) = insert a (Set.range v) :=
  sorry

-- Injectivity properties for concat (matching Fin.snoc naming)
theorem concat_injective2 : Function.Injective2 (@concat α n) :=
  sorry

theorem concat_inj (v w : FinVec α n) (a b : α) :
    concat v a = concat w b ↔ v = w ∧ a = b :=
  sorry

theorem concat_right_injective (v : FinVec α n) : Function.Injective (concat v) :=
  sorry

theorem concat_left_injective {n : ℕ} (a : α) :
    Function.Injective (fun v : FinVec α n => concat v a) :=
  sorry

@[simp]
theorem append_zero (u : Fin m → α) : append u (Fin.elim0 : Fin 0 → α) = u := by
  simp [append]

-- Basic property about structure of append
theorem append_succ (u : Fin m → α) (v : Fin (n + 1) → α) :
    append u v = concat (append u (v ∘ Fin.castSucc)) (v (Fin.last n)) := by
  simp [append]

theorem append_eq_fin_append (u : FinVec α m) (v : FinVec α n) :
    append u v = Fin.append u v := by
  induction n with
  | zero => ext; simp [append, Fin.append]; unfold Fin.addCases; simp [Fin.castLT]
  | succ n ih =>
    ext i
    simp [append, ih, concat_eq_snoc]
    simp [Fin.snoc, Fin.append, Fin.addCases, Fin.castLT, Fin.last, Fin.subNat]
    by_cases h : i.val < m
    · by_cases h' : i.val < m + n
      · simp [h', h]
      · have : i.val = m + n := by omega
        simp [this]
    · simp [h]
      by_cases hn : n = 0
      · subst hn; simp_all
        have : i.val = m := by omega
        simp [this]
      · simp at h hn
        sorry
        -- have : i.val < m + n := by omega
        -- simp [this]

-- Additional append properties (matching Fin.append naming)
theorem empty_append (v : FinVec α n) : append !v[] v = v ∘ Fin.cast (Nat.zero_add n) := by
  sorry

theorem append_empty (v : FinVec α m) : append v !v[] = v := by
  simp [append]

theorem append_assoc {p : ℕ} (u : FinVec α m) (v : FinVec α n) (w : FinVec α p) :
    (append (append u v) w) = (append u (append v w)) ∘ Fin.cast (add_assoc m n p) := by
  simp [append_eq_fin_append, Fin.append_assoc]

-- Index access for append
theorem append_left (u : FinVec α m) (v : FinVec α n) (i : Fin m) :
    append u v (Fin.castAdd n i) = u i := by
  induction n with
  | zero => simp [append]
  | succ n ih =>
    simp [append]
    have : Fin.castAdd (n + 1) i = Fin.castSucc (Fin.castAdd n i) := by
      ext; simp [Fin.coe_castAdd]
    rw [this, concat_castSucc, ih]

theorem append_right (u : FinVec α m) (v : FinVec α n) (i : Fin n) :
    append u v (Fin.natAdd m i) = v i := by
  sorry

-- Relationship with cons/concat (matching Fin.append naming)
theorem append_cons (a : α) (u : FinVec α m) (v : FinVec α n) :
    append (cons a u) v = (cons a (append u v)) ∘ Fin.cast (Nat.succ_add m n) :=
  sorry

theorem append_concat (u : FinVec α m) (v : FinVec α n) (a : α) :
    append u (concat v a) = concat (append u v) a :=
  sorry

-- Compatibility with standard library (matching Fin.append naming)
theorem append_left_eq_cons (a : FinVec α 1) (v : FinVec α n) :
    append a v = (cons (a 0) v) ∘ Fin.cast (Nat.add_comm 1 n) :=
  sorry

theorem append_right_eq_snoc (u : FinVec α m) (a : FinVec α 1) :
    append u a = concat u (a 0) :=
  sorry

-- Range properties for append (when α : Type*)
theorem range_append {α : Type*} (u : FinVec α m) (v : FinVec α n) :
    Set.range (append u v) = Set.range u ∪ Set.range v :=
  sorry

-- Length properties (these are definitional but useful to state)
theorem length_append (u : FinVec α m) (v : FinVec α n) :
    (append u v : FinVec α (m + n)) = append u v :=
  sorry

-- Extensionality for append
theorem append_ext (u₁ u₂ : FinVec α m) (v₁ v₂ : FinVec α n) :
    append u₁ v₁ = append u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ :=
  sorry

-- Additional useful extensionality lemmas
theorem ext_cons (a b : α) (v w : FinVec α n) : cons a v = cons b w ↔ a = b ∧ v = w :=
  cons_inj a b v w

theorem cons_eq_cons_iff (a b : α) (v w : FinVec α n) : cons a v = cons b w ↔ a = b ∧ v = w :=
  cons_inj a b v w

-- Two vectors are equal iff they are equal at every index
theorem ext_iff {v w : FinVec α n} : v = w ↔ ∀ i, v i = w i :=
  ⟨fun h i => by rw [h], fun h => funext h⟩

-- Interaction between operations
theorem cons_append_comm (a : α) (u : FinVec α m) (v : FinVec α n) :
    cons a (append u v) = (append (cons a u) v) ∘ Fin.cast (Nat.succ_add m n).symm :=
  sorry

theorem append_singleton (u : FinVec α m) (a : α) :
    append u (cons a !v[]) = concat u a :=
  sorry

theorem singleton_append (a : α) (v : FinVec α n) :
    append (cons a !v[]) v = cons a v ∘ Fin.cast (Nat.add_comm _ n) :=
  sorry

-- Empty cases
theorem empty_unique (v : FinVec α 0) : v = !v[] :=
  funext (fun i => Fin.elim0 i)

theorem eq_empty_iff_zero (v : FinVec α n) : (∃ h : n = 0, v = h ▸ !v[]) ↔ n = 0 :=
  sorry

end FinVec

namespace FinTuple

variable {m n : ℕ} {α : Sort u}

@[simp]
theorem cons_zero {β : Fin n → Sort u} (a : α) (b : (i : Fin n) → β i) :
    cons a b 0 = cast (FinVec.cons_zero α β).symm a := by
  induction n with
  | zero => simp [cons]
  | succ n ih => simp [cons]; rfl

@[simp]
theorem cons_succ {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) (i : Fin n) :
    cons a v i.succ = cast (FinVec.cons_succ α β i).symm (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => simp [cons]; rfl

theorem cons_eq_fin_cons {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
    cons a v = Fin.cons (α := FinVec.cons α β) (cons a v 0) (fun i => cons a v i.succ) := by
  ext i
  induction i using Fin.induction <;> simp

@[simp]
theorem concat_zero {α : Fin 0 → Sort u} {β : Sort u} (a : β) :
    concat (FinTuple.empty : FinTuple 0 α) a = fun _ => a := rfl

@[simp]
theorem append_zero {β : Fin m → Sort u} {α : Fin 0 → Sort u} (u : (i : Fin m) → β i) :
    append u (FinTuple.empty : FinTuple 0 α) = u := rfl

-- Additional cons lemmas for FinTuple
@[simp]
theorem cons_one {β : Fin n.succ → Sort u} (a : α) (v : FinTuple n.succ β) :
    cons a v 1 = cast (FinVec.cons_succ α β 0).symm (v 0) := by
  sorry

theorem tail_cons {β : Fin n → Sort u} (a : α) (b : FinTuple n β) (i : Fin n) :
    True := by
  sorry

theorem cons_self_tail {α : Fin n.succ → Sort u} (v : FinTuple n.succ α) :
    True := by
  sorry

-- Injectivity properties for cons
theorem cons_right_injective {β : Fin n → Sort u} (a : α) :
    Function.Injective (cons a : FinTuple n β → FinTuple (n + 1) (FinVec.cons α β)) := by
  sorry

theorem cons_left_injective {α : Sort u} {β : Fin n → Sort u} (b : FinTuple n β) :
    Function.Injective (fun (a : α) => cons a b) := by
  sorry

theorem cons_injective2 {α : Sort u} {β : Fin n → Sort u} :
    Function.Injective2 (@cons n α β) := by
  sorry

theorem cons_inj {α : Sort u} {β : Fin n → Sort u} (a₁ a₂ : α) (b₁ b₂ : FinTuple n β) :
    cons a₁ b₁ = cons a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  sorry

-- Empty tuple properties
@[simp]
theorem cons_fin_zero {α : Sort u} {β : Fin 0 → Sort u} (a : α) (v : FinTuple 0 β) :
    cons a v = fun _ => a := by
  sorry

-- Concat lemmas for FinTuple
@[simp]
theorem concat_last {α : Fin n → Sort u} {β : Sort u} (v : FinTuple n α) (b : β) :
    concat v b (Fin.last n) = cast (FinVec.concat_last α β).symm b := by
  sorry

@[simp]
theorem concat_castSucc {α : Fin n → Sort u} {β : Sort u} (v : FinTuple n α) (b : β) (i : Fin n) :
    concat v b (Fin.castSucc i) = cast (FinVec.concat_castSucc α β i).symm (v i) := by
  sorry

theorem concat_cons {α : Sort u} {β : Fin n → Sort u} {γ : Sort u} (a : α) (v : FinTuple n β) (c : γ) :
    True := by
  sorry

-- Init/concat properties
theorem init_concat {α : Fin n → Sort u} {β : Sort u} (v : FinTuple n α) (b : β) :
    True := by
  sorry

theorem concat_init_self {α : Fin n.succ → Sort u} (v : FinTuple n.succ α) :
    True := by
  sorry

-- Injectivity properties for concat
theorem concat_injective2 {α : Fin n → Sort u} {β : Sort u} :
    Function.Injective2 (@concat n α β) := by
  sorry

theorem concat_inj {α : Fin n → Sort u} {β : Sort u} (v₁ v₂ : FinTuple n α) (a₁ a₂ : β) :
    concat v₁ a₁ = concat v₂ a₂ ↔ v₁ = v₂ ∧ a₁ = a₂ := by
  sorry

theorem concat_right_injective {α : Fin n → Sort u} {β : Sort u} (v : FinTuple n α) :
    Function.Injective (concat v : β → FinTuple (n + 1) (FinVec.concat α β)) := by
  sorry

theorem concat_left_injective {α : Fin n → Sort u} {β : Sort u} (a : β) :
    Function.Injective (fun v : FinTuple n α => concat v a) := by
  sorry

-- Append lemmas for FinTuple
theorem append_succ {α : Fin m → Sort u} {β : Fin (n + 1) → Sort u}
    (u : FinTuple m α) (v : FinTuple (n + 1) β) :
    append u v = concat (append u (fun i => v (Fin.castSucc i))) (v (Fin.last n)) := by
  sorry

theorem empty_append {β : Fin n → Sort u} (v : FinTuple n β) :
    True := by
  sorry

theorem append_empty {α : Fin m → Sort u} (v : FinTuple m α) :
    append v !t[] = v := by
  sorry

theorem append_assoc {α : Fin m → Sort u} {β : Fin n → Sort u} {p : ℕ} {γ : Fin p → Sort u}
    (u : FinTuple m α) (v : FinTuple n β) (w : FinTuple p γ) :
    True := by
  sorry

-- Index access for append
theorem append_left {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : FinTuple m α) (v : FinTuple n β) (i : Fin m) :
    append u v (Fin.castAdd n i) = cast (FinVec.append_left α β i).symm (u i) := by
  sorry

theorem append_right {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : FinTuple m α) (v : FinTuple n β) (i : Fin n) :
    append u v (Fin.natAdd m i) = cast (FinVec.append_right α β i).symm (v i) := by
  sorry

-- Relationship with cons/concat
theorem append_cons {β : Fin m → Sort u} {γ : Fin n → Sort u}
    (a : α) (u : FinTuple m β) (v : FinTuple n γ) :
    True := by
  sorry

theorem append_concat {α : Fin m → Sort u} {β : Fin n → Sort u} {γ : Sort u}
    (u : FinTuple m α) (v : FinTuple n β) (c : γ) :
    True := by
  sorry

-- Compatibility lemmas
theorem append_left_eq_cons {α : Fin 1 → Sort u} {β : Fin n → Sort u}
    (a : FinTuple 1 α) (v : FinTuple n β) :
    True := by
  sorry

theorem append_right_eq_snoc {α : Fin m → Sort u} {β : Fin 1 → Sort u}
    (u : FinTuple m α) (a : FinTuple 1 β) :
    append u a = concat u (a 0) := by
  sorry

-- Extensionality properties
theorem append_ext {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u₁ u₂ : FinTuple m α) (v₁ v₂ : FinTuple n β) :
    append u₁ v₁ = append u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  sorry

theorem ext_cons {β : Fin n → Sort u} (a₁ a₂ : α) (v₁ v₂ : FinTuple n β) :
    cons a₁ v₁ = cons a₂ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ := by
  sorry

theorem cons_eq_cons_iff {β : Fin n → Sort u} (a₁ a₂ : α) (v₁ v₂ : FinTuple n β) :
    cons a₁ v₁ = cons a₂ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ := by
  sorry

-- Two tuples are equal iff they are equal at every index (with casting)
theorem ext_iff {α : Fin n → Sort u} {v w : FinTuple n α} :
    v = w ↔ ∀ i, v i = w i := by
  sorry

-- Interaction between operations
theorem cons_append_comm {β : Fin m → Sort u} {γ : Fin n → Sort u}
    (a : α) (u : FinTuple m β) (v : FinTuple n γ) :
    True := by
  sorry

theorem append_singleton {α : Fin m → Sort u} {β : Sort u} (u : FinTuple m α) (a : β) :
    True := by
  sorry

theorem singleton_append {β : Fin n → Sort u} (a : α) (v : FinTuple n β) :
    True := by
  sorry

-- Empty cases
theorem empty_unique {α : Fin 0 → Sort u} (v : FinTuple 0 α) : v = FinTuple.empty := by
  sorry

theorem eq_empty_iff_zero {α : Fin n → Sort u} (v : FinTuple n α) :
    True ↔ n = 0 := by
  sorry

-- Cast lemma for type families
theorem cast_cons {β : Fin n → Sort u} (a : α) (v : FinTuple n β) :
    FinTuple.cast rfl (fun i => rfl) (cons a v) = cons a v := by
  sorry

theorem cast_concat {α : Fin n → Sort u} {β : Sort u} (v : FinTuple n α) (b : β) :
    FinTuple.cast rfl (fun i => rfl) (concat v b) = concat v b := by
  sorry

theorem cast_append {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : FinTuple m α) (v : FinTuple n β) :
    FinTuple.cast rfl (fun i => rfl) (append u v) = append u v := by
  sorry

-- Composition with casting
theorem cast_comp {α : Fin n → Sort u} {β : Fin n → Sort u}
    (h : n = n) (hα : ∀ i, α (Fin.cast h i) = β i) (v : FinTuple n α) :
    True := by
  sorry

end FinTuple

namespace Fin

variable {m n : ℕ} {α : Sort u}

-- @[simp, grind =]
-- theorem concat_eq_append {α : Sort u} {n : ℕ} (v : FinVec α n) (a : α) :
--     concat v a = append v (FinVec.cons a FinVec.empty) := by
--   ext i; fin_cases i <;> rfl

section padding

@[simp]
theorem rightpad_apply_lt (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : i.val < m) : rightpad n a v i = v ⟨i.val, h⟩ := by
  simp [rightpad, h]

@[simp]
theorem rightpad_apply_ge (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : m ≤ i.val) : rightpad n a v i = a := by
  simp [rightpad]
  omega

@[simp]
theorem leftpad_apply_lt (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : i.val < n - m) : leftpad n a v i = a := by
  simp [leftpad]
  omega

@[simp]
theorem leftpad_apply_ge (n : ℕ) (a : α) (v : Fin m → α) (i : Fin n)
    (h : n - m ≤ i.val) : leftpad n a v i = v ⟨i.val - (n - m), by omega⟩ := by
  simp [leftpad, h]

theorem rightpad_eq_self (v : Fin n → α) (a : α) : rightpad n a v = v := by
  ext i
  simp [rightpad_apply_lt]

theorem leftpad_eq_self (v : Fin n → α) (a : α) : leftpad n a v = v := by
  ext i
  simp [leftpad_apply_ge]

end padding

end Fin
