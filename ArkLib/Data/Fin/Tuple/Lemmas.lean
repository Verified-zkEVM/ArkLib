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

-- lemma Fin.match_zero {n : ℕ} {α : Sort u} {β : Fin n → Sort u} (a : α) (b : (i : Fin n) → β i) :
--     (fun i : Fin (n + 1) => match i with
--       | ⟨0, _⟩ => a
--       | ⟨i + 1, h⟩ => b ⟨i, Nat.succ_lt_succ_iff.mp h⟩  (fun i : Fin (n + 1) => match i with
--         | ⟨0, _⟩ => α
--         | ⟨i + 1, h⟩ => β i)) 0 = a := rfl

namespace FinVec

variable {m n : ℕ} {α : Sort u}

instance : Unique (FinVec α 0) where
  default := !v[]
  uniq v := by
    ext i
    exact Fin.elim0 i

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
    Set.range (a ::ᵛ v) = insert a (Set.range v) := by
  rw [cons_eq_fin_cons]
  simp

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
theorem concat_eq_fin_snoc (v : FinVec α n) (a : α) : concat v a = Fin.snoc v a := by
  ext i
  by_cases h : i.val < n
  · have : i = Fin.castSucc ⟨i.val, h⟩ := by ext; simp
    rw [this, concat_castSucc, Fin.snoc_castSucc]
  · have : i = Fin.last n := by
      ext; simp; omega
    rw [this, concat_last, Fin.snoc_last]

theorem concat_cons_eq_cons_concat (a : α) (v : FinVec α n) (b : α) :
    concat (a ::ᵛ v) b = a ::ᵛ (concat v b) := by
  simp only [concat_eq_fin_snoc, cons_eq_fin_cons]
  exact Eq.symm (Fin.cons_snoc_eq_snoc_cons a v b)

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
    Set.range (concat v a) = insert a (Set.range v) := by
  rw [concat_eq_fin_snoc]
  simp

-- Injectivity properties for concat (matching Fin.snoc naming)
theorem concat_injective2 : Function.Injective2 (@concat α n) := by
  intro v w a b h
  rw [concat_eq_fin_snoc, concat_eq_fin_snoc] at h
  simp at h
  exact h

theorem concat_inj (v w : FinVec α n) (a b : α) :
    concat v a = concat w b ↔ v = w ∧ a = b := by
  rw [concat_eq_fin_snoc, concat_eq_fin_snoc]; simp

theorem concat_right_injective (v : FinVec α n) : Function.Injective (concat v) := by
  intro x y h
  rw [concat_eq_fin_snoc, concat_eq_fin_snoc] at h
  simp at h
  exact h

theorem concat_left_injective {n : ℕ} (a : α) :
    Function.Injective (fun v : FinVec α n => concat v a) := by
  intro x y h
  simp_rw [concat_eq_fin_snoc] at h
  simpa using h

@[simp]
theorem zero_append {u : FinVec α 0} (v : FinVec α n) :
    append u v = v ∘ Fin.cast (Nat.zero_add n) := by
  induction n with
  | zero => simp [append, Unique.uniq]
  | succ n ih =>
    simp [append, ih, concat_eq_fin_snoc]
    ext i
    simp [Fin.castSucc, Fin.last, Fin.snoc]
    by_cases h : i.val < n
    · simp [h]; rfl
    · have : i.val = n := by omega
      simp [this, Fin.cast]

@[simp]
theorem append_zero (u : Fin m → α) : append u (Fin.elim0 : Fin 0 → α) = u := rfl

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
    simp [append, ih, concat_eq_fin_snoc]
    simp [Fin.snoc, Fin.append, Fin.addCases, Fin.castLT, Fin.last, Fin.subNat]
    by_cases h : i.val < m
    · have : i.val < m + n := by omega
      simp [h]
      by_cases hn : n = 0
      · subst hn; simp_all
      · simp at h hn
        simp_all
    · by_cases h' : i.val < m + n
      · simp [h', h]
      · have : i.val = m + n := by omega
        simp [this]

-- Additional append properties (matching Fin.append naming)
@[simp]
theorem empty_append (v : FinVec α n) : append !v[] v = v ∘ Fin.cast (Nat.zero_add n) :=
  zero_append v

@[simp]
theorem append_empty (v : FinVec α m) : append v !v[] = v := rfl

theorem append_assoc {p : ℕ} (u : FinVec α m) (v : FinVec α n) (w : FinVec α p) :
    (append (append u v) w) = (append u (append v w)) ∘ Fin.cast (add_assoc m n p) := by
  simp [append_eq_fin_append, Fin.append_assoc]

-- Index access for append
@[simp]
theorem append_left (u : FinVec α m) (v : FinVec α n) (i : Fin m) :
    append u v (Fin.castAdd n i) = u i := by
  induction n with
  | zero => simp [append]
  | succ n ih =>
    simp [append]
    have : Fin.castAdd (n + 1) i = Fin.castSucc (Fin.castAdd n i) := by
      ext; simp [Fin.coe_castAdd]
    rw [this, concat_castSucc, ih]

@[simp]
theorem append_right (u : FinVec α m) (v : FinVec α n) (i : Fin n) :
    append u v (Fin.natAdd m i) = v i := by
  rw [append_eq_fin_append]
  simp

-- Relationship with cons/concat (matching Fin.append naming)
@[simp]
theorem append_cons (a : α) (u : FinVec α m) (v : FinVec α n) :
    append (cons a u) v = (cons a (append u v)) ∘ Fin.cast (Nat.succ_add m n) := by
  simp only [append_eq_fin_append, cons_eq_fin_cons]
  exact Fin.append_cons a u v

theorem append_concat (u : FinVec α m) (v : FinVec α n) (a : α) :
    append u (concat v a) = concat (append u v) a := by
  simp only [append_eq_fin_append, concat_eq_fin_snoc]
  exact Fin.append_snoc u v a

-- Compatibility with standard library (matching Fin.append naming)
theorem append_left_eq_cons (a : FinVec α 1) (v : FinVec α n) :
    append a v = (cons (a 0) v) ∘ Fin.cast (Nat.add_comm 1 n) := by
  simp only [append_eq_fin_append, cons_eq_fin_cons]
  exact Fin.append_left_eq_cons a v

theorem append_right_eq_snoc (u : FinVec α m) (a : FinVec α 1) :
    append u a = concat u (a 0) := by
  simp only [append_eq_fin_append, concat_eq_fin_snoc]
  exact Fin.append_right_eq_snoc u a

@[simp]
lemma append_zero_of_succ_left {u : Fin (m + 1) → α} {v : Fin n → α} :
    (append u v) 0 = u 0 := by
  simp [append_eq_fin_append]

@[simp]
lemma append_last_of_succ_right {u : Fin m → α} {v : Fin (n + 1) → α} :
    (append u v) (Fin.last (m + n)) = v (Fin.last n) := by
  simp [append_eq_fin_append]

-- Range properties for append (when α : Type*)
theorem range_append {α : Type*} (u : FinVec α m) (v : FinVec α n) :
    Set.range (append u v) = Set.range u ∪ Set.range v := by
  induction n with
  | zero => simp [append]
  | succ n ih =>
    simp [append, ih, range_concat]
    ext i
    simp; sorry

-- Extensionality for append
theorem append_ext (u₁ u₂ : FinVec α m) (v₁ v₂ : FinVec α n) :
    append u₁ v₁ = append u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  simp only [append_eq_fin_append]
  constructor <;> intro h
  · sorry
  · simp [h]

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
    cons a (append u v) = (append (cons a u) v) ∘ Fin.cast (Nat.succ_add m n).symm := by
  simp only [append_cons]
  ext i; simp

theorem append_singleton (u : FinVec α m) (a : α) :
    append u (cons a !v[]) = concat u a := by
  simp only [append_eq_fin_append, cons_eq_fin_cons, concat_eq_fin_snoc, empty]
  ext i
  simp [Fin.append_right_cons]

theorem singleton_append (a : α) (v : FinVec α n) :
    append (cons a !v[]) v = cons a v ∘ Fin.cast (Nat.add_comm _ n) := by
  simp only [append_eq_fin_append, empty]
  ext i
  simp [Fin.cast]
  sorry

-- Empty cases
theorem empty_unique (v : FinVec α 0) : v = !v[] :=
  funext (fun i => Fin.elim0 i)

theorem eq_empty_iff_zero (v : FinVec α n) : (∃ h : n = 0, v = h ▸ !v[]) ↔ n = 0 :=
  sorry

end FinVec

/-! ### Lemmas for `FinTuple` -/

namespace FinTuple

variable {m n : ℕ} {α : Sort u}

instance {α : Fin 0 → Sort u} : Unique (FinTuple 0 α) where
  uniq := fun v => by ext i; exact Fin.elim0 i

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

@[simp]
theorem cons_one {β : Fin n.succ → Sort u} (a : α) (v : FinTuple n.succ β) :
    cons a v 1 = cast (FinVec.cons_succ α β 0).symm (v 0) := by
  induction n with
  | zero => simp [cons]
  | succ n ih => simp [cons]; rfl

theorem cons_eq_fin_cons {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
    cons a v = Fin.cons (α := FinVec.cons α β) (cons a v 0) (fun i => cons a v i.succ) := by
  ext i
  induction i using Fin.induction <;> simp

@[simp]
theorem concat_zero {α : Fin 0 → Sort u} {β : Sort u} (a : β) :
    concat (!t⟨α⟩[] : FinTuple 0 α) a = fun _ => a := rfl

@[simp]
theorem concat_castSucc {α : Fin n → Sort u} {β : Sort u} (v : FinTuple n α) (b : β) (i : Fin n) :
    concat v b (Fin.castSucc i) = cast (FinVec.concat_castSucc α β i).symm (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp [concat]
    induction i using Fin.induction <;> simp [ih]

@[simp]
theorem concat_last {α : Fin n → Sort u} {β : Sort u} (v : FinTuple n α) (b : β) :
    concat v b (Fin.last n) = cast (FinVec.concat_last α β).symm b := by
  induction n with
  | zero => simp [concat]
  | succ n ih =>
    have : Fin.last (n + 1) = (Fin.last n).succ := by simp
    rw! [this, concat, cons_succ, ih]
    rfl

theorem concat_eq_fin_snoc {α : Fin n → Sort u} {β : Sort u} (v : FinTuple n α) (b : β) :
    concat v b = Fin.snoc (α := FinVec.concat α β)
      (fun i => cast (FinVec.concat_castSucc _ _ i).symm (v i))
      (cast (FinVec.concat_last _ _).symm b) := by
  induction n with
  | zero => ext; simp [concat, Fin.snoc]
  | succ n ih =>
    simp [concat, cons, ih]
    ext i
    split <;> simp [Fin.snoc]

-- theorem tail_cons {β : Fin n → Sort u} (a : α) (b : FinTuple n β) (i : Fin n) :
--     True := by
--   sorry

theorem cons_self_tail {α : Fin n.succ → Sort u} (v : FinTuple n.succ α) :
    True := by
  sorry

-- Injectivity properties for cons
theorem cons_right_injective {β : Fin n → Sort u} (a : α) :
    Function.Injective (cons a : FinTuple n β → FinTuple (n + 1) (FinVec.cons α β)) := by
  intro x y h
  rw [cons_eq_fin_cons, cons_eq_fin_cons] at h
  sorry
  -- exact Fin.cons_right_injective _

theorem cons_left_injective {α : Sort u} {β : Fin n → Sort u} (b : FinTuple n β) :
    Function.Injective (fun (a : α) => cons a b) := by
  simp [cons_eq_fin_cons]
  intro x y h
  simp at h
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

@[simp]
theorem append_zero {β : Fin m → Sort u} {α : Fin 0 → Sort u} (u : (i : Fin m) → β i) :
    append u (FinTuple.empty : FinTuple 0 α) = u := rfl

@[simp]
theorem append_empty {α : Fin m → Sort u} (v : FinTuple m α) : append v !t[] = v := rfl

@[simp]
theorem append_succ {α : Fin m → Sort u} {β : Fin (n + 1) → Sort u}
    (u : FinTuple m α) (v : FinTuple (n + 1) β) :
    append u v = concat (append u (fun i => v (Fin.castSucc i))) (v (Fin.last n)) := by
  induction n <;> simp [append]

@[simp]
theorem empty_append {α : Fin 0 → Sort u} {β : Fin n → Sort u} (v : FinTuple n β) :
    append (FinTuple.empty : FinTuple 0 α) v =
      fun i : Fin (0 + n) => cast (by simp) (v <| i.cast (by omega)) := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    simp [append, ih]
    ext i
    by_cases h : i.val < n
    · have : i = Fin.castSucc (⟨i.val, by simp [h]⟩) := by ext; simp
      rw [this, concat_castSucc]
      simp [Fin.cast]
    · have : i = Fin.last (0 + n) := by ext; simp; omega
      rw! [this, concat_last]
      simp only [Fin.last, Fin.cast_mk]
      sorry

-- Index access for append
@[simp]
theorem append_left {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : FinTuple m α) (v : FinTuple n β) (i : Fin m) :
    append u v (Fin.castAdd n i) = cast (FinVec.append_left α β i).symm (u i) := by
  induction n with
  | zero => simp [append]
  | succ n ih =>
    simp only [append_succ]
    have : Fin.castAdd (n + 1) i = Fin.castSucc (Fin.castAdd n i) := by ext; simp
    rw! [this, concat_castSucc, ih]
    simp

@[simp]
theorem append_right {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : FinTuple m α) (v : FinTuple n β) (i : Fin n) :
    append u v (Fin.natAdd m i) = cast (FinVec.append_right α β i).symm (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [append_succ]
    by_cases h : i.val < n
    · have : Fin.natAdd m i = (Fin.castSucc (⟨m + i.val, by simp [h]⟩)) := by ext; simp
      rw! [this, concat_castSucc]
      have : ⟨m + i.val, by simp [h]⟩ = Fin.natAdd m ⟨i, h⟩ := by ext; simp
      rw! [this, ih]
      simp
    · have hi : i = Fin.last n := by ext; simp; omega
      have : Fin.natAdd m i = Fin.last (m + n) := by ext; simp; omega
      rw! [this, concat_last, hi]

theorem append_eq_fin_addCases {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : FinTuple m α) (v : FinTuple n β) :
    append u v = Fin.addCases (motive := FinVec.append α β)
      (fun i => cast (FinVec.append_left α β i).symm (u i))
      (fun i => cast (FinVec.append_right α β i).symm (v i)) := by
  ext i
  by_cases h : i.val < m
  · have : i = Fin.castAdd n ⟨i, by omega⟩ := by ext; simp
    rw [this]
    simp only [Fin.addCases_left, append_left]
  · have : i = Fin.natAdd m ⟨i.val - m, by omega⟩ := by ext; simp; omega
    rw [this]
    simp only [Fin.addCases_right, append_right]

theorem append_assoc {α : Fin m → Sort u} {β : Fin n → Sort u} {p : ℕ} {γ : Fin p → Sort u}
    (u : FinTuple m α) (v : FinTuple n β) (w : FinTuple p γ) :
    append (append u v) w =
      fun i => cast (by simp [FinVec.append_assoc])
        (append u (append v w) (i.cast (by omega))) := by sorry
  -- induction p with
  -- | zero => simp [append]
  -- | succ p ih =>
  --   simp [append, ih, concat_last]
  --   ext i
  --   simp [Fin.castSucc, Fin.last, concat_eq_fin_snoc, Fin.snoc]
  --   by_cases h : i.val < m + n + p
  --   · simp [h]

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

instance {α : Fin 0 → Sort u} : Unique (FinTuple 0 α) where
  default := FinTuple.empty
  uniq v := by
    ext i
    simp [FinTuple.empty]
    exact Fin.elim0 i

-- Cast lemma for type families
theorem cast_cons {β : Fin n → Sort u} (a : α) (v : FinTuple n β) :
    FinTuple.cast rfl (fun _ => rfl) (cons a v) = cons a v := by
  simp only [Fin.cast_eq_self, cons_eq_fin_cons, cons_zero, cons_succ]
  ext _
  simp [FinTuple.cast]

theorem cast_concat {α : Fin n → Sort u} {β : Sort u} (v : FinTuple n α) (b : β) :
    FinTuple.cast rfl (fun _ => rfl) (concat v b) = concat v b := by
  simp only [Fin.cast_eq_self, concat_eq_fin_snoc]
  ext _
  simp [FinTuple.cast]

theorem cast_append {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : FinTuple m α) (v : FinTuple n β) :
    FinTuple.cast rfl (fun _ => rfl) (append u v) = append u v := by
  simp only [Fin.cast_eq_self, append_eq_fin_addCases]
  ext _
  simp [FinTuple.cast]

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
