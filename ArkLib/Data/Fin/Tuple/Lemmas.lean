/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Tuple.Notation

/-!
  # Lemmas for new operations on `Fin`-indexed (heterogeneous) vectors
-/

universe u

namespace Fin

variable {m n : ℕ} {α : Sort u}

instance : Unique (Fin 0 → α) where
  default := !v[]
  uniq v := by
    ext i
    exact elim0 i

@[simp]
theorem vcons_zero (a : α) (v : Fin n → α) : (a ::ᵛ v) 0 = a := by
  induction n with
  | zero => simp [vcons]
  | succ n ih => simp [vcons]; rfl

@[simp]
theorem vcons_succ (a : α) (v : Fin n → α) (i : Fin n) : (a ::ᵛ v) i.succ = v i := by
  induction n with
  | zero => exact elim0 i
  | succ n ih => simp [vcons, succ]

theorem vcons_eq_cons (a : α) (v : Fin n → α) : a ::ᵛ v = cons a v := by
  ext i
  induction i using induction <;> simp

-- Additional index access lemmas (cons_zero and cons_succ already defined above)
@[simp]
theorem vcons_one (a : α) (v : Fin (n + 1) → α) : (a ::ᵛ v) 1 = v 0 := by
  convert vcons_succ a v 0

@[simp]
theorem vcons_empty (a : α) : a ::ᵛ !v[] = !v[a] := rfl

@[simp]
theorem vcons_of_one (a : α) {i : Fin 1} : !v[a] i = a := rfl

-- Head/Tail Operations for cons (matching Fin.cons naming)
@[simp]
theorem tail_vcons (a : α) (v : Fin n → α) : tail (a ::ᵛ v) = v := by
  ext i
  simp [tail]

@[simp]
theorem vcons_self_tail (v : Fin (n + 1) → α) : (v 0) ::ᵛ (tail v) = v := by
  ext i
  induction i using induction <;> simp [tail]

-- Injectivity Properties (matching Fin.cons naming)
theorem vcons_right_injective (a : α) :
    Function.Injective (vcons a : (Fin n → α) → Fin (n + 1) → α) := by
  intro v w h
  have : tail (a ::ᵛ v) = tail (a ::ᵛ w) := by
    ext i; rw [h]
  rwa [tail_vcons, tail_vcons] at this

theorem vcons_left_injective (v : Fin n → α) : Function.Injective (fun a => a ::ᵛ v) := by
  intro a b h
  have := congr_fun h 0
  simp at this
  exact this

theorem vcons_injective2 : Function.Injective2 (@vcons α n) := by
  intro a₁ v₁ a₂ v₂ h
  rw [vcons_eq_cons, vcons_eq_cons] at h
  exact cons_injective2 h

theorem vcons_inj (a b : α) (v w : Fin n → α) : a ::ᵛ v = b ::ᵛ w ↔ a = b ∧ v = w := by
  constructor
  · intro h
    exact vcons_injective2 h
  · intro ⟨ha, hv⟩
    rw [ha, hv]

-- Empty Vector Properties
@[simp]
theorem vcons_fin_zero (a : α) (v : Fin 0 → α) : a ::ᵛ v = fun _ => a := by
  simp [vcons]

theorem vcons_eq_const (a : α) : a ::ᵛ (fun _ : Fin n => a) = fun _ => a := by
  ext i
  induction i using induction <;> simp

-- Range Properties for cons (when α : Type*)
theorem range_vcons {α : Type*} (a : α) (v : Fin n → α) :
    Set.range (a ::ᵛ v) = insert a (Set.range v) := by
  rw [vcons_eq_cons]
  simp

@[simp]
theorem vconcat_zero (a : α) : vconcat !v[] a = !v[a] := by
  simp [vconcat]

@[simp]
theorem vconcat_last (v : Fin n → α) (a : α) : vconcat v a (Fin.last n) = a := by
  induction n with
  | zero => simp [vconcat]
  | succ n ih =>
    simp [vconcat, vcons, last]
    exact ih _

@[simp]
theorem vconcat_castSucc (v : Fin n → α) (a : α) (i : Fin n) :
    vconcat v a (castSucc i) = v i := by
  induction n with
  | zero => exact elim0 i
  | succ n ih =>
    simp [vconcat]
    cases i using cases with
    | zero => simp
    | succ i => simp [ih]

-- Additional concat properties (matching Fin.snoc naming)
theorem vconcat_eq_snoc (v : Fin n → α) (a : α) : vconcat v a = snoc v a := by
  ext i
  by_cases h : i.val < n
  · have : i = Fin.castSucc ⟨i.val, h⟩ := by ext; simp
    rw [this, vconcat_castSucc, snoc_castSucc]
  · have : i = Fin.last n := by
      ext; simp; omega
    rw [this, vconcat_last, snoc_last]

theorem vconcat_vcons_eq_vcons_vconcat (a : α) (v : Fin n → α) (b : α) :
    vconcat (a ::ᵛ v) b = a ::ᵛ (vconcat v b) := by
  simp only [vconcat_eq_snoc, vcons_eq_cons]
  exact Eq.symm (cons_snoc_eq_snoc_cons a v b)

-- Init/snoc properties (matching Fin.snoc naming)
theorem init_vconcat (v : Fin n → α) (a : α) :
    (fun i => vconcat v a (Fin.castSucc i)) = v := by
  ext i
  simp [vconcat_castSucc]

theorem vconcat_init_self (v : Fin (n + 1) → α) :
    vconcat (fun i => v (Fin.castSucc i)) (v (Fin.last n)) = v := by
  ext i
  by_cases h : i.val < n
  · have : i = Fin.castSucc ⟨i.val, h⟩ := by ext; simp
    rw [this, vconcat_castSucc]
  · have : i = Fin.last n := by
      ext; simp; omega
    rw [this]
    simp [vconcat_last]

-- Range properties for concat (when α : Type*)
theorem range_vconcat {α : Type*} (v : Fin n → α) (a : α) :
    Set.range (vconcat v a) = insert a (Set.range v) := by
  rw [vconcat_eq_snoc]
  simp

-- Injectivity properties for concat (matching Fin.snoc naming)
theorem vconcat_injective2 : Function.Injective2 (@vconcat α n) := by
  intro v w a b h
  rw [vconcat_eq_snoc, vconcat_eq_snoc] at h
  simp at h
  exact h

theorem vconcat_inj (v w : Fin n → α) (a b : α) :
    vconcat v a = vconcat w b ↔ v = w ∧ a = b := by
  rw [vconcat_eq_snoc, vconcat_eq_snoc]; simp

theorem vconcat_right_injective (v : Fin n → α) : Function.Injective (vconcat v) := by
  intro x y h
  rw [vconcat_eq_snoc, vconcat_eq_snoc] at h
  simp at h
  exact h

theorem vconcat_left_injective {n : ℕ} (a : α) :
    Function.Injective (fun v : Fin n → α => vconcat v a) := by
  intro x y h
  simp_rw [vconcat_eq_snoc] at h
  simpa using h

@[simp]
theorem zero_vappend {u : Fin 0 → α} (v : Fin n → α) :
    vappend u v = v ∘ Fin.cast (Nat.zero_add n) := by
  induction n with
  | zero => simp [vappend, Unique.uniq]
  | succ n ih =>
    simp [vappend, ih, vconcat_eq_snoc]
    ext i
    simp [Fin.castSucc, Fin.last, Fin.snoc]
    by_cases h : i.val < n
    · simp [h]; rfl
    · have : i.val = n := by omega
      simp [this, Fin.cast]

@[simp]
theorem vappend_zero (u : Fin m → α) : vappend u !v[] = u := rfl

theorem vappend_succ (u : Fin m → α) (v : Fin (n + 1) → α) :
    vappend u v = vconcat (vappend u (v ∘ castSucc)) (v (last n)) := by
  simp [vappend]

theorem vappend_eq_append (u : Fin m → α) (v : Fin n → α) :
    vappend u v = append u v := by
  induction n with
  | zero => ext; simp [vappend, append]; unfold addCases; simp [castLT]
  | succ n ih =>
    ext i
    simp [vappend, ih, vconcat_eq_snoc]
    simp [snoc, append, addCases, castLT, last, subNat]
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

@[simp]
theorem vempty_vappend (v : Fin n → α) : vappend !v[] v = v ∘ Fin.cast (Nat.zero_add n) :=
  zero_vappend v

@[simp]
theorem vappend_vempty (v : Fin m → α) : vappend v !v[] = v := rfl

theorem vappend_assoc {p : ℕ} (u : Fin m → α) (v : Fin n → α) (w : Fin p → α) :
    (vappend (vappend u v) w) = (vappend u (vappend v w)) ∘ Fin.cast (add_assoc m n p) := by
  simp [vappend_eq_append, append_assoc]

-- Index access for append
@[simp]
theorem vappend_left (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    vappend u v (castAdd n i) = u i := by
  induction n with
  | zero => simp [vappend]
  | succ n ih =>
    simp [vappend]
    have : castAdd (n + 1) i = castSucc (castAdd n i) := by
      ext; simp [coe_castAdd]
    rw [this, vconcat_castSucc, ih]

@[simp]
theorem vappend_right (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    vappend u v (natAdd m i) = v i := by
  rw [vappend_eq_append]
  simp

lemma vappend_left_of_lt {m n : ℕ} {α : Sort u}
    (u : Fin m → α) (v : Fin n → α) (i : Fin (m + n)) (h : i.val < m) :
      vappend u v i = u ⟨i, h⟩ := by
  simp [vappend_eq_append, append, addCases, castLT, h]

lemma vappend_right_of_not_lt {m n : ℕ} {α : Sort u}
    (u : Fin m → α) (v : Fin n → α) (i : Fin (m + n)) (h : ¬ i.val < m) :
      vappend u v i = v ⟨i - m, by omega⟩ := by
  simp [vappend_eq_append, append, addCases, h, subNat]

@[simp]
theorem vappend_vcons (a : α) (u : Fin m → α) (v : Fin n → α) :
    vappend (vcons a u) v = (vcons a (vappend u v)) ∘ Fin.cast (Nat.succ_add m n) := by
  simp only [vappend_eq_append, vcons_eq_cons]
  exact append_cons a u v

theorem vappend_vconcat (u : Fin m → α) (v : Fin n → α) (a : α) :
    vappend u (vconcat v a) = vconcat (vappend u v) a := by
  simp only [vappend_eq_append, vconcat_eq_snoc]
  exact append_snoc u v a

-- Compatibility with standard library (matching Fin.append naming)
theorem vappend_left_eq_cons (a : Fin 1 → α) (v : Fin n → α) :
    vappend a v = (vcons (a 0) v) ∘ Fin.cast (Nat.add_comm 1 n) := by
  simp only [vappend_eq_append, vcons_eq_cons]
  exact append_left_eq_cons a v

theorem vappend_right_eq_snoc (u : Fin m → α) (a : Fin 1 → α) :
    vappend u a = vconcat u (a 0) := by
  simp only [vappend_eq_append, vconcat_eq_snoc]
  exact append_right_eq_snoc u a

lemma vappend_zero_of_succ_left {u : Fin (m + 1) → α} {v : Fin n → α} :
    (vappend u v) 0 = u 0 := by
  simp [vappend_eq_append]

@[simp]
lemma vappend_last_of_succ_right {u : Fin m → α} {v : Fin (n + 1) → α} :
    (vappend u v) (last (m + n)) = v (last n) := by
  simp [vappend_eq_append]

-- Range properties for append (when α : Type*)
theorem range_vappend {α : Type*} (u : Fin m → α) (v : Fin n → α) :
    Set.range (vappend u v) = Set.range u ∪ Set.range v := by
  induction n with
  | zero => simp [vappend]
  | succ n ih =>
    simp [vappend, ih, range_vconcat]
    ext i
    simp; sorry

-- Extensionality for append
theorem vappend_ext (u₁ u₂ : Fin m → α) (v₁ v₂ : Fin n → α) :
    vappend u₁ v₁ = vappend u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  simp only [vappend_eq_append]
  constructor <;> intro h
  · sorry
  · simp [h]

-- Additional useful extensionality lemmas
theorem ext_vcons (a b : α) (v w : Fin n → α) : vcons a v = vcons b w ↔ a = b ∧ v = w :=
  vcons_inj a b v w

theorem vcons_eq_vcons_iff (a b : α) (v w : Fin n → α) : vcons a v = vcons b w ↔ a = b ∧ v = w :=
  vcons_inj a b v w

-- Two vectors are equal iff they are equal at every index
theorem vext_iff {v w : Fin n → α} : v = w ↔ ∀ i, v i = w i :=
  ⟨fun h i => by rw [h], fun h => funext h⟩

-- Interaction between operations
theorem vcons_vappend_comm (a : α) (u : Fin m → α) (v : Fin n → α) :
    vcons a (vappend u v) = (vappend (vcons a u) v) ∘ Fin.cast (Nat.succ_add m n).symm := by
  simp only [vcons_eq_cons, vappend_eq_append]
  ext i; simp [append_cons]

theorem vappend_singleton (u : Fin m → α) (a : α) :
    vappend u (vcons a !v[]) = vconcat u a := by
  simp only [vappend_eq_append, vcons_eq_cons, vconcat_eq_snoc, vempty]
  ext i
  simp [append_right_cons]

theorem singleton_append (a : α) (v : Fin n → α) :
    vappend (vcons a !v[]) v = vcons a v ∘ Fin.cast (Nat.add_comm _ n) := by
  simp only [vappend_eq_append, vcons_eq_cons, vempty]
  ext i
  simp [Fin.cast]
  sorry

-- Empty cases
theorem empty_unique (v : Fin 0 → α) : v = !v[] :=
  funext (fun i => elim0 i)

theorem eq_empty_iff_zero (v : Fin n → α) : (∃ h : n = 0, v = h ▸ !v[]) ↔ n = 0 :=
  sorry

/-! ### Lemmas for heterogeneous vectors -/

variable {m n : ℕ} {α : Sort u}

instance {α : Fin 0 → Sort u} : Unique ((i : Fin 0) → α i) where
  uniq := fun v => by ext i; exact elim0 i

@[simp]
theorem dcons_zero {β : Fin n → Sort u} (a : α) (b : (i : Fin n) → β i) :
    dcons a b 0 = cast (vcons_zero α β).symm a := by
  induction n <;> rfl

@[simp]
theorem dcons_succ {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) (i : Fin n) :
    dcons a v i.succ = cast (vcons_succ α β i).symm (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => rfl

@[simp]
theorem dcons_one {β : Fin (n + 1) → Sort u} (a : α) (v : (i : Fin (n + 1)) → β i) :
    dcons a v 1 = cast (vcons_succ α β 0).symm (v 0) := by
  induction n <;> rfl

theorem dcons_eq_cons {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
    dcons a v = cons (α := vcons α β) (dcons a v 0) (fun i => dcons a v i.succ) := by
  ext i
  induction i using induction <;> simp

@[simp]
theorem dconcat_zero {α : Fin 0 → Sort u} {β : Sort u} (a : β) :
    dconcat !t⟨α⟩[] a = fun _ => a := rfl

@[simp]
theorem dconcat_castSucc {α : Fin n → Sort u} {β : Sort u}
    (v : (i : Fin n) → α i) (b : β) (i : Fin n) :
    dconcat v b (castSucc i) = cast (vconcat_castSucc α β i).symm (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp [dconcat]
    induction i using induction <;> simp [ih]

@[simp]
theorem dconcat_last {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
    dconcat v b (last n) = cast (vconcat_last α β).symm b := by
  induction n with
  | zero => simp [dconcat]
  | succ n ih =>
    have : last (n + 1) = (last n).succ := by simp
    rw! [this, dconcat, dcons_succ, ih]
    rfl

theorem dconcat_eq_fin_snoc {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
    dconcat v b = snoc (α := vconcat α β)
      (fun i => cast (vconcat_castSucc _ _ i).symm (v i))
      (cast (vconcat_last _ _).symm b) := by
  induction n with
  | zero => ext; simp [dconcat, snoc]
  | succ n ih =>
    simp [dconcat, dcons, ih]
    ext i
    split <;> simp [snoc]

-- theorem tail_cons {β : Fin n → Sort u} (a : α) (b : FinTuple n β) (i : Fin n) :
--     True := by
--   sorry

-- theorem dcons_self_tail {α : Fin n.succ → Sort u} (v : (i : Fin (n + 1)) → α i) :
--     True := by
--   sorry

-- Injectivity properties for cons
theorem dcons_right_injective {β : Fin n → Sort u} (a : α) :
    Function.Injective (dcons a : ((i : Fin n) → β i) → (i : Fin (n + 1)) → vcons α β i) := by
  intro x y h
  rw [dcons_eq_cons, dcons_eq_cons] at h
  simp [dcons_eq_cons] at h
  apply funext_iff.mp at h
  ext i
  have := h i
  have aux_lemma {α β : Sort u} {h : α = β} (x y : α) (hCast : cast h x = cast h y) : x = y := by
    subst h; simp_all
  exact aux_lemma (x i) (y i) this

theorem dcons_left_injective {α : Sort u} {β : Fin n → Sort u} (b : (i : Fin n) → β i) :
    Function.Injective (fun (a : α) => dcons a b) := by
  simp [dcons_eq_cons]
  intro x y h
  simp at h
  have aux_lemma {α β : Sort u} {h : α = β} (x y : α) (hCast : cast h x = cast h y) : x = y := by
    subst h; simp_all
  exact aux_lemma x y h

theorem dcons_injective2 {α : Sort u} {β : Fin n → Sort u} :
    Function.Injective2 (@dcons n α β) := by
  sorry

theorem dcons_inj {α : Sort u} {β : Fin n → Sort u} (a₁ a₂ : α) (b₁ b₂ : (i : Fin n) → β i) :
    dcons a₁ b₁ = dcons a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  sorry

-- Empty tuple properties
@[simp]
theorem dcons_fin_zero {α : Sort u} {β : Fin 0 → Sort u} (a : α) (v : (i : Fin 0) → β i) :
    dcons a v = fun _ => a := by
  sorry

theorem dconcat_dcons {α : Sort u} {β : Fin n → Sort u} {γ : Sort u} (a : α) (v : (i : Fin n) → β i) (c : γ) :
    True := by
  sorry

-- Init/concat properties
theorem dinit_dconcat {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
    True := by
  sorry

theorem dconcat_init_self {α : Fin n.succ → Sort u} (v : (i : Fin (n + 1)) → α i) :
    True := by
  sorry

-- Injectivity properties for concat
theorem dconcat_injective2 {α : Fin n → Sort u} {β : Sort u} :
    Function.Injective2 (@dconcat n α β) := by
  sorry

theorem dconcat_inj {α : Fin n → Sort u} {β : Sort u} (v₁ v₂ : (i : Fin n) → α i) (a₁ a₂ : β) :
    dconcat v₁ a₁ = dconcat v₂ a₂ ↔ v₁ = v₂ ∧ a₁ = a₂ := by
  sorry

theorem dconcat_right_injective {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) :
    Function.Injective (dconcat v : β → (i : Fin (n + 1)) → vconcat α β i) := by
  sorry

theorem dconcat_left_injective {α : Fin n → Sort u} {β : Sort u} (a : β) :
    Function.Injective (fun v : (i : Fin n) → α i => dconcat v a) := by
  sorry

@[simp]
theorem dappend_zero {β : Fin m → Sort u} {α : Fin 0 → Sort u} (u : (i : Fin m) → β i) :
    dappend u !t⟨α⟩[] = u := rfl

@[simp]
theorem dappend_empty {α : Fin m → Sort u} (v : (i : Fin m) → α i) : dappend v !t[] = v := rfl

@[simp]
theorem dappend_succ {α : Fin m → Sort u} {β : Fin (n + 1) → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin (n + 1)) → β i) :
    dappend u v = dconcat (dappend u (fun i => v (castSucc i))) (v (last n)) := by
  induction n <;> simp [dappend]

@[simp]
theorem dempty_dappend {α : Fin 0 → Sort u} {β : Fin n → Sort u} (v : (i : Fin n) → β i) :
    dappend !t⟨α⟩[] v =
      fun i : Fin (0 + n) => cast (by simp) (v <| i.cast (by omega)) := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    simp [dappend, ih]
    ext i
    by_cases h : i.val < n
    · have : i = Fin.castSucc (⟨i.val, by simp [h]⟩) := by ext; simp
      rw [this, dconcat_castSucc]
      simp [Fin.cast]
    · have : i = Fin.last (0 + n) := by ext; simp; omega
      rw! [this, dconcat_last]
      simp only [Fin.last, Fin.cast_mk]
      sorry

-- Index access for append
@[simp]
theorem dappend_left {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (i : Fin m) :
    dappend u v (castAdd n i) = cast (vappend_left α β i).symm (u i) := by
  induction n with
  | zero => simp [dappend]
  | succ n ih =>
    simp only [dappend_succ]
    have : castAdd (n + 1) i = castSucc (castAdd n i) := by ext; simp
    rw! [this, dconcat_castSucc, ih]
    simp

@[simp]
theorem dappend_right {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (i : Fin n) :
    dappend u v (natAdd m i) = cast (vappend_right α β i).symm (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [dappend_succ]
    by_cases h : i.val < n
    · have : natAdd m i = (castSucc (⟨m + i.val, by simp [h]⟩)) := by ext; simp
      rw! [this, dconcat_castSucc]
      have : ⟨m + i.val, by simp [h]⟩ = natAdd m ⟨i, h⟩ := by ext; simp
      rw! [this, ih]
      simp
    · have hi : i = last n := by ext; simp; omega
      have : natAdd m i = last (m + n) := by ext; simp; omega
      rw! [this, dconcat_last, hi]

theorem dappend_eq_addCases {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) :
    dappend u v = addCases (motive := vappend α β)
      (fun i => cast (vappend_left α β i).symm (u i))
      (fun i => cast (vappend_right α β i).symm (v i)) := by
  ext i
  by_cases h : i.val < m
  · have : i = castAdd n ⟨i, by omega⟩ := by ext; simp
    rw [this]
    simp only [addCases_left, dappend_left]
  · have : i = natAdd m ⟨i.val - m, by omega⟩ := by ext; simp; omega
    rw [this]
    simp only [addCases_right, dappend_right]

theorem dappend_assoc {α : Fin m → Sort u} {β : Fin n → Sort u} {p : ℕ} {γ : Fin p → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (w : (i : Fin p) → γ i) :
    dappend (dappend u v) w =
      fun i => cast (by simp [vappend_assoc])
        (dappend u (dappend v w) (i.cast (by omega))) := by sorry
  -- induction p with
  -- | zero => simp [append]
  -- | succ p ih =>
  --   simp [append, ih, concat_last]
  --   ext i
  --   simp [Fin.castSucc, Fin.last, concat_eq_fin_snoc, Fin.snoc]
  --   by_cases h : i.val < m + n + p
  --   · simp [h]

-- Relationship with cons/concat
theorem dappend_dcons {β : Fin m → Sort u} {γ : Fin n → Sort u}
    (a : α) (u : (i : Fin m) → β i) (v : (i : Fin n) → γ i) :
    True := by
  sorry

theorem dappend_dconcat {α : Fin m → Sort u} {β : Fin n → Sort u} {γ : Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (c : γ) :
    True := by
  sorry

-- Compatibility lemmas
theorem dappend_left_eq_dcons {α : Fin 1 → Sort u} {β : Fin n → Sort u}
    (a : (i : Fin 1) → α i) (v : (i : Fin n) → β i) :
    True := by
  sorry

theorem dappend_right_eq_dconcat {α : Fin m → Sort u} {β : Fin 1 → Sort u}
    (u : (i : Fin m) → α i) (a : (i : Fin 1) → β i) :
    dappend u a = dconcat u (a 0) := by
  sorry

-- Extensionality properties
theorem dappend_ext {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u₁ u₂ : (i : Fin m) → α i) (v₁ v₂ : (i : Fin n) → β i) :
    dappend u₁ v₁ = dappend u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  sorry

theorem ext_dcons {β : Fin n → Sort u} (a₁ a₂ : α) (v₁ v₂ : (i : Fin n) → β i) :
    dcons a₁ v₁ = dcons a₂ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ := by
  sorry

theorem dcons_eq_dcons_iff {β : Fin n → Sort u} (a₁ a₂ : α) (v₁ v₂ : (i : Fin n) → β i) :
    dcons a₁ v₁ = dcons a₂ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ := by
  sorry

-- Two tuples are equal iff they are equal at every index (with casting)
theorem dext_iff {α : Fin n → Sort u} {v w : (i : Fin n) → α i} :
    v = w ↔ ∀ i, v i = w i := by
  aesop

-- Interaction between operations
theorem dcons_dappend_comm {β : Fin m → Sort u} {γ : Fin n → Sort u}
    (a : α) (u : (i : Fin m) → β i) (v : (i : Fin n) → γ i) :
    True := by
  sorry

theorem dappend_singleton {α : Fin m → Sort u} {β : Sort u} (u : (i : Fin m) → α i) (a : β) :
    True := by
  sorry

theorem singleton_dappend {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
    True := by
  sorry

instance {α : Fin 0 → Sort u} : Unique ((i : Fin 0) → α i) where
  default := fun i => elim0 i
  uniq v := by
    ext i
    simp [elim0]
    exact Fin.elim0 i

-- Cast lemma for type families
-- theorem cast_cons {β : Fin n → Sort u} (a : α) (v : FinTuple n β) :
--     FinTuple.cast rfl (fun _ => rfl) (cons a v) = cons a v := by
--   simp only [Fin.cast_eq_self, cons_eq_fin_cons, cons_zero, cons_succ]
--   ext _
--   simp [cast]

-- theorem cast_dconcat {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
--     cast rfl (fun _ => rfl) (dconcat v b) = dconcat v b := by
--   simp only [Fin.cast_eq_self, dconcat_eq_fin_snoc]
--   ext _
--   simp [cast]

-- theorem cast_dappend {α : Fin m → Sort u} {β : Fin n → Sort u}
--     (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) :
--     cast rfl (fun _ => rfl) (dappend u v) = dappend u v := by
--   simp only [Fin.cast_eq_self, dappend_eq_addCases]
--   ext _
--   simp [cast]

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
