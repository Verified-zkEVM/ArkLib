/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Tuple.Notation

/-!
  # Lemmas for new operations on `Fin`-indexed (heterogeneous) vectors
-/

universe u v w

private lemma cast_eq_cast_same_type {α β : Sort u} (h1 h2 : α = β) {x y : α}
    (h : cast h1 x = cast h2 y) : x = y := by
  subst_vars
  rfl

namespace Fin

variable {m n : ℕ} {α : Sort u}

instance : Unique (Fin 0 → α) where
  uniq v := by
    ext i
    exact elim0 i

instance {α : Fin 0 → Sort u} : Unique ((i : Fin 0) → α i) where
  uniq := fun v => by ext i; exact elim0 i

@[simp]
theorem dcons_zero {motive : Fin (n + 1) → Sort u} (a : motive 0)
    (v : (i : Fin n) → motive i.succ) : (a ::ᵈ⟨motive⟩ v) 0 = a := by
  induction n <;> simp [dcons]; rfl

@[simp]
theorem vcons_zero (a : α) (v : Fin n → α) : (a ::ᵛ v) 0 = a :=
  dcons_zero (motive := fun _ => α) a v

@[simp]
theorem dcons_succ {motive : Fin (n + 1) → Sort u} (a : motive 0)
    (v : (i : Fin n) → motive i.succ) (i : Fin n) : (a ::ᵈ⟨motive⟩ v) i.succ = v i := by
  induction n with
  | zero => exact elim0 i
  | succ n ih => simp [dcons, succ]

@[simp]
theorem vcons_succ (a : α) (v : Fin n → α) (i : Fin n) : (a ::ᵛ v) i.succ = v i :=
  dcons_succ (motive := fun _ => α) a v i

/-- `dcons` is equal to `cons`. Marked as `csimp` to allow for switching to the `cons`
  implementation during execution. -/
@[csimp]
theorem dcons_eq_cons : @dcons = @cons := by
  ext n motive a v i
  induction i using induction <;> simp

theorem vcons_eq_cons (a : α) (v : Fin n → α) : a ::ᵛ v = cons a v := by
  have := dcons_eq_cons
  apply funext_iff.mp at this
  have := this n
  apply funext_iff.mp at this
  have := this (fun _ => α)
  apply funext_iff.mp at this
  have := this a
  apply funext_iff.mp at this
  have := this v
  exact this

@[simp]
theorem dcons_one {motive : Fin (n + 2) → Sort u} (a : motive 0)
    (v : (i : Fin (n + 1)) → motive i.succ) : (a ::ᵈ⟨motive⟩ v) 1 = v 0 :=
  dcons_succ a v 0

@[simp]
theorem vcons_one (a : α) (v : Fin (n + 1) → α) : (a ::ᵛ v) 1 = v 0 :=
  vcons_succ a v 0

@[simp]
theorem vcons_empty (a : α) : a ::ᵛ !v[] = !v[a] := rfl

@[simp]
theorem vcons_of_one (a : α) {i : Fin 1} : !v[a] i = match i with | 0 => a := rfl

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
theorem vcons_fin_zero (a : α) (v : Fin 0 → α) : a ::ᵛ v = fun i => match i with | 0 => a := rfl

theorem vcons_eq_const (a : α) : a ::ᵛ (fun _ : Fin n => a) = fun _ => a := by
  ext i
  induction i using induction <;> simp

-- Range Properties for cons (when α : Type*)
theorem range_vcons {α : Type*} (a : α) (v : Fin n → α) :
    Set.range (a ::ᵛ v) = insert a (Set.range v) := by
  rw [vcons_eq_cons]
  simp

@[simp]
theorem dconcat_zero {motive : Fin 1 → Sort u} (a : motive (last 0)) :
    !d⟨fun _ : Fin 0 => motive (castSucc _)⟩[] :+ᵈ⟨motive⟩ a = !d⟨motive⟩[a] := rfl

@[simp]
theorem vconcat_zero (a : α) : vconcat !v[] a = !v[a] :=
  dconcat_zero (motive := fun _ => α) a

@[simp]
theorem dconcat_last {motive : Fin (n + 1) → Sort u} (v : (i : Fin n) → motive (castSucc i))
    (a : motive (last n)) : (v :+ᵈ⟨motive⟩ a) (last n) = a := by
  induction n with
  | zero => simp [dconcat]
  | succ n ih =>
    simp [dconcat, dcons, last]
    exact ih _ _

@[simp]
theorem vconcat_last (v : Fin n → α) (a : α) : vconcat v a (Fin.last n) = a :=
  dconcat_last (motive := fun _ => α) v a

@[simp]
theorem dconcat_castSucc {motive : Fin (n + 1) → Sort u} (v : (i : Fin n) → motive (castSucc i))
    (a : motive (last n)) (i : Fin n) : (v :+ᵈ⟨motive⟩ a) (castSucc i) = v i := by
  induction n with
  | zero => exact elim0 i
  | succ n ih =>
    simp [dconcat]
    cases i using cases with
    | zero => simp
    | succ i => simp [ih]

@[simp]
theorem vconcat_castSucc (v : Fin n → α) (a : α) (i : Fin n) :
    vconcat v a (castSucc i) = v i :=
  dconcat_castSucc (motive := fun _ => α) v a i

/-- `dconcat` is equal to `snoc`. Marked as `csimp` to allow for switching to the `snoc`
  implementation during execution. -/
@[csimp]
theorem dconcat_eq_snoc : @dconcat = @snoc := by
  ext n motive v a i
  by_cases h : i.val < n
  · have : i = Fin.castSucc ⟨i.val, h⟩ := by ext; simp
    rw [this, dconcat_castSucc, snoc_castSucc]
  · have : i = Fin.last n := by
      ext; simp; omega
    rw [this, dconcat_last, snoc_last]

theorem vconcat_eq_snoc (v : Fin n → α) (a : α) : vconcat v a = snoc v a := by
  have := dconcat_eq_snoc
  apply funext_iff.mp at this
  have := this n
  apply funext_iff.mp at this
  have := this (fun _ => α)
  apply funext_iff.mp at this
  have := this v
  apply funext_iff.mp at this
  have := this a
  exact this

theorem dconcat_dcons_eq_dcons_dconcat {motive : Fin (n + 2) → Sort u} (a : motive 0)
    (v : (i : Fin n) → motive (succ (castSucc i))) (b : motive (last (n + 1))) :
    (a ::ᵈ v) :+ᵈ⟨motive⟩ b = a ::ᵈ⟨motive⟩ (v :+ᵈ b) := by
  ext i
  match n with
  | 0 => cases i using cases <;> simp [dconcat, dcons]
  | n + 1 =>
    cases i using cases with
    | zero => simp [dcons_eq_cons, dconcat_eq_snoc]
    | succ i =>
      by_cases hi : i = last (n + 1)
      · rw [hi]; simp
        have : last (_ + 1 + 1) = (last (n + 1)).succ := by simp
        rw! (castMode := .all) [this, dcons_succ]
        simp
      · have : i.succ = (i.castPred hi).succ.castSucc := by simp
        rw [dcons_succ]
        rw! (castMode := .all) [this, dconcat_castSucc]

theorem vconcat_vcons_eq_vcons_vconcat (a : α) (v : Fin n → α) (b : α) :
    vconcat (a ::ᵛ v) b = a ::ᵛ (vconcat v b) :=
  dconcat_dcons_eq_dcons_dconcat (motive := fun _ => α) a v b

-- Init/snoc properties (matching Fin.snoc naming)
theorem init_dconcat {motive : Fin (n + 1) → Sort u} (v : (i : Fin n) → motive (castSucc i))
    (a : motive (last n)) : (fun i => (v :+ᵈ⟨motive⟩ a) (castSucc i)) = v := by
  ext i
  simp [dconcat_castSucc]

theorem init_vconcat (v : Fin n → α) (a : α) :
    (fun i => vconcat v a (Fin.castSucc i)) = v :=
  init_dconcat (motive := fun _ => α) v a

theorem dconcat_init_self {motive : Fin (n + 1) → Sort u} (v : (i : Fin (n + 1)) → motive i) :
    (fun i => v (castSucc i)) :+ᵈ⟨motive⟩ (v (last n)) = v := by
  ext i
  by_cases h : i.val < n
  · have : i = Fin.castSucc ⟨i.val, h⟩ := by ext; simp
    rw [this, dconcat_castSucc]
  · have : i = Fin.last n := by
      ext; simp; omega
    rw [this]
    simp [dconcat_last]

theorem vconcat_init_self (v : Fin (n + 1) → α) :
    vconcat (fun i => v (Fin.castSucc i)) (v (Fin.last n)) = v :=
  dconcat_init_self (motive := fun _ => α) v

theorem range_vconcat {α : Type*} (v : Fin n → α) (a : α) :
    Set.range (vconcat v a) = insert a (Set.range v) := by
  rw [vconcat_eq_snoc]
  simp

-- Injectivity properties for concat (matching Fin.snoc naming)
theorem dconcat_injective2 {motive : Fin (n + 1) → Sort u} :
    Function.Injective2 (@dconcat n motive) := by
  intro v w a b h
  constructor
  · ext i
    have := congr_fun h (castSucc i)
    simp [dconcat_castSucc] at this
    exact this
  · have := congr_fun h (last n)
    simp [dconcat_last] at this
    exact this

theorem vconcat_injective2 : Function.Injective2 (@vconcat α n) :=
  dconcat_injective2 (motive := fun _ => α)

theorem dconcat_inj {motive : Fin (n + 1) → Sort u} (v w : (i : Fin n) → motive (castSucc i))
    (a b : motive (last n)) :
    (v :+ᵈ⟨motive⟩ a) = (w :+ᵈ⟨motive⟩ b) ↔ v = w ∧ a = b := by
  constructor
  · exact @dconcat_injective2 _ motive v w a b
  · intro ⟨hv, ha⟩
    rw [hv, ha]

theorem vconcat_inj (v w : Fin n → α) (a b : α) :
    vconcat v a = vconcat w b ↔ v = w ∧ a = b :=
  dconcat_inj (motive := fun _ => α) v w a b

theorem dconcat_right_injective {motive : Fin (n + 1) → Sort u}
    (v : (i : Fin n) → motive (castSucc i)) :
    Function.Injective (dconcat (motive := motive) v) := by
  intro x y h
  have : dconcat (motive := motive) v x = dconcat (motive := motive) v y := h
  exact (dconcat_inj v v x y).mp this |>.2

theorem vconcat_right_injective (v : Fin n → α) : Function.Injective (vconcat v) :=
  dconcat_right_injective (motive := fun _ => α) v

theorem dconcat_left_injective {motive : Fin (n + 1) → Sort u} (a : motive (last n)) :
    Function.Injective (fun v => dconcat (motive := motive) v a) := by
  intro x y h
  exact (dconcat_inj x y a a).mp h |>.1

theorem vconcat_left_injective {n : ℕ} (a : α) :
    Function.Injective (fun v : Fin n → α => vconcat v a) :=
  dconcat_left_injective (motive := fun _ => α) a

@[simp]
theorem zero_dappend {motive : Fin (0 + n) → Sort u} {u : (i : Fin 0) → motive (castAdd n i)}
    (v : (i : Fin n) → motive (natAdd 0 i)) :
    dappend (motive := motive) u v = fun i => cast (by simp) (v (i.cast (by omega))) := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    simp [dappend, ih, dconcat_eq_snoc, Fin.cast, last]
    ext i
    by_cases h : i.val < n
    · have : i = Fin.castSucc ⟨i.val, by simp [h]⟩ := by ext; simp
      rw [this, snoc_castSucc]
      simp
    · have : i.val = n := by omega
      have : i = Fin.last _ := by ext; simp [this]
      rw! [this, snoc_last]
      simp
      rw! (castMode := .all) [Nat.zero_add]
      simp [cast]
      generalize_proofs h1 h2 h3 h4 h5 h6
      clear * -
      set u := v ⟨n, h3⟩
      sorry

@[simp]
theorem zero_vappend {u : Fin 0 → α} (v : Fin n → α) :
    vappend u v = v ∘ Fin.cast (Nat.zero_add n) :=
  zero_dappend (motive := fun _ => α) v

@[simp]
theorem dappend_zero {motive : Fin (m + 0) → Sort u} (u : (i : Fin m) → motive (castAdd 0 i)) :
    dappend (motive := motive) u !d⟨fun _ : Fin 0 => motive (natAdd m _)⟩[] = u := rfl

@[simp]
theorem vappend_zero (u : Fin m → α) {v : Fin 0 → α}: vappend u v = u := rfl

theorem dappend_succ {motive : Fin (m + (n + 1)) → Sort u}
    (u : (i : Fin m) → motive (castAdd (n + 1) i))
    (v : (i : Fin (n + 1)) → motive (natAdd m i)) :
    dappend (motive := motive) u v =
      (dappend u (fun i => v (castSucc i))) :+ᵈ⟨motive⟩ (v (last n)) := by
  ext i
  simp [dappend]

theorem vappend_succ (u : Fin m → α) (v : Fin (n + 1) → α) :
    vappend u v = vconcat (vappend u (v ∘ castSucc)) (v (last n)) :=
  dappend_succ (motive := fun _ => α) u v

/-- `dappend` is equal to `addCases`. Marked as `csimp` to allow for switching to the `addCases`
  implementation during execution. -/
@[csimp]
theorem dappend_eq_addCases : @dappend = @addCases := by
  ext m n motive u v i
  induction n with
  | zero => simp [dappend, addCases, castLT]
  | succ n ih =>
    simp [dappend, dconcat_eq_snoc]
    have ih' : ∀ (motive : Fin (m + n) → Sort _)
      (u : (i : Fin m) → motive (castAdd n i))
      (v : (i : Fin n) → motive (natAdd m i)),
        dappend (motive := motive) u v = addCases (motive := motive) u v := by
      intro motive_1 u_1 v_1
      ext x : 1
      apply ih
    rw [ih' (fun i => motive i.castSucc) u (fun i => v (castSucc i))]
    simp [snoc, addCases, last, castLT, subNat]
    by_cases h : i.val < m
    · have : i.val < m + n := by omega
      simp [h, this]
    · by_cases h' : i.val < m + n
      · simp [h', h]; sorry
      · have : i.val = m + n := by omega
        simp [this]
        rw! [this, Nat.add_sub_cancel_left]
        simp [cast]
        sorry

/-- `vappend` is equal to `append`. Marked as `csimp` to allow for switching to the `append`
  implementation during execution. -/
@[csimp]
theorem vappend_eq_append : @vappend = @append := by
  ext
  rw [vappend, dappend_eq_addCases]
  simp [append]

@[simp]
theorem dempty_dappend {motive : Fin (0 + n) → Sort u} (v : (i : Fin n) → motive (natAdd 0 i)) :
    dappend (motive := motive) !d⟨fun _ : Fin 0 => motive (castAdd n _)⟩[] v =
      fun i => cast (by simp) (v (i.cast (by omega))) :=
  zero_dappend v

@[simp]
theorem vempty_vappend (v : Fin n → α) : vappend !v[] v = v ∘ Fin.cast (Nat.zero_add n) :=
  zero_vappend v

@[simp]
theorem dappend_dempty {motive : Fin (m + 0) → Sort u} (v : (i : Fin m) → motive (castAdd 0 i)) :
    dappend (motive := motive) v !d⟨fun _ : Fin 0 => motive (natAdd m _)⟩[] = v := rfl

@[simp]
theorem vappend_vempty (v : Fin m → α) : vappend v !v[] = v := rfl

theorem dappend_assoc {p : ℕ} {motive : Fin (m + n + p) → Sort u}
    (u : (i : Fin m) → motive (castAdd p (castAdd n i)))
    (v : (i : Fin n) → motive (castAdd p (natAdd m i)))
    (w : (i : Fin p) → motive (natAdd (m + n) i)) : True := sorry
    -- dappend (motive := motive) (dappend u v) w =
    -- dappend (m := m) (n := n + p) (motive := motive ∘ Fin.cast (Nat.add_assoc m n p).symm) u
    --   (dappend
    --     (motive := fun i : Fin (n + p) =>
    --       motive (Fin.cast (Nat.add_assoc _ _ _).symm (natAdd m i)))
    --     v (sorry)) := by sorry
  -- ext i
  -- simp [dappend]
  -- have : castAdd p (castAdd n i) = castAdd (n + p) i := by
  --   ext; simp [coe_castAdd]
  -- rw [this, dconcat_castSucc, dconcat_castSucc]
  -- simp [dappend]
  -- have : castAdd p (natAdd m i) = castAdd (m + p) i := by
  --   ext; simp [coe_castAdd]
  -- sorry

theorem vappend_assoc {p : ℕ} (u : Fin m → α) (v : Fin n → α) (w : Fin p → α) :
    (vappend (vappend u v) w) = (vappend u (vappend v w)) ∘ Fin.cast (add_assoc m n p) := by
  simp [vappend_eq_append, append_assoc]

@[simp]
theorem dappend_left {motive : Fin (m + n) → Sort u} (u : (i : Fin m) → motive (castAdd n i))
    (v : (i : Fin n) → motive (natAdd m i)) (i : Fin m) :
    dappend (motive := motive) u v (castAdd n i) = u i := by
  rw [dappend_eq_addCases, addCases_left]

@[simp]
theorem vappend_left (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    vappend u v (castAdd n i) = u i :=
  dappend_left (motive := fun _ => α) u v i

@[simp]
theorem dappend_right {motive : Fin (m + n) → Sort u} (u : (i : Fin m) → motive (castAdd n i))
    (v : (i : Fin n) → motive (natAdd m i)) (i : Fin n) :
    dappend (motive := motive) u v (natAdd m i) = v i := by
  rw [dappend_eq_addCases, addCases_right]

@[simp]
theorem vappend_right (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    vappend u v (natAdd m i) = v i :=
  dappend_right (motive := fun _ => α) u v i

lemma dappend_left_of_lt {motive : Fin (m + n) → Sort u}
    (u : (i : Fin m) → motive (castAdd n i)) (v : (i : Fin n) → motive (natAdd m i))
    (i : Fin (m + n)) (h : i.val < m) :
      dappend (motive := motive) u v i = cast (by simp) (u ⟨i, h⟩) := by
  simp [dappend_eq_addCases, addCases, castLT, h]

lemma vappend_left_of_lt {m n : ℕ} {α : Sort u}
    (u : Fin m → α) (v : Fin n → α) (i : Fin (m + n)) (h : i.val < m) :
      vappend u v i = u ⟨i, h⟩ :=
  dappend_left_of_lt (motive := fun _ => α) u v i h

lemma dappend_right_of_not_lt {motive : Fin (m + n) → Sort u}
    (u : (i : Fin m) → motive (castAdd n i)) (v : (i : Fin n) → motive (natAdd m i))
    (i : Fin (m + n)) (h : ¬ i.val < m) :
      dappend (motive := motive) u v i = dcast (by ext; simp; omega) (v ⟨i - m, by omega⟩) := by
  simp [dappend_eq_addCases, addCases, h, subNat, dcast, cast]
  sorry

lemma vappend_right_of_not_lt {m n : ℕ} {α : Sort u}
    (u : Fin m → α) (v : Fin n → α) (i : Fin (m + n)) (h : ¬ i.val < m) :
      vappend u v i = v ⟨i - m, by omega⟩ :=
  dappend_right_of_not_lt (motive := fun _ => α) u v i h

-- @[simp]
-- theorem dappend_dcons {motive : Fin ((m + 1) + n) → Sort u} (a : motive 0)
--     (u : (i : Fin m) → motive (succ (castAdd n i)))
--     (v : (i : Fin n) → motive (natAdd (m + 1) i)) :
--     dappend (motive := motive) (a ::ᵈ⟨motive⟩ u) v =
--       fun i => cast (by simp) (dcons a
-- (dappend (motive := fun i => motive (cast (by omega) i)) u v)
--         (i.cast (Nat.succ_add m n))) := by
--   sorry

@[simp]
theorem vappend_vcons (a : α) (u : Fin m → α) (v : Fin n → α) :
    vappend (vcons a u) v = (vcons a (vappend u v)) ∘ Fin.cast (Nat.succ_add m n) := by
  simp only [vappend_eq_append, vcons_eq_cons]
  exact append_cons a u v

-- theorem dappend_dconcat {motive : Fin (m + (n + 1)) → Sort u}
--     (u : (i : Fin m) → motive (cast (by omega) (castAdd (n + 1) i)))
--     (v : (i : Fin n) → motive (cast (by omega) (natAdd m (castSucc i))))
--     (a : motive (cast (by omega) (natAdd m (last n)))) :
--     dappend (motive := fun i => motive (cast (by omega) i)) u (dconcat v a) =
--       dconcat (motive := fun i => motive (cast (by omega) i)) (dappend u v) a := by
--   sorry

theorem vappend_vconcat (u : Fin m → α) (v : Fin n → α) (a : α) :
    vappend u (vconcat v a) = vconcat (vappend u v) a := by
  simp only [vappend_eq_append, vconcat_eq_snoc]
  exact append_snoc u v a

-- theorem dappend_left_eq_dcons {motive : Fin (1 + n) → Sort u}
--     (a : (i : Fin 1) → motive (cast (by omega) (castAdd n i)))
--     (v : (i : Fin n) → motive (cast (by omega) (natAdd 1 i))) :
--     dappend (motive := fun i => motive (cast (by omega) i)) a v =
--       fun i => cast (by simp) (dcons (a 0) v (i.cast (Nat.add_comm 1 n))) := by
--   sorry

theorem vappend_left_eq_cons (a : Fin 1 → α) (v : Fin n → α) :
    vappend a v = (vcons (a 0) v) ∘ Fin.cast (Nat.add_comm 1 n) := by
  simp only [vappend_eq_append, vcons_eq_cons]
  exact append_left_eq_cons a v

-- theorem dappend_right_eq_dconcat
--     {motive : Fin (m + 1) → Sort u} (u : (i : Fin m) → motive (cast (by omega) (castAdd 1 i)))
--     (a : (i : Fin 1) → motive (cast (by omega) (natAdd m i))) :
--     dappend (motive := motive) u a = dconcat u (a 0) := by
--   sorry

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
  | zero => simp
  | succ n ih =>
    simp [vappend_succ, ih, range_vconcat]
    ext i
    simp
    sorry

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
    vappend !v[a] v = vcons a v ∘ Fin.cast (Nat.add_comm _ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [vappend_succ]
    ext i
    induction i using induction with
    | zero => unfold vappend vconcat dappend dconcat; sorry
    | succ i ih => simp [ih]; sorry

-- Empty cases
theorem empty_unique (v : Fin 0 → α) : v = !v[] :=
  funext (fun i => elim0 i)

/-! ### Lemmas for functorial vectors (binary first, then unary) -/

/- Binary functorial lemmas for `fcons₂`, `fconcat₂`, `fappend₂`. -/
section FunctorialBinary

variable {A : Sort u} {B : Sort v} {F₂ : A → B → Sort w} {m n : ℕ}

@[simp]
theorem fcons₂_zero {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (a : F₂ α₁ α₂) (b : (i : Fin n) → F₂ (β₁ i) (β₂ i)) :
    fcons₂ (F := F₂) a b 0 = cast (by simp [Fin.vcons_zero]) a := by
  induction n <;> rfl

@[simp]
theorem fcons₂_succ {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (a : F₂ α₁ α₂) (b : (i : Fin n) → F₂ (β₁ i) (β₂ i)) (i : Fin n) :
    fcons₂ (F := F₂) a b i.succ =
      cast (by simp [Fin.vcons_succ]) (b i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ _ _ => rfl

@[simp]
theorem fcons₂_one {α₁ : A} {α₂ : B} {β₁ : Fin (n + 1) → A} {β₂ : Fin (n + 1) → B}
    (a : F₂ α₁ α₂) (b : (i : Fin (n + 1)) → F₂ (β₁ i) (β₂ i)) :
    fcons₂ (F := F₂) a b 1 = b 0 := by
  induction n <;> rfl

theorem fcons₂_right_injective {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (a : F₂ α₁ α₂) :
    Function.Injective
      (fcons₂ (F := F₂) a : ((i : Fin n) → F₂ (β₁ i) (β₂ i)) → (i : Fin (n + 1)) → _ ) := by
  intro x y h; ext i
  have := congr_fun h i.succ
  simp at this
  exact cast_eq_cast_same_type _ _ this

theorem fcons₂_left_injective {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (b : (i : Fin n) → F₂ (β₁ i) (β₂ i)) :
    Function.Injective (fun a : F₂ α₁ α₂ => fcons₂ (F := F₂) a b) := by
  intro x y h
  have := congr_fun h 0
  simp at this
  exact cast_eq_cast_same_type _ _ this

theorem fcons₂_injective2 {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B} :
    Function.Injective2 (@fcons₂ A B F₂ n α₁ β₁ α₂ β₂) := by
  intro a₁ b₁ a₂ b₂ h
  constructor
  · have := congr_fun h 0; simp at this
    exact cast_eq_cast_same_type _ _ this
  · ext i
    have := congr_fun h i.succ; simp at this
    exact cast_eq_cast_same_type _ _ this

theorem fcons₂_inj {α₁ : A} {α₂ : B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (a₁ a₂ : F₂ α₁ α₂) (b₁ b₂ : (i : Fin n) → F₂ (β₁ i) (β₂ i)) :
    fcons₂ (F := F₂) a₁ b₁ = fcons₂ (F := F₂) a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · intro h; exact fcons₂_injective2 (n := n) (β₁ := β₁) (β₂ := β₂) h
  · intro ⟨ha, hb⟩; simp [ha, hb]

@[simp]
theorem fconcat₂_castSucc {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B}
    (v : (i : Fin n) → F₂ (α₁ i) (α₂ i)) (a : F₂ β₁ β₂) (i : Fin n) :
    fconcat₂ (F := F₂) v a (castSucc i) =
      cast (by simp [vconcat_castSucc]) (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp [fconcat₂]
    induction i using induction with
    | zero => simp
    | succ i ih' => simp [ih]

@[simp]
theorem fconcat₂_last {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B}
    (v : (i : Fin n) → F₂ (α₁ i) (α₂ i)) (a : F₂ β₁ β₂) :
    fconcat₂ (F := F₂) v a (last n) = cast (by simp [vconcat_last]) a := by
  induction n with
  | zero => simp [fconcat₂]
  | succ n ih =>
    have : last (n + 1) = (last n).succ := by simp
    rw! [this, fconcat₂, fcons₂_succ, ih]; rfl

theorem fconcat₂_injective2 {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B} :
    Function.Injective2 (@fconcat₂ A B F₂ n α₁ β₁ α₂ β₂) := by
  intro v₁ a₁ v₂ a₂ h
  constructor
  · ext i
    have := congr_fun h (castSucc i); simp at this
    exact cast_eq_cast_same_type _ _ this
  · have := congr_fun h (last n); simp at this
    exact cast_eq_cast_same_type _ _ this

theorem fconcat₂_inj {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B}
    (v₁ v₂ : (i : Fin n) → F₂ (α₁ i) (α₂ i)) (a₁ a₂ : F₂ β₁ β₂) :
    fconcat₂ (F := F₂) v₁ a₁ = fconcat₂ (F := F₂) v₂ a₂ ↔ v₁ = v₂ ∧ a₁ = a₂ := by
  constructor
  · intro h; exact fconcat₂_injective2 (n := n) (α₁ := α₁) (α₂ := α₂) (β₁ := β₁) (β₂ := β₂) h
  · intro ⟨hv, ha⟩; simp [hv, ha]

theorem fconcat₂_right_injective {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B}
    (v : (i : Fin n) → F₂ (α₁ i) (α₂ i)) :
    Function.Injective (fconcat₂ (F := F₂) v :
      F₂ β₁ β₂ → (i : Fin (n + 1)) → F₂ (Fin.vconcat α₁ β₁ i) (Fin.vconcat α₂ β₂ i)) := by
  intro x y h; exact (fconcat₂_inj (α₁ := α₁) (α₂ := α₂) v v x y).mp h |>.2

theorem fconcat₂_left_injective {α₁ : Fin n → A} {α₂ : Fin n → B} {β₁ : A} {β₂ : B} (a : F₂ β₁ β₂) :
    Function.Injective (fun v : (i : Fin n) → F₂ (α₁ i) (α₂ i) => fconcat₂ (F := F₂) v a) := by
  intro x y h; exact (fconcat₂_inj (α₁ := α₁) (α₂ := α₂) x y a a).mp h |>.1

@[simp]
theorem fappend₂_zero {α₁ : Fin m → A} {α₂ : Fin m → B} {β₁ : Fin 0 → A} {β₂ : Fin 0 → B}
    (u : (i : Fin m) → F₂ (α₁ i) (α₂ i)) :
    fappend₂ (F := F₂) u (!h⦃F₂⦄⟨β₁⟩⟨β₂⟩[] : (i : Fin 0) → F₂ (β₁ i) (β₂ i)) = u := rfl

@[simp]
theorem fappend₂_succ {α₁ : Fin m → A} {α₂ : Fin m → B}
    {β₁ : Fin (n + 1) → A} {β₂ : Fin (n + 1) → B}
    (u : (i : Fin m) → F₂ (α₁ i) (α₂ i)) (v : (i : Fin (n + 1)) → F₂ (β₁ i) (β₂ i)) :
    fappend₂ (F := F₂) u v =
      fconcat₂ (F := F₂) (fappend₂ (F := F₂) u (fun i => v (castSucc i))) (v (last n)) := by
  induction n <;> simp [fappend₂]

@[simp]
theorem fappend₂_left {α₁ : Fin m → A} {α₂ : Fin m → B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (u : (i : Fin m) → F₂ (α₁ i) (α₂ i)) (v : (i : Fin n) → F₂ (β₁ i) (β₂ i)) (i : Fin m) :
    fappend₂ (F := F₂) u v (castAdd n i) =
      cast (by simp [vappend_left]) (u i) := by
  induction n with
  | zero => simp [fappend₂]
  | succ n ih =>
    simp only [fappend₂_succ]
    have : castAdd (n + 1) i = castSucc (castAdd n i) := by ext; simp
    rw! [this, fconcat₂_castSucc, ih]
    simp

@[simp]
theorem fappend₂_right {α₁ : Fin m → A} {α₂ : Fin m → B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (u : (i : Fin m) → F₂ (α₁ i) (α₂ i)) (v : (i : Fin n) → F₂ (β₁ i) (β₂ i)) (i : Fin n) :
    fappend₂ (F := F₂) u v (natAdd m i) =
      cast (by simp [vappend_right]) (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [fappend₂_succ]
    by_cases h : i.val < n
    · have : natAdd m i = castSucc ⟨m + i.val, by simp [h]⟩ := by ext; simp
      rw! [this, fconcat₂_castSucc]
      have : ⟨m + i.val, by simp [h]⟩ = natAdd m ⟨i, h⟩ := by ext; simp
      rw! [this, ih]; simp
    · have hi : i = last n := by ext; simp; omega
      have : natAdd m i = last (m + n) := by ext; simp; omega
      rw! [this, fconcat₂_last, hi]

theorem fappend₂_ext {α₁ : Fin m → A} {α₂ : Fin m → B} {β₁ : Fin n → A} {β₂ : Fin n → B}
    (u₁ u₂ : (i : Fin m) → F₂ (α₁ i) (α₂ i)) (v₁ v₂ : (i : Fin n) → F₂ (β₁ i) (β₂ i)) :
    fappend₂ (F := F₂) u₁ v₁ = fappend₂ (F := F₂) u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  constructor
  · intro h; constructor
    · ext i
      have := congr_fun h (castAdd n i); simp at this
      exact cast_eq_cast_same_type _ _ this
    · ext i
      have := congr_fun h (natAdd m i); simp at this
      exact cast_eq_cast_same_type _ _ this
  · intro ⟨hu, hv⟩; simp [hu, hv]

end FunctorialBinary

section FunctorialUnary

variable {A : Sort u} {F : A → Sort v} {m n : ℕ} {α : A}

@[simp]
theorem fcons_zero {β : Fin n → A} (a : F α) (b : (i : Fin n) → F (β i)) :
    fcons a b 0 = cast (by simp [vcons_zero]) a := by
  induction n <;> rfl

@[simp]
theorem fcons_succ {β : Fin n → A} (a : F α) (v : (i : Fin n) → F (β i)) (i : Fin n) :
    fcons a v i.succ = cast (by simp [vcons_succ]) (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => rfl

@[simp]
theorem fcons_one {β : Fin (n + 1) → A} (a : F α) (v : (i : Fin (n + 1)) → F (β i)) :
    fcons a v 1 = v 0 := by
  induction n <;> rfl

-- Injectivity properties for fcons
theorem fcons_right_injective {β : Fin n → A} (a : F α) :
    Function.Injective (fcons a : ((i : Fin n) → F (β i)) → (i : Fin (n + 1)) → _) := by
  intro x y h
  ext i
  have := congr_fun h i.succ
  simp at this
  exact cast_eq_cast_same_type _ _ this

theorem fcons_left_injective {β : Fin n → A} (b : (i : Fin n) → F (β i)) :
    Function.Injective (fun (a : F α) => fcons a b) := by
  intro x y h
  have := congr_fun h 0
  simp at this
  exact cast_eq_cast_same_type _ _ this

theorem fcons_injective2 {β : Fin n → A} :
    Function.Injective2 (@fcons A F n α β) := by
  intro a₁ b₁ a₂ b₂ h
  constructor
  · have := congr_fun h 0
    simp at this
    exact cast_eq_cast_same_type _ _ this
  · ext i
    have := congr_fun h (succ i)
    simp at this
    exact cast_eq_cast_same_type _ _ this

theorem fcons_inj {β : Fin n → A} (a₁ a₂ : F α) (b₁ b₂ : (i : Fin n) → F (β i)) :
    fcons a₁ b₁ = fcons a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · intro i; have := fcons_injective2 i; exact this
  · intro ⟨ha, hb⟩
    rw [ha, hb]

@[simp]
theorem fconcat_zero {α : Fin 0 → A} {β : A} (a : F β) : !h⦃F⦄⟨α⟩[] :+ʰ a =
  fun i => match i with | 0 => a := rfl

@[simp]
theorem fconcat_castSucc {α : Fin n → A} {β : A}
    (v : (i : Fin n) → F (α i)) (b : F β) (i : Fin n) :
    (v :+ʰ⦃F⦄ b) (castSucc i) = cast (by simp [vconcat_castSucc]) (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp [fconcat]
    induction i using induction <;> simp [ih]

@[simp]
theorem fconcat_last {α : Fin n → A} {β : A} (v : (i : Fin n) → F (α i)) (b : F β) :
    fconcat v b (last n) = cast (by simp [vconcat_last]) b := by
  induction n with
  | zero => simp [fconcat]
  | succ n ih =>
    have : last (n + 1) = (last n).succ := by simp
    rw! [this, fconcat, fcons_succ, ih]
    rfl

-- Injectivity properties for fconcat
theorem fconcat_injective2 {α : Fin n → A} {β : A} :
    Function.Injective2 (@fconcat A F n α β) := by
  intro v₁ a₁ v₂ a₂ h
  constructor
  · ext i
    have := congr_fun h (castSucc i)
    simp at this
    exact cast_eq_cast_same_type _ _ this
  · have := congr_fun h (last n)
    simp at this
    exact cast_eq_cast_same_type _ _ this

theorem fconcat_inj {α : Fin n → A} {β : A}
    (v₁ v₂ : (i : Fin n) → F (α i)) (a₁ a₂ : F β) :
    fconcat v₁ a₁ = fconcat v₂ a₂ ↔ v₁ = v₂ ∧ a₁ = a₂ := by
  constructor
  · intro h; exact fconcat_injective2 h
  · intro ⟨hv, ha⟩
    rw [hv, ha]

theorem fconcat_right_injective {α : Fin n → A} {β : A} (v : (i : Fin n) → F (α i)) :
    Function.Injective (fconcat v : F β → (i : Fin (n + 1)) → F (vconcat α β i)) := by
  intro x y h
  exact (fconcat_inj v v x y).mp h |>.2

theorem fconcat_left_injective {α : Fin n → A} {β : A} (a : F β) :
    Function.Injective (fun v : (i : Fin n) → F (α i) => fconcat v a) := by
  intro x y h
  exact (fconcat_inj x y a a).mp h |>.1

/-! Functorial append (unary F) lemmas -/

@[simp]
theorem fappend_zero {β : Fin m → A} {α : Fin 0 → A}
    (u : (i : Fin m) → F (β i)) :
    fappend u (!h⦃F⦄⟨α⟩[] : (i : Fin 0) → F (α i)) = u := rfl

@[simp]
theorem fappend_succ {α : Fin m → A} {β : Fin (n + 1) → A}
    (u : (i : Fin m) → F (α i)) (v : (i : Fin (n + 1)) → F (β i)) :
    fappend u v = fconcat (fappend u (fun i => v (castSucc i))) (v (last n)) := by
  induction n <;> simp [fappend]

@[simp]
theorem fappend_left {α : Fin m → A} {β : Fin n → A}
    (u : (i : Fin m) → F (α i)) (v : (i : Fin n) → F (β i)) (i : Fin m) :
    fappend u v (castAdd n i) = cast (by simp [vappend_left]) (u i) := by
  induction n with
  | zero => simp [fappend]
  | succ n ih =>
    simp only [fappend_succ]
    have : castAdd (n + 1) i = castSucc (castAdd n i) := by ext; simp
    rw! [this, fconcat_castSucc, ih]
    simp

@[simp]
theorem fappend_right {α : Fin m → A} {β : Fin n → A}
    (u : (i : Fin m) → F (α i)) (v : (i : Fin n) → F (β i)) (i : Fin n) :
    fappend u v (natAdd m i) = cast (by simp [vappend_right]) (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [fappend_succ]
    by_cases h : i.val < n
    · have : natAdd m i = (castSucc (⟨m + i.val, by simp [h]⟩)) := by ext; simp
      rw! [this, fconcat_castSucc]
      have : ⟨m + i.val, by simp [h]⟩ = natAdd m ⟨i, h⟩ := by ext; simp
      rw! [this, ih]
      simp
    · have hi : i = last n := by ext; simp; omega
      have : natAdd m i = last (m + n) := by ext; simp; omega
      rw! [this, fconcat_last, hi]

theorem fappend_ext {α : Fin m → A} {β : Fin n → A}
    (u₁ u₂ : (i : Fin m) → F (α i)) (v₁ v₂ : (i : Fin n) → F (β i)) :
    fappend u₁ v₁ = fappend u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  constructor
  · intro h
    constructor
    · ext i
      have := congr_fun h (castAdd n i)
      simp at this
      exact cast_eq_cast_same_type _ _ this
    · ext i
      have := congr_fun h (natAdd m i)
      simp at this
      exact cast_eq_cast_same_type _ _ this
  · intro ⟨hu, hv⟩
    rw [hu, hv]

end FunctorialUnary

/-! ### Lemmas for heterogeneous vectors -/

@[simp]
theorem hcons_zero {β : Fin n → Sort u} (a : α) (b : (i : Fin n) → β i) :
    hcons a b 0 = cast (vcons_zero α β).symm a := by
  simp [hcons, fcons_zero]

@[simp]
theorem hcons_succ {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) (i : Fin n) :
    hcons a v i.succ = cast (vcons_succ α β i).symm (v i) := by
  simp [hcons, fcons_succ]

@[simp]
theorem hcons_one {β : Fin (n + 1) → Sort u} (a : α) (v : (i : Fin (n + 1)) → β i) :
    hcons a v 1 = cast (vcons_succ α β 0).symm (v 0) := by
  simp [hcons, fcons_one]

theorem hcons_eq_cons {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
    hcons a v = cons (α := vcons α β) (hcons a v 0) (fun i => hcons a v i.succ) := by
  ext i
  induction i using induction <;> simp

@[simp]
theorem hconcat_zero {α : Fin 0 → Sort u} {β : Sort u} (a : β) :
    hconcat !h⟨α⟩[] a = fun i => match i with | 0 => a := rfl

@[simp]
theorem hconcat_castSucc {α : Fin n → Sort u} {β : Sort u}
    (v : (i : Fin n) → α i) (b : β) (i : Fin n) :
    hconcat v b (castSucc i) = cast (vconcat_castSucc α β i).symm (v i) := by
  simp [hconcat, fconcat_castSucc]

@[simp]
theorem hconcat_last {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
    hconcat v b (last n) = cast (vconcat_last α β).symm b := by
  simp [hconcat, fconcat_last]

theorem hconcat_eq_snoc {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
    hconcat v b = snoc (α := vconcat α β)
      (fun i => cast (vconcat_castSucc _ _ i).symm (v i))
      (cast (vconcat_last _ _).symm b) := by
  induction n with
  | zero => ext; simp [hconcat, snoc, fconcat]; split; simp
  | succ n ih =>
    ext i; sorry
    -- split <;> simp [snoc]

-- Injectivity properties for cons (from functorial versions)
theorem hcons_right_injective {β : Fin n → Sort u} (a : α) :
    Function.Injective (hcons a : ((i : Fin n) → β i) → (i : Fin (n + 1)) → vcons α β i) := by
  exact fcons_right_injective (F := id) a

theorem hcons_left_injective {α : Sort u} {β : Fin n → Sort u} (b : (i : Fin n) → β i) :
    Function.Injective (fun (a : α) => hcons a b) := by
  exact fcons_left_injective (F := id) b

theorem hcons_injective2 {α : Sort u} {β : Fin n → Sort u} :
    Function.Injective2 (@hcons n α β) := by
  exact fcons_injective2 (F := id)

theorem hcons_inj {α : Sort u} {β : Fin n → Sort u} (a₁ a₂ : α) (b₁ b₂ : (i : Fin n) → β i) :
    hcons a₁ b₁ = hcons a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  exact fcons_inj (F := id) a₁ a₂ b₁ b₂

-- Empty tuple properties
@[simp]
theorem hcons_fin_zero {α : Sort u} {β : Fin 0 → Sort u} (a : α) (v : (i : Fin 0) → β i) :
    hcons a v = fun i => match i with | 0 => a := by
  ext i; rfl

theorem hconcat_hcons {α : Sort u} {β : Fin n → Sort u} {γ : Sort u} (a : α) (v : (i : Fin n) → β i) (c : γ) :
    True := by
  sorry

-- Init/concat properties
theorem dinit_hconcat {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
    True := by
  sorry

theorem hconcat_init_self {α : Fin n.succ → Sort u} (v : (i : Fin (n + 1)) → α i) :
    True := by
  sorry

-- Injectivity properties for concat (from functorial versions)
theorem hconcat_injective2 {α : Fin n → Sort u} {β : Sort u} :
    Function.Injective2 (@hconcat n α β) := by
  exact fconcat_injective2 (F := id)

theorem hconcat_inj {α : Fin n → Sort u} {β : Sort u} (v₁ v₂ : (i : Fin n) → α i) (a₁ a₂ : β) :
    hconcat v₁ a₁ = hconcat v₂ a₂ ↔ v₁ = v₂ ∧ a₁ = a₂ := by
  exact fconcat_inj (F := id) v₁ v₂ a₁ a₂

theorem hconcat_right_injective {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) :
    Function.Injective (hconcat v : β → (i : Fin (n + 1)) → vconcat α β i) := by
  exact fconcat_right_injective (F := id) v

theorem hconcat_left_injective {α : Fin n → Sort u} {β : Sort u} (a : β) :
    Function.Injective (fun v : (i : Fin n) → α i => hconcat v a) := by
  exact fconcat_left_injective (F := id) a

@[simp]
theorem happend_zero {β : Fin m → Sort u} {α : Fin 0 → Sort u} (u : (i : Fin m) → β i) :
    happend u !h⟨α⟩[] = u :=
  fappend_zero (F := id) u

@[simp]
theorem happend_empty {α : Fin m → Sort u} {β : Fin 0 → Sort u} (v : (i : Fin m) → α i) :
    happend v !h⟨β⟩[] = v := rfl

@[simp]
theorem happend_succ {α : Fin m → Sort u} {β : Fin (n + 1) → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin (n + 1)) → β i) :
    happend u v = hconcat (happend u (fun i => v (castSucc i))) (v (last n)) := by
  exact fappend_succ (F := id) u v

@[simp]
theorem dempty_happend {α : Fin 0 → Sort u} {β : Fin n → Sort u} (v : (i : Fin n) → β i) :
    happend !d⟨α⟩[] v =
      fun i : Fin (0 + n) => cast (by simp) (v <| i.cast (by omega)) := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    simp [happend]
    ext i
    by_cases h : i.val < n
    · have : i = Fin.castSucc (⟨i.val, by simp [h]⟩) := by ext; simp
      rw [this, fconcat_castSucc]
      simp [Fin.cast]
      sorry
    · have : i = Fin.last (0 + n) := by ext; simp; omega
      rw! [this, fconcat_last]
      simp only [Fin.last, Fin.cast_mk]
      sorry

-- Index access for append
@[simp]
theorem happend_left {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (i : Fin m) :
    happend u v (castAdd n i) = cast (vappend_left α β i).symm (u i) := by
  simp [happend, fappend_left]

@[simp]
theorem happend_right {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (i : Fin n) :
    happend u v (natAdd m i) = cast (vappend_right α β i).symm (v i) := by
  simp [happend, fappend_right]

theorem happend_eq_addCases {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) :
    happend u v = addCases (motive := vappend α β)
      (fun i => cast (vappend_left α β i).symm (u i))
      (fun i => cast (vappend_right α β i).symm (v i)) := by
  ext i
  by_cases h : i.val < m
  · have : i = castAdd n ⟨i, by omega⟩ := by ext; simp
    rw [this]
    simp only [addCases_left, happend_left]
  · have : i = natAdd m ⟨i.val - m, by omega⟩ := by ext; simp; omega
    rw [this]
    simp only [addCases_right, happend_right]

theorem happend_assoc {α : Fin m → Sort u} {β : Fin n → Sort u} {p : ℕ} {γ : Fin p → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (w : (i : Fin p) → γ i) :
    happend (happend u v) w =
      fun i => cast (by simp [vappend_assoc])
        (happend u (happend v w) (i.cast (by omega))) := by sorry
  -- induction p with
  -- | zero => simp [append]
  -- | succ p ih =>
  --   simp [append, ih, concat_last]
  --   ext i
  --   simp [Fin.castSucc, Fin.last, concat_eq_fin_snoc, Fin.snoc]
  --   by_cases h : i.val < m + n + p
  --   · simp [h]

-- Relationship with cons/concat
theorem happend_hcons {β : Fin m → Sort u} {γ : Fin n → Sort u}
    (a : α) (u : (i : Fin m) → β i) (v : (i : Fin n) → γ i) :
    True := by
  sorry

theorem happend_hconcat {α : Fin m → Sort u} {β : Fin n → Sort u} {γ : Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (c : γ) :
    True := by
  sorry

-- Compatibility lemmas
theorem happend_left_eq_hcons {α : Fin 1 → Sort u} {β : Fin n → Sort u}
    (a : (i : Fin 1) → α i) (v : (i : Fin n) → β i) :
    True := by
  sorry

theorem happend_right_eq_hconcat {α : Fin m → Sort u} {β : Fin 1 → Sort u}
    (u : (i : Fin m) → α i) (a : (i : Fin 1) → β i) :
    happend u a = hconcat u (a 0) := by
  sorry

theorem happend_ext {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u₁ u₂ : (i : Fin m) → α i) (v₁ v₂ : (i : Fin n) → β i) :
    happend u₁ v₁ = happend u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  simp [happend]
  exact fappend_ext (F := id) u₁ u₂ v₁ v₂

theorem ext_hcons {β : Fin n → Sort u} (a₁ a₂ : α) (v₁ v₂ : (i : Fin n) → β i) :
    hcons a₁ v₁ = hcons a₂ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ :=
  hcons_inj a₁ a₂ v₁ v₂

theorem hcons_eq_hcons_iff {β : Fin n → Sort u} (a₁ a₂ : α) (v₁ v₂ : (i : Fin n) → β i) :
    hcons a₁ v₁ = hcons a₂ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ :=
  hcons_inj a₁ a₂ v₁ v₂

-- Two tuples are equal iff they are equal at every index (with casting)
theorem dext_iff {α : Fin n → Sort u} {v w : (i : Fin n) → α i} :
    v = w ↔ ∀ i, v i = w i := by
  aesop

-- Interaction between operations
theorem hcons_happend_comm {β : Fin m → Sort u} {γ : Fin n → Sort u}
    (a : α) (u : (i : Fin m) → β i) (v : (i : Fin n) → γ i) :
    True := by
  sorry

theorem happend_singleton {α : Fin m → Sort u} {β : Sort u} (u : (i : Fin m) → α i) (a : β) :
    True := by
  sorry

theorem singleton_happend {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
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

-- theorem cast_hconcat {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
--     cast rfl (fun _ => rfl) (hconcat v b) = hconcat v b := by
--   simp only [Fin.cast_eq_self, hconcat_eq_fin_snoc]
--   ext _
--   simp [cast]

-- theorem cast_happend {α : Fin m → Sort u} {β : Fin n → Sort u}
--     (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) :
--     cast rfl (fun _ => rfl) (happend u v) = happend u v := by
--   simp only [Fin.cast_eq_self, happend_eq_addCases]
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
