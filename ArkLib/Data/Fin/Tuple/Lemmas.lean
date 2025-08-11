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
--       fun i => cast (by simp) (dcons a (dappend (motive := fun i => motive (cast (by omega) i)) u v)
--         (i.cast (Nat.succ_add m n))) := by
--   sorry

@[simp]
theorem vappend_vcons (a : α) (u : Fin m → α) (v : Fin n → α) :
    vappend (vcons a u) v = (vcons a (vappend u v)) ∘ Fin.cast (Nat.succ_add m n) := by
  simp only [vappend_eq_append, vcons_eq_cons]
  exact append_cons a u v

-- theorem dappend_dconcat {motive : Fin (m + (n + 1)) → Sort u} (u : (i : Fin m) → motive (cast (by omega) (castAdd (n + 1) i)))
--     (v : (i : Fin n) → motive (cast (by omega) (natAdd m (castSucc i)))) (a : motive (cast (by omega) (natAdd m (last n)))) :
--     dappend (motive := fun i => motive (cast (by omega) i)) u (dconcat v a) =
--       dconcat (motive := fun i => motive (cast (by omega) i)) (dappend u v) a := by
--   sorry

theorem vappend_vconcat (u : Fin m → α) (v : Fin n → α) (a : α) :
    vappend u (vconcat v a) = vconcat (vappend u v) a := by
  simp only [vappend_eq_append, vconcat_eq_snoc]
  exact append_snoc u v a

-- -- Compatibility with standard library (matching Fin.append naming)
-- theorem dappend_left_eq_dcons {motive : Fin (1 + n) → Sort u} (a : (i : Fin 1) → motive (cast (by omega) (castAdd n i)))
--     (v : (i : Fin n) → motive (cast (by omega) (natAdd 1 i))) :
--     dappend (motive := fun i => motive (cast (by omega) i)) a v =
--       fun i => cast (by simp) (dcons (a 0) v (i.cast (Nat.add_comm 1 n))) := by
--   sorry

theorem vappend_left_eq_cons (a : Fin 1 → α) (v : Fin n → α) :
    vappend a v = (vcons (a 0) v) ∘ Fin.cast (Nat.add_comm 1 n) := by
  simp only [vappend_eq_append, vcons_eq_cons]
  exact append_left_eq_cons a v

-- theorem dappend_right_eq_dconcat {motive : Fin (m + 1) → Sort u} (u : (i : Fin m) → motive (cast (by omega) (castAdd 1 i)))
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

@[simp]
theorem tcons_zero {β : Fin n → Sort u} (a : α) (b : (i : Fin n) → β i) :
    tcons a b 0 = cast (vcons_zero α β).symm a := by
  induction n <;> rfl

@[simp]
theorem tcons_succ {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) (i : Fin n) :
    tcons a v i.succ = cast (vcons_succ α β i).symm (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => rfl

@[simp]
theorem tcons_one {β : Fin (n + 1) → Sort u} (a : α) (v : (i : Fin (n + 1)) → β i) :
    tcons a v 1 = cast (vcons_succ α β 0).symm (v 0) := by
  induction n <;> rfl

theorem tcons_eq_cons {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
    tcons a v = cons (α := vcons α β) (tcons a v 0) (fun i => tcons a v i.succ) := by
  ext i
  induction i using induction <;> simp

@[simp]
theorem tconcat_zero {α : Fin 0 → Sort u} {β : Sort u} (a : β) :
    tconcat !t⟨α⟩[] a = fun i => match i with | 0 => a := rfl

@[simp]
theorem tconcat_castSucc {α : Fin n → Sort u} {β : Sort u}
    (v : (i : Fin n) → α i) (b : β) (i : Fin n) :
    tconcat v b (castSucc i) = cast (vconcat_castSucc α β i).symm (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp [tconcat]
    induction i using induction <;> simp [ih]

@[simp]
theorem tconcat_last {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
    tconcat v b (last n) = cast (vconcat_last α β).symm b := by
  induction n with
  | zero => simp [tconcat]
  | succ n ih =>
    have : last (n + 1) = (last n).succ := by simp
    rw! [this, tconcat, tcons_succ, ih]
    rfl

theorem tconcat_eq_fin_snoc {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
    tconcat v b = snoc (α := vconcat α β)
      (fun i => cast (vconcat_castSucc _ _ i).symm (v i))
      (cast (vconcat_last _ _).symm b) := by
  induction n with
  | zero => ext; simp [tconcat, snoc]; split; simp
  | succ n ih =>
    simp [tconcat, tcons, ih]
    ext i
    split <;> simp [snoc]

-- theorem tail_cons {β : Fin n → Sort u} (a : α) (b : FinTuple n β) (i : Fin n) :
--     True := by
--   sorry

-- theorem tcons_self_tail {α : Fin n.succ → Sort u} (v : (i : Fin (n + 1)) → α i) :
--     True := by
--   sorry

-- Injectivity properties for cons
theorem tcons_right_injective {β : Fin n → Sort u} (a : α) :
    Function.Injective (tcons a : ((i : Fin n) → β i) → (i : Fin (n + 1)) → vcons α β i) := by
  intro x y h
  rw [tcons_eq_cons, tcons_eq_cons] at h
  simp [tcons_eq_cons] at h
  apply funext_iff.mp at h
  ext i
  have := h i
  have aux_lemma {α β : Sort u} {h : α = β} (x y : α) (hCast : cast h x = cast h y) : x = y := by
    subst h; simp_all
  exact aux_lemma (x i) (y i) this

theorem tcons_left_injective {α : Sort u} {β : Fin n → Sort u} (b : (i : Fin n) → β i) :
    Function.Injective (fun (a : α) => tcons a b) := by
  simp [tcons_eq_cons]
  intro x y h
  simp at h
  have aux_lemma {α β : Sort u} {h : α = β} (x y : α) (hCast : cast h x = cast h y) : x = y := by
    subst h; simp_all
  exact aux_lemma x y h

theorem tcons_injective2 {α : Sort u} {β : Fin n → Sort u} :
    Function.Injective2 (@tcons n α β) := by
  sorry

theorem tcons_inj {α : Sort u} {β : Fin n → Sort u} (a₁ a₂ : α) (b₁ b₂ : (i : Fin n) → β i) :
    tcons a₁ b₁ = tcons a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  sorry

-- Empty tuple properties
@[simp]
theorem tcons_fin_zero {α : Sort u} {β : Fin 0 → Sort u} (a : α) (v : (i : Fin 0) → β i) :
    tcons a v = fun i => match i with | 0 => a := by
  ext i; rfl

theorem tconcat_tcons {α : Sort u} {β : Fin n → Sort u} {γ : Sort u} (a : α) (v : (i : Fin n) → β i) (c : γ) :
    True := by
  sorry

-- Init/concat properties
theorem dinit_tconcat {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
    True := by
  sorry

theorem tconcat_init_self {α : Fin n.succ → Sort u} (v : (i : Fin (n + 1)) → α i) :
    True := by
  sorry

-- Injectivity properties for concat
theorem tconcat_injective2 {α : Fin n → Sort u} {β : Sort u} :
    Function.Injective2 (@tconcat n α β) := by
  sorry

theorem tconcat_inj {α : Fin n → Sort u} {β : Sort u} (v₁ v₂ : (i : Fin n) → α i) (a₁ a₂ : β) :
    tconcat v₁ a₁ = tconcat v₂ a₂ ↔ v₁ = v₂ ∧ a₁ = a₂ := by
  sorry

theorem tconcat_right_injective {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) :
    Function.Injective (tconcat v : β → (i : Fin (n + 1)) → vconcat α β i) := by
  sorry

theorem tconcat_left_injective {α : Fin n → Sort u} {β : Sort u} (a : β) :
    Function.Injective (fun v : (i : Fin n) → α i => tconcat v a) := by
  sorry

@[simp]
theorem tappend_zero {β : Fin m → Sort u} {α : Fin 0 → Sort u} (u : (i : Fin m) → β i) :
    tappend u !t⟨α⟩[] = u := rfl

@[simp]
theorem tappend_empty {α : Fin m → Sort u} (v : (i : Fin m) → α i) : tappend v !t[] = v := rfl

@[simp]
theorem tappend_succ {α : Fin m → Sort u} {β : Fin (n + 1) → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin (n + 1)) → β i) :
    tappend u v = tconcat (tappend u (fun i => v (castSucc i))) (v (last n)) := by
  induction n <;> simp [tappend]

@[simp]
theorem dempty_tappend {α : Fin 0 → Sort u} {β : Fin n → Sort u} (v : (i : Fin n) → β i) :
    tappend !d⟨α⟩[] v =
      fun i : Fin (0 + n) => cast (by simp) (v <| i.cast (by omega)) := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    simp [tappend, ih]
    ext i
    by_cases h : i.val < n
    · have : i = Fin.castSucc (⟨i.val, by simp [h]⟩) := by ext; simp
      rw [this, tconcat_castSucc]
      simp [Fin.cast]
    · have : i = Fin.last (0 + n) := by ext; simp; omega
      rw! [this, tconcat_last]
      simp only [Fin.last, Fin.cast_mk]
      sorry

-- Index access for append
@[simp]
theorem tappend_left {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (i : Fin m) :
    tappend u v (castAdd n i) = cast (vappend_left α β i).symm (u i) := by
  induction n with
  | zero => simp [tappend]
  | succ n ih =>
    simp only [tappend_succ]
    have : castAdd (n + 1) i = castSucc (castAdd n i) := by ext; simp
    rw! [this, tconcat_castSucc, ih]
    simp

@[simp]
theorem tappend_right {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (i : Fin n) :
    tappend u v (natAdd m i) = cast (vappend_right α β i).symm (v i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [tappend_succ]
    by_cases h : i.val < n
    · have : natAdd m i = (castSucc (⟨m + i.val, by simp [h]⟩)) := by ext; simp
      rw! [this, tconcat_castSucc]
      have : ⟨m + i.val, by simp [h]⟩ = natAdd m ⟨i, h⟩ := by ext; simp
      rw! [this, ih]
      simp
    · have hi : i = last n := by ext; simp; omega
      have : natAdd m i = last (m + n) := by ext; simp; omega
      rw! [this, tconcat_last, hi]

theorem tappend_eq_addCases {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) :
    tappend u v = addCases (motive := vappend α β)
      (fun i => cast (vappend_left α β i).symm (u i))
      (fun i => cast (vappend_right α β i).symm (v i)) := by
  ext i
  by_cases h : i.val < m
  · have : i = castAdd n ⟨i, by omega⟩ := by ext; simp
    rw [this]
    simp only [addCases_left, tappend_left]
  · have : i = natAdd m ⟨i.val - m, by omega⟩ := by ext; simp; omega
    rw [this]
    simp only [addCases_right, tappend_right]

theorem tappend_assoc {α : Fin m → Sort u} {β : Fin n → Sort u} {p : ℕ} {γ : Fin p → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (w : (i : Fin p) → γ i) :
    tappend (tappend u v) w =
      fun i => cast (by simp [vappend_assoc])
        (tappend u (tappend v w) (i.cast (by omega))) := by sorry
  -- induction p with
  -- | zero => simp [append]
  -- | succ p ih =>
  --   simp [append, ih, concat_last]
  --   ext i
  --   simp [Fin.castSucc, Fin.last, concat_eq_fin_snoc, Fin.snoc]
  --   by_cases h : i.val < m + n + p
  --   · simp [h]

-- Relationship with cons/concat
theorem tappend_tcons {β : Fin m → Sort u} {γ : Fin n → Sort u}
    (a : α) (u : (i : Fin m) → β i) (v : (i : Fin n) → γ i) :
    True := by
  sorry

theorem tappend_tconcat {α : Fin m → Sort u} {β : Fin n → Sort u} {γ : Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) (c : γ) :
    True := by
  sorry

-- Compatibility lemmas
theorem tappend_left_eq_tcons {α : Fin 1 → Sort u} {β : Fin n → Sort u}
    (a : (i : Fin 1) → α i) (v : (i : Fin n) → β i) :
    True := by
  sorry

theorem tappend_right_eq_tconcat {α : Fin m → Sort u} {β : Fin 1 → Sort u}
    (u : (i : Fin m) → α i) (a : (i : Fin 1) → β i) :
    tappend u a = tconcat u (a 0) := by
  sorry

-- Extensionality properties
theorem tappend_ext {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u₁ u₂ : (i : Fin m) → α i) (v₁ v₂ : (i : Fin n) → β i) :
    tappend u₁ v₁ = tappend u₂ v₂ ↔ u₁ = u₂ ∧ v₁ = v₂ := by
  sorry

theorem ext_tcons {β : Fin n → Sort u} (a₁ a₂ : α) (v₁ v₂ : (i : Fin n) → β i) :
    tcons a₁ v₁ = tcons a₂ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ := by
  sorry

theorem tcons_eq_tcons_iff {β : Fin n → Sort u} (a₁ a₂ : α) (v₁ v₂ : (i : Fin n) → β i) :
    tcons a₁ v₁ = tcons a₂ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ := by
  sorry

-- Two tuples are equal iff they are equal at every index (with casting)
theorem dext_iff {α : Fin n → Sort u} {v w : (i : Fin n) → α i} :
    v = w ↔ ∀ i, v i = w i := by
  aesop

-- Interaction between operations
theorem tcons_tappend_comm {β : Fin m → Sort u} {γ : Fin n → Sort u}
    (a : α) (u : (i : Fin m) → β i) (v : (i : Fin n) → γ i) :
    True := by
  sorry

theorem tappend_singleton {α : Fin m → Sort u} {β : Sort u} (u : (i : Fin m) → α i) (a : β) :
    True := by
  sorry

theorem singleton_tappend {β : Fin n → Sort u} (a : α) (v : (i : Fin n) → β i) :
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

-- theorem cast_tconcat {α : Fin n → Sort u} {β : Sort u} (v : (i : Fin n) → α i) (b : β) :
--     cast rfl (fun _ => rfl) (tconcat v b) = tconcat v b := by
--   simp only [Fin.cast_eq_self, tconcat_eq_fin_snoc]
--   ext _
--   simp [cast]

-- theorem cast_tappend {α : Fin m → Sort u} {β : Fin n → Sort u}
--     (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) :
--     cast rfl (fun _ => rfl) (tappend u v) = tappend u v := by
--   simp only [Fin.cast_eq_self, tappend_eq_addCases]
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
