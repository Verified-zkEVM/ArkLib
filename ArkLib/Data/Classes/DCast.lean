/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.DepRewrite

/-! # Dependent casts

This file contains type classes for dependent or custom cast operations

This allows us to state theorems with more refined casts, without which we cannot make progress in
proving them -/

universe u v w

section Prelude

-- Some missing theorems about `cast` and `congrArg`

theorem cast_eq_cast_iff {α β γ : Sort u} {h : α = γ} {h' : β = γ} {a : α} {b : β} :
    cast h a = cast h' b ↔ a = cast (h'.trans h.symm) b := by cases h'; cases h; simp

theorem cast_symm {α β : Sort u} {h : α = β} {a : α} {b : β} :
    cast h a = b ↔ a = cast h.symm b := by
  cases h; simp

theorem congrArg₃ {α β γ δ : Sort*} {f : α → β → γ → δ} {a a' : α} {b b' : β} {c c' : γ}
    (h : a = a') (h' : b = b') (h'' : c = c') : f a b c = f a' b' c' := by
  cases h; cases h'; cases h''; rfl

theorem congrArg₄ {α β γ δ ε : Sort*} {f : α → β → γ → δ → ε} {a a' : α} {b b' : β} {c c' : γ}
    {d d' : δ} (h : a = a') (h' : b = b') (h'' : c = c') (h''' : d = d') :
      f a b c d = f a' b' c' d' := by
  cases h; cases h'; cases h''; cases h'''; rfl

end Prelude

/-- `DCast` is a type class for custom cast operations on an indexed type family `β a`

We require the cast operation `dcast`, along with the property that `dcast` reduces to `id` under
reflexivity. -/
class DCast (α : Sort*) (β : α → Sort*) where
  dcast : ∀ {a a' : α}, a = a' → β a → β a'
  dcast_id : ∀ {a : α}, dcast (Eq.refl a) = id

export DCast (dcast dcast_id)
attribute [simp] dcast_id

section DCast

variable {α : Sort*} {β : α → Sort*} [DCast α β] {a a' a'' : α} {b : β a} {b' : β a'}

/-- The default instance for `DCast` -/
instance (priority := low) : DCast α β where
  dcast h := cast (congrArg β h)
  dcast_id := by intro a; funext b; simp only [cast_eq, id_eq]

@[simp]
theorem dcast_eq : dcast (Eq.refl a) b = b := by
  simp

theorem dcast_symm (ha : a = a') (hb : dcast ha b = b') : dcast (ha.symm) b' = b := by
  cases ha; cases hb; simp

@[simp]
theorem dcast_trans (h : a = a') (h' : a' = a'') :
    dcast h' (dcast h b) = dcast (h.trans h') b := by
  cases h; cases h'; simp

theorem dcast_eq_dcast_iff (h : a = a'') (h' : a' = a'') :
    dcast h b = dcast h' b' ↔ b = dcast (h'.trans h.symm) b' := by
  cases h; cases h'; simp

theorem heq_of_dcast (ha : a = a') (hb : dcast ha b = b') : HEq b b' := by
  cases ha; cases hb; simp

theorem dcast_fun {γ : (a : α) → β a → Sort*} {f : (b : β a) → γ a b} :
    f (dcast rfl b) = dcast (α := β a) (β := γ a) dcast_eq.symm (f b) := by
  rw! [dcast_eq]
  exact dcast_eq.symm

-- TODO: figure out the most general form of these composition / naturality theorems

theorem dcast_fun₂ {a₁ a₂ a₁' a₂' : α} {h₁ : a₁ = a₁'} {h₂ : a₂ = a₂'} {f : α → α → α}
    {g : (a₁ : α) → (a₂ : α) → β a₁ → β a₂ → β (f a₁ a₂)} {b₁ : β a₁} {b₂ : β a₂} :
    dcast (by cases h₁; cases h₂; rfl) (g a₁ a₂ b₁ b₂) = g a₁' a₂' (dcast h₁ b₁) (dcast h₂ b₂) := by
  cases h₁; cases h₂; simp

theorem dcast_eq_root_cast (h : a = a') : dcast h b = _root_.cast (congrArg β h) b := by
  cases h; simp

end DCast

/-- `DCast₂` is a type class for custom cast operations on a doubly-indexed type family `γ a b`,
  given an underlying dependent cast `DCast α β`

We require the cast operation `dcast₂`, along with the property that `dcast₂` reduces to `id` under
reflexivity. -/
class DCast₂ (α : Sort*) (β : α → Sort*) (γ : (a : α) → β a → Sort*) [DCast α β] where
  dcast₂ : ∀ {a a' : α} {b : β a} {b' : β a'},
    (ha : a = a') → (dcast ha b = b') → γ a b → γ a' b'
  dcast₂_id : ∀ {a : α} {b : β a}, dcast₂ (Eq.refl a) dcast_eq = (id : γ a b → γ a b)

export DCast₂ (dcast₂ dcast₂_id)
attribute [simp] dcast₂_id

section DCast₂

variable {α : Sort*} {β : α → Sort*} {γ : (a : α) → β a → Sort*} [DCast α β] [DCast₂ α β γ]
  {a a' a'' : α} {b : β a} {b' : β a'} {b'' : β a''} {c : γ a b} {c' : γ a' b'} {c'' : γ a'' b''}

/-- Default instance for `DCast₂` -/
instance (priority := low) : DCast₂ α β γ where
  dcast₂ ha hb c := by
    refine cast ?_ c
    cases ha; simp at hb; cases hb; rfl
  dcast₂_id := by intros; rfl

@[simp]
theorem dcast₂_eq : dcast₂ (Eq.refl a) dcast_eq c = c := by
  simp

@[simp]
theorem dcast₂_eq' (h : a = a) (h' : dcast h b = b) : dcast₂ h h' c = c := by
  cases h; simp

theorem dcast₂_symm (ha : a = a') (hb : dcast ha b = b') (hc : dcast₂ ha hb c = c') :
    dcast₂ ha.symm (dcast_symm ha hb) c' = c := by
  cases ha; simp at hb; cases hb; simp at hc; cases hc; simp

@[simp]
theorem dcast₂_trans (ha : a = a') (ha' : a' = a'')
    (hb : dcast ha b = b') (hb' : dcast ha' b' = b'') :
      dcast₂ ha' hb' (dcast₂ ha hb c) = dcast₂ (ha.trans ha') (by simp [← hb', ← hb]) c := by
  cases ha; simp at hb; cases hb; simp

theorem dcast₂_eq_dcast₂_iff (ha : a = a'') (ha' : a' = a'')
    (hb : dcast ha b = b'') (hb' : dcast ha' b' = b'') :
    dcast₂ ha hb c = dcast₂ ha' hb' c' ↔
      c = dcast₂ (ha'.trans ha.symm)
        ((dcast_eq_dcast_iff ha ha').mp (hb.trans hb'.symm)).symm c' := by
  cases ha; cases ha'; simp at hb; cases hb; simp at hb'; cases hb'; simp

theorem dcast₂_dcast : dcast₂ rfl rfl c = dcast dcast_eq.symm c := by
  rw! [dcast_eq]; simp

instance instDCast₁₂ : DCast (β a) (γ a) where
  dcast hb c := dcast₂ (Eq.refl a) (by simp [hb]) c
  dcast_id := by intros; ext c; exact dcast₂_eq

instance instDCastPSigma : DCast ((a : α) ×' β a) (fun a => γ a.1 a.2) where
  dcast hab c := dcast₂ (by cases hab; simp) (by cases hab; simp) c
  dcast_id := by intros; ext c; simp

instance instDCastSigma {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    [DCast α β] [DCast₂ α β γ] : DCast ((a : α) × β a) (fun a => γ a.1 a.2) where
  dcast hab c := dcast₂ (by cases hab; simp) (by cases hab; simp) c
  dcast_id := by intros; ext c; simp

instance instDCastForall : DCast α (fun a => ∀ b : β a, γ a b) where
  dcast ha f := fun b => dcast₂ ha ((dcast_trans ha.symm ha).trans dcast_eq) (f (dcast ha.symm b))
  dcast_id := by
    intros a; funext f; funext b
    simp
    rw! [dcast_eq]
    simp

end DCast₂

/-- `DCast₃` is a type class for custom cast operations on a triply-indexed type family `δ a b c`,
  given underlying dependent casts `DCast α β` and `DCast₂ α β γ`

We require the cast operation `dcast₃`, along with the property that `dcast₃` reduces to `id` under
reflexivity. -/
class DCast₃ (α : Sort*) (β : α → Sort*) (γ : (a : α) → β a → Sort*)
    (δ : (a : α) → (b : β a) → γ a b → Sort*) [DCast α β] [DCast₂ α β γ] where
  dcast₃ : ∀ {a a' : α} {b : β a} {b' : β a'} {c : γ a b} {c' : γ a' b'},
    (ha : a = a') → (hb : dcast ha b = b') → (hc : dcast₂ ha hb c = c') → δ a b c → δ a' b' c'
  dcast₃_id : ∀ {a : α} {b : β a} {c : γ a b},
    dcast₃ (Eq.refl a) dcast_eq dcast₂_eq = (id : δ a b c → δ a b c)

export DCast₃ (dcast₃ dcast₃_id)
attribute [simp] dcast₃_id

section DCast₃

variable {α : Sort*} {β : α → Sort*} {γ : (a : α) → β a → Sort*}
  {δ : (a : α) → (b : β a) → γ a b → Sort*}
  [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ]
  {a a' a'' : α} {b : β a} {b' : β a'} {b'' : β a''}
  {c : γ a b} {c' : γ a' b'} {c'' : γ a'' b''}
  {d : δ a b c} {d' : δ a' b' c'} {d'' : δ a'' b'' c''}

/-- Default instance for `DCast₃` -/
instance (priority := low) : DCast₃ α β γ δ where
  dcast₃ ha hb hc d := by
    refine cast ?_ d
    cases ha; simp at hb; cases hb; simp at hc; cases hc; rfl
  dcast₃_id := by intros; rfl

@[simp]
theorem dcast₃_eq : dcast₃ (Eq.refl a) dcast_eq dcast₂_eq d = d := by
  simp

theorem dcast₃_symm (ha : a = a') (hb : dcast ha b = b') (hc : dcast₂ ha hb c = c')
    (hd : dcast₃ ha hb hc d = d') :
    dcast₃ ha.symm (dcast_symm ha hb) (dcast₂_symm ha hb hc) d' = d := by
  cases ha; simp at hb; cases hb; simp at hc; cases hc; simp at hd; cases hd; simp

@[simp]
theorem dcast₃_trans (ha : a = a') (ha' : a' = a'')
    (hb : dcast ha b = b') (hb' : dcast ha' b' = b'')
    (hc : dcast₂ ha hb c = c') (hc' : dcast₂ ha' hb' c' = c'') :
    dcast₃ ha' hb' hc' (dcast₃ ha hb hc d) =
    dcast₃ (ha.trans ha') (by simp [← hb', ← hb]) (by simp [← hc', ← hc]) d := by
  cases ha; simp at hb; cases hb; simp at hc; cases hc; simp

theorem dcast₃_eq_dcast₃_iff (ha : a = a') (hb : dcast ha b = b') (hc : dcast₂ ha hb c = c') :
    dcast₃ ha hb hc d = d' ↔ d = dcast₃ ha.symm (dcast_symm ha hb) (dcast₂_symm ha hb hc) d' := by
  cases ha; simp at hb; cases hb; simp at hc; cases hc; simp

theorem dcast₃_dcast₂ : dcast₃ rfl rfl rfl d = dcast₂ dcast_eq.symm dcast₂_dcast.symm d := by
  rw! [dcast_eq]; rw! [dcast₂_eq]; simp

instance instDCast₂₃ {a : α} : DCast₂ (β a) (γ a) (δ a) where
  dcast₂ ha hb c := dcast₃ (Eq.refl a) (by cases ha; simp) (by cases ha; cases hb; simp) c
  dcast₂_id := by intros; funext; simp

instance instDCast₁₃ {a : α} {b : β a} : DCast (γ a b) (δ a b) where
  dcast hc d := dcast₃ (Eq.refl a) dcast_eq (by cases hc; simp) d
  dcast_id := by intros; ext; simp

instance instDCast₂PSigma : DCast₂ ((a : α) ×' β a) (fun a => γ a.1 a.2) (fun a => δ a.1 a.2)
    where
  dcast₂ ha hb c := dcast₃ (by cases ha; simp) (by cases ha; simp) (by cases ha; cases hb; simp) c
  dcast₂_id := by intros; funext; simp

instance instDCast₂Sigma {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    {δ : (a : α) → (b : β a) → γ a b → Type*}
    [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ] :
    DCast₂ ((a : α) × β a) (fun a => γ a.1 a.2) (fun a => δ a.1 a.2) where
  dcast₂ ha hb c := dcast₃ (by cases ha; simp) (by cases ha; simp) (by cases ha; cases hb; simp) c
  dcast₂_id := by intros; funext; simp

instance instDCast₂Forall :
    DCast₂ α (fun a => ∀ b : β a, γ a b) (fun a f => ∀ b : β a, δ a b (f b)) where
  dcast₂ ha hb c := fun b => dcast₃ ha (by simp)
    (by cases ha; cases hb; rw! [dcast_eq]; simp) (c (dcast ha.symm b))
  dcast₂_id := by intros; funext; simp; rw! [dcast_eq]; simp

instance instDCastPSigmaPSigma :
    DCast ((a : α) ×' (b : β a) ×' γ a b) (fun a => δ a.1 a.2.1 a.2.2) where
  dcast hc d := dcast₃ (by cases hc; simp) (by cases hc; simp) (by cases hc; simp) d
  dcast_id := by intros; ext; simp

instance instDCastSigmaSigma {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    {δ : (a : α) → (b : β a) → γ a b → Type*}
    [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ] :
    DCast ((a : α) × (b : β a) × γ a b) (fun a => δ a.1 a.2.1 a.2.2) where
  dcast hc d := dcast₃ (by cases hc; simp) (by cases hc; simp) (by cases hc; simp) d
  dcast_id := by intros; ext; simp

instance instDCastForallForall :
    DCast α (fun a => ∀ b : β a, ∀ c : γ a b, δ a b c) where
  dcast ha d := fun b c => dcast₃ ha (by cases ha; simp) (by cases ha; simp)
    (d (dcast ha.symm b) (dcast₂ ha.symm rfl c))
  dcast_id := by intros; funext; simp; rw! [dcast_eq]; rw! [dcast₂_eq]; simp

instance instDCastPSigmaForall :
    DCast ((a : α) ×' (β a)) (fun ab => ∀ c : γ ab.1 ab.2, δ ab.1 ab.2 c) where
  dcast hab d := fun c => dcast₃ (by cases hab; simp) (by cases hab; simp) (by cases hab; simp)
    (d (dcast₂ (by cases hab; simp) (by cases hab; simp) c))
  dcast_id := by intros; funext; simp; rw! [dcast₂_eq]; simp

instance instDCastSigmaForallForall {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    {δ : (a : α) → (b : β a) → γ a b → Type*}
    [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ] :
    DCast ((a : α) × (β a)) (fun ab => ∀ c : γ ab.1 ab.2, δ ab.1 ab.2 c) where
  dcast hab d := fun c => dcast₃ (by cases hab; simp) (by cases hab; simp) (by cases hab; simp)
    (d (dcast₂ (by cases hab; simp) (by cases hab; simp) c))
  dcast_id := by intros; funext; simp; rw! [dcast₂_eq]; simp

end DCast₃

namespace Fin

/-- `Fin.cast` as a `DCast` (which should override the default instance). -/
instance instDCast : DCast Nat Fin where
  dcast h := Fin.cast h
  dcast_id := by simp only [Fin.cast_refl, implies_true]

theorem cast_eq_dcast {m n : ℕ} (h : m = n) (a : Fin m) :
    Fin.cast h a = dcast h a := rfl

end Fin
