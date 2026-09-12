/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, scaraven
-/
module

public import Mathlib.Logic.Basic
public import CompPoly.Data.Classes.DCast

/-!
# Congruence lemmas for heterogeneous equality

Transport, function application, dependent functions, products, and monadic operations preserve
heterogeneous equality when the corresponding types are equal.
-/

@[expose] public section

universe u v

/-! ### Transports -/

/-- Transporting along `dcast` does not change a term up to `HEq`. -/
theorem heq_dcast {α : Sort u} {β : α → Sort v} [DCast α β] {a a' : α} (h : a = a') (b : β a) :
    HEq (dcast h b) b := by
  subst h
  rw [dcast_eq]

/-! ### Functions -/

/-- Congruence for function application: applying `HEq` functions to `HEq` arguments gives `HEq`
results. -/
theorem heq_apply {α α' : Sort u} {β β' : Sort v} (hα : α = α') (hβ : β = β')
    {f : α → β} {f' : α' → β'} (hf : HEq f f') {a : α} {a' : α'} (ha : HEq a a') :
    HEq (f a) (f' a') := by
  subst hα
  subst hβ
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq ha
  rfl

/-- Extensionality for `HEq` of non-dependent functions: two functions between propositionally
equal domains and codomains are `HEq` as soon as they agree on `HEq` arguments. -/
theorem heq_funext {α α' : Sort u} {β β' : Sort v} (hα : α = α') (hβ : β = β')
    {f : α → β} {f' : α' → β'}
    (h : ∀ (a : α) (a' : α'), HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  subst hα
  subst hβ
  exact heq_of_eq (funext fun a => eq_of_heq (h a a HEq.rfl))

/-- Extensionality for `HEq` of dependent functions over a *fixed* domain: two sections of
propositionally equal families are `HEq` as soon as they agree pointwise. -/
theorem heq_pi {α : Sort u} {β β' : α → Sort v} (hβ : β = β')
    {f : (a : α) → β a} {g : (a : α) → β' a} (h : ∀ a, HEq (f a) (g a)) : HEq f g := by
  subst hβ
  exact heq_of_eq (funext fun a => eq_of_heq (h a))

/-- Congruence for applying `HEq` dependent functions over a *fixed* domain at a common
argument. -/
theorem heq_dapply {α : Sort u} {β β' : α → Sort v} (hβ : β = β')
    {f : (a : α) → β a} {g : (a : α) → β' a} (h : HEq f g) (a : α) : HEq (f a) (g a) := by
  subst hβ
  obtain rfl := eq_of_heq h
  rfl

/-! ### Products -/

/-- Congruence for pairing. -/
theorem heq_prod {A A' B B' : Type u} (hA : A = A') (hB : B = B')
    {a : A} {a' : A'} (ha : HEq a a') {b : B} {b' : B'} (hb : HEq b b') :
    HEq ((a, b) : A × B) ((a', b') : A' × B') := by
  subst hA
  subst hB
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  rfl

/-- Congruence for the first projection. -/
theorem heq_fst {A A' B B' : Type u} (hA : A = A') (hB : B = B') {x : A × B} {x' : A' × B'}
    (h : HEq x x') : HEq x.1 x'.1 := by
  subst hA
  subst hB
  obtain rfl := eq_of_heq h
  rfl

/-- Congruence for the second projection. -/
theorem heq_snd {A A' B B' : Type u} (hA : A = A') (hB : B = B') {x : A × B} {x' : A' × B'}
    (h : HEq x x') : HEq x.2 x'.2 := by
  subst hA
  subst hB
  obtain rfl := eq_of_heq h
  rfl

/-! ### Monadic operations -/

/-- Congruence for `pure`. -/
theorem heq_pure {M : Type u → Type v} [Monad M] {α α' : Type u} (hα : α = α')
    {a : α} {a' : α'} (h : HEq a a') : HEq (pure a : M α) (pure a' : M α') := by
  subst hα
  obtain rfl := eq_of_heq h
  rfl

/-- Congruence for `>>=`. -/
theorem heq_bind {M : Type u → Type v} [Monad M] {α α' β β' : Type u} (hα : α = α') (hβ : β = β')
    {x : M α} {x' : M α'} (hx : HEq x x') {f : α → M β} {f' : α' → M β'} (hf : HEq f f') :
    HEq (x >>= f) (x' >>= f') := by
  subst hα
  subst hβ
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hf
  rfl
