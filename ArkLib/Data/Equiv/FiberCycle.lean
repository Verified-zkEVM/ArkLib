/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! # Cycles of the fibers of a finite map -/

@[expose] public section

namespace Equiv.Perm

variable {β γ : Type*} {k : ℕ} [DecidableEq β]

/-- The fiber over `b`, listed in increasing order. -/
def fiberList (f : Fin k → β) (b : β) : List (Fin k) :=
  (List.finRange k).filter (fun a => f a = b)

@[simp]
theorem mem_fiberList (f : Fin k → β) (b : β) (a : Fin k) :
    a ∈ fiberList f b ↔ f a = b := by
  simp [fiberList]

/-- Rotate one fiber, leaving its complement fixed. -/
def rotateFiber (f : Fin k → β) (b : β) : Perm (Fin k) :=
  (fiberList f b).formPerm

private theorem rotateFiber_preserves (f : Fin k → β) (b : β) {a : Fin k} (ha : f a = b) :
    f (rotateFiber f b a) = b := by
  apply (mem_fiberList f b _).mp
  exact List.formPerm_mem_iff_mem.mpr ((mem_fiberList f b a).mpr ha)

private theorem rotateFiber_symm_preserves (f : Fin k → β) (b : β) {a : Fin k} (ha : f a = b) :
    f ((rotateFiber f b).symm a) = b := by
  apply (mem_fiberList f b _).mp
  apply List.formPerm_mem_iff_mem.mp
  change rotateFiber f b ((rotateFiber f b).symm a) ∈ fiberList f b
  simpa using (mem_fiberList f b a).mpr ha

/-- Rotate each nonempty fiber of `f` in increasing order, fixing singleton fibers. -/
def fiberCycle (f : Fin k → β) : Perm (Fin k) where
  toFun a := rotateFiber f (f a) a
  invFun a := (rotateFiber f (f a)).symm a
  left_inv a := by
    change (rotateFiber f (f (rotateFiber f (f a) a))).symm
      (rotateFiber f (f a) a) = a
    rw [rotateFiber_preserves f (f a) rfl]
    exact (rotateFiber f (f a)).symm_apply_apply a
  right_inv a := by
    change rotateFiber f (f ((rotateFiber f (f a)).symm a))
      ((rotateFiber f (f a)).symm a) = a
    rw [rotateFiber_symm_preserves f (f a) rfl]
    exact (rotateFiber f (f a)).apply_symm_apply a

theorem fiberCycle_apply (f : Fin k → β) (a : Fin k) : f (fiberCycle f a) = f a :=
  rotateFiber_preserves f (f a) rfl

private theorem fiberCycle_pow_apply (f : Fin k → β) (n : ℕ) (a : Fin k) :
    f ((fiberCycle f ^ n) a) = f a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', mul_apply, fiberCycle_apply f _, ih]

private theorem fiberCycle_pow_eq (f : Fin k → β) (a : Fin k) (n : ℕ) :
    (fiberCycle f ^ n) a = (rotateFiber f (f a) ^ n) a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_apply, mul_apply]
    change rotateFiber f (f ((fiberCycle f ^ n) a)) ((fiberCycle f ^ n) a) = _
    rw [fiberCycle_pow_apply f n a, ih]

/-- Two points lie on the same cycle exactly when they have the same image under `f`. -/
theorem sameCycle_fiberCycle_iff (f : Fin k → β) (a b : Fin k) :
    (fiberCycle f).SameCycle a b ↔ f a = f b := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    exact (fiberCycle_pow_apply f n a).symm
  · intro h
    have hcycle := ((List.nodup_finRange k).filter
      (fun x => f x = f a)).isCycleOn_formPerm
    have ha : a ∈ fiberList f (f a) := (mem_fiberList f (f a) a).mpr rfl
    have hb : b ∈ fiberList f (f a) := (mem_fiberList f (f a) b).mpr h.symm
    obtain ⟨n, hn⟩ := (hcycle.2 ha hb).exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, fiberCycle_pow_eq]
    exact hn

/-- Invariance under the fiber cycle is equivalent to being constant on each fiber. -/
theorem fiberCycle_invariant_iff (f : Fin k → β) (g : Fin k → γ) :
    (∀ a, g (fiberCycle f a) = g a) ↔ ∀ a b, f a = f b → g a = g b := by
  constructor
  · intro h a b hab
    obtain ⟨n, hn⟩ := ((sameCycle_fiberCycle_iff f a b).mpr hab).exists_nat_pow_eq
    have hpow : ∀ k : ℕ, g ((fiberCycle f ^ k) a) = g a := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ', mul_apply, h, ih]
    rw [← hn]
    exact (hpow n).symm
  · intro h a
    exact h _ _ (fiberCycle_apply f a)

end Equiv.Perm
