/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Simultaneous specialization of polynomial equations

Outside a bounded union of roots, a finite family of polynomial equations vanishes
exactly where its members are identically zero. For powers batching, each member is
the discrepancy at one evaluation coordinate; identically zero discrepancies are
precisely the common agreements. No restriction on characteristic is needed.
-/

@[expose] public section

namespace Polynomial

open Classical in
/-- If at least `L` of `n` polynomial discrepancies vanish identically and all have
degree at most `ℓ`, at most `ℓ * (n - L)` challenges can create extra zeros.
This is the accidental-agreement step for polynomial-curve sampling. -/
theorem exists_exceptional_evaluation_family
    {F : Type*} [Field F] {n L ℓ : ℕ} (p : Fin n → F[X])
    (hdegree : ∀ i, (p i).natDegree ≤ ℓ)
    (hzero : L ≤ (Finset.univ.filter fun i ↦ p i = 0).card) :
    ∃ exceptional : Finset F, exceptional.card ≤ ℓ * (n - L) ∧
      ∀ z ∉ exceptional, ∀ i, (p i).eval z = 0 ↔ p i = 0 := by
  classical
  let active := Finset.univ.filter fun i ↦ p i ≠ 0
  refine ⟨active.biUnion (fun i ↦ (p i).roots.toFinset), ?_, ?_⟩
  · have hactive : active.card ≤ n - L := by
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i ↦ p i = 0)
      simp only [Finset.card_univ, Fintype.card_fin] at hpartition
      dsimp [active]
      omega
    calc
      (active.biUnion (fun i ↦ (p i).roots.toFinset)).card
          ≤ ∑ i ∈ active, (p i).roots.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ active, ℓ := Finset.sum_le_sum fun i _ ↦
        ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)).trans (hdegree i)
      _ = active.card * ℓ := by simp
      _ ≤ ℓ * (n - L) := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right ℓ hactive
  · intro z hz i
    constructor
    · intro heval
      by_contra hne
      apply hz
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, ?_⟩
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr heval)
    · intro heq
      simp [heq]

end Polynomial
