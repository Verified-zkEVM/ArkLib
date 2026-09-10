/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.Tauto

/-!
# Double counting after discarding fewer than k agreement positions

Every candidate retains at least A-k+1 incidences when fewer than k positions are
removed. Double counting expresses this as a sum of the remaining fiber sizes.
-/

@[expose] public section

namespace AffineHilbert

open scoped BigOperators

/-- Removing fewer than k positions leaves the stated total number of incidences.
The removed positions need not be incidences of every candidate. -/
theorem finiteAgreementIncidence_lower {X : Type*} {n A k : ℕ}
    (S : Finset X) (Bad : Finset (Fin n)) (zero : X → Fin n → Prop)
    [∀ x i, Decidable (zero x i)] (hkA : k ≤ A) (hBad : Bad.card < k)
    (hA : ∀ x ∈ S, A ≤ (Finset.univ.filter (zero x)).card) :
    S.card * (A - k + 1) ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ Bad), (S.filter fun x ↦ zero x i).card := by
  classical
  let good : Finset (Fin n) := Finset.univ.filter (fun i ↦ i ∉ Bad)
  have hpoint : ∀ x ∈ S, A - k + 1 ≤ (good.filter (zero x)).card := by
    intro x hx
    have hcover := Finset.card_le_card_sdiff_add_card
      (s := Finset.univ.filter (zero x)) (t := Bad)
    have heq : (Finset.univ.filter (zero x)) \ Bad = good.filter (zero x) := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, good]
      tauto
    rw [heq] at hcover
    have := hA x hx
    omega
  calc
    S.card * (A - k + 1) = ∑ _x ∈ S, (A - k + 1) := by simp
    _ ≤ ∑ x ∈ S, (good.filter (zero x)).card := Finset.sum_le_sum hpoint
    _ = ∑ i ∈ good, (S.filter fun x ↦ zero x i).card := by
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow zero (s := S) (t := good)

end AffineHilbert
