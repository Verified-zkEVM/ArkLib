/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.Submodule.Union
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for finite-submodule avoidance

The examples below exercise the sharp equality case through an ordinary import. The two
coordinate hyperplanes in `(Fin 2 → ZMod 2)` form a family whose size equals the field size, so
Mathlib's strict-cardinality union theorem cannot supply the witness. The second example checks
that no finite-dimensionality instance is required of the ambient module.
-/

namespace Submodule

/-- At the equality boundary over `ZMod 2`, a vector avoids both coordinate hyperplanes. -/
example : ∃ x : Fin 2 → ZMod 2, ∀ i, x i ≠ 0 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let p (i : Fin 2) : Submodule (ZMod 2) (Fin 2 → ZMod 2) :=
    LinearMap.ker (LinearMap.proj i)
  have hp : ∀ i ∈ (Finset.univ : Finset (Fin 2)), p i ≠ ⊤ := by
    intro i _ htop
    have hmem : Pi.single i (1 : ZMod 2) ∈ p i := by
      rw [htop]
      exact Submodule.mem_top
    simp [p] at hmem
  have hcard : (Finset.univ : Finset (Fin 2)).card ≤ Nat.card (ZMod 2) := by
    simpa only [Nat.card_eq_fintype_card] using
      (show (Finset.univ : Finset (Fin 2)).card ≤ Fintype.card (ZMod 2) by decide)
  obtain ⟨x, hx⟩ := exists_forall_notMem_of_card_le Finset.univ p hp hcard
  exact ⟨x, fun i ↦ by simpa [p] using hx i (Finset.mem_univ i)⟩

/-- Two proper submodules of the infinite-dimensional space `ℕ → ZMod 2` do not cover it. -/
example (p : Fin 2 → Submodule (ZMod 2) (ℕ → ZMod 2)) (hp : ∀ i, p i ≠ ⊤) :
    ∃ x : ℕ → ZMod 2, ∀ i, x ∉ p i := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_forall_notMem_of_card_le Finset.univ p (fun i _ ↦ hp i) (by simp)
  exact ⟨x, fun i ↦ hx i (Finset.mem_univ i)⟩

end Submodule
