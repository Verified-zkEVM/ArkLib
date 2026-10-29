/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.PermutationFingerprint
public import ArkLib.ProofSystem.Plonk.Relation.Basic
public import ArkLib.ProofSystem.Plonk.Encoding.Domain

/-! # Plonk copy constraints as permutation fingerprints

The three disjoint cosets label all wire positions distinctly. Their labeled product
fingerprint characterizes the copy constraints and bounds acceptance of a false copy claim.
-/

@[expose] public section

namespace Plonk

variable {F : Type} [Field F] {m n : ℕ} {D : EvaluationDomain F n}

/-- The three cosets embed the wire positions into the field. -/
def CosetLabels.labelEmbedding (L : CosetLabels D) : Fin (3 * n) ↪ F :=
  ⟨L.label, L.label_injective⟩

@[simp]
theorem CosetLabels.labelEmbedding_apply (L : CosetLabels D) (u : Fin (3 * n)) :
    L.labelEmbedding u = L.label u := rfl

namespace ConstraintSystem

/-- Copy-consistent occurrence values pass every labeled permutation challenge. -/
theorem fingerprint_eq_zero_of_copyConstraints (cs : ConstraintSystem F m n)
    (L : CosetLabels D) (W : Fin (3 * n) → F) (hW : cs.CopyConstraintsSatisfied W)
    (β γ : F) :
    PermutationFingerprint.fingerprint W L.labelEmbedding cs.perm β γ = 0 := by
  apply PermutationFingerprint.fingerprint_eq_zero
  funext u
  exact (cs.copyConstraints_iff_invariant W).mp hW u

/-- All labeled permutation challenges accept exactly the copy-consistent assignments. -/
theorem copyConstraints_iff_fingerprint_eq_zero (cs : ConstraintSystem F m n)
    (L : CosetLabels D) (W : Fin (3 * n) → F) :
    cs.CopyConstraintsSatisfied W ↔
      ∀ β γ, PermutationFingerprint.fingerprint W L.labelEmbedding cs.perm β γ = 0 := by
  rw [← PermutationFingerprint.invariant_iff_fingerprint_eq_zero]
  exact (cs.copyConstraints_iff_invariant W).trans ⟨fun h => funext h, fun h => congrFun h⟩

open scoped ProbabilityTheory NNReal

/-- A false copy claim passes a joint uniform challenge with probability at most
`(3n - 1) / |F|`. -/
theorem prob_fingerprint_eq_zero_le [Fintype F] [SampleableType F]
    (cs : ConstraintSystem F m n) (L : CosetLabels D) (W : Fin (3 * n) → F)
    (hW : ¬ cs.CopyConstraintsSatisfied W) :
    Pr{let r ← $ᵗ (F × F)}[
      PermutationFingerprint.fingerprint W L.labelEmbedding cs.perm r.1 r.2 = 0] ≤
      (((3 * n - 1 : ℕ) : ℝ≥0) / Fintype.card F : ℝ≥0) := by
  have hInvariant : W ∘ cs.perm ≠ W := by
    intro h
    exact hW ((cs.copyConstraints_iff_invariant W).mpr (congrFun h))
  simpa only [Fintype.card_fin] using
    PermutationFingerprint.prob_fingerprint_eq_zero_le W L.labelEmbedding cs.perm hInvariant

end ConstraintSystem
end Plonk
