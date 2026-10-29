/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Plonk.Relation.PermutationFingerprint
import Mathlib.Algebra.Field.ZMod

/-! # Plonk permutation fingerprints over a small prime field -/

namespace ArkLibTest.PlonkFingerprint

open Plonk
open scoped ProbabilityTheory NNReal

private abbrev F := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def domain : EvaluationDomain F 1 where
  node _ := 1
  injective := fun _ _ _ => Subsingleton.elim _ _

private def cosets : CosetLabels domain where
  k₁ := 2
  k₂ := 3
  k₁_ne_zero := by decide
  k₂_ne_zero := by decide
  disjoint_left_right := Set.disjoint_range_iff.mpr (by decide)
  disjoint_left_output := Set.disjoint_range_iff.mpr (by decide)
  disjoint_right_output := Set.disjoint_range_iff.mpr (by decide)

-- The left and right occurrences share variable zero; the output is variable one.
private def circuit : ConstraintSystem F 2 1 := ![Gate.add 0 0 1]

private def honest : Fin 3 → F := circuit.occurrences ![2, 4]

private def altered : Fin 3 → F := ![2, 3, 4]

private def honestFingerprint : F → F → F :=
  PermutationFingerprint.fingerprint honest cosets.labelEmbedding circuit.perm

private def alteredFingerprint : F → F → F :=
  PermutationFingerprint.fingerprint altered cosets.labelEmbedding circuit.perm

example : List.ofFn cosets.label = [1, 2, 3] := by decide

example : List.ofFn (fun u => (circuit.perm u).val) = [1, 0, 2] := by decide

example : circuit.CopyConstraintsSatisfied honest := circuit.occurrences_copy _

private theorem altered_not_copy : ¬ circuit.CopyConstraintsSatisfied altered := by
  unfold ConstraintSystem.CopyConstraintsSatisfied
  decide

example : ∀ β γ, honestFingerprint β γ = 0 :=
  circuit.fingerprint_eq_zero_of_copyConstraints cosets honest (circuit.occurrences_copy _)

example : circuit.CopyConstraintsSatisfied altered ↔ ∀ β γ, alteredFingerprint β γ = 0 :=
  circuit.copyConstraints_iff_fingerprint_eq_zero cosets altered

example : alteredFingerprint 1 1 = 6 := by decide

example : (PermutationFingerprint.polynomial altered cosets.labelEmbedding circuit.perm) ≠ 0 := by
  apply PermutationFingerprint.polynomial_ne_zero
  intro h
  exact altered_not_copy ((circuit.copyConstraints_iff_invariant altered).mpr (congrFun h))

example :
    (PermutationFingerprint.polynomial altered cosets.labelEmbedding circuit.perm).totalDegree ≤
      2 :=
  PermutationFingerprint.totalDegree_polynomial_le altered cosets.labelEmbedding circuit.perm

example [SampleableType F] :
    Pr{let r ← $ᵗ (F × F)}[alteredFingerprint r.1 r.2 = 0] ≤ (2 / 7 : ℝ≥0) := by
  convert circuit.prob_fingerprint_eq_zero_le cosets altered altered_not_copy using 1 <;>
    norm_num [alteredFingerprint]
  congr 2

example (β γ : F) :
    PermutationFingerprint.fingerprint (Fin.elim0 : Fin 0 → F)
      ⟨Fin.elim0, fun u => Fin.elim0 u⟩ (Equiv.refl _) β γ = 0 := by
  simp [PermutationFingerprint.fingerprint]

-- Exactly thirteen of the forty-nine joint challenges accept the false copy claim.
example : ((Finset.univ : Finset (F × F)).filter
    (fun r => alteredFingerprint r.1 r.2 = 0)).card = 13 := by decide

private def fingerprintRuntimeChecks : IO Unit := do
  unless (∀ β γ, honestFingerprint β γ = 0) do
    throw (IO.userError "Unexpected honest permutation fingerprint")
  unless (alteredFingerprint 1 1 = 6) do
    throw (IO.userError "Unexpected false copy fingerprint")
  let bad := (Finset.univ : Finset (F × F)).filter
    (fun r => alteredFingerprint r.1 r.2 = 0)
  unless (bad.card = 13 ∧ bad.card ≤ 2 * 7) do
    throw (IO.userError "Unexpected false copy acceptance count")
  IO.println "Plonk permutation fingerprint runtime checks passed."

/-- info: Plonk permutation fingerprint runtime checks passed. -/
#guard_msgs in
#eval fingerprintRuntimeChecks

end ArkLibTest.PlonkFingerprint
