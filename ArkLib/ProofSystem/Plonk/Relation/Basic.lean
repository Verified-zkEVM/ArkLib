/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.ConstraintSystem.Plonk

/-! # Variable and occurrence relations for Plonk

A full variable assignment induces values at the three wire positions of each gate. Copy
constraints express precisely when occurrence values extend to such an assignment. The computable
reconstruction uses the least occurrence of each used variable and assigns zero to unused
variables. Designated occurrences of the public variables preserve their public-input equations
under reconstruction.
-/

@[expose] public section

namespace Plonk.ConstraintSystem

variable {R : Type} {m n ℓ : ℕ}

/-- The occurrence values induced by a full variable assignment. -/
def occurrences (cs : ConstraintSystem R m n) (z : Fin m → R) : Fin (3 * n) → R :=
  z ∘ cs.wireAt

/-- Full assignments induce copy-consistent occurrence values. -/
theorem occurrences_copy (cs : ConstraintSystem R m n) (z : Fin m → R) :
    cs.CopyConstraintsSatisfied (cs.occurrences z) := by
  intro u v huv
  exact congrArg z huv

section Reconstruction

variable [Zero R]

/-- Reconstruct variables from their least occurrence, assigning zero to unused variables. -/
def assignmentOfOccurrences (cs : ConstraintSystem R m n) (w : Fin (3 * n) → R)
    (v : Fin m) : R :=
  if hv : (cs.partition v).Nonempty then w ((cs.partition v).min' hv) else 0

/-- Reconstruction agrees with every occurrence when copy constraints hold. -/
theorem assignmentOfOccurrences_at_wire (cs : ConstraintSystem R m n)
    (w : Fin (3 * n) → R) (hw : cs.CopyConstraintsSatisfied w) (u : Fin (3 * n)) :
    cs.assignmentOfOccurrences w (cs.wireAt u) = w u := by
  have hu : u ∈ cs.partition (cs.wireAt u) := (cs.mem_partition_iff_wireAt _ _).2 rfl
  rw [assignmentOfOccurrences, dite_eq_left ⟨u, hu⟩]
  exact hw _ u ((cs.mem_partition_iff_wireAt _ _).1 (Finset.min'_mem _ _))

/-- Unused variables receive zero under reconstruction. -/
theorem assignmentOfOccurrences_eq_zero (cs : ConstraintSystem R m n)
    (w : Fin (3 * n) → R) (v : Fin m) (hv : ∀ u, cs.wireAt u ≠ v) :
    cs.assignmentOfOccurrences w v = 0 := by
  apply dite_eq_right
  rintro ⟨u, hu⟩
  exact hv u ((cs.mem_partition_iff_wireAt v u).1 hu)

/-- Encoding a reconstructed copy-consistent assignment recovers all occurrence values. -/
theorem occurrences_assignmentOfOccurrences (cs : ConstraintSystem R m n)
    (w : Fin (3 * n) → R) (hw : cs.CopyConstraintsSatisfied w) :
    cs.occurrences (cs.assignmentOfOccurrences w) = w := by
  funext u
  exact cs.assignmentOfOccurrences_at_wire w hw u

/-- Copy constraints hold exactly when the occurrence values extend to full variables. -/
theorem copyConstraints_iff_exists_assignment (cs : ConstraintSystem R m n)
    (w : Fin (3 * n) → R) :
    cs.CopyConstraintsSatisfied w ↔ ∃ z : Fin m → R, cs.occurrences z = w := by
  constructor
  · intro hw
    exact ⟨cs.assignmentOfOccurrences w, cs.occurrences_assignmentOfOccurrences w hw⟩
  · rintro ⟨z, rfl⟩
    exact cs.occurrences_copy z

end Reconstruction

variable [CommRing R]

/-- The gate residual evaluated directly on its left, right, and output occurrences. -/
def rowResidual (cs : ConstraintSystem R m n) (w : Fin (3 * n) → R) (i : Fin n) : R :=
  let a := w (finProdFinEquiv ((0 : Fin 3), i))
  let b := w (finProdFinEquiv ((1 : Fin 3), i))
  let c := w (finProdFinEquiv ((2 : Fin 3), i))
  (cs i).qL * a + (cs i).qR * b + (cs i).qO * c +
    (cs i).qM * (a * b) + (cs i).qC

/-- Gate evaluation is unchanged when a variable assignment is expressed as occurrences. -/
@[simp]
theorem rowResidual_occurrences (cs : ConstraintSystem R m n) (z : Fin m → R)
    (i : Fin n) : cs.rowResidual (cs.occurrences z) i = (cs i).eval z := by
  simp [rowResidual, occurrences, wireAt, Gate.eval]

/-- The full-variable relation with an arbitrary embedding of public variables. -/
def variableRelation (cs : ConstraintSystem R m n) (publicPos : Fin ℓ ↪ Fin m)
    (x : Fin ℓ → R) (z : Fin m → R) : Prop :=
  cs.accepts z ∧ ∀ j, z (publicPos j) = x j

/-- The occurrence relation includes gates, copies, and designated public occurrences. -/
def occurrenceRelation (cs : ConstraintSystem R m n)
    (publicOccurrence : Fin ℓ → Fin (3 * n)) (x : Fin ℓ → R)
    (w : Fin (3 * n) → R) : Prop :=
  cs.CopyConstraintsSatisfied w ∧ (∀ i, cs.rowResidual w i = 0) ∧
    ∀ j, w (publicOccurrence j) = x j

/-- The wiring permutation expresses precisely the copy equations in the occurrence relation. -/
theorem occurrenceRelation_iff_invariant (cs : ConstraintSystem R m n)
    (publicOccurrence : Fin ℓ → Fin (3 * n)) (x : Fin ℓ → R)
    (w : Fin (3 * n) → R) :
    cs.occurrenceRelation publicOccurrence x w ↔
      (∀ u, w (cs.perm u) = w u) ∧ (∀ i, cs.rowResidual w i = 0) ∧
        ∀ j, w (publicOccurrence j) = x j := by
  rw [occurrenceRelation, cs.copyConstraints_iff_invariant]

/-- Encoding preserves the full-variable relation when the public occurrences are covered. -/
theorem occurrences_relation (cs : ConstraintSystem R m n)
    (publicPos : Fin ℓ ↪ Fin m) (publicOccurrence : Fin ℓ → Fin (3 * n))
    (hpublic : ∀ j, cs.wireAt (publicOccurrence j) = publicPos j)
    (x : Fin ℓ → R) (z : Fin m → R) (hz : cs.variableRelation publicPos x z) :
    cs.occurrenceRelation publicOccurrence x (cs.occurrences z) := by
  refine ⟨cs.occurrences_copy z, ?_, ?_⟩
  · intro i
    rw [rowResidual_occurrences]
    exact hz.1 i
  · intro j
    change z (cs.wireAt (publicOccurrence j)) = x j
    rw [hpublic j]
    exact hz.2 j

/-- Reconstructing a valid occurrence assignment preserves every gate and public input. -/
theorem assignmentOfOccurrences_relation (cs : ConstraintSystem R m n)
    (publicPos : Fin ℓ ↪ Fin m) (publicOccurrence : Fin ℓ → Fin (3 * n))
    (hpublic : ∀ j, cs.wireAt (publicOccurrence j) = publicPos j)
    (x : Fin ℓ → R) (w : Fin (3 * n) → R)
    (hw : cs.occurrenceRelation publicOccurrence x w) :
    cs.variableRelation publicPos x (cs.assignmentOfOccurrences w) := by
  constructor
  · intro i
    change (cs i).eval _ = 0
    rw [← rowResidual_occurrences, cs.occurrences_assignmentOfOccurrences w hw.1]
    exact hw.2.1 i
  · intro j
    rw [← hpublic j, cs.assignmentOfOccurrences_at_wire w hw.1]
    exact hw.2.2 j

/-- Variable and occurrence witnesses define the same language with public-occurrence coverage. -/
theorem exists_variable_iff_exists_occurrence (cs : ConstraintSystem R m n)
    (publicPos : Fin ℓ ↪ Fin m) (publicOccurrence : Fin ℓ → Fin (3 * n))
    (hpublic : ∀ j, cs.wireAt (publicOccurrence j) = publicPos j) (x : Fin ℓ → R) :
    (∃ z, cs.variableRelation publicPos x z) ↔
      ∃ w, cs.occurrenceRelation publicOccurrence x w := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨cs.occurrences z,
      cs.occurrences_relation publicPos publicOccurrence hpublic x z hz⟩
  · rintro ⟨w, hw⟩
    exact ⟨cs.assignmentOfOccurrences w,
      cs.assignmentOfOccurrences_relation publicPos publicOccurrence hpublic x w hw⟩

end Plonk.ConstraintSystem
