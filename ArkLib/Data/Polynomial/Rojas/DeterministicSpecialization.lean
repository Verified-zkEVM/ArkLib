/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.PerturbationCoefficient
public import ArkLib.Data.Polynomial.SquarefreeSupport

/-!
# Deterministic specialization scan for Rojas Steps 0--3

For a candidate parameter `ε`, the upstream toric-GCP evaluator supplies the
Step-1 eliminant and the `2n` shifted eliminants from Steps 2--3. The executable
guard checks that exactly `2n` shifted polynomials were supplied, that each is
nonzero, and that each has the expected number of
distinct geometric parameter values, measured by squarefree-support degree.
The scan returns the first passing candidate.

The theorem here is intentionally conditional on the finite candidate list
containing a passing value. Rojas's hyperplane-avoidance argument, the explicit
extension-field candidate construction, and the sparse resultant producer are
still required to prove that condition for actual polynomial systems.
-/

@[expose] public section

namespace ArkLib.Rojas

open CompPoly CompPoly.CPolynomial

variable {F : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F]
variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- All eliminants evaluated at one deterministic Step-0 parameter. -/
structure SpecializationCandidate where
  parameter : F
  eliminant : CPolynomial F
  shiftedEliminants : List (CPolynomial F)

/-- Proof-facing meaning of the executable expected-support-degree guard. -/
def HasExpectedSupportDegree (dimension expectedDegree : ℕ)
    (candidate : SpecializationCandidate (F := F)) : Prop :=
  candidate.shiftedEliminants.length = 2 * dimension ∧
  candidate.eliminant ≠ 0 ∧
    (squarefreeSupport p candidate.eliminant).natDegree = expectedDegree ∧
    ∀ shifted ∈ candidate.shiftedEliminants,
      shifted ≠ 0 ∧ (squarefreeSupport p shifted).natDegree = expectedDegree

/-- Executable genericity guard for the Step-1 and Step-2/3 eliminants. -/
def hasExpectedSupportDegree (dimension expectedDegree : ℕ)
    (candidate : SpecializationCandidate (F := F)) : Bool :=
  candidate.shiftedEliminants.length == 2 * dimension &&
  candidate.eliminant != 0 &&
    (squarefreeSupport p candidate.eliminant).natDegree == expectedDegree &&
    candidate.shiftedEliminants.all fun shifted ↦
      shifted != 0 && (squarefreeSupport p shifted).natDegree == expectedDegree

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem hasExpectedSupportDegree_eq_true_iff
    (dimension expectedDegree : ℕ) (candidate : SpecializationCandidate (F := F)) :
    hasExpectedSupportDegree p dimension expectedDegree candidate = true ↔
      HasExpectedSupportDegree p dimension expectedDegree candidate := by
  simp [hasExpectedSupportDegree, HasExpectedSupportDegree, List.all_eq_true,
    bne_iff_ne, beq_iff_eq, and_assoc]

/-- Return the first candidate whose full Step-1--3 family passes the guard. -/
def selectSpecialization? (dimension expectedDegree : ℕ)
    (candidates : List (SpecializationCandidate (F := F))) :
    Option (SpecializationCandidate (F := F)) :=
  candidates.find? (hasExpectedSupportDegree p dimension expectedDegree)

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem selectSpecialization?_sound
    {dimension expectedDegree : ℕ} {candidates : List (SpecializationCandidate (F := F))}
    {selected : SpecializationCandidate (F := F)}
    (hselected : selectSpecialization? p dimension expectedDegree candidates = some selected) :
    HasExpectedSupportDegree p dimension expectedDegree selected ∧ selected ∈ candidates := by
  rw [selectSpecialization?, List.find?_eq_some_iff_getElem] at hselected
  obtain ⟨hvalid, i, hi, hget, _⟩ := hselected
  refine ⟨(hasExpectedSupportDegree_eq_true_iff p dimension expectedDegree selected).mp hvalid, ?_⟩
  exact hget ▸ List.getElem_mem hi

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem selectSpecialization?_exists_iff
    (dimension expectedDegree : ℕ) (candidates : List (SpecializationCandidate (F := F))) :
    (∃ selected, selectSpecialization? p dimension expectedDegree candidates = some selected) ↔
      ∃ candidate ∈ candidates, HasExpectedSupportDegree p dimension expectedDegree candidate := by
  rw [← Option.isSome_iff_exists, selectSpecialization?, List.find?_isSome]
  constructor
  · rintro ⟨candidate, hmem, hvalid⟩
    exact ⟨candidate, hmem,
      (hasExpectedSupportDegree_eq_true_iff p dimension expectedDegree candidate).mp hvalid⟩
  · rintro ⟨candidate, hmem, hvalid⟩
    exact ⟨candidate, hmem,
      (hasExpectedSupportDegree_eq_true_iff p dimension expectedDegree candidate).mpr hvalid⟩

end ArkLib.Rojas
