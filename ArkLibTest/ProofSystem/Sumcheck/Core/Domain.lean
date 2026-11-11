/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.DomainEquivalence

/-! # Multiplicity of indexed Sumcheck domains -/

@[expose] public section

namespace Sumcheck.Core.DomainTest
open Polynomial Finset

/-- The constant polynomial one has indexed sum two over the list of two zeroes. -/
example : roundSum ([0, 0] : List ℕ).get (0 : Fin 2) Fin.elim0
    (1 : MvPolynomial (Fin 1) ℕ) = 2 := by
  simp [roundSum]

/-- The list specialization counts both occurrences of the same evaluation point. -/
example : (∑ i : Fin ([0, 0] : List ℕ).length, (1 : ℕ[X]).eval
    (([0, 0] : List ℕ).get i)) = 2 := by
  rw [sum_domain_list ([0, 0] : List ℕ) (fun x => (1 : ℕ[X]).eval x)]
  simp

/-- The singleton embedding enumerates the deduplicated domain containing zero. -/
def zeroDomain : Fin 1 ↪ ℕ :=
  ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

/-- Deduplicating the two zeroes changes the constant polynomial's sum to one. -/
example : (∑ x ∈ univ.map zeroDomain, (1 : ℕ[X]).eval x) = 1 := by
  simp

run_cmd
  for decl in [``Sumcheck.Core.sum_domain_embedding, ``Sumcheck.Core.sum_domain_list,
      ``Sumcheck.Core.roundSum, ``Sumcheck.Core.projectedRoundPolynomial,
      ``Sumcheck.Core.projectedRoundPolynomial_embedding, ``Sumcheck.Core.sum_evalExcept_indices,
      ``Sumcheck.Core.sum_projectedRoundPolynomial, ``Sumcheck.Core.roundSum_succ] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.DomainTest

namespace Sumcheck.Core.DomainTest
open Polynomial MvPolynomial

/-- Repeating zero twice makes the initial sum of the constant-one input equal to two. -/
example : indexedRelation ([0, 0] : List ℕ).get (0 : Fin 2) ⟨2, Fin.elim0⟩
    (⟨1, by rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]; intro i; simp⟩ :
      ℕ⦃≤ 0⦄[X Fin 1]) := by
  simp [indexedRelation, roundSum]

/-- Replacing the repeated domain by a singleton changes the truth of the claim. -/
example : ¬ indexedRelation ([0] : List ℕ).get (0 : Fin 2) ⟨2, Fin.elim0⟩
    (⟨1, by rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]; intro i; simp⟩ :
      ℕ⦃≤ 0⦄[X Fin 1]) := by
  simp [indexedRelation, roundSum]

/-- Multiplicities are counted independently in every variable of the remaining sum. -/
example : roundSum ([0, 0] : List ℕ).get (0 : Fin 3) Fin.elim0
    (1 : MvPolynomial (Fin 2) ℕ) = 4 := by
  simp [roundSum]

run_cmd
  for decl in [``Sumcheck.Core.indexedRelation, ``Sumcheck.Core.indexedRelation_last] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.DomainTest
