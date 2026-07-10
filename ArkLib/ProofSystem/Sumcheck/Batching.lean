/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/

import ArkLib.ProofSystem.Sumcheck.Domain
import ArkLib.ProofSystem.Sumcheck.Spec.General

/-!
# Batched sum-check claims

This file provides a semantic claim layer for batching sum-check instances over a common domain.
It relates a function-valued summand to ArkLib's degree-bounded polynomial oracle statement and
reuses the standard sum-check oracle reduction.

## References

* [Lund, C., Fortnow, L., Karloff, H., and Nisan, N., *Algebraic methods for interactive
    proof systems*][LFKN92]
-/

noncomputable section

open MvPolynomial OracleComp OracleSpec ProtocolSpec
open scoped BigOperators

namespace Sumcheck.Batching

/-- A semantic sum-check claim in `n` variables. -/
structure Claim (R : Type) (n : ℕ) where
  /-- The summand evaluated at a point. -/
  summand : (Fin n → R) → R
  /-- The claimed sum over the evaluation domain. -/
  target : R

namespace Claim

variable {R : Type} [CommSemiring R] {n degree m : ℕ}

/-- A claim is valid when its summand sums to its target over the given uniform domain. -/
def IsValid (claim : Claim R n) (domain : Fin m ↪ R) : Prop :=
  ∑ x ∈ (Finset.univ.map domain) ^ᶠ n, claim.summand x = claim.target

/-- The oracle polynomial represents the semantic summand at every field point. -/
def MatchesOracle (claim : Claim R n)
    (oStmt : ∀ i, Spec.OracleStatement R n degree i) : Prop :=
  ∀ x, MvPolynomial.eval x (oStmt ()).val = claim.summand x

/-- The input relation connecting a semantic claim to ArkLib's polynomial oracle statement. -/
def relation (claim : Claim R n) (domain : Fin m ↪ R) :
    Set (((Spec.StatementRound R n 0) ×
      (∀ i, Spec.OracleStatement R n degree i)) × Unit) :=
  { input |
    input.1.1.target = claim.target ∧
      claim.MatchesOracle input.1.2 ∧ claim.IsValid domain }

/-- The semantic input relation refines ArkLib's initial sum-check relation. -/
theorem relation_subset_spec (claim : Claim R n) (domain : Fin m ↪ R) :
    claim.relation (degree := degree) domain ⊆ Spec.relationRound R n degree domain 0 := by
  rintro ⟨⟨stmt, oStmt⟩, _⟩ ⟨htarget, hmatches, hvalid⟩
  change ∑ x ∈ (Finset.univ.map domain) ^ᶠ (n - (0 : Fin (n + 1))),
    (oStmt ()).val ⸨stmt.challenges, x⸩ = stmt.target
  simp only [Fin.val_zero, Nat.sub_zero]
  have hchallenges : stmt.challenges = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  calc
    _ = ∑ x ∈ (Finset.univ.map domain) ^ᶠ n, claim.summand x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hchallenges]
      simpa only [Fin.elim0_append, Function.comp_apply] using hmatches x
    _ = claim.target := hvalid
    _ = stmt.target := htarget.symm

end Claim

/-- A family of same-domain sum-check claims. -/
structure Family (R : Type) (n count : ℕ) where
  /-- The claims in the family. -/
  claim : Fin count → Claim R n

namespace Family

variable {R : Type} [CommSemiring R] {n count m : ℕ}

/-- The random linear combination `∑ j, ρ ^ j • claim j`. -/
def batch (claims : Family R n count) (ρ : R) : Claim R n where
  summand x := ∑ j : Fin count, ρ ^ (j : ℕ) * (claims.claim j).summand x
  target := ∑ j : Fin count, ρ ^ (j : ℕ) * (claims.claim j).target

/-- Batching preserves validity for every fixed batching scalar. -/
theorem batch_isValid (claims : Family R n count) (domain : Fin m ↪ R)
    (hvalid : ∀ j, (claims.claim j).IsValid domain) (ρ : R) :
    (claims.batch ρ).IsValid domain := by
  classical
  simp only [Claim.IsValid, batch]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum]
  rw [hvalid j]

end Family

variable {R : Type} [Field R] [DecidableEq R] [SampleableType R]

/-- ArkLib's sum-check oracle reduction over the Boolean hypercube. -/
def oracleReduction {ι : Type} (oSpec : OracleSpec ι) (degree n : ℕ) :
    OracleReduction oSpec
      (Spec.StatementRound R n 0) (Spec.OracleStatement R n degree) Unit
      (Spec.StatementRound R n (.last n)) (Spec.OracleStatement R n degree) Unit
      (Spec.pSpec R degree n) :=
  Spec.oracleReduction R degree (boolEmbedding R) n oSpec

end Sumcheck.Batching
