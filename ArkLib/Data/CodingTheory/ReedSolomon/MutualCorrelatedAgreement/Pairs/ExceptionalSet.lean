/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.Family
/-! # Simultaneous accidental-agreement bounds for correlated pairs

A finite family of polynomial pairs with at least `L` common agreements has one
exceptional set, of size at most the family size times `n - L`, outside which
every pair has exactly its common agreement set. The threshold is arbitrary.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial
open scoped BigOperators

/-- A common exceptional set for a finite pair family charges only positions outside
the common agreements, uniformly over all challenges and every pair in the family. -/
theorem exists_exceptional_correlatedPairFamily
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
    {n L : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (pairs : Finset (F[X] × F[X]))
    (hcommon : ∀ pair ∈ pairs,
      L ≤ (commonPolynomialAgreementSet domain f g pair.1 pair.2).card) :
    ∃ exceptional : Finset E, exceptional.card ≤ pairs.card * (n - L) ∧
      ∀ pair ∈ pairs, ∀ z ∉ exceptional,
        polynomialAgreementSet (mappedDomain domain iota)
            (fun i ↦ iota (f i) + z * iota (g i))
            (correlatedPairSpecialization iota z pair) =
          commonPolynomialAgreementSet domain f g pair.1 pair.2 := by
  classical
  choose exceptional hcard hagree using
    (fun pair : F[X] × F[X] ↦
      exists_exceptional_graphLine_challenges domain f g pair.1 pair.2 iota)
  refine ⟨pairs.biUnion exceptional, ?_, ?_⟩
  · calc
      (pairs.biUnion exceptional).card ≤ ∑ pair ∈ pairs, (exceptional pair).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _pair ∈ pairs, (n - L) := by
        apply Finset.sum_le_sum
        intro pair hpair
        exact (hcard pair).trans (Nat.sub_le_sub_left (hcommon pair hpair) n)
      _ = pairs.card * (n - L) := by simp
  · intro pair hpair z hz
    apply hagree pair z
    intro hmem
    exact hz (Finset.mem_biUnion.mpr ⟨pair, hpair, hmem⟩)

end

end ReedSolomon
