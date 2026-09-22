/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.Family

/-!
# One exceptional set for a finite family of pairs

Fix an evaluation domain `domain : ι ↪ F`, received words `f g : ι → F`, a field homomorphism
`φ : F →+* E`, and a finite family `pairs` of polynomial pairs over `F`. For each pair `(P, Q)`,
`ReedSolomon.exists_exceptional_graphLine_challenges_le_disagreement` gives at most
`Fintype.card ι - #(polynomialAgreementSet domain g Q)` challenges outside which the agreement set
of the specialization `P.map φ + C z * Q.map φ` with the affine word `φ ∘ f + z • φ ∘ g` is exactly
the common agreement set of `(P, Q)` with `(f, g)`. The union over the family is one exceptional
set that works for every pair at once.

## Main statements

* `ReedSolomon.exists_exceptional_correlatedPairFamily_le_sum`: the union, of size at most the sum
  of the per-pair disagreement counts of the second polynomial.
* `ReedSolomon.exists_exceptional_correlatedPairFamily`: if every pair has at least `L` common
  agreements, the size is at most `#pairs * (Fintype.card ι - L)`.

## References

Ported from `Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Pairs/ExceptionalSet.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
`exists_exceptional_correlatedPairFamily` has the source statement, with the coordinate type
`Fin n` generalized to any finite type `ι` and the source's `mappedDomain domain iota` written out
as `domain.trans ⟨φ, φ.injective⟩`. It is derived from the new
`exists_exceptional_correlatedPairFamily_le_sum`, which counts only the coordinates where the
second polynomial of each pair disagrees with `g` and needs no threshold.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

variable {F E ι : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [Fintype ι]

/-- **One exceptional set for a finite family, counted by disagreements.** For a finite family
`pairs`, there is one set of at most `∑ (P, Q) ∈ pairs, (Fintype.card ι - #(agreement of Q with
g))` challenges `z`, outside which, for every pair `(P, Q)` in the family, the agreement set of
`correlatedPairSpecialization φ z (P, Q)` with the affine word `φ ∘ f + z • φ ∘ g` is exactly the
common agreement set of `(P, Q)` with `(f, g)`.

No degree bound on the pairs is needed. -/
theorem exists_exceptional_correlatedPairFamily_le_sum (domain : ι ↪ F) (f g : ι → F)
    (φ : F →+* E) (pairs : Finset (F[X] × F[X])) :
    ∃ exceptional : Finset E,
      exceptional.card ≤
        ∑ pair ∈ pairs, (Fintype.card ι - (polynomialAgreementSet domain g pair.2).card) ∧
      ∀ pair ∈ pairs, ∀ z ∉ exceptional,
        polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
            (fun i ↦ φ (f i) + z * φ (g i)) (correlatedPairSpecialization φ z pair) =
          commonPolynomialAgreementSet domain f g pair.1 pair.2 := by
  classical
  choose exceptional hcard hagree using fun pair : F[X] × F[X] ↦
    exists_exceptional_graphLine_challenges_le_disagreement domain f g pair.1 pair.2 φ
  refine ⟨pairs.biUnion exceptional, Finset.card_biUnion_le.trans (Finset.sum_le_sum
    fun pair _ ↦ hcard pair), fun pair hpair z hz ↦ hagree pair z fun hmem ↦ hz ?_⟩
  exact Finset.mem_biUnion.mpr ⟨pair, hpair, hmem⟩

/-- **One exceptional set for a finite family with a common-agreement threshold.** If every pair
in `pairs` has at least `L` common agreements with `(f, g)`, the exceptional set of
`exists_exceptional_correlatedPairFamily_le_sum` has at most `#pairs * (Fintype.card ι - L)`
elements: the common agreement set of `(P, Q)` is contained in the agreement set of `Q` with `g`.

The threshold `L` is arbitrary; for `L = 0` the bound is `#pairs * Fintype.card ι`. -/
theorem exists_exceptional_correlatedPairFamily {L : ℕ} (domain : ι ↪ F) (f g : ι → F)
    (φ : F →+* E) (pairs : Finset (F[X] × F[X]))
    (hcommon : ∀ pair ∈ pairs,
      L ≤ (commonPolynomialAgreementSet domain f g pair.1 pair.2).card) :
    ∃ exceptional : Finset E, exceptional.card ≤ pairs.card * (Fintype.card ι - L) ∧
      ∀ pair ∈ pairs, ∀ z ∉ exceptional,
        polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
            (fun i ↦ φ (f i) + z * φ (g i)) (correlatedPairSpecialization φ z pair) =
          commonPolynomialAgreementSet domain f g pair.1 pair.2 := by
  obtain ⟨exceptional, hcard, hagree⟩ :=
    exists_exceptional_correlatedPairFamily_le_sum domain f g φ pairs
  refine ⟨exceptional, hcard.trans ?_, hagree⟩
  rw [← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun pair hpair ↦ Nat.sub_le_sub_left ((hcommon pair hpair).trans
    (Finset.card_le_card fun i hi ↦ ?_)) _
  exact (mem_polynomialAgreementSet ..).mpr ((mem_commonPolynomialAgreementSet ..).mp hi).2

end ReedSolomon
