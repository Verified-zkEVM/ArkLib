/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine

/-!
# Exact line agreement at full message dimension

Let the message-degree bound and the agreement threshold both equal the block length
`Fintype.card ι`. A candidate polynomial that meets the threshold then agrees with the affine
received word `f + z • g` at every coordinate. Interpolating `f` and `g` on all coordinates gives
one pair `F₀ G₀` such that every such candidate, at every challenge, is `F₀ + C z * G₀` and its
agreement set is the common agreement set of the pair, which is every coordinate. So line mutual
correlated agreement holds at full dimension with no exceptional challenges, over any field.

This is the endpoint that the transfer theorems for message-degree bounds of at most
`Fintype.card ι - 2` do not cover.

## Main statements

* `ReedSolomon.exists_exactPair_fullDimension`: one pair explains every full-agreement candidate.
* `ReedSolomon.exists_exceptional_fullDimension_lineMCA`: the exceptional set is empty.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

/-- **One pair at full dimension.** There are `F₀ G₀` of degree below `Fintype.card ι` such that
for every challenge `z`, every `P` of degree below `Fintype.card ι` agreeing with `f + z • g` at
all `Fintype.card ι` coordinates is `F₀ + C z * G₀`, and its agreement set is the common agreement
set of `F₀` with `f` and `G₀` with `g`.

At full dimension the agreement threshold forces agreement everywhere, so no exceptional challenge
is needed. -/
theorem exists_exactPair_fullDimension {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (f g : ι → F) :
    ∃ F₀ G₀ : F[X], F₀.degree < Fintype.card ι ∧ G₀.degree < Fintype.card ι ∧
      ∀ z (P : F[X]), P.degree < Fintype.card ι →
        Fintype.card ι ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        P = F₀ + C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, hfg, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample domain f g Finset.univ Finset.card_univ
  refine ⟨F₀, G₀, hF₀, hG₀, fun z P hP hcard ↦ ?_⟩
  have hfull : polynomialAgreementSet domain (fun i ↦ f i + z * g i) P = Finset.univ :=
    Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) hcard)
  have heval : ∀ i, P.eval (domain i) = f i + z * g i := fun i ↦
    (mem_polynomialAgreementSet ..).mp (hfull ▸ Finset.mem_univ i)
  refine ⟨?_, ?_⟩
  · simpa using hrecognize (RingHom.id F) z P hP fun i _ ↦ heval i
  · rw [hfull, eq_comm, Finset.eq_univ_iff_forall]
    exact fun i ↦ (mem_commonPolynomialAgreementSet ..).mpr (hfg i (Finset.mem_univ i))

/-- **Full-dimension line MCA.** The empty set of challenges is exceptional for line mutual
correlated agreement at full dimension: for every challenge, every candidate of degree below
`Fintype.card ι` agreeing at all coordinates is `F₀ + C z * G₀` for a pair of degree below
`Fintype.card ι` with the same agreement set. -/
theorem exists_exceptional_fullDimension_lineMCA {F ι : Type*} [Field F] [DecidableEq F]
    [Fintype ι] (domain : ι ↪ F) (f g : ι → F) :
    ∃ exceptional : Finset F, exceptional.card = 0 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < Fintype.card ι →
        Fintype.card ι ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        ∃ F₀ G₀ : F[X], F₀.degree < Fintype.card ι ∧ G₀.degree < Fintype.card ι ∧
          P = F₀ + C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, hpair⟩ := exists_exactPair_fullDimension domain f g
  exact ⟨∅, rfl, fun z _ P hP hcard ↦ ⟨F₀, G₀, hF₀, hG₀, hpair z P hP hcard⟩⟩

end ReedSolomon
