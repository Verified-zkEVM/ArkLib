/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Basic
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.KKH26Asymptotic
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.LargeAlphabet
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Linear
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.SubspaceDesign

/-!
# Combinatorial bounds on the maximised list size

Upper and lower bounds on `Code.Lambda` — the block-maximised list size of a code at a
given relative radius. The two families answer opposite questions about the same quantity:

* **Upper bounds** exhibit a radius at which the list is provably small, so they certify list
  decodability. The one here is for codes carrying a *subspace-design* profile
  (`CodingTheory.IsSubspaceDesign`), which is the abstraction folded Reed-Solomon codes satisfy;
  its two code-family consequences are `frs_lambda_le_capacity` and `um_lambda_le_capacity`, for
  folded Reed-Solomon and univariate multiplicity codes. A second upper bound,
  `rs_random_domain_lambda_le`, is probabilistic: a Reed-Solomon code on a *uniformly random*
  evaluation domain is list-decodable near capacity with high probability.
* **Lower bounds** exhibit a radius at which the list is provably large, so they rule out list
  decodability above a threshold: volume/averaging bounds valid for every code over a finite
  alphabet (`lambda_ge_elias_volume` and `lambda_ge_entropy_volume`), a bound on random linear
  codes, and Reed-Solomon-specific separations
  (`rs_lambda_superpoly_extension`, `rs_lambda_large_prime`). The proved
  `rs_codimension_one_list_size` is a separate elementary interpolation lemma, not the missing
  [JH01] high-rate separation.
* **Neither** is `linear_card_le_generalized_singleton`, which bounds `|C|` rather than a list and
  belongs to a third group with `large_alphabet_lambda_lower`: constraints on the *code* implied by
  a list-size bound. Its arithmetic half, with no list-decoding premise at all, is
  `linear_card_le_of_rate_radius`; the barrier's own consequence — attaining the generalized
  Singleton bound *exactly* forces an exponentially large alphabet — is
  `large_alphabet_card_ge_exp_of_inv_length`.

Together they bracket the largest radius at which a code family can be list-decoded with a given
list size — the quantity the Grand List Decoding Challenge of [ABF26] asks about.

## Quantification conventions

The asymptotic statements below quantify over "infinitely many `q`", existentially-bound codes,
and "sufficiently large `n`". These are captured uniformly:

* *Type-level data* (alphabet `F`, index type `ι`) is **universally** quantified, at the theorem's
  outermost binder when the statement holds for every instantiation, and *inside* an existential
  when the source constructs the code. The caller instantiates.
* *Numeric quantifiers* ("there exists `α > 0`") stay inside the statement as `∃` on numeric data.
* *Sufficiently large `n`* becomes an explicit existential threshold `n₀ : ℕ` followed by
  `n₀ ≤ Fintype.card ι`. This is the `Filter.Eventually` shape without a filter in a pure
  statement.
* *Infinitely many `q`* becomes `∃ qs : ℕ → ℕ, StrictMono qs ∧ ∀ i, P (qs i)` — note the
  prime-power requirement is a **conjunct**, never the antecedent of an implication, which a
  non-prime-power sequence would satisfy vacuously.
* *Exact rates* `k = ρ · n` are unsatisfiable for irrational `ρ`. Where a source treats `ρ · n` as
  an integer "for exposition", the dimension is pinned two-sidedly into the band
  `ρ ≤ k/n ≤ ρ + 1/n`, admitting `k = ⌈ρ·n⌉`. Where a source's constants genuinely depend on the
  exact rate, the equality is kept and the statement is vacuous at irrational `ρ` — as in the
  source, whose asymptotic form fixes `ρ` and quantifies over lengths realising it.

## Where things live

This file is the umbrella; the statements are in `Bounds/`.

* `Bounds/Basic.lean` — the three counting identities everything else rests on.
* `Bounds/Linear.lean` — bounds valid for every linear code: Elias volume and its entropy form, the
  rate–radius arithmetic, the generalized Singleton bound, random linear codes.
* `Bounds/LargeAlphabet.lean` — the barrier that attaining the generalized Singleton bound forces an
  exponentially large alphabet, over the four-file development in `Bounds/LargeAlphabet/`.
* `Bounds/ReedSolomon.lean` — two Reed-Solomon separations, the internal codimension-one lemma, and
  the random-evaluation-domain upper bound. The distinct [JH01] result is not formalised.
* `Bounds/SubspaceDesign.lean` — [CZ25]'s upper bound, its two reformulations, and the folded-RS and
  multiplicity-code corollaries, over the machinery in `Bounds/AgreementHypergraph.lean`.
* `Bounds/KKH26.lean` and `Bounds/KKH26Asymptotic.lean` — the concrete [KKH26] useful-family
  templates and the derived ABF26 Theorem 3.15.

## External admits

Three statements are admitted with a tagged `sorry`, never an `axiom`: the random-linear-code bound
(`random_linear_lambda_lower`, [GLMRSW22]), the extension-field Reed-Solomon separation
(`rs_lambda_superpoly_extension`, [BKR06]), and the random-evaluation-domain bound
(`rs_random_domain_lambda_le`, [AGL24]). Source locators and formulation notes are recorded in the
defining modules and knowledge-base pages.

One derivation inherits an admit and is therefore reachable-`sorryAx`, carrying no more information
than its input: `random_linear_lambda_lower_exists`.

Everything else is proved and axiom-clean, including the alphabet-generic volume/averaging lower
bounds `lambda_ge_elias_volume` and `lambda_ge_entropy_volume` and their field specializations
`linear_lambda_ge_elias_volume` and `linear_lambda_ge_entropy_volume`, both halves of the
generalized Singleton bound (`linear_card_le_of_rate_radius`,
`linear_card_le_generalized_singleton`), the prime-field Reed-Solomon separation
`rs_lambda_large_prime`, the elementary `rs_codimension_one_list_size`, the [AGL23]
large-alphabet barrier
`large_alphabet_lambda_lower` with its `η = Θ(1/n)` consequence
`large_alphabet_card_ge_exp_of_inv_length`, the number-theoretic KKH sum-set estimate
`two_pow_mul_choose_le_card_sumSet` ([KKH26] Lemma 1, proved via a signed subset-sum
embedding and a resultant/root-of-unity argument), and — the deepest of them — [CZ25]'s
subspace-design theorem `subspaceDesign_lambda_le` with the four results derived from it, which
means `frs_lambda_le_capacity` and `um_lambda_le_capacity`, the statements that folded Reed-Solomon
and univariate multiplicity codes achieve list-decoding capacity, now hold unconditionally in-tree.
The KKH asymptotic result `exists_rs_asymptotic_Lambda_lower_bound` is likewise proved from the
concrete vanilla template; it carries smooth-domain existence as an explicit `supply` hypothesis
and does not depend on the sum-set estimate.

Two source-side weakenings apply throughout and are not repeated on each declaration: [CZ25] and
[AGL24] both state *average-radius* list-decodability, of which the plain `Λ` bound formalised here
is a consequence; and where a source constructs a code, the Lean existentially binds it rather than
reproducing the construction.

Two statements from [ABF26] §3 remain absent: one by decision and one awaiting primary-source
verification.

* Theorem 3.14 is not represented because the cited [JH01] primary source was unavailable for
  verification. `rs_codimension_one_list_size` records only the elementary theorem proved here.
* The algorithmic hardness barrier (Theorem 3.16, [CW07]) is **deliberately** absent: it needs a
  computational-hardness framework ArkLib does not have — an adversary/advantage/running-time
  layer — and without one, a statement of it would be vacuous or would be about something other than
  hardness.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  §3 is the source of every statement in this file.
* [Eli57] Elias. *List decoding for noisy channels*. 1957. The volume/averaging lower bound.
* [MS77] MacWilliams, Sloane. *The Theory of Error-Correcting Codes*. 1977. Chapter 10, §11,
  Lemma 7 gives the binary single-binomial-shell estimate used to derive the q-ary entropy form.
* [ST20] Shangguan, Tamo. *Combinatorial list-decoding of Reed-Solomon codes beyond the Johnson
  radius*. 2020. Theorem 1.2, the generalized Singleton bound.
* [BDG24] Brakensiek, Dhar, Gopi. *Improved field size bounds for higher order MDS codes*. IEEE
  Trans. Inf. Theory 70(10), 2024. Cited by [ABF26] at "Corollary 1.7, Thm 1.8" for the `ℓ = 2`
  case. **Locator unverified:** in the arXiv version (2212.11262v2) those numbers are a statement
  about MR tensor codes and an average-radius `LD-MDS(≤2)` corollary, and all of its items are
  `ε`-free *exact*-achievement results rather than the `η`-parameterized form; the journal version
  may renumber. Only [AGL23] visibly supports the `η`-form, of which [BDG24] is the `ε = 0`,
  `ℓ = 2`, linear-MDS corner. Check the journal PDF before relying on these locators.
* [AGL23] Alrabiah, Guruswami, Li. *AG codes have no list-decoding friends: approaching the
  generalized Singleton bound requires exponential alphabets*. arXiv:2308.13424, 2023. Generalizes
  [BDG24] to all `ℓ`; together they are the large-alphabet barrier.
* [GLMRSW22] Guruswami, Li, Mosheiff, Resch, Silas, Wootters. *Bounds for list-decoding and
  list-recovery of random linear codes*. 2022. Theorem 4.1.
* [BKR06] Ben-Sasson, Kopparty, Radhakrishnan. *Subspace polynomials and list decoding of
  Reed-Solomon codes*. 2006. Corollary 2.2.
* [GHSZ02] Guruswami, Håstad, Sudan, Zuckerman. *Combinatorial bounds for list decoding*. 2002.
  Corollary 20.
* [JH01] Justesen, Høholdt. *Bounds on list decoding of MDS codes*. 2001. Theorem 2; closed-access
  primary source and not formalised here.
* [CZ25] Chen, Zhang. *Explicit folded Reed-Solomon and multiplicity codes achieve relaxed
  generalized Singleton bounds*. 2025. Theorem B.5 and Corollary 2.21.
* [AGL24] Alrabiah, Guruswami, Li. *Randomly punctured Reed-Solomon codes achieve list-decoding
  capacity over linear-sized fields*. STOC 2024. Theorem 1.1 is `rs_random_domain_lambda_le`. Its
  predecessors, cited by [ABF26] as context, are [BGM23] Brakensiek, Gopi, Makam, *Generic
  Reed-Solomon codes achieve list-decoding capacity*, STOC 2023 (exponential alphabet); [GZ23] Guo,
  Zhang, *Randomly punctured Reed-Solomon codes achieve the list decoding capacity over
  polynomial-size alphabets*, FOCS 2023; and [AGGLZ25] Alrabiah, Guo, Guruswami, Li, Zhang, *Random
  Reed-Solomon codes achieve list-decoding capacity with linear-sized alphabets*, Advances in
  Combinatorics, 2025, which combines the two.
* [CW07] Cheng, Wan. *On the list and bounded distance decodability of Reed-Solomon codes*. SIAM J.
  Comput. 37(1), 2007. Not formalised, see above.
* [DG25dist] Diamond, Gruen. *On the distribution of the distances of random words*. ePrint
  2025/2010, 2025. Refines the volume estimate. **Not** ArkLib's existing `DG25`, which is the same
  authors' *Proximity Gaps in Interleaved Codes* — a different paper.
-/
