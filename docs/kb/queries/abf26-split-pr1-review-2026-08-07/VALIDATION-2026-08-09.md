# PR #701 review validation — 2026-08-09

This is the current-tip companion to the immutable 2026-08-07 review snapshot. It validates
the snapshot findings, the subsequent fix sweep, and an independent adversarial pass against
ArkLib, `~/abf26-refs/`, and `~/ef-millenium/`. The snapshot reports themselves remain unchanged
because they describe commit `ffa0733a`.

## Validation rule

A declaration was not removed merely because `rg` found no current consumer. Tactic use,
downstream branches, and a documented staged interface all count. In particular,
`Fin.induction_three` has concrete `simp only` consumers in the later toy-problem split and is
correctly retained. Conversely, a future-use claim does not rescue an abstraction whose theorem
is true for every input for purely logical reasons.

## Consolidated disposition

| Review | Validated disposition at the current tip |
| --- | --- |
| R1 Probability | The Lemma 6.12 narrative, exact dot-product equality, casts, `d = 0` documentation, and minor style findings were corrected. The Schwartz–Zippel duplication is now structurally eliminated: the ABF-shaped theorem derives from the pre-existing arbitrary-sampling-set result. Indicator unfolding has one primitive in `ProbabilityTheory`, with compatibility wrappers. The “dead” `Fin.induction_three` finding is rejected because a later split has concrete tactic consumers. Zero current consumers of the staged probability results is not by itself a defect. |
| R2 Combinatorial | Claim B.1 was rechecked clause-by-clause and remains faithful, non-vacuous, and directionally correct. Citations, the `≤` conclusion spelling, broken references, downstream-use prose, and plain-`Prop` probability hypothesis are corrected. The proof-only fiber helpers are private, so their finite-type specialization is no longer presented as a general public Finset API. The intended later Lemma 6.12 consumer justifies retaining the theorem. |
| R3 Distance/list/erasure | Wiki/type/docstring issues, entropy reuse, list-bound bridge types, and the `disagreementCols` bridge were corrected. `Lambda` now uses `Set.encard`; an infinite list contributes `⊤`, while finite hypotheses occur only at `ncard`/numeric bridges. The tautological erasure-support predicate and arbitrary-function existence theorem were removed. Their substantive metric core was generalized to `Code.eq_of_disagreementCols_subset_of_card_lt_minDist` and reused by erasure consistency. |
| R4 Johnson | The public ABF26 T3.2 theorem is guard-free, with the Plotkin corner handled internally. `Jqℓ` is defined through the existing `J`; `Jcap` is integrated beside it. Mathlib-equivalent remapping declarations were removed. Real/NNReal/ENNReal list-decoding bridges and the first RS consumer are present. The retained `lin_shift_*` family is a distinct field-translation API, not removable merely because its immediate caller changed. The field-alphabet MDS corollary remains an accurately documented scope gap, not a false claim. |
| R5 RS families | The general interleaved-code finrank theorem, folded-domain RS bridge, shared `s = 1` encoder lemma, admissibility strengthening, decidable conjunct order, exact MDS wording, redundant hypotheses, audit text, and module inventories were corrected. The stronger admissibility condition is load-bearing and grounded in GR08/GK16; it is not silently passed off as literal ABF26 D2.14. |
| R6 Subspace/Wronskian | L2.17 is available for every `r ≥ 1`, in source-shaped nonzero-code and total nonnegative-profile forms. T2.18 documents both source defects and retains its necessary `L`/membership data because the proof uses both admissibility clauses. The determinant, root-multiplicity, adapted-basis, finite-dimensional transfer, composition-degree, Frobenius, and Kummer helpers now live in `ToMathlib`. `ker_proj_eq_vanish_at` is retained as the carrier-faithfulness bridge for the definition; zero direct consumers is not evidence that it is meaningless. |
| R7 Extension codes | The presentation wraps Mathlib `Algebra`/`Basis` rather than recreating them. Basis-free span and presentation-independence theorems are proved; `IsSystematic` has coordinate-level consumers. Redundant hypotheses, universes, citations, notation, carrier docs, and overstatements were corrected. Encoder-level D2.20 and the DP distance equality remain explicitly missing; the image-level API does not claim to prove them. |
| R8 Duplication | D1–D6 and D9–D10 were resolved by reuse/bridges/generalization; D7 helpers were promoted to their generic homes; D11 was linked through the module-alphabet Singleton development. D12 is rejected as a deletion argument: `ExtensionFieldPresentation` is paper-shaped data whose fields are canonical Mathlib objects and whose methods support theorem statements. D13 is rejected because the later split consumes the Fin induction lemmas. D8 is treated as a documented project namespace choice, not mathematical duplication; the probability theorem chain itself is consolidated. D14 disappeared with the remap cleanup and uniform-equivalence promotion. |
| R9 Vacuity/axioms | The exhaustive clean axiom/sorry/build findings remain valid. The two genuine semantic issues found after that snapshot—erasure tautology and infinite-list collapse—are now removed. Pre-existing `sorryAx` carriers remain outside this contribution and no new declaration depends on them. |
| R10 Docs/integration | Current docs now distinguish proved, partial, and missing items; citations and module routing are corrected. Generated KB output is restored to `origin/main` because feature PRs must not commit it. The immutable snapshot remains historically accurate, and this file supplies the current-tip disposition. The GitHub PR body still needs to be synchronized at final handoff if the branch is pushed. |
| R11 Library value | The RS/Johnson and list-decoding crossings, Mathlib reuse, universe/instance cleanup, entropy integration, systematic-code consumers, and generic helper placement are addressed. “Nine modules have no importer” is rejected as a standalone deletion criterion: several are foundations for named later splits. Public statements are retained only where mathematically meaningful; proof-only combinatorial helpers and the vacuous erasure API are not. |

## Independent-review corrections

The later independent pass initially overclassified three items as merge blockers. They are
corrected here:

1. Missing UM-T2.18, encoder-level extension-code, module-alphabet MDS, and DP-distance results
   are honest staged scope gaps, not defects in the theorems that are present. Documentation must
   not claim that the full paper item is complete.
2. Lack of an immediate importer is evidence to investigate, not a deletion rule. Concrete later
   branch consumers and stable foundational value were checked before retaining APIs.
3. Generated knowledge-base files and a stale PR description are integration defects, not
   mathematical defects; they nevertheless block merge until the diff/description is clean.

## Remaining formalization scope (not claimed complete by this PR)

- the univariate-multiplicity half of ABF26 T2.18;
- an encoder-level extension-code abstraction and its systematic encoder equality;
- the Diamond–Posen minimum-distance equality;
- a module-alphabet MDS Johnson corollary for the paper's interleaved-RS motivating case;
- an algorithm/cost model for ABF26 D6.4/L6.5.

These are recorded as missing/partial in the audit. None is represented by a vacuous theorem or
hidden behind `sorry` in this contribution.
