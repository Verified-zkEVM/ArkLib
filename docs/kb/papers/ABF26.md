---
kind: paper
bibkey: ABF26
title: "Open Problems in List Decoding and Correlated Agreement"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: https://proximityprize.org/
source_metadata: ../sources/ABF26/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/Basic/Entropy.lean
  - ArkLib/Data/CodingTheory/HammingBallVolume.lean
  - ArkLib/Data/CodingTheory/Erasure.lean
  - ArkLib/Data/CodingTheory/ExtensionCodes.lean
  - ArkLib/Data/CodingTheory/JohnsonBound/Family.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/Interleaved.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26Asymptotic.lean
  - ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean
  - ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean
  - ArkLib/Data/CodingTheory/ProximityGap/Errors.lean
  - ArkLib/Data/CodingTheory/ProximityGap/InformationSetLowerBound.lean
  - ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean
  - ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges/CapacityBounds.lean
  - ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean
  - ArkLib/Data/CodingTheory/SubspaceDesign.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/Interleaved.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean
  - ArkLib/Data/Polynomial/ClassicalWronskian.lean
  - ArkLib/Data/Polynomial/FoldedWronskian.lean
  - ArkLib/Data/Probability/Combinatorial.lean
---

# ABF26

## At A Glance

`ABF26` is Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement* (2026),
the survey manuscript accompanying the Ethereum Foundation **Proximity Prize**.
It collects the definitions, known bounds, and open problems around list decoding, proximity
gaps, and (mutual) correlated agreement for the code families used by modern IOP-based proof
systems, and states the prize challenges in terms of those quantities.

It is the paper that the whole ABF26 layer of `ArkLib/Data/CodingTheory` formalizes.
Section/definition numbers quoted in ArkLib docstrings (`ABF26 Definition 2.14`,
`ABF26 Theorem 2.18`, `ABF26 Theorem 3.2`, `ABF26 Claim B.1`, …) always refer to this
manuscript, not to the original sources it cites — those get their own keys (`GR08`, `GK16`,
`GG25`, `GX13`, `GW13`, `KSY14`, `Joh62`, `BCFW25`).

## What ArkLib Uses From This Paper

- **§2 preliminaries.** Definition 2.2 (`q`-ary entropy) → `CodingTheory.qEntropy`;
  Definition 2.3 (restricted Hamming distance) is not formalized;
  Definition 2.4 (Hamming-ball volume) → `CodingTheory.hammingBallVolume`;
  Definition 2.5 (the rate convention `ρ(C) = log_{|Σ|}|C| / n`, which fixes `ρ = k/(s·n)` for
  folded codes); Definition 2.8 (`Λ(C, δ, f)` and the maximised `|Λ(C, δ)|`) →
  `ListDecodability.Lambda`; Lemma 2.6 (MDS characterisation).
- **§2.4 code families.** Definition 2.9 (interleaved codes, consumed via the pre-existing
  `Code.interleavedCodeSet` / `^⋈`); Definition 2.13 (interleaved Reed–Solomon) →
  `ReedSolomon.Interleaved.irsCode`; Definition 2.14 (`(L,s)`-admissible `ω`) →
  `ReedSolomon.Folded.Admissible`; Definition 2.15 (folded Reed–Solomon, after `GR08`) →
  `ReedSolomon.Folded.frsCode`, with folded-point and encoder injectivity and the exact
  saturation formula `dim_frsCode_eq_min`.
- **§2.5 subspace designs.** Definition 2.16 (after `GX13`) → `CodingTheory.IsSubspaceDesign`;
  Lemma 2.17 (after `GG25`) → `CodingTheory.subspaceDesign_tau_lower`; Theorem 2.18 (after
  `GK16`) → `CodingTheory.isSubspaceDesign_frsCode` (folded-RS half) and
  `CodingTheory.isSubspaceDesign_umCode` (univariate-multiplicity half).
- **§2.6 extension codes.** Definition 2.19 (extension-field presentation) →
  `CodingTheory.ExtensionFieldPresentation`; Definition 2.20 (extension code) →
  `CodingTheory.extensionEncode`, packaged with its proved `F`-linearity as
  `extensionEncodeLinearMap` and with injectivity preservation `extensionEncode_injective`, plus
  the image-level `extensionCode` / `extensionCodeSubmodule`;
  the encoder identity on embedded messages → `extensionEncode_comp_algebraMap` (which needs
  **no** systematicity, unlike the remark following D2.20 — see `BCFW25.md`); Lemma
  2.21 (after `BCFW25` Lemma D.3) →
  `CodingTheory.lambda_extensionCode_eq_lambda_interleaved`; the Diamond–Posen minimum-distance
  equality → `CodingTheory.minDist_extensionCode`.
- **§3 list-decoding bounds.** Definition 3.1 (the `J_{q,ℓ}`, `J_q`, `J` radius family) →
  `JohnsonBound.Jqℓ`, the pre-existing `JohnsonBound.J`, and `JohnsonBound.Jcap`; Theorem 3.2
  (after `Joh62`) → `CodingTheory.johnson_bound_lambda_le_ell`; Corollary 3.3 (MDS list-size
  corollary) → the arbitrary-finite-alphabet metric theorem
  `CodingTheory.mds_johnson_lambda_le_of_rate_distance`, with field-linear wrapper
  `mds_johnson_lambda_le` and the three code-family instantiations
  `rs_lambda_le_johnson_mds`, `irs_lambda_le_johnson_mds`, `frs_lambda_le_johnson_mds`. The
  Plotkin regime → `CodingTheory.plotkin_card_le_ell`.
- **§1 prize carriers and §4 errors.** `ProximityGap/GrandChallenges.lean` contains the
  adjacent-grid and radius-one endpoint answers. `ProximityGap/Errors.lean` contains `epsPg`,
  `epsCa`, and their comparisons with affine-line `mcaError`. The information-set lower bound is
  in `InformationSetLowerBound.lean`.
- **§4–§5 bound catalogue.** `ProximityGap/CapacityBounds.lean` and
  `Connections/ListDecodingAndCA.lean` state the externally sourced upper/lower bounds and
  connections on the canonical error and list-size carriers. `LineDecoding.lean` uses the
  close-and-aligned formulation from GG25 Definition 3.1 and its MCA consequence; this corrects
  the missing close-set intersection in ABF26 Definition 4.20. The prize witness consuming the
  BCHKS25 upper bound is isolated in `GrandChallenges/CapacityBounds.lean`.
- **§3.15 and the KKH appendix.** `ListDecodability/Bounds/KKH26.lean` contains the concrete
  useful-family and sum-set templates; `KKH26Asymptotic.lean` derives the asymptotic list lower
  bound while carrying finite-field/smooth-domain existence as an explicit hypothesis.
- **§2 interleaving list size.** Lemma 2.10 is represented by
  `InterleavedCode.lambda_interleaved_le_choose_mul_pow` in
  `ListDecodability/Bounds/Interleaved.lean`, stated on the canonical `Code.Lambda` carrier.
- **§6 toy problem and erasure correction.** `ProofSystem/ToyProblem/` formalizes Constructions
  6.2 and 6.9, their completeness/security layer, and executable checked scalar-RS/row-wise IRS
  erasure decoders and extractors. `CodingTheory.eq_of_consistent_with_erased` supplies the generic
  metric-uniqueness ingredient. The paper's generic algorithm for every additive code and its
  operation bound remain outside ArkLib's current cost model.
- **Appendix A.2 multiplicity codes.** Definitions A.6 / A.7 (after `GW13`, `KSY14`) →
  `ReedSolomon.Multiplicity.umEvalOnPoints` / `umCode`.
- **Appendix B counting.** Claim B.1 →
  `Probability.exists_large_image_of_pairwise_collision_bound`.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/SubspaceDesign.lean`](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean)
  — D2.16 / L2.17 / T2.18, the largest ABF26 module.
- [`ArkLib/Data/Polynomial/FoldedWronskian.lean`](../../../ArkLib/Data/Polynomial/FoldedWronskian.lean)
  — the `GK16` machinery for T2.18's folded-RS half.
- [`ArkLib/Data/Polynomial/ClassicalWronskian.lean`](../../../ArkLib/Data/Polynomial/ClassicalWronskian.lean)
  — GK16 Definition 9 and Lemma 10 machinery for T2.18's univariate-multiplicity half.
- [`ArkLib/Data/CodingTheory/JohnsonBound/Family.lean`](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean)
  — §3 radius family, T3.2, alphabet-generic C3.3, and field/RS wrappers.
- [`ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean),
  [`Interleaved.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/Interleaved.lean),
  [`Multiplicity.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean)
  — §2.4 and §A.2 code families.
- [`ArkLib/Data/CodingTheory/ExtensionCodes.lean`](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean)
  — D2.19/D2.20 at both encoder and code-image level, L2.21, and the DP25 distance equality.
- [`ArkLib/Data/CodingTheory/Erasure.lean`](../../../ArkLib/Data/CodingTheory/Erasure.lean)
  — generic metric support for §6.2.
- [`ArkLib/ProofSystem/ToyProblem/`](../../../ArkLib/ProofSystem/ToyProblem)
  — exact/relaxed relations, Constructions 6.2/6.9, completeness and knowledge-soundness
  contracts, executable RS/IRS decoding/extraction, and neutral FRS reference points.
- [`ArkLib/Data/CodingTheory/HammingBallVolume.lean`](../../../ArkLib/Data/CodingTheory/HammingBallVolume.lean),
  [`Basic/Entropy.lean`](../../../ArkLib/Data/CodingTheory/Basic/Entropy.lean)
  — D2.4 / D2.2 support for the §3 lower bounds.
- [`ArkLib/Data/Probability/Combinatorial.lean`](../../../ArkLib/Data/Probability/Combinatorial.lean)
  — Claim B.1.
- [`ArkLib/Data/CodingTheory/ProximityGap/Errors.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean),
  [`InformationSetLowerBound.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/InformationSetLowerBound.lean),
  and [`GrandChallenges.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean)
  — §1 and §4 numeric MCA/CA infrastructure and prize carriers.
- [`CapacityBounds.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean),
  [`LineDecoding.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean),
  and [`Connections/ListDecodingAndCA.lean`](../../../ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean)
  — the §4–§5 theorem catalogue.
- [`ListDecodability/Bounds/KKH26.lean`](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26.lean)
  and [`KKH26Asymptotic.lean`](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26Asymptotic.lean)
  — the appendix templates and Theorem 3.15.
- The running faithfulness ledger is
  [`docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`](../audits/open-problems-list-decoding-and-correlated-agreement.md);
  it, not this page, is the place to record per-statement coverage.

## Version Notes

- `ABF26` is a manuscript accompanying the Proximity Prize; there is no ePrint number, so cite
  it by key and by section/statement number only.
- **The PDF and the authors' current source diverge.** The reference PDF used for ArkLib's
  transcriptions (`~/abf26-refs/ABF26.pdf`, PDF creation date **2026-04-08**) is a build that
  predates several upstream corrections. The concrete instance that matters for ArkLib:
  **Definition 3.1 prints the Johnson list factor as `ℓ/(ℓ−1)`, but the correct factor is
  `(ℓ−1)/ℓ`.** The printed form is mathematically wrong — `ℓ/(ℓ−1) > 1` makes
  `J_{q,ℓ} > J_q`, i.e. a *finite* list budget would buy a larger radius than the `ℓ → ∞`
  limit, and it makes the Johnson denominator negative. The authors fixed this upstream on
  **2026-06-13**. ArkLib's `Jqℓ` uses `(ℓ−1)/ℓ`, matching the classical statement (GRS12
  Exercise 7.8, key `codingtheory`); the deviation from the PDF is deliberate and documented at
  the definition.
- Practical consequence: **when re-checking an ArkLib statement against ABF26, check the
  authors' current source, not only the 2026-04-08 PDF.** A mismatch against the PDF is not by
  itself evidence of an ArkLib transcription error.

## Known Divergences From ArkLib

Four source discrepancies affect ArkLib's formal interface. ArkLib uses the corrected forms.

1. **Definition 3.1's list factor is inverted** (`ℓ/(ℓ−1)` for `(ℓ−1)/ℓ`) — see Version Notes.
   Fixed in Lean; already fixed upstream.
2. **Definition 2.14 omits the intra-orbit condition.** As printed, admissibility quantifies
   over `binom(L,2)` — *distinct* pairs only — so nothing constrains `α` against itself and
   `ω = 1` is admissible for every `L` and every `s`, contradicting the definition's own stated
   purpose. Under the literal Def 2.14 the folded-RS distance claim is false: brute force over
   `(ZMod 11)^k` with `L` the quadratic-residue subgroup, `s = 2`, `ω = 1` gives true minimum
   distances `5, 4, 3, 2, 1` for `k = 1..5` against the formula's `5, 5, 4, 4, 3`.
   `ReedSolomon.Folded.Admissible` therefore adds the intra-orbit clause
   `α · ωⁱ ≠ α` for `0 < i < s`; together with the printed clause this is exactly injectivity
   of `(α, i) ↦ α · ωⁱ`, which is `GR08`'s own setup. The strengthening is
   **hypothesis-position only**, so every ArkLib FRS theorem is *weaker* than ABF26's printed
   claim, never stronger.
3. **Theorem 2.18 has two missing hypotheses, not one.**
   (a) There is no order condition on `ω`. GK16 Lemma 12, the result T2.18 rests on, requires
   `γ` to be a **generator** of `F*`; without it T2.18 is false (compiled refutation over
   `𝔽₁₇` with `ι = Fin 7`, `s = 2`, `k = 3`, `ω = −1`). ArkLib restores it as
   `hω_gen : orderOf ω = Fintype.card F − 1`.
   (b) `0 ∈ L` is permitted, and with `0 ∈ L` T2.18 is false **even with** the order condition
   (compiled refutation: `ZMod 5`, `domain = (0, 1)`, `s = 3`, `k = 2`, `ω = 2` a generator, so
   `Σ dim Aᵢ / n = 1/2 > 1/3 = dim A · τ(1)`). In ArkLib this is excluded as a side effect of
   the strengthened `Admissible` (the intra-orbit clause rules out `α = 0` for `s ≥ 2`), so the
   Lean statement is correct as it stands — but the clause is load-bearing for T2.18.
   Note that `GK16` itself is not affected by (b): its §4.2 setup requires `F_q(α) = F_{q^r}`
   with `|S_α| = r·t`, which excludes `α = 0`.
4. **Definition 4.20 omits the close-set intersection required by line decoding.** Its printed
   conclusion counts every challenge satisfying affine alignment, even when the sampled line is
   not close to the selected codeword. GG25 Definition 3.1 counts challenges satisfying both
   proximity and alignment, and GG25 Theorem 3.5 proves the MCA implication for that definition.
   The printed ABF26 pair is false: for the zero code of length two over `𝔽₃`, take
   `δ = 1/2`, `a = 1`, and `b = n+1 = 3`. The printed line-decodability condition holds because
   every codeword family is identically zero and hence aligns on all three challenges. An ambient
   affine line whose two coordinates vanish at distinct challenges nevertheless has MCA bad-event
   probability at least `2/3`, exceeding the claimed `a/|F| = 1/3`. Consequently
   `IsLineDecodable` and `IsLineDecodable.mcaError_le` follow GG25 rather than the printed ABF26
   definition and theorem.

Directions in which ArkLib is *weaker* than the paper (all deliberate, none unsound):

- `subspaceDesign_tau_lower` restricts L2.17's conclusion to `r ≥ 1`. This is a genuine
  correction, not a narrowing: both ABF26 L2.17 and GG25 L2.16 are literally false at `r = 0`,
  since `dim A ≤ 0` forces `A = ⊥` and the design inequality degenerates, leaving `τ 0`
  unconstrained. It also adds `hτ_nonneg`, needed only to carry the `C = ⊥` branch; the
  source-shaped `C ≠ ⊥` form is `subspaceDesign_tau_lower_of_ne_bot`.
- D6.4/L6.5's algorithm and running-time claim are absent. Only their reusable metric uniqueness
  ingredient is present; no vacuous cost-free existence predicate is advertised.

The UM half of T2.18 is instead slightly more general than the printed survey statement:
`isSubspaceDesign_umCode` needs no separate `|F| > |ι|` assumption because the evaluation
domain is already an injection, and it uses the mathematically sufficient endpoint-inclusive
guard `k ≤ ringChar F` for degree-`< k` messages.

## Open Formalization Gaps

- **D2.3.** Restricted Hamming distance `Δ_T` is not formalized; only the full-domain Hamming
  and relative-distance notions exist.
- **§3 remainder.** Theorems 3.4–3.13 have a Lean statement under
  `ArkLib/Data/CodingTheory/ListDecodability/Bounds/`; Definition 3.1 / Theorem 3.2 /
  Corollary 3.3 (the Johnson family) are the pre-existing `Jqℓ` / `johnson_bound_lambda_le_ell` /
  `mds_johnson_lambda_le_of_rate_distance` under `JohnsonBound/`. **3.16 is absent by
  design; 3.15 is present in the KKH modules.** Theorem 3.14 still awaits primary-source
  verification of [JH01] Theorem 2; the proved `rs_codimension_one_list_size` is a different
  internal lemma. What remains for the admitted catalogue is *proof*, plus the fidelity gaps
  below.
  - Proved in-tree and axiom-clean: Lemma 3.7 (Elias volume bound, by the paper's own averaging
    argument), both halves of Theorem 3.9, Corollary 3.8, Theorem 3.13, and — the deepest
    of them — Theorem 3.4 at [CZ25] Theorem B.5's `(k−1)`-level premise, which makes Corollary 3.5,
    the two `η`-forms, and the univariate-multiplicity sibling axiom-clean along with it; and
    Theorem 3.10, whose consequence `large_alphabet_card_ge_exp_of_inv_length` is axiom-clean with
    it. The internal codimension-one Reed-Solomon interpolation lemma is also axiom-clean.
    Six of these landed from one round of Aleph prover runs (ArkLib #724–#728, #732).
  - Admitted with the source statement in the docstring: Theorem 3.6, Theorem 3.11, Theorem 3.12.
    `random_linear_lambda_lower_exists` is *derived* from Theorem 3.11, so it inherits that admit.
  - **§3 numbering follows the tex, not the cached PDF.** The cached [ABF26] build stops at Theorem
    3.14 and numbers the [CW07] barrier 3.15; the tex inserts the [KKH26] asymptotic Reed-Solomon
    lower bound as **Theorem 3.15** and pushes [CW07] to **3.16**. Theorem 3.15 is now derived from
    the formalized appendix templates. Theorem 3.16 stays unformalized **by decision** — it needs
    a computational-hardness framework.
  - Fidelity gaps to close, in rough priority order: (i) Theorem 3.14 needs the closed-access JH01
    primary source before a formal statement can be justified; (ii) Theorem 3.10 is stated for a
    linear code over a field, whereas the paper states it for an arbitrary code
    `C : Σ^k → Σ^n`;
    (iii) Theorem 3.10's rate is pinned by equality, hence vacuous at irrational `ρ` (the `∃ n₀`
    concern is settled: the threshold sits outside `∀ η`, so the paper's `η = Θ(1/n)` corollary is
    reachable and is derived). The old Theorem 3.11 off-by-one and Theorem 3.12 all-real
    overgeneralisation are closed: Lean now uses `Lambda < L` / `L ≤ Lambda` for [GLMRSW22] and
    rational parameters for [BKR06]. The checked [MS77] source is a binary shell estimate; the
    q-ary ball statement remains valid as a proved generalisation, not a verbatim attribution.
  - **Two paper defects found in §3 and owed upstream**: Theorem 3.9 drops [ST20]'s integrality
    convention *and* the non-negative-exponent guard its pigeonhole needs, and is false without
    either; Theorem 3.4's premise, read at Theorem 2.18's printed profile, is false (it needs
    [CZ25]'s `(k−1)` level). Both have compiled axiom-clean counterexamples.
- **L2.10.** The interleaved-code list-size comparison is present as an external `[GGR11]` leaf;
  proving it in-tree remains open.
- **§6.** A cost model for erasure correction, without which D6.4/L6.5 carry no content; and
  §6.4.1 Lemma 6.12, the intended consumer of Claim B.1. Claim B.1 and its supporting probability
  lemmas exist; the erasure algorithm, its cost model, and the Lemma 6.12 application do not.
- **§4, §5.** The cited bounds and list-decoding/CA connections are catalogued with 18 new
  external admits, while their arithmetic corollaries and carrier bridges are proved in-tree.
  The random-RS MCA result and the draft-only MCA conjecture remain outside this layer. See the
  ledger for each statement's source-side guards and normalization choices.

## Source Access

- Source metadata: [`../sources/ABF26/metadata.yml`](../sources/ABF26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
- Prize site: <https://proximityprize.org/>
