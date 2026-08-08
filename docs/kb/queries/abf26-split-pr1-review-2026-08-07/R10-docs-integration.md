# R10 — Documentation accuracy, conventions, and repo integration (PR #701 @ `ffa0733a`)

Scope: PR body, `docs/wiki/coding-theory-conventions.md`, `docs/wiki/probability-conventions.md`,
`docs/wiki/README.md`, `docs/wiki/repo-map.md`,
`docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`, `ArkLib.lean`,
module docstrings of all 29 touched `.lean` files.

Severity summary: **0 CRITICAL, 0 HIGH, 7 MEDIUM, 7 LOW.**
No mathematical defect found in this cluster; every finding is doc-accuracy / convention /
integration. All headline theorems the docstrings advertise as "proved, sorry-free" really are
(verified by `#print axioms`, see Clean bill).

---

### [MEDIUM] The PR body is materially stale: it advertises 2 unproven admits that no longer
exist, and never mentions a whole new 406-line module

- **Where**: PR #701 body, §"What lands"/D and §"Verification".
- **What's wrong** (each item verified against `ffa0733a`):
  1. `"SubspaceDesign.lean (new) — ... the layer's **only two `sorry`s**, both tagged external
     admits: subspaceDesign_tau_lower (L2.17, [GG25]) and frs_is_subspaceDesign_gk16 (T2.18,
     [GK16])"` — **FALSE**. Both were proved by `b8b4b87b` and `dab6d75c`. There are **zero**
     `sorry` tokens in any PR-touched module.
  2. `"Sorry census: exactly 2 new proof-term sorries"` — **FALSE**, it is 0.
  3. `"Exhaustive axiom probe: 400 declarations across all 21 touched Lean modules ... the only
     sorryAx carriers are the two admits above plus the pre-existing Fin.sumCases WIP"` —
     the module count is stale (**29** `.lean` files are touched, 11 of them new), and the
     `sorryAx` sentence is stale (only the pre-existing `Fin.sumCases` remains).
  4. `ArkLib/Data/Polynomial/FoldedWronskian.lean` (**406 lines, brand-new module**, the entire
     GK16 Def-11/Lemma-12 toolkit) is **not mentioned anywhere in the body**. Neither is
     `LinearCode.singleton_bound_module` (the new module-alphabet Singleton bound that carries
     L2.17), nor `ProbabilityTheory.Pr_decide_eq_tsum_indicator` added to
     `Data/Probability/Notation.lean` (+11).
  5. `"Adversarial review gate (8 independent reviewers ...): 0 critical, 0 high findings ...
     Medium/low findings remediated in the final commit"` — that gate ran at `14d88a31`; four
     later commits (`b8b4b87b`, `df245b71`, `7690cafb`, `dab6d75c`, ≈1200 new lines) post-date
     it. A **second, 5-reviewer** gate covered the GK16 work (`ffa0733a`, "0 critical/high/
     medium, 3 low"), which the body does not mention. "the final commit" is no longer final.
  6. `"lake build green (4196 jobs)"` — now **4197** jobs (main drift).
  7. `"the (file, error-kind) multiset is byte-identical to origin/main"` — now differs in
     exactly two entries, **both attributable to main's drift, not to the PR**
     (`ProximityGap/Folding.lean : ERR_IBY` 2→1 from main's own commits; and
     `BCIKS20/AffineSpaces.lean : ERR_NUM_LIN` embeds the file's line count, which the PR's
     one-line `open Probability` bumps 2326→2327). See "Clean bill" — the substantive claim
     (**zero new lint from the PR**) is TRUE and I verified it.
- **Evidence**:
  - `git diff --name-only 4f386913..ffa0733a -- '*.lean' | wc -l` → 29; `git diff --name-status
    ... | grep '^A'` → 11 new files, incl. `ArkLib/Data/Polynomial/FoldedWronskian.lean`.
  - grep for `sorry` across all PR-touched files: only comments plus the pre-existing
    `ArkLib/Data/Fin/Basic.lean:333`.
  - `(session-local probe) r10-axioms.lean` → `subspaceDesign_tau_lower` and
    `frs_is_subspaceDesign_gk16` both `[propext, Classical.choice, Quot.sound]`.
  - `SCRATCH/lintk-main.txt` vs `SCRATCH/lintk-pr.txt` (linter output with line numbers
    stripped): 2-line diff, both explained above; **zero** lint hits in any of the 11 new files.
  - `git log --format=%B -1 ffa0733a` (the 5-reviewer gate).
- **Refutation attempt**: I checked whether the body might have been written against an earlier
  head and the PR retargeted — no; the body claims are simply out of date. I also verified the
  body's *other* claims and most hold (see Clean bill), so this is staleness, not fabrication.
- **Suggested fix**: (per the standing instruction, **we must not edit the PR body**) — ask the
  author to refresh it: 0 sorries, 29 modules / 11 new, add `FoldedWronskian.lean` +
  `singleton_bound_module` to §D, and re-word the review-gate paragraph to cover both gates.

---

### [MEDIUM] `docs/wiki/coding-theory-conventions.md` states two facts about existing API that
are provably wrong (both about `Code.dist` / `‖C‖₀`)

- **Where**: `docs/wiki/coding-theory-conventions.md:68-69` and the Type-conventions table row at
  `:121`; also `:66` (`Δ₀'`).
- **What's wrong**:
  - `":68  ‖C‖₀ — dist C (the inf-of-pairwise-distance form, ℕ∞)."` → `Code.dist C : ℕ`, not `ℕ∞`.
  - `":69  Distinct from Code.minDist C : ℕ which uses an existential rather than infimum."` →
    **both** are `sInf` of a set carved out by existentials. The real difference is `≤ d` vs
    `= d` inside the set-builder. As written, the sentence is wrong on both halves.
  - `":121  | Min distance of a code (absolute) | ℕ (Code.minDist) / ℕ∞ (dist, ‖C‖₀) |"` → both
    are `ℕ`; there is no `ℕ∞` form here (`dist' : ℕ∞` is the *computable* variant, which the
    table lists elsewhere).
  - `":66  Δ₀'(u, C) — distFromCode' C u (computable variant, ℕ)"` → it is `ℕ∞`.
- **Evidence**: `(session-local probe) r10-types.lean` / `r10-types2.lean` output:
  `@Code.dist : ... → Set (n → R) → ℕ`, `@Code.distFromCode' : ... → ℕ∞`, and
  `#print Code.minDist` = `fun C => sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ Δ₀(u, v) = d}`, vs
  `Distance.lean:167` `dist C := sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ Δ₀(u,v) ≤ d}`.
- **Cross-check that makes this worse**: the *same PR* adds a "## Type conventions" block to
  `ArkLib/Data/CodingTheory/Basic/Distance.lean:41-51` which says
  `"Min distance of a code (absolute): ℕ — Code.minDist, ‖C‖₀"` — **correct**, and in direct
  contradiction with the new wiki page. (The Distance.lean block has its own error:
  `"Computable variants: ℚ≥0 — δᵣ', Δ₀'"` — `Δ₀'`/`dist'` are `ℕ∞`.) The likely source of the
  wiki error is the *pre-existing* prose 20 lines further down in the same docstring
  (`Distance.lean:68`, "`dist C` ... the infimum (in `ℕ∞`)"), which the PR did not fix.
- **Refutation attempt**: I checked whether `dist` might be `ℕ∞` on `origin/main` and got
  narrowed by the PR — no, `Distance.lean:167` is untouched by this PR and is `ℕ` on both.
- **Suggested fix**: correct the three rows; fix `Distance.lean:41-51`'s "Computable variants"
  line and the stale `ℕ∞` in the pre-existing "Main Definitions" paragraph while in there.

---

### [MEDIUM] The conventions page's normative `<codeFamily>_<quantity>_<regime>_<authors><year>`
scheme has **zero** conforming instances in the tree, and the PR's own new theorems violate it

- **Where**: `docs/wiki/coding-theory-conventions.md:12-43` ("Theorem naming").
- **What's wrong**: all five worked examples (`linear_epsCA_1_5_johnson_bgks20`,
  `rs_epsMCA_johnson_range_bchks25`, `rs_epsCA_breakdown_cs25`,
  `linear_lambda_ge_elias_volume_eli57`, `rs_lambda_high_rate_jh01`) plus the disambiguation
  example `rs_epsCA_bchks25_item2` **do not exist anywhere in `ArkLib/`**. The page hedges
  generically at :5-10 ("several examples below are drawn from [the next split]") but *every*
  example is from the next split, so a reader of this PR cannot check the convention against a
  single real name. Meanwhile the statement-level bounds this PR *does* add do not follow it:
  | new decl | deviation |
  |---|---|
  | `mds_johnson_lambda_le` | slot order is family_regime_quantity, and **no `<authors><year>`** (ABF26 C3.3) |
  | `johnson_bound_lambda_le_ell` | **no `<codeFamily>`**, no `<authors><year>` (ABF26 T3.2 [Joh62]) |
  | `johnson_card_le_ell`, `plotkin_card_le_ell` | no family, no author-year; `card` is not one of the listed `<quantity>` values |
  | `subspaceDesign_tau_lower` | family ✓, but `tau` is not a listed quantity and there is no `_gg25` |
  | `lambda_extensionCode_eq_lambda_interleaved` | quantity-first, no `_bcfw25` (the audit row credits BCFW25 Lem D.3) |
  Only `frs_is_subspaceDesign_gk16` is close (`frs` + `gk16`), and even it uses `is_<Property>`
  rather than a `<quantity>`.
- **Evidence**: `grep -rn "<name>" ArkLib/ --include=*.lean` returns 0 files for all six
  examples; the new-declaration list is `git diff 4f386913..ffa0733a` filtered to
  `theorem|lemma|def|...` lines.
- **Refutation attempt**: I checked whether the scheme is meant to apply only to ε-error bounds
  (in which case `mds_johnson_lambda_le` would be out of scope) — no: the page says "bound an
  ε-error **or list-size** for a specific code family", and `lambda` is explicitly one of the
  `<quantity>` slots, so list-size theorems are squarely in scope.
- **Suggested fix**: either rename the new list-size theorems to fit
  (`mds_lambda_johnson_abf26`, `linear_lambda_johnson_joh62`, …), or relax the page to describe
  the scheme as aspirational and mark each example row `(next split)` individually.

---

### [MEDIUM] The conventions page documents identifiers that do not exist and are **not** marked
"next split"

- **Where**: `docs/wiki/coding-theory-conventions.md:49`, `:128`, `:130`, `:177`.
- **Classification of every Lean identifier / path on the page**:
  - **(a) exists** — `qEntropy`, `Jqℓ`, `Jcap`, `Lambda`, `closeCodewordsRel`,
    `hammingBallVolume`, `frsEvalOnPoints`, `IsMDS`, `IsSubspaceDesign`, `Admissible`,
    `ExtensionFieldPresentation`, `WordStack`, `InterleavedWord`, `ReedSolomon.code`,
    `Folded.frsCode`, `Interleaved.irsCode`, `Multiplicity.umCode`, `extensionCode`,
    `LinearCode.rate`, `minRelHammingDistCode`, `relDistFromCode(')`, `distFromCode(')`,
    `hammingDist`, `hammingNorm`, `dist`, `dist'`, `minDist`, `relHammingBallInterleavedCode`,
    `interleaveCode`, `interleave`, `interleave₂`, `stackify`, plus all four file paths
    `Basic/{Distance,RelativeDistance,LinearCode}.lean`, `InterleavedCode.lean`,
    and `ProximityGap.*` as a namespace. All notation strings verified against their
    declarations (see Clean bill).
  - **(b) missing but explicitly marked "(next split)"** — acceptable:
    `restrictedRelHammingDist` + `Δ[T]` (:50, :95-97, :126), `IsFAdditive` (:51),
    `LineDecodable` at :51, and the four paths `ProximityGap/Errors.lean`,
    `ProximityGap/CapacityBounds.lean`, `ListDecoding/Bounds.lean`,
    `Connections/ListDecodingAndCA.lean` (:7-9).
  - **(c) missing and presented as current — FINDINGS**:
    - `epsCA`, `epsMCA` at **:49** (listed as current "Paper-named function" examples).
    - `epsCA`, `epsMCA`, `Lambda` at **:128** (Type-conventions "Proximity radius δ argument" row
      — of the three only `Lambda` exists, and *its* `δ` is `ℝ`, so the claimed
      "`ℝ≥0` (preferred)" convention has **no** instance in the tree).
    - `epsCA`, `epsMCA`, `epsPG` at **:130** (ε-errors row) — none exist.
    - `LineDecodable` at **:177** (File/namespace-layout section) — unmarked here, unlike :51.
    - **`IsMDS` at :176 is mis-namespaced**: the page says `CodingTheory.*` holds it; it is
      `LinearCode.IsMDS` (`Basic/LinearCode.lean:297`, inside `namespace LinearCode`).
- **Evidence**: `grep -rn "\bepsCA\b" ArkLib/ --include=*.lean` → 0 files (likewise `epsMCA`,
  `epsPG`, `LineDecodable`, `IsFAdditive`, `restrictedRelHammingDist`);
  `#check @LinearCode.IsMDS` succeeds, `@CodingTheory.IsMDS` does not.
- **Refutation attempt**: I checked whether `epsCA`/`epsMCA` might live under a namespace my
  grep missed — no, `grep -rn epsCA ArkLib/` returns nothing at all.
- **Suggested fix**: mark :49/:128/:130/:177 rows `(next split)` the way :50/:51/:126 already
  are, and change `IsMDS` → `LinearCode.IsMDS` at :176.

---

### [MEDIUM] The audit matrix's §3 rows are **not** "brought to the post-PR tree" — the PR's
largest new file (859 lines) closes three §3 items that the audit still records as
missing/present-but-different

- **Where**: `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`,
  "## Section 3: List Decoding" table (untouched by the PR — `git diff` shows no §3 hunk).
- **What's wrong**:
  - `Definition 3.1 Johnson functions J_{q,ℓ}, J_q, J | present-but-different | ... not the
    paper's full three-function family` — **stale**: `JohnsonBound/Family.lean` adds `Jqℓ` and
    `Jcap`, completing the family.
  - `Theorem 3.2 Johnson bound | present-but-different | ... rather than the exact paper
    packaging` — **stale**: `johnson_bound_lambda_le_ell` *is* the exact paper packaging,
    proved, axiom-clean.
  - `Corollary 3.3 MDS coarse Johnson corollary | **missing** | ... not present as a named
    result` — **FALSE at this commit**: `CodingTheory.mds_johnson_lambda_le` exists, is proved
    and axiom-clean.
  - Consequential: `Lemma 3.7` / `Corollary 3.8` notes still say "Depends on missing
    Elias/Hamming-volume formalization"; the volume (`hammingBallVolume`, D2.4) and the entropy
    (`qEntropy`, D2.2) now exist.
  This directly contradicts the PR body's "Items landing with later splits stay marked
  missing/deferred" — these items land *here*.
- **Evidence**: `git diff 4f386913..ffa0733a -- docs/kb/audits/...` contains no `## Section 3`
  hunk; `#print axioms CodingTheory.mds_johnson_lambda_le` →
  `[propext, Classical.choice, Quot.sound]`.
- **Refutation attempt**: I re-read the whole audit file in case §3 was updated elsewhere (e.g. a
  new §3.1 subsection) — it was not; §3's table is byte-identical to the merge-base.
- **Suggested fix**: update the D3.1 / T3.2 / C3.3 rows (and the L3.7/C3.8 dependency notes) in
  the same PR, in the same format as the §2 rewrite.

---

### [MEDIUM] The audit matrix's "Existing Inconsistencies" and Roadmap sections are contradicted
by the PR itself

- **Where**: same file, "## Existing Inconsistencies" item 5, and "### Phase 1" item 4 /
  "### Phase 3" items 1-5, "### Phase 6" item 2.
- **What's wrong**:
  - Item 5 reads: *"Several code families used centrally by the paper are absent. Folded
    Reed-Solomon, univariate multiplicity codes, subspace-design codes, and extension-field codes
    are not yet represented directly in ArkLib."* — **all four are added by this PR**
    (`ReedSolomon/Folded.lean`, `ReedSolomon/Multiplicity.lean`, `SubspaceDesign.lean`,
    `ExtensionCodes.lean`). Flatly false at `ffa0733a`.
  - Phase 1 item 4 ("Add a maximized list-size function `listSize` or `Lambda`") — done here.
  - Phase 3 items 1-5 (IRS API, FRS + admissibility, UM codes, extension presentations/codes,
    subspace designs) — all five done here.
  - Phase 6 item 2 ("Add an erasure-correction abstraction at the coding-theory layer, with the
    generic additive-code existence theorem") — done here (`Erasure.lean`).
- **Evidence**: the four modules exist and their headline decls are axiom-clean (probe above);
  the audit text is unchanged in the diff.
- **Suggested fix**: strike item 5 and tick off the completed roadmap items, or add a dated
  "status as of this PR" line.

---

### [MEDIUM] The PR adds 11 new citation keys, **none** of which resolve in
`blueprint/src/references.bib` — a direct `CONTRIBUTING.md` / `blueprint-and-citations.md`
violation, nearly tripling the repo's dangling-key debt

- **Where**: `Erasure.lean`, `ExtensionCodes.lean`, `JohnsonBound/Family.lean`,
  `ReedSolomon/{Folded,Interleaved,Multiplicity}.lean`, `SubspaceDesign.lean`,
  `Polynomial/FoldedWronskian.lean`, `Probability/Combinatorial.lean`.
- **Source**: `CONTRIBUTING.md` §Citation Standards: *"All academic papers must have entries in
  `blueprint/src/references.bib`. When adding a new paper, add the BibTeX entry, use the citation
  key in your Lean file, and list it in the References section."*
  `docs/wiki/blueprint-and-citations.md` §Citation Workflow steps 3-4 add the
  `docs/kb/papers/KEY.md` obligation.
- **What's wrong**: new dangling keys are
  `ABF26, BuenzCFW25, GG25, GK16, GR08, GRS12, GuruswamiRS12, GW13, GX13, Joh62, KSY14`
  (11), on top of 6 pre-existing (`AER24, BCG+19, BS08, GRS25, h01, hr10`). None has a
  `docs/kb/papers/KEY.md` either. Note `ABF26` is the *primary* source of the whole ABF26 split
  programme, so this will recur in splits 3/4.
  Two same-paper key collisions inside the PR:
  - `Erasure.lean` uses **both** `[GRS12]` (docstring line 32) and `[GuruswamiRS12]` (line 18)
    for Guruswami-Rudra-Sudan.
  - `ExtensionCodes.lean:37,44` uses `[BuenzCFW25]` while the audit row for the same lemma
    credits `BCFW25`; and `:47` cites `[DiamondP23]` where the bib actually has key `DP23`.
- **Evidence**:
  `comm -13 <(keys used at merge-base) <(keys used now, minus keys present in references.bib)`
  → the 11 keys above; `grep -oP '^@\w+\{\K[^,]+' blueprint/src/references.bib` lists 55 keys,
  none of them these; `ls docs/kb/papers/` has no page for any of them.
- **Refutation attempt**: I checked whether the repo has a second `.bib` — `ls
  blueprint/src/*.bib` returns exactly one file. I also checked whether dangling keys are already
  the norm — 6 exist pre-PR out of 42 used keys, so this is an established but small debt that
  the PR nearly triples rather than an accepted practice.
- **Suggested fix**: add the 11 BibTeX entries (+ `docs/kb/papers/*.md` stubs per the wiki), and
  normalise `GuruswamiRS12`→`GRS12`, `BuenzCFW25`→`BCFW25`, `DiamondP23`→`DP23`.

---

### [LOW] The "Tagged sorry comments" section of the conventions page documents a convention with
zero instances, and cites a "partial proof" that is complete

- **Where**: `docs/wiki/coding-theory-conventions.md:148-169`.
- **What's wrong**: the page prescribes `sorry -- ABF26-X.Y; <classification> [Citation].` and
  says "Reviewers should expect the `ABF26-X.Y` tag in the comment to match an audit-doc row" —
  but there are **no `sorry`s at all** in the PR's modules, and
  `grep -rn "external admit" ArkLib/` returns nothing. It also says
  *"the partial proof of `hammingBallVolume_eq_ncard_hammingBall` decomposes into
  `card_filter_hammingDist_eq` and a small Set/Finset conversion"* — that theorem is **complete
  and axiom-clean**, not partial.
- **Evidence**: sorry grep over the 29 touched files (only the pre-existing `Fin/Basic.lean:333`);
  `#print axioms CodingTheory.hammingBallVolume_eq_ncard_hammingBall` →
  `[propext, Classical.choice, Quot.sound]`.
- **Suggested fix**: either mark the whole section "(applies to the proximity-gap split, which
  carries the external admits; this layer has none)" or drop the
  `hammingBallVolume_eq_ncard_hammingBall` sentence.

---

### [LOW] The audit's D2.15 row claims a bridge is "awaited" that this PR closed

- **Where**: audit §2 row `D2.15`, phrase *"the `Admissible → injective` bridge `dim_frsCode`'s
  `h_encoder_inj` awaited"*.
- **What's wrong**: `ReedSolomon/Folded.lean:211-216` — `dim_frsCode` takes
  `(hadm : Admissible …) (hω : ω ≠ 0) (hk : k ≤ s * Fintype.card ι)` and has **no**
  `h_encoder_inj` hypothesis; injectivity is derived internally from `hadm`. The row is stale.
  The same staleness appears in `Folded.lean`'s own module docstring (`:25`), which describes
  `dim_frsCode` as holding *"under FRS encoder injectivity"*.
- **Suggested fix**: reword both to "derived from `Admissible` + `ω ≠ 0` + `k ≤ s·n`".

---

### [LOW] The audit doc and the conventions page contradict each other on paper-shortcut notation

- **Where**: audit §2 rows `D2.9` and `D2.11` ("Lean target" column) vs
  `coding-theory-conventions.md:110-114`.
- **What's wrong**: the audit lists as targets `scoped notation "_^≡_"` (D2.9) and
  `scoped notation "RS[" F ", " L ", " k "]"` (D2.11); the conventions page states the exact
  opposite — *"The paper's `RS[F, L, k]`, `IRS[…]`, `FRS[…]`, `UM[…]` shortcuts are **not**
  introduced as Lean notation. Per design decision (polish-plan D2)."* Neither notation exists
  (`grep -rn 'notation.*"RS\[\|notation.*≡' ArkLib/` → 0 hits). Relatedly the D2.5 row says
  *"Paper-style `δ_min` / `ρ` scoped-notation file was once planned but never materialised"* —
  the `ρ` scoped notation **does** exist (`Basic/LinearCode.lean:252`) and the conventions page
  documents it.
- **Suggested fix**: drop the notation targets from D2.9/D2.11 (design decision is recorded), and
  correct the `ρ` half of D2.5.

---

### [LOW] Two new modules have no `## References` section despite citing ABF26, and the
`## References` format is inconsistent with `CONTRIBUTING.md`

- **Where**: `ArkLib/Data/CodingTheory/Basic/Entropy.lean` (cites "ABF26 Definition 2.2",
  Corollary 3.8, Theorem 3.11, Theorem 4.17 — no References section);
  `ArkLib/Data/CodingTheory/HammingBallVolume.lean` (cites "ABF26 Definition 2.4", Lemma 3.7,
  Corollary 3.8 — no References section). Format: `CONTRIBUTING.md` mandates
  `* [Author Last Name, First Initial, *Title*][citation_key]`; only `Combinatorial.lean` and
  `Multiplicity.lean` follow it. `Erasure.lean`'s References section is free prose with no
  bracket keys at all; `Family.lean`, `Folded.lean`, `Interleaved.lean`, `SubspaceDesign.lean`,
  `ExtensionCodes.lean`, `FoldedWronskian.lean` use `- [KEY] Author. Title.`
- **Suggested fix**: add the two missing sections; normalise the format.

---

### [LOW] Several new declarations do not fit the page's own definition-naming table, and the
table itself is internally inconsistent

- **Where**: `docs/wiki/coding-theory-conventions.md:47-53` vs the PR's new decls.
- **What's wrong**:
  - Table says predicates use `IsX` style, then lists `Admissible` (not `IsX`) as an example of
    that convention; the PR also adds `SupportsErasureCorrection` (a `Prop`-valued predicate, not
    `IsX`). `IsSystematic` and `IsSubspaceDesign` do conform.
  - Table says "Descriptive function | **snake_case** describing the math" then gives three
    **camelCase** examples (`hammingBallVolume`, `frsEvalOnPoints`, `restrictedRelHammingDist`).
  - Table says "Structure | PascalCase | `ExtensionFieldPresentation`, `WordStack`,
    `InterleavedWord`" — the latter two are `abbrev`s for `Matrix`
    (`InterleavedCode.lean:109,122`), not structures. Only `ExtensionFieldPresentation` is one.
  - Table says code families are "namespaced + **`Code` suffix**" and gives `ReedSolomon.code`,
    which has no `Code` suffix.
  - `min_dist_le_d` (`JohnsonBound/Family.lean`) uses `min_dist` where the repo spells it
    `minDist` everywhere else.
- **Suggested fix**: soften the table wording, or rename `Admissible` → `IsAdmissible` and
  `SupportsErasureCorrection` → `IsErasureCorrectable` (both have few call sites today).

---

### [LOW] `additive_code_supports_erasure_correction_grs12` is named for a hypothesis it does not
have

- **Where**: `ArkLib/Data/CodingTheory/Erasure.lean:125-126`.
- **What's wrong**: the theorem is
  `theorem additive_code_supports_erasure_correction_grs12 (C : Set (ι → F)) :
   SupportsErasureCorrection C` — it takes an **arbitrary set**, with no additivity/linearity
  hypothesis. The docstring is honest ("proves that *every* code satisfies the predicate") and
  the audit row is honest, but the name says "additive_code" and readers will assume a
  linearity hypothesis. (This is a naming/labelling point only; the vacuity question — that
  `SupportsErasureCorrection` is satisfiable for *every* code because ArkLib's model is
  cost-free — is documented in both the module docstring and the L6.5 audit row, and belongs to
  the vacuity reviewer.)
- **Suggested fix**: rename to `code_supportsErasureCorrection_grs12`, or note in the docstring
  why the paper's "additive" qualifier is dropped.

---

### [LOW] `docs/wiki/repo-map.md` is not updated for the eight new `Data/` modules outside
`ReedSolomon/`

- **Where**: `docs/wiki/repo-map.md` — the PR updates only the Reed-Solomon bullet.
- **What's wrong**: the PR adds `SubspaceDesign.lean`, `ExtensionCodes.lean`, `Erasure.lean`,
  `HammingBallVolume.lean`, `Basic/Entropy.lean`, `JohnsonBound/Family.lean`,
  `Polynomial/FoldedWronskian.lean`, `Probability/Combinatorial.lean` — none gets a repo-map
  entry, and `Polynomial/FoldedWronskian.lean` sits in a subtree repo-map *does* enumerate
  file-by-file (it names `Data/Polynomial/Trivariate.lean` and `Data/Matrix/Vandermonde.lean`).
- **Mitigation** (why this is only LOW): repo-map's own preamble says *"This repo is easiest to
  navigate by subtree, not by individual file name"*, and all eight land inside directories the
  map already covers, so `AGENTS.md`'s "structure change" trigger is arguably not fired. The two
  new wiki pages **are** correctly linked from `docs/wiki/README.md` (both in the index and in
  the maintenance list), and `scripts/check-docs-integrity.py` passes.
- **Suggested fix**: one bullet for the folded-Wronskian toolkit (it is the non-obvious one:
  a `Polynomial/` file whose only consumer is a `CodingTheory/` theorem).

---

## Clean bill

Checked and found genuinely correct:

**PR body claims that hold** (verified individually against `ffa0733a`):
- "exactly six in-tree consumers gain a one-line `open Probability`" — exactly 6 files, each a
  single `+open Probability` line (`AffineGenerator`, `BCIKS20/AffineSpaces`,
  `BCIKS20/ReedSolomonGap`, `DG25/MainResults`, `MCAGenerator`, `RbrGame`).
- "`ReedSolomon.lean` is intentionally untouched" — TRUE, absent from the diff.
- "Two new top-level namespaces: `CodingTheory` and `Probability`" — TRUE; `git grep -l
  "^namespace CodingTheory" 4f386913` and the `Probability` equivalent both return nothing.
- "the re-exposed `prob_schwartz_zippel_mv_polynomial` is byte-identical to main's" — TRUE at the
  statement level (signature character-identical to `origin/main:546-550`; only the proof is
  replaced by delegation to the new generalisation). Fully-qualified name changes only by the
  disclosed namespace move.
- "One rider commit fixes the 1-line `Finset.prod` deprecation from #534" — TRUE, `55aeff13`,
  exactly one line (`Finset.prod_eq_mul_prod_diff_singleton` →
  `Finset.prod_eq_mul_prod_sdiff_singleton`), and the Data zero-warning gate is now GREEN
  ("No ArkLib/Data non-sorry warnings found").
- "docstring on the pre-existing `Fin.sumCases` WIP sorry (not new debt)" — TRUE.
- Every decl the body names in §A-§D exists: `prob_polynomial_identity_le`,
  `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le`, `Fin.induction_three(')`,
  `Code.disagreementCols`, `minRelHammingDistCode_{mem,le,of_empty}`,
  `minDist_div_card_eq_minRelHammingDistCode`, `qEntropy`, `SupportsErasureCorrection`,
  `additive_code_supports_erasure_correction_grs12`, `hammingBallVolume`, `Lambda`,
  `Lambda_le_iff_listDecodable`, `Jqℓ`, `Jcap`, `johnson_card_le_ell`, `plotkin_card_le_ell`,
  `johnson_bound_lambda_le_ell`, `mds_johnson_lambda_le`, `IsMDS_iff_rate_distance(')`,
  `frsCode`, `Admissible`, `irsCode`, `dim_irsCode`, `umCode`, `IsSubspaceDesign`,
  `extensionCode`, `lambda_extensionCode_eq_lambda_interleaved`.
- The `Admissible` "deliberate documented strengthening" note is real and thorough:
  `Folded.lean:53-76` states the deviation, why the paper's literal D2.14 admits `ω^j = 1`, and
  the boundary cases (`ω ≠ 0` not required; `0 ∈ L` excluded only implicitly and only for
  `s ≥ 2`). Honest.

**Docstring honesty** — every "proved / sorry-free / axiom-clean" claim I could find is TRUE.
`(session-local probe) r10-axioms.lean` shows all of the following depend on exactly
`[propext, Classical.choice, Quot.sound]`: `subspaceDesign_tau_lower`,
`frs_is_subspaceDesign_gk16`, `lambda_extensionCode_eq_lambda_interleaved`,
`additive_code_supports_erasure_correction_grs12`, `hammingBallVolume_eq_ncard_hammingBall`,
`mds_johnson_lambda_le`, `johnson_bound_lambda_le_ell`, `minDist_frsCode`, `dim_frsCode`,
`dim_irsCode`, `mem_umCode_one_iff_mem_rsCode`,
`Probability.exists_large_image_of_pairwise_collision_bound`,
`Polynomial.foldedWronskian_ne_zero_of_linearIndependent`, `LinearCode.singleton_bound_module`,
`LinearCode.IsMDS_iff_rate_distance`, `ListDecodable.Lambda_le_iff_listDecodable`.
In particular the `SubspaceDesign.lean` header's "(**proved**, sorry-free)" on both L2.17 and
T2.18 is accurate, and its pointer *"see the audit's T2.18 row for the 2026-07-21 correction
record"* resolves: that row exists and says exactly what the docstring claims (restored GK16's
`orderOf ω = |F|−1`, counterexample `ω = −1` over 𝔽₁₀₁, PAPER_REVS #13).
`FoldedWronskian.lean`'s Main-statements descriptions match the actual signatures
(`natDegree_foldedWronskian_le : ... ≤ σ * k` under `∀ j, (P j).natDegree ≤ k`;
`foldedWronskian_ne_zero_of_linearIndependent` carries `orderOf ω = |F| − 1` and
`k ≤ |F| − 1`, matching the header's "`ω` a generator of `Fˣ` and `deg < k ≤ |F| − 1`").

**`ArkLib.lean`** — GENERATED, NOT HAND-EDITED. I re-ran the generator's exact pipeline
(`git ls-files -- 'ArkLib/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /'`, i.e.
`scripts/update-lib.sh` lines 38-40) into
`SCRATCH/ArkLib.lean.regen`; `diff` against the tracked file is **empty**. The +11 import lines
correspond **exactly** to the 11 new `.lean` files (one each), in sort order, no extras and none
missing. `scripts/check-imports.sh` also passes inside `validate.sh`.

**Audit matrix §2 / A.7 / B.1 / D6.4 / L6.5 decl names** — every Lean identifier cited in the
rewritten §2 table and in the new D6.4/L6.5/A.7/B.1 rows resolves to a declaration that exists at
this commit with that exact name (43 names checked individually, including
`prob_polynomial_identity_le`, `MvPolynomial.totalDegree_le_of_degreeOf_lt`,
`Multiplicity.mem_umCode_one_iff_mem_rsCode`, `LinearCode.singleton_bound_module`,
`foldedWronskian_ne_zero_of_linearIndependent`, `pow_dvd_det_of_forall_mem_col_dvd`,
`sum_fiber_sq_eq`, `cauchy_schwarz_fiber`, `extensionCodeSubmodule`,
`coe_extensionCodeSubmodule`, `eq_of_consistent_with_erased`, `umEvalOnPoints`,
`admissible_foldedPoints_injective`, `frsEvalOnPoints_domRestrict_injective`).
The L2.17 and T2.18 rows **were** updated by the later commits and correctly read
`present (**PROVEN**)` with sorry-free/axiom-clean notes — no overstatement.
Every §2 row marked missing/deferred really is absent (`InterleavedCode.lambda_le_ggr11` → 0 hits;
`restrictedRelHammingDist` → 0 hits).

**Conventions page — notation section verified line by line against the declarations.** All of
`Δ₀(u,v)`, `Δ₀(u,C)`, `Δ₀'(u,C)`, `‖u‖₀`, `‖C‖₀`, `‖C‖₀'`, `δᵣ(u,v)`, `δᵣ(u,C)`, `δᵣ'(w,C)`,
`δᵣ C`, `C ^⋈ κ`, `⋈| u`, `u ⋈₂ v`, `⋈⁻¹| u`, `Λᵢ(u,C,δ)` map to exactly the declarations the
page claims (checked against `Distance.lean:126/128/182/189/690/890`,
`RelativeDistance.lean:40/52/582/723`, `InterleavedCode.lean:289/293/300/518/798`). The claim
that these are global despite living inside `namespace Code` is correct (`notation` is global;
`namespace Code` opens at `Distance.lean:122` / `RelativeDistance.lean:19`). The `ρ` claim is
exactly right: `LinearCode.lean:252` is `scoped syntax &"ρ" term : term`, non-reserved so `ρ`
stays usable as a variable. The "Conspicuously absent" section is correct: there is **no**
`Λ(` notation anywhere (only `Λᵢ(` and a scoped `Λ𞁒(` in `Basic/BlockRelDistance.lean`), and no
`δ_min` notation. Type-conventions rows for pairwise Hamming distance (`ℕ`), distance-to-code
(`ℕ∞`), relative pairwise (`ℚ≥0`), relative-to-code (`ENNReal`), min-relative (`ℚ≥0`), rate
(`ℚ≥0`), probabilities (`ENNReal`), list sizes (`ℕ∞`), degree bound (`degreeLT`), linear carrier
(`Submodule F (ι → A)`), non-linear carrier (`Set (ι → A)`) all verified correct by `#check`.
The namespace-layout claims for `CodingTheory.*` (`qEntropy`, `IsSubspaceDesign`,
`ExtensionFieldPresentation`, `extensionCode` — all really in `namespace CodingTheory`),
`ReedSolomon.*` (`Folded.frsCode`, `Folded.Admissible`, `Interleaved.irsCode`,
`Multiplicity.umCode`), and `ProximityGap.*` (namespace exists) are correct apart from the
`IsMDS`/`LineDecodable` entries flagged above.

**`docs/wiki/probability-conventions.md`** — fully accurate. `Instances.lean` and
`Combinatorial.lean` both live in `namespace Probability`; `Notation.lean` uses
`namespace ProbabilityTheory`; the `_root_` escape hatch it prescribes is actually used
(`Instances.lean:605  lemma _root_.MvPolynomial.totalDegree_le_of_degreeOf_lt`,
`_root_.PMF.map_uniformOfFintype_of_fiber_const`, `_root_.Fintype.card_fun_fin_one_eq`). No
root-level `prob_*`/`Pr_*` helper is re-introduced. Both new wiki pages are linked from
`docs/wiki/README.md`.

**Module docstrings** — all 11 new files have a `# Title` and a summary; 9 of 11 have
`## References`; `Folded.lean`, `Interleaved.lean`, `Multiplicity.lean`, `SubspaceDesign.lean`,
`ExtensionCodes.lean`, `FoldedWronskian.lean` have proper `## Main definitions` /
`## Main statements`(`## Main lemmas`) sections. No docstring overstates what is proven — the
opposite is true in two places (`Folded.lean:25` and the D2.15 audit row *understate*, claiming a
hypothesis/bridge that has since been discharged; flagged LOW above). `Folded.lean`'s "Not the
FRI fold" disambiguation section is accurate and genuinely useful — it correctly names
`ProximityGap/Folding.lean` (`foldWord`), `Data/Polynomial/SplitFold.lean` (`splitNth`),
`Data/Polynomial/FoldingPolynomial.lean` (`polyFold`) as the different construction.
`Multiplicity.lean` is commendably honest about the un-baked `char(F) ≥ k` requirement.

**`./scripts/validate.sh --docs`** — all pre-docs stages **PASS**:
`lake build` completed successfully (4197 jobs; only pre-existing `sorry` warnings, the sole
`ArkLib/Data` one being `Fin/Basic.lean`), "No ArkLib/Data non-sorry warnings found",
`check-imports.sh` "All imports are up to date", "All documentation integrity checks passed",
"Knowledge base lint passed". The final `DISABLE_EQUATIONS=1 lake build ArkLib:docs` stage is a
cold ~8700-job docgen build that was still running at report time (it had reached ~5700/8694 with
zero errors); log at `SCRATCH/validate-docs.log`. I additionally ran
`scripts/check-docs-integrity.py` and `scripts/kb/lint.py` standalone — both pass.

**Style lint** — `git ls-files 'ArkLib/*.lean' | xargs ./scripts/lint-style.py` reports **zero**
hits in any of the 11 new files, and the (file, error-kind) multiset differs from `origin/main`
only in the two entries attributable to main's own drift (documented in finding 1). So the
substance of the body's "zero new lint" claim is confirmed.
