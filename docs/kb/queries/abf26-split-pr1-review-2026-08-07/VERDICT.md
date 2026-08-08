# PR #701 — full fresh adversarial review: VERDICT

**PR**: Verified-zkEVM/ArkLib#701 — *feat(coding-theory): ABF26 foundations and code families [split 2/4]*
**Head reviewed**: `ffa0733a` (== `origin/feat/abf26-split-ct-data`, == PR head)
**Base**: `origin/main` @ `02d759d5` (merge-base `4f386913`; main is 4 commits ahead)
**Date**: 2026-08-07
**Method**: 11 independent adversarial reviewers (R1–R11) + a lead pass, every finding
required to carry a compiled probe, an exact source quote, or an exact `path:line`
pointer to the declaration it duplicates. ~40 compiled probes under `probes/`.
Reports: `findings/R{1..11}-*.md`.

---

## 1. Verdict

**Mathematically: GO. Merge-ready: NOT YET — but nothing blocking is mathematical.**

- **0 CRITICAL, 2 HIGH, 42 MEDIUM, 65 LOW.**
- **No false statement was found.** No vacuous hypothesis set, no trivially-true
  conclusion, no proof cheat, no `sorry`, no non-standard axiom.
- Both HIGH findings are **duplication / missed-generalization**, i.e. exactly the axis
  the reviewer brief was told to prioritise. Both are mechanical to fix.
- The two formerly-admitted crown jewels (ABF26 L2.17, T2.18) are **genuinely proven**,
  and the T2.18 proof is a faithful, correctly-streamlined rendering of GK16 Theorem 14.

### Merge bar (user's wording: "progresses the library beyond its immediate use for ABF26")
**Clears it on the mathematics; only partly clears it on integration.** 9 of the 11 new
modules currently have zero importers and zero users; the two advertised bridges into
existing ArkLib developments have no crosser. R11 compiled the crossings — they are 1–2
lines each — so this is cheap to fix, not structural.

---

## 2. What is genuinely strong (validated, not assumed)

1. **ABF26 T2.18 / GK16 Thm 14 is a real proof.** `foldedWronskian` is GK16 Definition 11
   verbatim (rows = `γ^i` twists, cols = polynomials — checked against the PDF).
   `foldedWronskian_ne_zero_of_linearIndependent` is GK16 Lemma 12 with GK16's own
   hypotheses (`m < |F| = q` ⇔ `k ≤ q−1`; `γ` a generator), proved by GK16's Appendix-A
   argument, correctly streamlined: it obtains the row dependency directly from the Moore
   matrix over `K = F[X]/(X^{q−1} − ω)` instead of clearing denominators over `F(X)`.
   The counting `(s−σ+1)·Σᵢ dim Aᵢ ≤ σ(k−1)` is GK16's own display at `r = 1`.
   **It also proves the irreducibility of `X^{q−1} − ω` that GK16 merely asserts**
   ("which happens to be irreducible") — Mathlib's Kummer criteria don't cover the even
   exponent `q−1`. That is a genuine contribution beyond the paper.
2. **Axiom hygiene, mechanically exhaustive.** 538 source-level declarations across all 28
   touched modules; 533 carry exactly `{propext, Classical.choice, Quot.sound}`. All 5
   `sorryAx` carriers are pre-existing (3 × `BCIKS20/AffineSpaces`, 1 × `ReedSolomonGap` —
   files whose entire diff is one `open Probability` line — plus the untouched
   `Fin.sumCases` WIP). Nothing new reaches any of them. No new `axiom`, no
   `native_decide`/`ofReduceBool`, no `unsafe`/`opaque`.
3. **Non-vacuity certified by the sharp criterion, not by mere satisfiability.** For
   `frs_is_subspaceDesign_gk16`, a compiled witness at `𝔽₅`, `ι = Fin 2`, `s = 2`, `k = 1`,
   `ω = 2`, `L = {1,4}` sits in the content-bearing regime `k < s·n` with `τ(1) = 1/4`,
   `τ(2) = 1/2` — both `< 1`, which is precisely what separates the claim from the free
   bound `≤ dim A` that the proof's own `hsum_le` establishes. `subspaceDesign_tau_lower`
   additionally has a compiled *negative* consequence (`¬ IsSubspaceDesign 2 (fun _ ↦ 1/4) ⊤`),
   so it demonstrably rules profiles out.
4. **Three separate paper defects found and correctly handled.** See §3 — this is real
   review value flowing back to the authors.
5. **The `[Field F]` removal across the existing Johnson development is model behaviour**:
   the PR *generalised the originals in place* rather than forking them, kept the old
   `prob_schwartz_zippel_mv_polynomial` as a corollary of its own generalization with a
   byte-identical signature, and updated all six affected consumers with a one-line
   `open Probability`. Zero statement drift across ~25 migrated declarations
   (byte-level diff vs `origin/main` after stripping namespaces).
6. **Linter suppressions hide nothing.** Every file was recompiled with the suppressed
   linters flipped on. `unusedSectionVars` — the one that could mask a "load-bearing
   hypothesis isn't" bug — fires **zero** times in both files that disable it. All
   surviving warnings are unused *instance* arguments the proofs need.
7. **Hygiene**: `lake build` green (4197 jobs); zero new `sorry`; `ArkLib/Data`
   zero-warning gate GREEN and the deprecation rider verified genuinely needed against the
   pinned Mathlib; "zero new lint" **verified** (730 errors on branch and on merge-base,
   line-shifts only; zero hits in any of the 11 new files); `ArkLib.lean` byte-identical to
   generator output; no import cycle; no consumer breakage; no semantic conflict with
   main's 4-commit drift.
8. Correct rejections by the PR that reviewers tried and failed to overturn: the "not the
   FRI fold" disambiguation is **true** (`ProximityGap/Folding.lean` shrinks the domain and
   drops the degree — the opposite construction); `irsCode` really is `RS ^⋈ Fin s` with no
   fork; `Lambda` really is a reformulation of `listDecodable`, not a fork;
   `Multiplicity.lean`'s use of *ordinary* iterated derivatives is correct (ABF26 Def A.6
   specifies exactly that under `char F ≥ k`) — there is no Hasse-derivative bug.

---

## 3. Paper defects found (report these upstream)

| # | Defect in ABF26 | Status in the Lean | Evidence |
|---|---|---|---|
| P1 | **Def 3.1's list factor is inverted.** The PDF prints `J_{q,ℓ}(δ) = (1−1/q)(1−√(1−(q/(q−1))·(ℓ/(ℓ−1))·δ))`. That makes `J_{q,ℓ} > J_q`, makes the radius *shrink* as the list grows, and diverges at `ℓ = 1`. | **Fixed** — Lean uses `(ℓ−1)/ℓ`, matching GRS12 Ex. 7.8. Already fixed upstream in the authors' tex (`ef-millenium` `c673766`, 2026-06-13, after the PDF build). | bbox-verified glyph positions in the PDF; upstream commit |
| P2 | **Def 2.14 omits the intra-orbit condition.** It quantifies over `(L choose 2)` — distinct pairs only — so `ω = 1` is admissible, contradicting the definition's own stated purpose ("an evaluation point appears only once"). | **Fixed** — `Admissible` adds the intra-orbit clause, documented as a deliberate strengthening. | Rendered PDF confirms `\binom{L}{2}`; compiled `paper_admits_one`; brute force at `ω = 1` gives true `minDist` 4/3/2/1 vs the formula's 5/4/4/3 for `k = 2..5` |
| P3 | **Thm 2.18 has *two* missing hypotheses, not one.** (a) No order condition on `ω`; (b) `0 ∈ L` is permitted. With `0 ∈ L`, T2.18 is false **even with** `ord ω = q−1`. GG25's restatement (Def 2.18 / Thm 2.19, `q > sn` only) is falsified by the same examples. | **(a) fixed and forensically documented** (`hω_gen`). **(b) fixed but undocumented** — the intra-orbit clause excludes `0 ∈ L` for `s ≥ 2`, so it is load-bearing for T2.18, yet only `Folded.lean` mentions the deviation, and only as a hedge. | (a) compiled refutation over `𝔽₁₇` (variant of the docstring's `𝔽₁₀₁`); GK16 L12 says "γ ∈ F\* be a generator". (b) compiled refutation: `ZMod 5`, `domain = (0,1)`, `s=3`, `k=2`, `ω=2` a generator ⇒ `Σ/n = 1/2 > 1/3 = dim A·τ(1)` |

---

## 4. HIGH findings (must fix)

### H1 — `JohnsonBound.Jqℓ` is the pre-existing `JohnsonBound.J` at a rescaled radius
- **Where**: `JohnsonBound/Family.lean:73` vs `JohnsonBound/Basic.lean:52`
- Compiled: `Jqℓ q ℓ δ = J q (((ℓ−1)/ℓ) * δ)` for `q ≠ 0`. No bridge lemma is exported, and
  `johnson_card_le_ell` re-derives `J`-facts from scratch. `main` already carries a second
  copy (`J'` at `Lemmas.lean:15`); this PR adds a third sibling.
- **Fix**: export the bridge as a lemma, define `Jqℓ` in terms of `J`, and have
  `johnson_card_le_ell` consume the existing `J` facts. Also fold in the dead `Jcap`
  (`Family.lean:88`), which duplicates the LHS of the pre-existing `sqrt_le_J` — whose
  statement literally *is* `Jcap δ ≤ J q δ`.

### H2 — `JohnsonBound.remap` trio duplicates Mathlib, which the same PR uses correctly elsewhere
- **Where**: `JohnsonBound/Expectations.lean:146,150,158`
- `remap` / `remap_injective` / `remap_hammingDist` are `rfl`-equal to
  `Equiv.piCongrRight` / `Equiv.injective` / `hammingDist_comp`. **The same PR calls the
  latter two directly in `ExtensionCodes.lean:323,328.**
- **Fix**: delete the trio, use Mathlib. (This also removes one of *three* different
  Hamming-transport idioms the PR introduces.)

---

## 5. MEDIUM findings, grouped (42 total; full detail in the per-cluster reports)

### A. Duplication / missed generalization (the user's top axis)
- **A1** Pre-existing `prob_eval_zero_le_div` (`Data/MvPolynomial/SchwartzZippelCounting.lean:126`)
  is a *strictly more general* probabilistic Schwartz–Zippel (arbitrary sampling sets, bound
  `d/m`) than the PR's new `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le`
  (`Probability/Instances.lean:550`, the `S i = univ` case). Two parallel SZ probability APIs
  in two namespaces with no cross-reference.
- **A2** `dim_irsCode` (`ReedSolomon/Interleaved.lean:70`): the 40-line proof is entirely
  RS-independent, and `InterleavedCode.lean` (803 lines) has **no** `finrank` lemma at all.
  The general `finrank F (MC ^⋈ κ) = |κ| · finrank F MC` compiles by the same script and
  re-derives `dim_irsCode` in 2 lines (also dropping a spurious `[Nonempty ι]`).
- **A3** `frsCode` **is** the plain RS code on the folded domain `ι × Fin s ↪ F` — GR08 Def 2.1's
  own framing. A compiled 15-line bridge turns `dim_frsCode` into a 4-line transport of the
  existing `ReedSolomon.dim_eq_deg_of_le` (and drops a superfluous `[NeZero k]`).
  (`minDist_frsCode` genuinely cannot transport — different metric. That part is fine.)
- **A4** `ExtensionCodes.lean`'s `ψ` / `φ` / `coord` are `rfl`-identical to `algebraMap` /
  `Basis.equivFun` / `Basis.coord`; `ψ_injective` *is* `FaithfulSMul.algebraMap_injective`.
  Worse: `extensionCodeSubmodule P C_B = Submodule.span F (ψ '' C_B)` (compiled), so
  `extensionCode` **provably does not depend on the presentation at all** (compiled
  `extensionCode P = extensionCode P'`) — which makes the 58-line `extensionCode_smul_mem`
  unnecessary and the whole `ExtensionFieldPresentation` apparatus optional for the definition.
- **A5** `Code.disagreementCols` (`Distance.lean:149`) = `Matrix.neqCols`
  (`Prelims.lean:50`, same directory) on transposes (compiled). The new docstring enumerates
  four other `disagreementSet`s and misses the one that really is the same function.
- **A6** `Folded.mem_frsCode_one_iff_mem_rsCode` and `Multiplicity.mem_umCode_one_iff_mem_rsCode`
  are one lemma written twice; a single encoder-parameterised lemma covering both compiles.
- **A7** `eq_of_consistent_with_erased` (`Erasure.lean:83`) is the `Option`-clothed case of a
  `projectedWord`-injectivity lemma belonging beside the pre-existing
  `LinearCode.projectedWord` (`Basic/LinearCode.lean:259`).
- **A8** Eight Mathlib-generic declarations sit outside `ToMathlib/`, including
  `Polynomial.pow_dvd_det_of_forall_mem_col_dvd` (a **Matrix** lemma in namespace
  `Polynomial`, in a Wronskian file) and `MvPolynomial.totalDegree_le_of_degreeOf_lt`,
  whose own docstring says it belongs in Mathlib while it sits in
  `Data/Probability/Instances.lean`.
- **A9** Namespace fragmentation: `namespace CodingTheory` **does not exist on `main`** — the
  PR introduces it as a third convention across six files (`JohnsonBound/Family.lean` carries
  two namespaces). Separately, `Probability` (Instances/Combinatorial) vs `ProbabilityTheory`
  (Notation.lean) splits a two-lemma chain across namespaces inside one directory.

### B. Statements weaker than advertised
- **B1** `subspaceDesign_tau_lower` narrows ABF26 L2.17 / GG25 L2.16 from `∀ r ∈ ℕ` to
  `r ∈ Finset.Icc 1 s`. The **byte-identical proof body** compiles for `∀ r ≥ 1` under
  `1 ≤ s`. Zero in-tree consumers, so the "no consumer needs it" justification buys nothing.
- **B2** `johnson_bound_lambda_le_ell` carries an extra `_h_radicand` guard making it strictly
  weaker than ABF26 Thm 3.2, and its docstring's justification — that the guard marks the
  radius "at which the list-size-ℓ claim is **false**" — is itself false, refuted by
  `plotkin_card_le_ell` 80 lines above it. The guard-free paper statement compiles in ~45
  lines from ingredients already in-tree.
- **B3** `Lambda_le_iff_listDecodable` is stated only at `ℓ : ℕ`, but every in-tree
  `listDecodable` consumer uses `ℓ : ℝ≥0` (`Stir/OutOfDomSmpl.lean:52,62`,
  `Stir/MainThm.lean:63`) and this PR's own Johnson bound produces `ENNReal.ofReal`. The
  docstring's "transfer … through this equivalence" does not hold through the stated lemma.
- **B4** `Lambda` inherits `Set.ncard`'s infinite ↦ 0, so `Lambda (univ : Code (Fin 1) ℚ) 1 = 0`
  and hence `listDecodable univ 1 0` (compiled). Not exploitable today (every shipped bound
  carries `[Finite F]`), and inherited from the pre-existing `listDecodable`.

### C. Content-free abstractions
- **C1** `SupportsErasureCorrection` (`Erasure.lean:66`) is a **tautology**: provable for every
  `C` with no hypotheses (compiled at `∅` and at `univ`), with **zero consumers**. ABF26 D6.4's
  entire content is the correction-time bound `ecor_C`, which is dropped; L6.5's entire content
  is `ecor_C = O((s·n)³)`. Consequently `additive_code_supports_erasure_correction_grs12`
  uses neither additivity (no such hypothesis exists) nor anything from GRS12 — its own
  docstring concedes the latter, but the *definition's* docstring simultaneously claims clause
  (ii) is "what makes the predicate non-vacuous". Clause (ii) pins the witness `E`, not `C`.
  The two docstrings contradict each other, and the name will mislead.
- **C2** `IsSystematic` is dead code, and the paper's only consequence of it —
  `C_F(ψ(v)) = ψ(C_B(v))`, which BCFW25 §D.2 uses for soundness — is **not expressible**:
  ABF26 D2.20 is encoder-level, ArkLib models the code image only.

### D. Integration ("progresses the library")
- **D1** 9 of 11 new modules have zero importers and zero users. The ~3 900 new lines form one
  connected component (`SubspaceDesign → {Folded, FoldedWronskian}`) plus **eight isolated islands**.
- **D2** **Both advertised bridges have no crosser, and the crossings compile today.**
  `mds_johnson_lambda_le` + the pre-existing proven `ReedSolomon.isMDS_code` give ArkLib's
  first RS list-size bound in **one line**. `Lambda_le_iff_listDecodable` +
  `johnson_bound_lambda_le_ell` + `Lambda_mono` give exactly the `listDecodable` shape that
  `Stir/MainThm.lean:72` and `Stir/OutOfDomSmpl.lean:55` currently **assume as an unfillable
  hypothesis** — 2 lines. This is the single strongest lever on the merge bar.
- **D3** Universe regression: 57 `Type` / 0 `Type*` in the new files, against 0/26, 0/23, 0/46
  in the existing siblings. `Lambda.{u,v}` is polymorphic but its theorems are `Type 0`-only;
  `ReedSolomon.code.{u,v}` is polymorphic but `frsCode`/`irsCode` are not;
  `singleton_bound_module` is polymorphic but `IsMDS_iff_rate_distance` in the same file is not.
  Verified free to fix: `IsSubspaceDesign` takes `Type*` with **no other change** and is defeq
  at `Type 0`.
- **D4** Spurious instance arguments on new *definitions* (`rfl`-verified): `frsCode` 2,
  `irsCode` 3, `extensionCode` 1 — while the linters that catch this are disabled file-wide in
  5 new files. Sibling `ReedSolomon.code` needs only `[Semiring F]`. Removable hypotheses on
  headline theorems too: 8 on L2.21, `_hδ_pos`/`_hδ_lt` confirmed removable by
  `lean_minimal_hypotheses`; and four `_`-prefixed hypotheses (`_hℓ_ge`, `_h_radicand`,
  `_hη_pos`, `_h_mds`) *are* used, so the prefix actively misleads.
- **D5** `Basic/Entropy.lean` doesn't earn module status: `qEntropy = Real.qaryEntropy / log q`
  (the PR proves it), it re-derives none of Mathlib's continuity/concavity API, imports no
  ArkLib, and never mentions a code.

### E. Documentation accuracy
- **E1** **PR body is materially stale.** Claims "exactly 2 new proof-term sorries … both tagged
  external admits in `SubspaceDesign.lean`" — there are **0**, both proven by later commits.
  "21 touched Lean modules" — it is **29** (11 new). The entire new 406-line
  `Data/Polynomial/FoldedWronskian.lean`, `LinearCode.singleton_bound_module`, and
  `Notation.lean`'s new lemma go unmentioned. The "400 declarations / 397 standard" census
  reproduces under no counting basis (actual: 538/533). The "8 independent reviewers, 0 critical,
  0 high" gate predates 4 later commits (~1200 lines). "4196 jobs" → 4197. The
  "byte-identical lint multiset" now differs in 2 entries (from main drift, not the PR).
  The "kills a `Fintype.ofFinite` diamond" claim is false — the refactor is defeq-preserving
  (`rfl` probe against the verbatim `origin/main` body), so there was no diamond.
  *Per your standing instruction I did not touch the body; it needs an author refresh.*
- **E2** `docs/wiki/coding-theory-conventions.md` — the durable library-facing artifact of this
  PR — states facts that are provably wrong about the API it documents:
  `‖C‖₀`/`Code.dist` is `ℕ`, not `ℕ∞`; `Code.minDist` does **not** "use an existential rather
  than infimum" (both are `sInf` over existentially-defined sets — the real difference is
  `≤ d` vs `= d`); `Δ₀'` is `ℕ∞`, not `ℕ`; `IsMDS` is `LinearCode.IsMDS`, not
  `CodingTheory.IsMDS`. **It contradicts the type-conventions block this same PR adds to
  `Distance.lean`** — which itself mistypes `Δ₀'`/`‖C‖₀'` as `ℚ≥0`.
- **E3** The page's normative naming scheme has **zero conforming instances**: all six worked
  examples don't exist, and the PR's own `mds_johnson_lambda_le`,
  `johnson_bound_lambda_le_ell`, `subspaceDesign_tau_lower`,
  `lambda_extensionCode_eq_lambda_interleaved` all violate it. It also documents 6
  non-existent identifiers (`epsCA`/`epsMCA`/`epsPG`, `LineDecodable`) as current rather than
  "next split", and a tagged-sorry convention with 0 instances whose only worked example
  (`hammingBallVolume_eq_ncard_hammingBall`) it calls a "partial proof with sub-sorries" when
  it is fully proven and axiom-clean.
- **E4** Audit doc **§3 was not updated** although this PR's largest file proves D3.1's missing
  family, T3.2, and **C3.3 which the audit still marks `missing`**. "Existing Inconsistencies #5"
  ("Folded RS, UM, subspace-design, extension codes … not yet represented") is flatly false at
  this commit — all four land here. Roadmap Phase 3 (all 5 items), 1.4 and 6.2 likewise done,
  unticked. Also: the audit records `Admissible` as a plain Def 2.14 transcription with no
  mention of the strengthening, so the ledger hides that every downstream theorem is weaker
  than ABF26's printed claim.
- **E5** **11 new citation keys, none in `blueprint/src/references.bib`** — `ABF26`, `GK16`,
  `GG25`, `GX13`, `GR08`, `GRS12`, `GuruswamiRS12`, `GW13`, `KSY14`, `Joh62`, `BuenzCFW25` —
  a direct `CONTRIBUTING.md:227` violation ("All academic papers must have entries"), ~3× the
  pre-existing debt of 6. Plus key collisions in the PR's own files: `GRS12` vs
  `GuruswamiRS12` in one file; `BuenzCFW25` vs the audit's `BCFW25`; `DiamondP23` inventing a
  third spelling of a paper already keyed `DP23`/`DP25`. The `DiamondP23` key makes the
  citation extractor drop `ExtensionCodes.lean` entirely. `Basic/Entropy.lean` and
  `HammingBallVolume.lean` cite ABF26 with no `## References` section at all.
- **E6** Docstring framing error repeated in two files: ABF26 Lemma 6.12's proof applies Claim
  B.1 **once**, not twice; the second counting step is a plain pigeonhole needing full
  injectivity, which B.1 cannot deliver. If the planned Lean route really uses B.1 twice, the
  resulting bound will be strictly weaker than Lemma 6.12 as printed.

---

## 6. The one unverified item

`lake build ArkLib:docs` (the `validate.sh --docs` docgen stage) did not complete. Three
independent attempts reached ~6 300–6 700 of ~8 700 jobs with **zero** stderr errors before
being stopped by memory pressure (an unrelated `lake build sha256challenge` on the machine was
holding ~20 GB). Since doc-gen4 aborts on a malformed docstring, clean stderr at 75% is decent
but not conclusive evidence. **Re-run `./scripts/validate.sh --lint --docs` on an idle machine
before merge.** All pre-docs stages pass (build 4197 jobs, `Data` warning gate green, imports
up to date, docs-integrity and kb-lint pass).

---

## 7. Recommended fix order

**Must, before merge**
1. H1, H2 (the two duplications) — mechanical.
2. A1–A5 (the remaining real duplications / missed generalizations), particularly the
   `InterleavedCode` `finrank` lemma (A2) and the `frsCode = RS on folded domain` bridge (A3):
   both *remove* code and strengthen the library.
3. E1 (author refresh of the PR body), E2/E3 (fix or cut the conventions page — as written it
   is a net negative), E4 (audit §3 + Admissible ledger row), E5 (bib entries + key collisions).
4. P3(b): document that the intra-orbit clause is load-bearing for T2.18 and report the
   `0 ∈ L` defect upstream alongside the `ω`-order one.
5. Re-run the docs gate on an idle machine.

**Strongly recommended (this is what clears the "progresses the library" bar)**
6. D2 — wire both bridges. The STIR crossing in particular discharges a hypothesis that
   `Stir/MainThm.lean` and `Stir/OutOfDomSmpl.lean` currently assume, which is the single most
   persuasive demonstration that this layer earns its place.
7. B1, B2 — state the two headline theorems at their sources' full strength; both proof bodies
   already compile at the stronger statement.
8. D3 — `Type*` sweep; verified free.
9. C1 — rename `additive_code_supports_erasure_correction_grs12` (drop the unearned `additive`
   and `grs12`), fix the contradicting docstring, and either park `Erasure.lean` until there is
   a cost model or state plainly in the audit that it is existence-only and tautological.

**Optional / judgement calls**
10. D4 (spurious binders), D5 (fold `Entropy.lean` into a neighbour), A6–A9, C2, B3/B4, E6,
    and the 65 LOW items.
