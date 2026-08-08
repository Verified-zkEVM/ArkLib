# R9 — Vacuity, axiom hygiene, build/lint hygiene (ArkLib PR #701 @ `ffa0733a`)

Scope: whole PR, three axes only (vacuity / axioms / build-lint). Base for all comparisons is
the merge-base `4f386913` (and `origin/main` `02d759d5` where stated).

**Headline: 0 CRITICAL, 0 HIGH.** The axiom surface is clean, no new `sorry`, and I could not
construct a vacuity attack on any new public theorem — the two headline results are certified
non-vacuous by compiled concrete instances. Everything below is MEDIUM/LOW hygiene.

---

## Part 1 — Exhaustive axiom sweep (mechanical)

**Probe**: `(session-local probe) R9-axioms.lean` and `(session-local probe) R9-axioms2.lean`
(imports all 28 touched Lean modules, walks `env.constants`, filters by
`env.getModuleIdxFor?`, runs `Lean.collectAxioms` on every constant).
Two passes because the first used `Name.isInternal`, which also skips `_private.*` names;
the second de-privatizes via `Lean.privateToUserName?` before the internal-detail filter, so
**every private lemma is covered too**.

Outputs (`SCRATCH/../tasks/bv0ax9fkb.output`, `b3wtjzp1s.output`):

| pass | scope | total | exactly `{propext, Classical.choice, Quot.sound}` | non-standard |
| --- | --- | --- | --- | --- |
| 1 | public + auto-generated, no private | 586 | 581 | 5 |
| 2 | source-level incl. private, no auto-generated | 538 | 533 | 5 |

**All 5 non-standard carriers are `sorryAx`, and all 5 are pre-existing:**

```
ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces  | ProximityGap.average_proximity_implies_proximity_of_linear_subspace
ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces  | ProximityGap.correlatedAgreement_affine_spaces
ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces  | ProximityGap.all_affine_elements_close
ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ReedSolomonGap| ProximityGap.proximity_gap_RSCodes
ArkLib.Data.Fin.Basic                                        | Fin.sumCases
```

Verified pre-existing: `git diff 4f386913..ffa0733a` touches
`BCIKS20/AffineSpaces.lean`, `BCIKS20/ReedSolomonGap.lean` with **exactly one added line each**
(`open Probability`), and `Data/Fin/Basic.lean` only with a docstring on `sumCases` plus two new
`Fin.induction_three*` lemmas. The `sorry` at `ArkLib/Data/Fin/Basic.lean:333` is untouched.

**Nothing new depends on `Fin.sumCases`** — `collectAxioms` is transitive, so any new declaration
consuming it (directly or through a helper in another file) would appear in the non-standard list.
None does.

**Both formerly-admitted results are genuinely proven and axiom-clean.** Directly verified:
`#print axioms` on a fully-applied concrete instance of `frs_is_subspaceDesign_gk16` reports
`[propext, Classical.choice, Quot.sound]` (`(session-local probe) R9-vacuity-sd4.lean`,
output `tasks/bpltj6s4y.output`).

### [MEDIUM] PR body's axiom/sorry census is stale in a way that under-reports the PR

- **Where**: PR #701 body, "Verification" section, and the `SubspaceDesign.lean` bullet.
- **What's wrong**: the body says `SubspaceDesign.lean` contains "**the layer's only two
  `sorry`s**, both tagged external admits", "**Sorry census: exactly 2 new proof-term sorries**",
  and "400 declarations across all 21 touched Lean modules … 397 carry exactly
  `{propext, Classical.choice, Quot.sound}`". At `ffa0733a` there are **zero** new sorries
  (commits `b8b4b87b` and `dab6d75c` proved both), and the counts don't reproduce: 28 touched
  Lean modules, 586 constants (incl. auto-generated, excl. private) / 538 source-level
  (incl. private), 5 `sorryAx` carriers all pre-existing. `lake build` reports 4197 jobs, not 4196.
- **Evidence**: probes above; `git log 4f386913..ffa0733a`; `SCRATCH/R9-build.log`.
- **Refutation attempt**: I tried three counting bases (all constants incl. internals; public
  non-internal; source-level incl. private) — none yields 400/397. Also checked whether "21
  modules" could mean the ABF26-only subset: the 11 new files hold 90 constants, not 400.
- **Suggested fix**: refresh the body's census (owner convention is push-commits-only, so this
  is a note for the author, not an edit request from me).

---

## Part 2 — Exhaustive vacuity sweep

Method: enumerated all ~120 declarations added by the diff
(`git diff … | grep -E '^\+\s*(theorem|lemma|def|…)'`), then for each public statement checked
the tell-tales (probability RHS ≥ 1, `ℕ∞`/`ENNReal` bound = `⊤`, `Nat` truncated subtraction,
division-by-zero, `Set.ncard` of an infinite set, `⊥`/empty-`ι`/`card = 0,1` degeneracies,
inclusion into `univ`, existential satisfied by the trivial witness), and compiled probes for
everything I could not clear by inspection.

**Result: no VACUOUS-HYP and no VACUOUS-CONC among the PR's public theorems.**

### Certified non-vacuous by compiled probe

**`CodingTheory.frs_is_subspaceDesign_gk16`** (`SubspaceDesign.lean:482`) — this is the one with
the most vacuity surface (its own docstring concedes a contentless regime `k ≥ s·|ι|`).
`(session-local probe) R9-vacuity-sd4.lean` compiles with **zero errors** and establishes, at
`F = ZMod 5`, `ι = Fin 2`, `s = 2`, `k = 1`, `ω = 2`, `L = {1, 4}`, `domain = ![1,4]`:

- every hypothesis holds — `hFn2 : |ι| < |F|`, `adm2 : Admissible L2 2 2`,
  `ord2 : orderOf (2 : 𝔽₅) = |𝔽₅| − 1`, `hLdom`, `ω ≠ 0` — i.e. **the hypothesis set is
  jointly satisfiable**, and inside the content-bearing regime `k = 1 < 4 = s·n`;
- `tau_lt_one`: the resulting profile is `τ(1) = 1/4`, `τ(2) = 1/2`, **strictly `< 1` on all of
  `[1, s]`**. This is the sharp non-vacuity criterion: the proof's own `hsum_le` shows
  `Σᵢ dim(A ⊓ ker projᵢ)/n ≤ dim A` holds for *every* code, so the theorem has content exactly
  when `τ r < 1`, which it does here;
- `dimA : Module.finrank 𝔽₅ (frsCode dom2 1 2 2) = 1` — the code is not `⊥`;
- `#print axioms A_instance` → `[propext, Classical.choice, Quot.sound]`.

**`CodingTheory.subspaceDesign_tau_lower`** (`SubspaceDesign.lean:133`) —
`(session-local probe) R9-vacuity-sd.lean` section B compiles and shows:

- `top_is_design`: `IsSubspaceDesign s (fun _ ↦ 1) ⊤` holds for any `s`, `ι`, `F`, so the
  hypothesis pair `(h_design, hτ_nonneg)` is satisfiable;
- at `F = ZMod 2`, `ι = Fin 2`, `s = 2`, `C = ⊤` the RHS is `finrank/(s·n) − 1/n = 1 − 1/2 = 1/2`,
  **strictly positive** — so the conclusion is not the trivial `τ ≥ (something ≤ 0)` that the
  `hτ_nonneg` degenerate branch produces;
- a genuine *negative* consequence compiles:
  `¬ IsSubspaceDesign 2 (fun _ ↦ (1:ℝ)/4) (⊤ : Submodule (ZMod 2) (Fin 2 → Fin 2 → ZMod 2))`.
  The theorem therefore rules candidate profiles *out*; it is not a tautology.

**`Probability.exists_large_image_of_pairwise_collision_bound`** (Claim B.1) — the one place a
`Nat`-truncated subtraction could silently collapse the bound. `(session-local probe) R9-vacuity-misc.lean`
elaborates the statement with `pp.numericTypes` and confirms the denominator is
`(1 : ENNReal) + (↑(Fintype.card S) − (1 : ENNReal)) * ε`, i.e. an **`ENNReal` subtraction of a
cast**, not `((Fintype.card S − 1 : ℕ) : ENNReal)`. (Both agree here anyway, but the shape is the
faithful one.) The bound degrades gracefully at `ε = ⊤` (RHS `= 0`) and at `S = ∅`.

### Cleared by inspection (with the specific degeneracy checked)

- `johnson_bound_lambda_le_ell` (T3.2): the radicand guard is *not* self-defeating — at
  `q = 2, ℓ = 2` it reads `δ_min ≤ 1`, always true, and `Jqℓ 2 2 δ_min = ½(1 − √(1−δ_min)) > 0`
  for `δ_min > 0`. So there are satisfying instances with a strictly positive radius.
  `Jqℓ q 0 δ = 0` and `Jqℓ q ℓ 0 = 0` are the only collapses and both are excluded/harmless
  (`2 ≤ ℓ`; `δ_min = 0` only for `|C| ≤ 1`).
- `mds_johnson_lambda_le` (C3.3): `IsMDS` is satisfiable (RS codes) and excludes `C = ⊥`
  (the proof derives `1 ≤ k` from `IsMDS` + `dist ≤ n`). The conclusion is non-trivial in the
  regime `1 − √ρ − η > 0`, e.g. `ρ = 1/2, η = 0.1` gives radius `≈ 0.193` and bound `10`.
  The `Lambda = 0` branch (negative radius) is an explicitly handled corner, not the whole
  theorem.
- `hammingBallVolume_eq_ncard_hammingBall`, `card_filter_hammingDist_eq`,
  `lambda_extensionCode_eq_lambda_interleaved`, `dim_frsCode`, `dim_irsCode`,
  `dim_irsCode_of_dvd`, `minDist_frsCode`, `mem_umCode_one_iff_mem_rsCode`,
  `IsMDS_iff_rate_distance(')`, `Pr_map_eq`, `prob_uniform_pi_mem_finset_eq`,
  `qEntropy_eq_qaryEntropy_div_log`, `foldedWronskian_ne_zero_of_linearIndependent`,
  `X_pow_card_sub_one_sub_C_irreducible`: all **equalities, iffs, or `≠ 0`/injectivity
  statements**, so structurally immune to conclusion-vacuity. Degenerate parameter values
  (`q = 1`, `i > n`, `s = 0`, `k = 0`) were checked to give correct, not vacuous, values.
- `singleton_bound_module`: `Nat` subtraction `card ι − (dist − 1)` degenerates to
  `finrank C ≤ finrank A · n` when `|C| ≤ 1` (`dist = 0`) — trivially true but correct, and
  this is the standard Singleton shape. Its real consumer (`subspaceDesign_tau_lower` step 5)
  runs in the `dist ≥ 1` regime.
- `prob_dotProduct_eq_zero_le`, `prob_uniform_le_inv_of_card_le_one`,
  `prob_polynomial_identity_le`: RHS `1/|F|` or `m(d−1)/|F|`, never `≥ 1` in the intended
  regime; `d = 0` makes `h_indiv_deg` unsatisfiable for `m ≥ 1` (docstring says so, correct),
  `d = 1` gives bound `0` with `Pr = 0` (constant nonzero `P`), which is tight, not vacuous.

### [MEDIUM] `SupportsErasureCorrection` is a tautology and has zero consumers

- **Where**: `ArkLib/Data/CodingTheory/Erasure.lean:66` (`def SupportsErasureCorrection`),
  `:125` (`additive_code_supports_erasure_correction_grs12`).
- **Source**: ABF26 D6.4 / L6.5 (via [GRS12]).
- **What's wrong**: `additive_code_supports_erasure_correction_grs12 (C : Set (ι → F)) :
  SupportsErasureCorrection C` takes **no hypotheses at all** — the predicate is provable for
  *every* set `C`, including `∅` and `univ`. As a *hypothesis* it therefore conveys zero
  information, and any future theorem written as
  `(h : SupportsErasureCorrection C) → …` will be silently equivalent to the unconditional
  statement. `grep -rn 'SupportsErasureCorrection' ArkLib/` shows **no consumer** outside
  `Erasure.lean`, so nothing is broken today — but the file currently buys nothing except a
  paper-row tick.
  Secondarily, the D6.4 docstring says clause (ii) "is what makes the predicate **non-vacuous**".
  That is the wrong word: clause (ii) makes the *corrector* non-hollow, but the predicate is a
  theorem-schema with or without it. A reader scanning for "is this a real assumption?" is
  actively misled.
- **Evidence**: `(session-local probe) R9-vacuity-misc.lean` compiles
  `example {ι F} [Fintype ι] [DecidableEq F] : ∀ C : Set (ι → F), SupportsErasureCorrection C`
  and the two concrete instances at `∅` and `univ`. Plus the theorem in the file itself.
- **Refutation attempt**: I looked for a strengthening that would make the predicate bite — a
  computability/complexity clause, a uniformity clause over `C`, or an efficiency parameter.
  The docstring explicitly disclaims all of them ("ArkLib's extractors are uniformly cost-free
  … deliberately not formalized here … the existence statement below requires nothing from
  [GRS12]"), so the tautology is intentional and *documented* — which is why this is MEDIUM,
  not HIGH. It is still a defect that the D6.4 docstring calls it "non-vacuous".
- **Suggested fix**: reword the D6.4 docstring's "non-vacuous" claim (it is about the corrector's
  shape, not about satisfiability), and add one sentence stating outright that
  `SupportsErasureCorrection C` is a theorem, not an assumption, so downstream statements must
  not take it as a hypothesis. Optionally hold the file until it has a consumer.

### [LOW] `Lambda` inherits `Set.ncard`'s "infinite ↦ 0" convention

- **Where**: `ArkLib/Data/CodingTheory/ListDecodability.lean:93` (`Lambda`).
- **What's wrong**: `Lambda C δ := ⨆ f, ((closeCodewordsRel C f δ).ncard : ℕ∞)` has no
  finiteness hypothesis. Over an infinite alphabet `Set.ncard` of an infinite list is `0`, so
  `Lambda C δ = 0` (and hence *every* `Lambda ≤ ℓ` bound) can hold while the true list is
  infinite. `Lambda_le_iff_listDecodable` is stated without `[Finite F]`, so it transports
  this degeneracy to `listDecodable` (harmlessly — both sides use `ncard`).
- **Evidence**: `Set.Infinite.ncard : s.Infinite → s.ncard = 0` (Mathlib); the PR's own
  `Lambda_ne_top` needs `[Finite F]` precisely because of this.
- **Refutation attempt**: I checked every PR-introduced consumer — `Lambda_mono`,
  `Lambda_le_card`, `Lambda_ne_top`, `johnson_bound_lambda_le_ell`, `mds_johnson_lambda_le`,
  `lambda_extensionCode_eq_lambda_interleaved` — and **all of them carry `[Finite F]` or
  `[Fintype …]`**, so no shipped statement is currently degenerate. That is why this is LOW.
  (This is a definitional observation resting on the Mathlib lemma, not on a bespoke witness;
  I did not carry a concrete `Lambda … = 0` instance to a compile.)
- **Suggested fix**: add a docstring line on `Lambda` warning that the definition is only
  meaningful under a finiteness assumption, and consider `[Finite F]` on
  `Lambda_le_iff_listDecodable` for uniformity.

---

## Part 3 — Build and lint hygiene

### `sorry` census — CLEAN

`grep -n '\bsorry\b'` over all 28 touched Lean files: the only real occurrence is the
pre-existing `ArkLib/Data/Fin/Basic.lean:333` (`Fin.sumCases`). Everything else is a comment
(`DG25/MainResults.lean:504,1147`, `Probability/Instances.lean:35,40`) or prose in a docstring
(`SubspaceDesign.lean:28,30` — which say "**proved**, sorry-free", now accurate).
Cross-checked against the axiom sweep: no `sorryAx` outside the 5 pre-existing carriers, so
no `sorry` is hiding behind a helper in another file. **VERIFIED.**

### `lake build` — GREEN

`SCRATCH/R9-build.log`: `Build completed successfully (4197 jobs)`.

### `ArkLib/Data` zero-warning gate — GREEN on the branch, and the rider is genuinely needed

```
$ python3 ./scripts/check-warning-log.py SCRATCH/R9-build.log \
    --path-prefix ArkLib/Data/ --exclude-substring 'declaration uses `sorry`' …
No ArkLib/Data non-sorry warnings found.     # exit 0
```
23 `ArkLib/Data` warnings total, all `declaration uses 'sorry'` (excluded by the gate).

Rider commit `55aeff13` verified necessary: `origin/main`'s
`ArkLib/Data/MvPolynomial/EvenAndOdd.lean:151` uses `Finset.prod_eq_mul_prod_diff_singleton`,
which in the pinned Mathlib is
`.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:201`
`@[deprecated (since := "2026-06-03")] alias prod_eq_mul_prod_diff_singleton := prod_eq_mul_prod_sdiff_singleton`
— i.e. main emits a deprecation warning under `ArkLib/Data/`, so the gate is red on main and
green here.

#### [LOW] The deprecation rider is scope creep

- **Where**: commit `55aeff13`, `ArkLib/Data/MvPolynomial/EvenAndOdd.lean`.
- **What's wrong**: a one-line fix to a file with no ABF26 content, riding a 4 900-line
  coding-theory PR. It is defensible (without it the PR's own `validate.sh` is red for a reason
  unrelated to the PR), but it belongs in a two-line PR of its own, where it can merge in
  minutes and unblock everyone.
- **Refutation attempt**: I checked whether the PR *needs* the fix to pass its own gate — it
  does, since `check-warning-log.py` is path-prefixed on all of `ArkLib/Data/`, not on the
  changed files. So the coupling is real. Still separable.
- **Suggested fix**: split into its own PR (or keep, and say so in the body — the body currently
  does not mention the rider at all).

### Style lint — the "byte-identical to main; zero new lint" claim is **VERIFIED**

Ran `scripts/lint-style.py` over the full `ArkLib/**/*.lean` set on (a) the branch and (b) a
`git archive` extraction of the merge-base `4f386913` into `SCRATCH/base-tree`
(no worktree added, primary checkout untouched):

- branch: **730** errors; merge-base: **730** errors;
- `diff` shows **only line-number shifts** on the same (file, error-kind) pairs. No new
  (file, error-kind) pair appears, none disappears.
- Against `origin/main` (`02d759d5`, 4 commits ahead) the only extra difference is one
  `ERR_IBY` in `ProximityGap/Folding.lean` that comes from main's newer commits, not from this PR.
- **Zero lint hits in any of the 11 new files.** (`SCRATCH/R9-lint-{branch2,base,main}.txt`.)

Caveat worth stating in the review: `./scripts/lint-style.sh` **exits non-zero on both**
(730 pre-existing errors), so `validate.sh --lint` is red on main and on the branch alike.
The PR does not make it worse; it also cannot make it pass.

`check-docs-integrity.py` and `scripts/kb/lint.py` both pass. `DISABLE_EQUATIONS=1 lake build
ArkLib:docs` was launched but had **not completed** within this review's window (machine at load
≈ 45 from a concurrent unrelated build). At the point I stopped waiting it had populated 4 872
`.lake/build/doc-data` entries and a 209 MB `api-docs.db` with **no error on stderr** — doc-gen4
aborts on a malformed docstring, so this is partial (not conclusive) evidence that the docstring
surface is clean. **Flagging as an unverified item rather than asserting it**; someone should
re-run `./scripts/validate.sh --lint --docs` on an idle machine before merge.

### `ArkLib.lean` — CONSISTENT

Reproduced the generator read-only
(`git ls-files -- 'ArkLib/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /'`)
rather than running `check-imports.sh` (which rewrites the tracked file): output is
**byte-identical** to the committed `ArkLib.lean`. All 11 new modules are present, sorted.

### Long-file cap — RESPECTED

Largest new file is `SubspaceDesign.lean` at 763 lines; largest touched file overall is the
pre-existing `BCIKS20/AffineSpaces.lean` (2327 lines, +1 line from this PR). The **only**
`linter.style.longFile` opt-out anywhere in `ArkLib/` is
`AffineSpaces.lean:2327: set_option linter.style.longFile 2400`, which is pre-existing.
No new file opts out, silently or otherwise. The build log contains no `longFile` warning
under `ArkLib/Data/`.

### Headers and module docstrings

All 11 new files carry the standard copyright block (`Copyright (c) 2026 ArkLib Contributors`
+ Apache-2.0 line + `Authors: Alexander Hicks`) and a `/-! # Title -/` module docstring —
confirmed independently by `lint-style.py` reporting zero `ERR_COP` / `ERR_MOD` on them.

#### [LOW] Two new files cite papers but have no `## References` section

- **Where**: `ArkLib/Data/CodingTheory/Basic/Entropy.lean`,
  `ArkLib/Data/CodingTheory/HammingBallVolume.lean`.
- **Source**: `CONTRIBUTING.md` §Citation Standards — "Each file that cites papers should have a
  `## References` section in its docstring header".
- **What's wrong**: both cite ABF26 (D2.2 / C3.8 / T3.11 and D2.4 / L3.7 / C3.8 respectively) in
  prose but have no `## References` block. Section inventory of the 11 new files:

  | file | sections present |
  | --- | --- |
  | `Basic/Entropy.lean` | *(none)* |
  | `HammingBallVolume.lean` | *(none)* |
  | `Erasure.lean` | References |
  | `JohnsonBound/Family.lean` | References |
  | `Probability/Combinatorial.lean` | References |
  | `ReedSolomon/Multiplicity.lean` | Notation, Layout, References |
  | `ReedSolomon/Folded.lean` | Main definitions, Main lemmas, References |
  | `ReedSolomon/Interleaved.lean` | Main definitions, Main lemmas, References |
  | `ExtensionCodes.lean` | Main definitions, Main statements, References |
  | `SubspaceDesign.lean` | Main definitions, Main statements, Deferred, References |
  | `Polynomial/FoldedWronskian.lean` | Main definitions, Main statements, References |

  (Only the two empty rows are `CONTRIBUTING` violations; the missing
  `## Main definitions`/`## Main statements` elsewhere is a soft convention, and
  `Folded`/`Interleaved` use `## Main lemmas` where the rest of the tree uses
  `## Main statements` — worth normalising.)
- **Suggested fix**: add `## References` to the two files; normalise `Main lemmas` →
  `Main statements`.

#### [LOW] No BibTeX entries for any of the PR's citation keys, and two citation formats

- **Where**: `blueprint/src/references.bib` vs the new files' References sections.
- **Source**: `CONTRIBUTING.md` — "All academic papers must have entries in
  `blueprint/src/references.bib`"; format `* [Author Last Name, First Initial, *Title*][key]`.
- **What's wrong**: none of `ABF26, GK16, GX13, GG25, GR08, GW13, KSY14, BuenzCFW25, Joh62,
  GRS12/GuruswamiRS12, DiamondP23, GGR11` exists in `references.bib` (55 keys there today).
  Separately, the PR uses two citation formats in its own new files: `Combinatorial.lean` and
  `Multiplicity.lean` use the mandated `* [Authors, *Title*][KEY]`; `SubspaceDesign.lean`,
  `Folded.lean`, `Interleaved.lean`, `ExtensionCodes.lean`, `JohnsonBound/Family.lean` use the
  reversed `- [KEY] Authors. *Title*.`.
- **Refutation attempt**: checked whether this is already systemic — of the 34 keys used in the
  mandated `][KEY]` form across `ArkLib/`, three (`ABF26`, `BS08`, `GRS25`) are missing from the
  bib, so `BS08`/`GRS25` are pre-existing precedent. That keeps this LOW, but `ABF26` and the
  eight new keys are this PR's to add.
- **Suggested fix**: add the BibTeX entries and use one format.

### Linter suppressions — re-enabled and audited, one by one

**Method**: copied each affected file to `(session-local probe) R9-lint-<file>.lean` with every
`set_option linter.X false` flipped to `true`, and compiled with `lake env lean`
(output `tasks/b248e879a.output`). Repo files untouched.

| file | suppressed | fires when re-enabled |
| --- | --- | --- |
| `SubspaceDesign.lean:49-51` | Fintype, Decidable, **SectionVars** | `subspaceDesign_tau_lower` (1 Fintype, ≥1 Decidable); `sum_rootMultiplicity_le_natDegree` (Decidable). **SectionVars: nothing.** |
| `ReedSolomon/Interleaved.lean:33-35` | Fintype, Decidable, SectionVars | **nothing at all** |
| `ExtensionCodes.lean:50-51` | Fintype, Decidable | `lambda_extensionCode_eq_lambda_interleaved` (both) |
| `HammingBallVolume.lean:31-32` | Decidable, Fintype | `hammingBallVolume_eq_ncard_hammingBall` (Decidable only) |
| `JohnsonBound/Family.lean:54-55` | Fintype, Decidable | `reidx_hammingDist`, `johnson_bound_lambda_le_ell`, `mds_johnson_lambda_le` |
| `ReedSolomon/Folded.lean:48` | Decidable | `admissible_foldedPoints_injective`, `frsEvalOnPoints_domRestrict_injective` |

**The key result for this review**: `linter.unusedSectionVars` — the linter whose suppression
could hide a "load-bearing hypothesis isn't" bug — **fires zero times in both files that disable
it**. There is no unused section variable being covered up. Every warning that does appear is
`unusedFintypeInType` / `unusedDecidableInType`, i.e. an *instance* argument that the proof needs
but the statement does not mention (Lean's suggested remedy is `classical` / `Finite` +
`Fintype.ofFinite`). None of them is a mathematical hypothesis, so none is a soundness or
vacuity concern.

#### [LOW] Dead and over-broad linter suppressions

- **Where**: `SubspaceDesign.lean:51`, `ReedSolomon/Interleaved.lean:33-35`,
  `HammingBallVolume.lean:32`.
- **What's wrong**: `Interleaved.lean` disables three linters and **none of them has anything to
  say**; `SubspaceDesign.lean`'s `unusedSectionVars` and `HammingBallVolume.lean`'s
  `unusedFintypeInType` are likewise inert. Dead suppressions rot: they silently absorb a real
  warning the next time the file is edited. Separately, all of these are **file-level**
  `set_option … false`, whereas the surrounding idiom (pre-existing
  `BCIKS20/AffineSpaces.lean:370,944`) scopes them per-declaration with `… in`.
- **Evidence**: the table above (compiled).
- **Suggested fix**: delete the inert ones; convert the live ones to `set_option … false in`
  immediately above the specific declaration, or (better, and what the linter asks for) drop the
  unused `[Fintype F]`/`[DecidableEq …]` from the statements and use `classical` /
  `Fintype.ofFinite` inside the proofs.

#### [LOW] Underscore-prefixed hypotheses that are in fact used

- **Where**: `JohnsonBound/Family.lean:401` (`_hℓ_ge`), `:402` (`_h_radicand`), `:601`
  (`_hη_pos`), `:602` (`_h_mds`).
- **What's wrong**: the `_` prefix is the Lean convention for "deliberately unused", and a
  reviewer scanning for hollow hypotheses will read these four as decoration. All four are
  actually consumed (`Family.lean:513, 515, 615, 758, 775`). Conversely
  `ExtensionCodes.lean:316`'s `_hδ_pos`/`_hδ_lt` and `Family.lean:529`'s `_hs1` really are
  unused — so the prefix carries no information at all in this file.
- **Evidence**: `grep -n '_hη_pos\|_h_mds\|_hδ_pos\|_hδ_lt\|_hℓ_ge\|_h_radicand\|_hs1'`.
- **Suggested fix**: drop the `_` from the four that are used; keep it on the genuinely-unused
  paper-fidelity hypotheses and say so in one docstring line (`lambda_extensionCode_eq_lambda_interleaved`
  is in fact *stronger* than L2.21 — it holds for every real `δ`).

#### [LOW] Nine consecutive blank lines

- **Where**: `ArkLib/Data/CodingTheory/JohnsonBound/Family.lean:518-527`.
- Leftover from an edit; `CONTRIBUTING.md` asks to avoid stray empty lines. Cosmetic.

---

## Clean bill

Checked and found genuinely OK (this is the coverage record):

**Axioms**
- All 538 source-level declarations (incl. private) across all 28 touched modules swept by
  metaprogram, not sampled; 533 carry exactly the three standard axioms.
- A second pass over 586 constants including auto-generated ones, to make sure nothing hides in
  equation lemmas / projections. Same 5 carriers.
- Confirmed the 4 `ProximityGap` `sorryAx` carriers sit in files whose entire diff is one
  `open Probability` line.
- Confirmed `Fin.sumCases`'s `sorry` at `Data/Fin/Basic.lean:333` is untouched (docstring only),
  and that nothing new reaches it transitively.
- `#print axioms` on a fully-applied `frs_is_subspaceDesign_gk16` instance: three standard axioms.
- No `axiom` declarations introduced anywhere in the diff; no `native_decide` (which would show
  up as `Lean.ofReduceBool` in the sweep, and does not), no `@[implemented_by]`, no `unsafe`,
  no `opaque`.

**Vacuity**
- All ~120 new declarations enumerated from the diff and triaged.
- The two headline theorems certified non-vacuous by compiled concrete instances, including the
  sharp criterion (`τ < 1`) rather than mere hypothesis-satisfiability.
- `subspaceDesign_tau_lower` shown to have real deductive power (compiled refutation of a
  candidate profile).
- Claim B.1's `ENNReal` denominator confirmed not to be a truncated `ℕ` subtraction.
- Degenerate corners individually checked: `q = 1`, `Fintype.card = 0/1`, `ι` empty
  (excluded by `[Nonempty ι]` where it matters), `C = ⊥`, `s = 0`, `k = 0`, `ℓ ∈ {0,1}`,
  `δ ≤ 0`, `d = 0` in `prob_polynomial_identity_le`, `i > n` in `card_filter_hammingDist_eq`,
  `s ∤ k` in `irsCode`.
- No `Set` inclusion into `univ`, no `⊤` bound, no probability RHS `≥ 1`, no existential
  discharged by a trivial witness among the new statements.

**Build / lint**
- Zero new `sorry`, cross-validated two ways (grep + axiom sweep).
- `lake build` green, 4197 jobs.
- `ArkLib/Data` zero-warning gate green (gate script run on the real build log).
- Deprecation rider verified against the pinned Mathlib's `@[deprecated]` attribute.
- Style-lint multiset compared against the merge-base *and* `origin/main`: identical modulo line
  numbers; zero hits in the 11 new files. The PR's "zero new lint" claim is VERIFIED.
- `ArkLib.lean` reproduced from the generator read-only: byte-identical.
- `check-docs-integrity.py`, `scripts/kb/lint.py`: pass.
- Long-file cap respected; the single opt-out in the tree is pre-existing.
- Copyright headers, `Authors:` lines, module docstrings present on all 11 new files.
- Every `set_option linter.* false` re-enabled in a probe copy and its output recorded.
- `docs/kb/audits/…` rows for L2.17 / T2.18 / L6.5 / B.1 / A.7 checked against the code: the
  "proved in-tree, sorry-free, axiom-clean" claims are accurate (unlike the PR body's).

**Not verified** (stated rather than asserted): `DISABLE_EQUATIONS=1 lake build ArkLib:docs`
did not finish inside this review's window.
