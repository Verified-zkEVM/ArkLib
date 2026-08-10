# PR #701 — fix-session bootstrap

**Purpose.** This is the single entry point for a fresh session whose job is to close the
remaining review findings on `feat/abf26-split-ct-data`. It is self-contained: read this file
and the four rows of §2 you are working on, and you should not need to re-derive anything.

**Do not re-run the review.** Three independent review passes are already complete and their
findings are validated. Re-reviewing wastes a session and risks re-litigating settled items
(see §5 for what is settled and must not be reopened).

---

## 1. State

| | |
|---|---|
| Branch | `feat/abf26-split-ct-data` |
| Tip at bootstrap | `81770af2` |
| Base | rebased onto `origin/main` `5fea8abf`; `origin/main` **is** an ancestor |
| Published PR head | **behind** — the branch is not pushed. See I1. |
| Build | `lake build` green (4202 jobs) pre-rebase; re-verify after any change |
| `ArkLib/Data` + `ArkLib/ToMathlib` non-sorry warning gates | green |
| Sorry / axioms | zero `sorry` in the layer; all changed declarations exactly `{propext, Classical.choice, Quot.sound}` |
| Style lint | `(file, error-kind)` multiset identical to merge-base — keep it that way |
| Safety branch | `backup/pre-rebase-abf26-split-pr1` (pre-rebase tip `d72b4330`) |

### Reading order for context

1. This file.
2. [`INDEPENDENT-REVIEW-2026-08-09.md`](INDEPENDENT-REVIEW-2026-08-09.md) — the most recent and
   most complete pass; the source of B1/H1/M1–M5/L1–L4 below.
3. [`VALIDATION-2026-08-09.md`](VALIDATION-2026-08-09.md) — per-cluster disposition at the tip.
4. [`VERDICT.md`](VERDICT.md) + `R1..R11-*.md` — the original 2026-08-07 snapshot. **Immutable
   and deliberately stale**: it describes `ffa0733a`, before two fix passes. Use it for the
   *reasoning* behind a finding, never for current declaration names or line numbers.

### Validation commands

```bash
lake build                                    # must stay green
python3 ./scripts/check-warning-log.py <log> --path-prefix ArkLib/Data/ \
    --exclude-substring 'declaration uses `sorry`' --label 'Data non-sorry warnings'
./scripts/validate.sh --docs                  # run SEPARATELY; see the note below
python3 scripts/kb/lint.py --strict-cited-pages
python3 scripts/check-docs-integrity.py
```

`./scripts/validate.sh --lint` fails on `main` too (large pre-existing style backlog) and
`set -euo pipefail` makes it abort **before** `--docs`, so always run `--docs` on its own. To
check you have added no lint, compare the `(file, error-kind)` multiset against the merge-base,
not the total. See `docs/wiki/quickstart.md`.

**Never commit `docs/kb/_generated/**`** — `docs/wiki/generated-files.md:23`. They must stay
byte-identical to `origin/main`. This has already bitten this PR twice.

For declaration inventories or axiom sweeps prefer
[lean4export](https://github.com/leanprover/lean4export) over regex scraping or ad-hoc
metaprograms; the latter produced four different declaration totals during this review.

---

## 2. Open findings

Ordered by what I would do first. Every one is validated — each has either a compiled probe or an
exact source quote behind it in the linked report.

### Group A — regressions from the second fix pass (do these first; all small)

| id | Finding | Where | Action |
|---|---|---|---|
| **A1** | Four lemmas carry `[Finite F]` that is **provably unnecessary**. All four are the *`Lambda`-bound → consumer* direction, where the hypothesis itself forces the point list finite (`Set.finite_of_encard_le_coe`), or where `ncard = 0` on an infinite set makes the bound free. Re-proved without it. | `Data/CodingTheory/ListDecodability.lean` — `ncard_closeCodewordsRel_le_Lambda`, `listDecodable_of_Lambda_le_natCast`, `Lambda_le_floor_of_toENNReal_le_ofReal`, `listDecodable_of_toENNReal_le_ofReal` | Drop `[Finite F]` from exactly these four. **Keep** it on `Lambda_le_iff_listDecodable`, `Lambda_le_floor_iff_listDecodable`, `_nnreal`, `Lambda_le_floor_of_listDecodable` — a compiled counterexample (`Code (Fin 1) ℚ`, `δ=1`, `ℓ=0`) refutes the `←` direction without it. Then fix `Lambda`'s docstring, which claims the bridges need `[Finite F]` "exactly where `encard` agrees" — it overclaims by four lemmas. |
| **A2** | Three declarations orphaned by the `encard` change. `Lambda_eq_iSup_encard` is now literally `rfl` with zero consumers yet still advertised in `## Main statements`. `ncard_closeCodewordsRel_le_Lambda`'s sole consumer now inlines `le_iSup`. `Pr_decide_eq_tsum_indicator`'s only user migrated to `Pr_eq_tsum_indicator`. | `ListDecodability.lean`, `Data/Probability/Notation.lean` | Delete, or give each a consumer and an honest docstring. `Pr_decide_eq_tsum_indicator` is a zero-consumer compatibility wrapper against the repo's no-alias doctrine — prefer deleting. |

### Group B — labelling and honesty (no theorem is false; all cheap)

| id | Finding | Where | Action |
|---|---|---|---|
| **B1** | `LinearCode.rate` is `finrank/n`, but ABF26 D2.5 rate over alphabet `F^s` is `finrank/(s·n)`. Compiled counterexample: `rate (⊤ : Submodule (ZMod 2) (Fin 1 → Fin 2 → ZMod 2)) = 2` where ABF26 gives `log_4 4 = 1`. The definition predates the PR, but the PR newly maps D2.5 onto it. | `Basic/LinearCode.lean` (defn), audit D2.5 row, `coding-theory-conventions.md` type table | **Do not silently change `rate`.** Document it as the base-field-dimension rate, correct only for `s = 1`, and correct the D2.5 mapping to say ABF's alphabet-normalized rate is `finrank/(s·n)` — which is what `subspaceDesign_tau_lower` and `frs_is_subspaceDesign_gk16` already use explicitly. Optionally add a normalized module-alphabet rate. |
| **B2** | `mds_johnson_lambda_le` is labelled ABF26 C3.3 "fully proven" but quantifies over `LinearCode ι F`, so it cannot express interleaved RS — the class the paper's C3.3 preamble singles out. | `JohnsonBound/Family.lean`, audit C3.3 row | Call it a field-linear specialization; record C3.3 as **partial**. (Generalizing needs the module-alphabet rate-distance bridge — that is B1's optional half and probably a later split.) |
| **B3** | The pre-existing `listDecodable` is still vacuous on infinite alphabets (`Set.ncard` = 0), and its docstring asserts the cardinality "is a natural number anyway" — false at that generality. `uniqueDecodable` inherits it. | `ListDecodability.lean` | Minimum: fix the false docstring. Changing the definition to `encard` touches STIR consumers → treat as a separate PR unless the owner says otherwise. |
| **B4** | `johnson_bound_lambda_le_ell` assumes `2 ≤ ℓ` while its docstring says "no side condition, exactly as in the paper"; ABF26 has `ℓ ≥ 1`. The `ℓ = 1` case is true and elementary (`J_{q,1}(δ) = 0`, a radius-0 list has ≤ 1 word). | `JohnsonBound/Family.lean` | Add the boundary case, or weaken the "exactly/no side condition" claim. A prior attempt hit a `DecidableEq α` instance mismatch between `closeCodewordsRel`'s `Classical.propDecidable` and the section instance — the existing proof works around it with `congr!`. |

### Group C — generality and placement (small code changes)

| id | Finding | Where | Action |
|---|---|---|---|
| **C1** | Three declarations carry `[Field F]` where weaker compiles: `ReedSolomon.mem_map_degreeLT_one_iff_mem_code` → `[CommSemiring F]`; `frsCode` + elementary membership/collapse API → the same ambient semiring as `frsEvalOnPoints`; `Polynomial.natDegree_comp_C_mul_X_le` → `[Semiring F]`. | `ReedSolomon.lean`, `ReedSolomon/Folded.lean`, `ToMathlib/Polynomial/CompositionDegree.lean` | Weaken. Keep fields for distance, dimension, admissibility and Kummer, which genuinely need them. The `[Field F]` on the shared collapse lemma is what forces both the folded and multiplicity `s = 1`/`m = 1` corollaries to fields unnecessarily. |
| **C2** | `reidx_hammingDist` hardcodes `e : ι ≃ Fin (Fintype.card ι)`; the same proof compiles for arbitrary `e : ι ≃ ι'`. It has four real consumers, so this is not dead code. Mathlib's `hammingDist_comp` transports alphabet values, not the coordinate index; no index-equivalence transport exists in Mathlib or ArkLib. | `JohnsonBound/Family.lean` | Generalize the signature and move it to `Basic/Distance.lean` or a `ToMathlib` Hamming module. |
| **C3** | `MvPolynomial.totalDegree_le_of_degreeOf_lt` went to `Data/MvPolynomial/Degrees.lean` while every other generic helper in the same sweep went to `ArkLib/ToMathlib/`, and its "intended Mathlib target next to `degreeOf_le_totalDegree`" note was dropped. | `Data/MvPolynomial/Degrees.lean` | Pick one convention. Either move it to `ToMathlib/MvPolynomial/Degrees.lean` or restore the upstream-target note explaining why it stays. |
| **C4** | `ExtensionFieldPresentation.coord` is documented as an "abbreviation" but is a `noncomputable def`; `def` and `abbrev` differ in reducibility. | `ExtensionCodes.lean` | Make it an `abbrev` or call it a thin definition. |

### Group D — stale documentation (mechanical)

| id | Finding | Where |
|---|---|---|
| **D1** | `[BCGM25]` References entry points at "the generalization note on `eq_of_consistent_with_erased`", deleted in the second fix pass. | `Erasure.lean:36-39` |
| **D2** | Audit still lists `sum_fiber_sq_eq` / `cauchy_schwarz_fiber` as Lean refs; both are now `private`. | audit `:137`; `Combinatorial.lean:57,132` |
| **D3** | The T2.18 audit row dropped its provenance record (the `ω = −1` over `𝔽₁₀₁` counterexample, PAPER_REVS #13) for vaguer prose. That falsification was hard-won — restore it. | audit T2.18 row |
| **D4** | `docs/kb/sources/GX13/metadata.yml` classifies GX13 as an `article` and says the bibliography has a different title; it is a STOC 2013 `@inproceedings` and the BibTeX title is already corrected. | `sources/GX13/metadata.yml` |
| **D5** | `docs/kb/papers/GW13.md` says `SubspaceDesign.lean` still claims the derivative operation is missing; it does not — the missing item is the multiplicity-Wronskian analogue. | `papers/GW13.md` |
| **D6** | Seven new `## References` sections do not follow `CONTRIBUTING.md`'s `* [Author Last Name, First Initial, *Title*][key]` format. Keys all resolve, so this is formatting only. | `ExtensionCodes`, `JohnsonBound/Family`, `ReedSolomon/{Folded,Interleaved,Multiplicity}`, `SubspaceDesign`, `Data/Polynomial/FoldedWronskian` |

### Group E — integration (owner action)

| id | Finding | Action |
|---|---|---|
| **I1** | The published PR head is behind this branch, and the PR body is materially stale: it claims two remaining `sorry`s (there are none), describes an earlier revision's statistics, and still says `Erasure.lean` supplies `SupportsErasureCorrection` for D6.4 and proves L6.5 — both were **deleted** as tautologies and the audit now records D6.4/L6.5 as *missing*. | Push the validated tree, then refresh the PR body. **The body must be edited by the repo owner, not by an agent.** |

---

## 3. Explicitly out of scope for the fix session

Do not start these without an owner decision; each is a separate PR.

- The univariate-multiplicity half of ABF26 T2.18 (needs a multiplicity analogue of the folded
  Wronskian).
- An encoder-level extension-code abstraction (`extensionEncode`) and D2.20's systematic encoder
  equality — ArkLib models the code *image*, so the paper's `C_F(ψ v) = ψ(C_B v)` is currently
  inexpressible.
- The Diamond–Posen minimum-distance equality for extension codes.
- A module-alphabet MDS Johnson corollary (B2's generalization).
- An algorithm/cost model for ABF26 D6.4/L6.5.
- Rewriting `ArkLib/ProofSystem/Stir` to *discharge* its assumed `listDecodable` hypothesis. The
  bridges now exist and the crossing compiles, but this changes another development's theorem
  statements.
- The pre-existing `GRS25` citation key (four files) and the `~730`-entry style-lint backlog —
  the owner wants cleanups systematic and separate.

---

## 4. Ground rules

1. **Never weaken a statement.** Dropping an unnecessary hypothesis is a strengthening and is
   wanted; adding one is not. If a fix would weaken a theorem, stop and report.
2. Verify per-file with `lake env lean <file>` using the project's real options, or the linters
   stay silent and you will miss warnings:
   `-DautoImplicit=false -Dlinter.mathlibStandardSet=true -Dlinter.style.longFile=1500 -Dlinter.style.header=false`.
   A fix agent previously reported suppressions as "unnecessary" having checked without these; a
   full build then surfaced 10 real warnings.
3. `#print axioms` is only meaningful for a declaration that elaborated. Build first.
4. Re-run the full build at any point where files that import each other have both changed;
   `lake env lean` reads existing `.olean`s and will happily check against a stale dependency.
5. Keep the immutable 2026-08-07 snapshot unedited.

---

## 5. Settled — do not reopen

These were raised and resolved; re-litigating them wastes the session.

- **The mathematics is sound.** Across three passes: no false theorem, no vacuous headline
  theorem, no proof cheat, no new `sorryAx`, no non-standard axiom. Both crown jewels
  (ABF26 L2.17, the folded half of T2.18) are genuine proofs; T2.18 faithfully renders
  [GK16] Theorem 14 and additionally *proves* the irreducibility of `X^{q−1} − ω` that GK16 only
  asserts.
- **`Jqℓ`'s `(ℓ−1)/ℓ` factor is correct.** The `~/abf26-refs` PDF's `ℓ/(ℓ−1)` is a source typo,
  fixed upstream 2026-06-13. Do not "restore" the PDF's form.
- **The strengthened `Admissible` is correct and load-bearing.** It rules out `ω = 1` and
  `0 ∈ L`, both admitted by literal ABF26 D2.14, and both of which falsify downstream results.
- **`Fin.induction_three`/`'` stay.** They have concrete `simp only` consumers in the later
  toy-problem split. An earlier pass deleted them as dead; that was wrong.
- **Zero importers is not a deletion criterion.** Several modules are foundations for named later
  splits. What *is* a defect is a public abstraction whose theorem is true for every input for
  purely logical reasons — which is why the erasure API was removed.
- **Schwartz–Zippel has zero statement drift.** The three ABF-shaped declarations are
  byte-identical to `origin/main`, and the derivation from `prob_eval_zero_le_div` is real.
- **`Lambda`'s `encard` definition is a strict improvement** over `ncard` (infinite lists give
  `⊤`, not `0`). Only the four binders in A1 are wrong, not the redefinition.
