# PR 701 — integration review verdict (2026-08-12)

Head reviewed: `b425ef51b`. Merge base with `origin/main`: `a4ac38e0e`; `origin/main` at
`015520d30`. Ground truth: the pinned ABF26 tex (`~/ef-millenium` @ `53a5055`),
`~/abf26-refs/ABF26.pdf`, and the cited source PDFs read first-hand.

## Headline

**GO on the mathematics.** No false statement, no vacuity, no new admit, no new axiom, every
headline declaration axiom-clean, every gate green. Faithfulness to the sources holds, including
at three points where the Lean is deliberately *sharper* than the printed paper.

**One HIGH finding, and it is a repo-integration one, not a mathematical one:** the
`namespace Probability` consolidation in `5037db407` breaks **seven open PRs**. This is
demonstrated, not conjectured — see F1.

Five MEDIUM findings are documentation drift created by the 2026-08-11 remediation itself: it
renamed two declarations and relocated a third, and the knowledge-base pages still name them at
their old names and locations. One further MEDIUM is a docstring over-claim in the new
interleaved material. F7–F12 are polish.

## Gates (all re-run fresh at `b425ef51b`)

| Gate | Result |
|---|---|
| `lake build ArkLib` | green |
| `./scripts/validate.sh` | green — 4220 jobs; no `ArkLib/Data` non-sorry warnings; 347 umbrella imports; docs integrity and KB lint green |
| `./scripts/validate.sh --lint` | exit 0; **no lint hit lands in any file this PR touches** (all remaining hits are in untouched `ToMathlib/Polynomial/*`, `ToVCVio/*`) |
| `#print axioms`, 32 declarations | every one exactly `[propext, Classical.choice, Quot.sound]` |
| New `sorry` / `axiom` | none. The only `sorry` in a touched file is the pre-existing zero-consumer `Fin.sumCases`; all other matches are prose or commented-out |
| Merge with `origin/main` @ `015520d30` | clean (`git merge-tree` exit 0) |
| Merge with #692 | see F1 / FW5 |
| Merge with #717 | clean apart from generated `ArkLib.lean` |

Declarations checked axiom-clean: `minDist_irsCode`, `minDist_irsCode_eq_minDist_rsCode`,
`irs_rate_distance`, `alphabetRate_irsCode_eq_min`, `alphabetRate_irsCode`,
`interleavedCodeSet_rsCode_eq_irsCode`, `dim_irsCode_eq_min`, `alphabetRate_frsCode`,
`frs_rate_distance_of_dvd`, `minDist_frsCode`, `dim_frsCode_eq_min`,
`irs_lambda_le_johnson_mds`, `frs_lambda_le_johnson_mds`, `rs_lambda_le_johnson_mds`,
`mds_johnson_lambda_le_of_rate_distance`, `mds_johnson_lambda_le`,
`johnson_bound_lambda_le_ell`, `frs_is_subspaceDesign_gk16`, `um_is_subspaceDesign_gk16`,
`subspaceDesign_tau_lower`, `subspaceDesign_tau_lower_of_ne_bot`,
`IsSubspaceDesign.mono_tau`, `lambda_extensionCode_eq_lambda_interleaved`,
`minDist_extensionCode`, `extensionEncode_comp_algebraMap`,
`mem_extensionCode_comp_algebraMap_iff`, `Code.minDist_interleavedCodeSet`,
`Code.finrank_moduleInterleavedCode`, `LinearCode.singleton_bound_module`,
`LinearCode.IsMDS_iff_rate_distance`, `Multiplicity.dim_umCode_eq_min`,
`mem_map_degreeLT_one_iff_mem_code`.

## Faithfulness, re-derived from the sources

**Which artefact is ground truth.** `~/ef-millenium/ef-millenium.pdf` is a **stale build** and
disagrees with the tex beside it on definition numbering (its `Definition 2.1` is a smooth
evaluation domain; its `.aux` is staler still). `~/abf26-refs/ABF26.pdf` carries the numbering the
Lean docstrings use, and it agrees item-for-item with the pinned tex. All numbering below is
that one.

| Item | Source reading | Lean | Verdict |
|---|---|---|---|
| D2.5 rate | `ρ(C) = log_{\|Σ\|}\|C\| / n` | `alphabetRate = dim/(s·n)` | faithful; `rate = dim/n` correctly kept distinct |
| L2.6 | MDS ⟺ `ρ = 1 − δ_min + 1/n` | `IsMDS_iff_rate_distance`, and the rate-distance equations | faithful |
| D2.9 | `C^{≡m} ⊆ (Σ^m)^n`, rows are codewords | `interleavedCodeSet` (rows of the transpose) | faithful |
| D2.13 | `IRS = (RS[F,L,k/s])^{≡s}` | `irsCode = (code domain (k/s)) ^⋈ Fin s` | faithful; the paper's tacit `s ∣ k` and the `⌊k/s⌋` truncation are documented and probed (Probe D) |
| D2.14 | inter-orbit clause only, over `\binom{L}{2}` | `Admissible` = inter-orbit **+ intra-orbit** | deliberate strengthening; all three counterexamples re-derived (`ω=1`, `0 ∈ L`, and the T2.18 order failure) and the first machine-checked (Probe A) |
| D2.15 | GR08 Def 2.1 fold | `frsCode`, plus `frsCode_eq_map_rsCode` | faithful, and the GR08 "bundling" framing is proved rather than asserted |
| D2.16 / L2.17 | GX13 / GG25 | `IsSubspaceDesign`, `subspaceDesign_tau_lower{,_of_ne_bot}` | faithful; the `r = 0` exclusion is genuinely forced |
| T2.18 profile | `τ(r) = s·ρ/(s−r+1)` on `[s]`, else `1` | both halves, at `alphabetRate` | faithful; `s − r + 1` is **real** subtraction in Lean (no `ℕ` truncation bug) |
| GK16 Def 9 / Def 11 | rows = iterated derivatives / `ω^i`-twists | `classicalWronskian` / `foldedWronskian` | exact |
| GK16 Lemma 12 | `γ ∈ F*` a generator, `m < \|F\|` | `orderOf ω = card F − 1`, `k ≤ card F − 1` | exact |
| GK16 Claim 19 | `mult(L,α) ≥ (t−s+1)·dim(W∩H_α)` | `(s − σ + 1) * finrank N`, Lean `s` = paper `t`, Lean `σ` = paper `s` | exact |
| GK16 Lemma 10 | `m < char F` | `ringChar F = 0 ∨ k ≤ ringChar F` | **sharper, and sharp**: `d!` must be a unit for `d < k`, i.e. `k ≤ char F`. Also matches ABF26 A.7's `char ≥ k`; the paper's own T2.18 `char > k` is the inconsistent one, already recorded |
| D2.19 / D2.20 / L2.21 | presentation, extension code, list-size equality | `ExtensionFieldPresentation`, `extensionCode`, `lambda_extensionCode_eq_lambda_interleaved` | faithful; the dropped `IsSystematic` is provably surplus (`φ_j(ψ x) = x·φ_j(1)`) and L2.21 is unconditional in `δ` |
| D3.1 `J_{q,ℓ}` | tex: `(ℓ−1)/ℓ`; **PDF prints the inverted `ℓ/(ℓ−1)`** | `Jqℓ q ℓ δ = J q (((ℓ−1)/ℓ)·δ)` | follows the tex. Independently confirmed: `ℓ/(ℓ−1)` would make `J_{q,ℓ} > J_q`, contradicting the paper's own "successively rougher bounds" |
| T3.2 / C3.3 | `\|Λ(C, J_{q,ℓ}(δ_min))\| ≤ ℓ`; `\|Λ(C, 1−√ρ−η)\| ≤ 1/(2ηρ)` | `johnson_bound_lambda_le_ell`, `mds_johnson_lambda_le_of_rate_distance` | faithful, and **proved in-tree**; the paper's constant is used, not the sharper classical `1/(2η√ρ)`, so numeric anchors are not poisoned |

Three deliberate sharpenings, all sound: the characteristic guard (`k ≤ char F` for
`m < char F`), the unconditional-in-`δ` L2.21, and the dropped `IsSystematic`. Two silent ones:
the univariate-multiplicity half drops both ABF26's `\|F\| > n` (documented) and GK16 §5.1's
`t ≤ m` (**not** documented — F11).

## Compiled probes

Eleven probes, all green. Full sources in the session scratchpad; each is a few lines and is
reproducible from the description.

| Probe | What it establishes |
|---|---|
| A | The `frs_rate_distance_of_dvd` docstring's counterexample is machine-**derived**, not asserted: at `ZMod 11`, `L = {1..5}`, `ω = −1`, `s = 2`, `k = 3`, instantiating `minDist_frsCode` gives `δ_min = 4` and `alphabetRate = 3/10`, so `4/5 ≠ 9/10`. `s ∣ k` is load-bearing |
| B | The divisible case is inhabited: the rate-distance equation instantiates at `k = s = 2` |
| C, G | Both Johnson consumers instantiate at concrete parameters — hypotheses jointly satisfiable, so neither is vacuous |
| D | The `⌊k/s⌋` truncation is real: at `k = 5`, `s = 2`, `dim = 4` (not 5) and `minDist = 4` |
| E | The saturated regime works: at `k = 20`, `s = 2`, `n = 5`, `alphabetRate = 1` and `minDist = 1` — this is what "no non-saturation hypothesis" buys |
| F | At `k/s = 0` the code is `⊥` and `minDist = 0`, while the closed form would predict `n + 1 = 6`. So `[NeZero (k/s)]` is load-bearing — see F2 |
| H | The advertised end-to-end chain works **generically**: `lambda_extensionCode_eq_lambda_interleaved` → `interleavedCodeSet_rsCode_eq_irsCode` → `irs_lambda_le_johnson_mds` gives an extension code over an RS base a Johnson list-size bound, at an arbitrary presentation and base field |
| I | The MEDIUM-1 remediation is contentful in characteristic zero, re-verified independently: `finrank ℚ (umCode domQ 3 2) = 3` and `um_is_subspaceDesign_gk16` instantiates over ℚ |
| J | `IsSubspaceDesign.mono_tau` does what a later split needs: coarsens the T2.18 profile to a constant-in-`r` bound without reopening `SubspaceDesign.lean` |
| K | `frs_is_subspaceDesign_gk16`'s extra `(L, hL_dom)` arguments are recoverable by instantiating `L := Finset.univ.map domain`, so they cost no strength — pure friction (F7) |

## Findings

### F1 — HIGH: the `namespace Probability` consolidation breaks seven open PRs

`5037db407` moved **19 pre-existing root-level** `prob_*`/`Pr_*` helpers in
`Data/Probability/Instances.lean` into `namespace Probability`. The six in-tree consumers were
fixed with a one-line `open Probability` each. No compatibility export and no deprecated alias
was added.

Demonstrated, not conjectured:

- `git merge-tree` reports #692 × #701 as **conflict-free**.
- The merged tree then **fails to build**: 10 × `Unknown identifier` in #692's new
  `ProximityGap/TensorGenerator.lean` (`prob_split_uniform_sampling_of_prod`,
  `prob_split_uniform_sampling_of_equiv_prod`, `Pr_le_Pr_of_implies`, `Pr_or_le`).
- Adding a single `open Probability` line to that file makes the merged tree build green
  (4221 jobs). So the two PRs are otherwise **fully compatible** — this is the only interaction.

Blast radius, measured against each PR head: **#692, #610, #611, #615, #634, #637, #383** all
use the moved helpers, across roughly thirty files, and **none** of them carries an
`open Probability`. Files that only exist on those branches cannot be pre-fixed by this PR:
`ProximityGap/TensorGenerator.lean`, `ProximityGenerator/{AffineGenerator,MCAGenerator,PolynomialGenerator}.lean`,
`ProofSystem/RingSwitching/Generic/{Batching,Reduction}.lean`,
`ProofSystem/Stir/OutOfDomSmpl.lean`, `ProofSystem/Binius/BinaryBasefold/**`,
`OracleReduction/Completeness.lean`.

`docs/wiki/probability-conventions.md`, added by this same PR, already prescribes the remedy —
*"If a downstream project has a concrete compatibility break on an older root-level helper name,
add an explicit, temporary compatibility export for that exact declaration and document the
consumer"* — but the escape hatch was never exercised, and the break is in-repo rather than
merely downstream.

This is a sequencing/API decision for the owner, not a defect. Three options:

1. **Compatibility export** for the 19 pre-existing names in `Instances.lean`, exactly as the
   conventions doc prescribes, with the consumers documented. One line, zero risk, no other PR
   breaks, and the namespace benefit is retained for new material. Recommended.
2. **Split the namespace move into its own small PR** that merges first, so the ~30 one-line
   fixes land as a single mechanical tree-wide sweep the other branches rebase onto, and #701
   shrinks by a commit.
3. **Merge as-is and announce**, accepting that seven PRs each need one line per file.

Note that `Probability` does not clash with any Mathlib namespace, so the naming choice itself
is fine; only the migration path is missing.

### F2 — MEDIUM: `minDist_irsCode` and `irs_rate_distance` over-claim in their docstrings

`minDist_irsCode` says "for **every** parameter choice" and `irs_rate_distance` says
"unconditionally in the parameters"; both carry `[NeZero s] [NeZero (k / s)]` and
`[Nonempty ι]`. Probe F shows `[NeZero (k/s)]` is load-bearing: at `k = 1`, `s = 2` the code is
`⊥`, so `minDist = 0` while the closed form predicts `n + 1`.

The claims are correct about what they are actually contrasting — no divisibility and no
non-saturation hypothesis, unlike the folded code — and that contrast is the valuable content.
The fix is to say "for every `k ≥ s`" (or "for every parameter choice in the stated instance
range") instead of "every". `b425ef51b` fixed exactly this class of over-claim for
`frs_rate_distance_of_dvd`'s biconditional; this one was missed.

### F3 — MEDIUM: a renamed declaration is still named at its old name in three documents

The 2026-08-11 remediation renamed `extensionEncode_comp_algebraMap_of_isSystematic` →
`extensionEncode_comp_algebraMap` (and the `mem_…` sibling). Three documents still name the old
one, and — worse — still credit systematicity with doing the work, which the fix disproved:

- `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md:52` ("systematic
  identity …", "systematic membership bridge")
- `docs/kb/papers/ABF26.md:66` ("the systematic encoder identity → …")
- `docs/kb/papers/BCFW25.md:73` ("proves the §D.2 systematic identity")

### F4 — MEDIUM: `J`'s location is stale after the HIGH-1 de-duplication

HIGH-1's fix kept the upstream copy in `JohnsonBound/Lemmas.lean` (renamed `J' → J`) and deleted
the downstream copy in `Basic.lean`. `docs/kb/papers/Joh62.md:95-102` was updated; these were
not:

- `docs/kb/audits/open-problems-…md:60` — locates `J` in `JohnsonBound/Basic.lean`
- `docs/kb/papers/Joh62.md:49-50` — "the pre-existing `JohnsonBound.J`, `sqrt_le_J`, … " under
  the `Basic.lean` heading
- `docs/kb/papers/Joh62.md:76` — "`Jcap` lives beside `J`"; they are now in different files

### F5 — MEDIUM: wrong namespace for the Johnson family

`docs/kb/papers/ABF26.md:70` names `CodingTheory.Jqℓ` and `CodingTheory.Jcap`. Both live in
`namespace JohnsonBound`. (`Joh62.md` was corrected for this in `2280432eb`; `ABF26.md` was
not.) The same line writes the family as "`J`, `Ĵ`, `J_{q,ℓ}`"; the paper's three are
`J_{q,ℓ}`, `J_q`, `J`.

### F6 — MEDIUM: the audit rows were not updated for the new module-alphabet material

`0fed05006` and `b425ef51b` added eleven declarations; CLAUDE.md requires the matching doc page
in the same PR, and `docs/wiki/repo-map.md` **was** updated (correctly, including the #692
deferral). The audit was not:

- **D2.13** advertises only `dim_irsCode`, omits `dim_irsCode_eq_min`,
  `minDist_irsCode_eq_minDist_rsCode`, `minDist_irsCode`, `alphabetRate_irsCode{,_eq_min}`,
  `irs_rate_distance`, `interleavedCodeSet_rsCode_eq_irsCode`; and it describes the dimension
  proof as going "via injective F-linear `(Fin s → ↥RS) → (ι → Fin s → F)` + `finrank_pi_fintype`",
  a mechanism that no longer exists (it is now `Code.moduleInterleavedCodeEquiv` /
  `finrank_moduleInterleavedCode`).
- **D2.15** omits `alphabetRate_frsCode` and `frs_rate_distance_of_dvd`.
- **C3.3** says module and interleaved codes "*can* use the generic metric core"; they now
  **do**, via `irs_lambda_le_johnson_mds` and `frs_lambda_le_johnson_mds`.

### F7 — LOW: `frs_is_subspaceDesign_gk16`'s signature diverges from every sibling

It takes `(L : Finset F) (hL_dom : ∀ i, domain i ∈ L) (hω_adm : Admissible L s ω)`, where
`minDist_frsCode`, `dim_frsCode{,_eq_min}`, `alphabetRate_frsCode`, `frs_rate_distance_of_dvd`
and `frs_lambda_le_johnson_mds` all take `Admissible (Finset.univ.map domain) s ω`. Probe K
shows the extra arguments cost no strength (instantiate `L := Finset.univ.map domain`), so this
is pure friction for any caller combining the two — the same class of signature inconsistency
`b425ef51b` fixed for the two Johnson consumers.

### F8 — LOW: `[NeZero (k / s)]` is awkward as an instance argument

A caller who knows `s ∣ k` cannot discharge it directly: Probe H needed
`rw [Nat.mul_div_cancel_left …]; infer_instance`. An explicit-hypothesis variant (`0 < k / s`)
or `_of_dvd` wrappers alongside `dim_irsCode_of_dvd` would remove it. Same point as F2 from the
API side.

### F9 — LOW: the naming-divergence table was not extended

`docs/wiki/coding-theory-conventions.md`'s "Where current names diverge, and why" table lists
five declarations but not the new `irs_lambda_le_johnson_mds`, `frs_lambda_le_johnson_mds`,
`irs_rate_distance`, `frs_rate_distance_of_dvd`, or `um_is_subspaceDesign_gk16` — all of which
diverge in the same way as entries already listed.

### F10 — LOW: `Admissible`'s docstring omits the ordered-pair reading

It explains that ABF26 D2.14 quantifies over unordered pairs `\binom{L}{2}`, but not that the
Lean form quantifies over **ordered** distinct pairs, i.e. asserts both `α·ω^i ≠ β` and
`β·ω^i ≠ α`. Both orders are used, one in each branch of
`admissible_foldedPoints_injective`'s `rcases le_total`, so the reading is load-bearing.

### F11 — LOW: one silent hypothesis drop is undocumented

`um_is_subspaceDesign_gk16`'s docstring records dropping ABF26's `\|F\| > n` and explains why.
It does not record that GK16 §5.1's `s ≤ t ≤ m < char(F_q)` also loses its `t ≤ m` conjunct
(Lean's `s ≤ k`). The drop is sound — without it the lifted block kernel is `⊥` and the bound is
bookkeeping — but the file's own standard is to say so.

### F12 — LOW: a resolved Mathlib-overlap note reads as unresolved

`docs/kb/papers/BCFW25.md:83-86` says `ExtensionFieldPresentation.coord` "re-derives
`Module.Basis.coord`" and that the module docstring's "no parallel implementation" claim "is
accurate for `ψ` and `φ` but not for `coord`". The Lean now states outright that `coord` **is**
`Basis.coord` and ships `coord_eq_basis_coord` as the `rfl` witness. The same passage names
`coord_add`/`coord_psi_smul`, which do not exist.

## Forward-looking — what the next split needs

### FW1 — #717 will break on the `listDecodable` strengthening, and its proof relies on the hole

PR #717 (*RS-codes are list decodable*, opened 2026-08-12) proves
`listDecodable_reedSolomon` against `main`'s definition. Its proof case-splits on
finite/infinite point list and discharges the **infinite** branch with
`Set.Infinite.ncard = 0` — precisely the unsoundness this PR's `Finite` conjunct closes — and it
assumes only `[Field F] [DecidableEq F]`, with no finiteness on `F`.

The theorem stays **true** under the new definition (a point list at radius `< 1 − ρ` is finite,
since agreement on `≥ m` positions pins the polynomial), but that branch will need a real
argument or a `[Finite F]` hypothesis.

Two actions, both small and both in this PR's interest:

- Ship the recovery lemma the 2026-08-11 review already recommended: `listDecodable` from an
  `ncard` bound under `[Finite F]`. `ListDecodability.lean` currently offers
  `Lambda_le_iff_listDecodable`, `listDecodable_of_Lambda_le_natCast` and
  `listDecodable_of_toENNReal_le_ofReal`, but nothing that takes a bare `ncard` bound — which is
  the shape a consumer arrives with.
- Flag the definition change in the PR body for the #717, STIR and WHIR owners. It is a
  correctness fix, and it is the second time it has been recommended.

### FW2 — #717 also overlaps mathematically, in two places

- `listDecodable_reedSolomon` bounds the RS list at the **sharper classical** `1/(2η√ρ)`; this
  PR's `rs_lambda_le_johnson_mds` bounds it at ABF26's coarser `1/(2ηρ)`. Keeping both is
  defensible — one is paper-faithful and feeds the numeric anchors, the other is sharp — but
  they must cross-reference, or the next contributor re-proves one of them.
- #717 adds `Code.agree` to `Basic/Distance.lean`, where this PR adds `Code.disagreementCols`.
  They are complementary (`agree + hammingDist = n`, which #717 proves). Whoever merges second
  owes the one-line bridge, or the tree acquires two primitives for one notion — exactly the
  situation `disagreementCols` was introduced to end.

### FW3 — the PR-1.5 scope document is stale in two rows

`~/ArkLib/docs/kb/queries/abf26-split-merge-2026-07-24/PR-1.5-SCOPE-2026-08-10.md` (on
`feat/abf26-plan`, not in this tree) records:

- "**C3.3 module-alphabet half** … **PROVE** … remains PR-1.5's first new theorem" — this PR now
  ships it (`irs_lambda_le_johnson_mds`, `frs_lambda_le_johnson_mds`, on top of the already
  alphabet-generic `mds_johnson_lambda_le_of_rate_distance`).
- "**T2.18 UM half** — **NOT in PR-1; separate W-track project**" — this PR ships it
  (`um_is_subspaceDesign_gk16`, via `ClassicalWronskian.lean`).

Update before PR-1.5 construction, or both will be implemented twice.

### FW4 — the one genuine forward gap: no module-alphabet `IsMDS` predicate

The PR-1.5 scope names "the module-alphabet rate-distance bridge (module `IsMDS` + iff)" as the
missing piece. This PR delivers C3.3 at module alphabets **without** such a predicate, by taking
the rate-distance equation as a hypothesis and supplying `irs_rate_distance` /
`frs_rate_distance_of_dvd` as the inputs. Generalising the `IsMDS` *predicate* to
`ModuleCode ι F A` is deliberately deferred to the #692 `IsMCA` line, recorded in
`docs/wiki/repo-map.md`.

Consequence to plan around: if PR-2's interleaved-RS MCA statements want to *say* "IRS is MDS"
as a predicate, that predicate still has to be built, and it belongs with #692's
generalisation of the same file rather than here. Note also the asymmetry inside
`Basic/LinearCode.lean` today: `singleton_bound_module` is generic in the alphabet `A` (using
`finrank F A`), while `alphabetRate` and `IsSubspaceDesign` are fixed to `Fin s → F`. That
matches ABF26's `Σ = F^s` and is the right scope for a faithfulness layer, but it is the seam a
module-`IsMDS` generalisation would have to cross.

### FW5 — #692 and #701 are otherwise fully compatible

Confirmed by building the merged tree, not by inspection: green at 4221 jobs once F1's one line
is supplied. The two PRs' edits to `Basic/LinearCode.lean` (this PR: `alphabetRate`,
`singleton_bound_module`, `IsMDS_iff_rate_distance`; #692: `projectedCodeSubmod` generalised to
`ModuleCode`) and to `InterleavedCode.lean` (this PR: `minDist_interleavedCodeSet`,
`moduleInterleavedCodeEquiv`, `finrank_moduleInterleavedCode`; #692:
`projectedCodeSubmod_moduleInterleavedCode_iff`) are disjoint and additive.

## Remediation applied

Owner decisions of 2026-08-12: **F1 = merge as-is and announce**; **F2–F12 + FW1 = apply now**.
Every change below either removes a hypothesis, replaces an instance argument with an equivalent
explicit one, or corrects prose. No conclusion is weakened and no statement is added beyond two
reusable lemmas.

1. **F1 — announced, not aliased.** `docs/wiki/probability-conventions.md` gains a *Migrating an
   in-flight branch* section: the nineteen moved names listed explicitly, the one-line fix
   (`open Probability` beside the existing `open scoped ProbabilityTheory`), the note that the
   failure mode is `Unknown identifier` and so cannot be missed, and the seven branches measured
   to need it with the specific files that only exist on them. It also records that a merged
   `#692` + consolidation tree was **built** to confirm the one line is the only interaction.
2. **F2 + F8 — the over-claim and the awkward instance argument fixed together.**
   `[NeZero (k / s)]` became an explicit `(hks : 0 < k / s)` on `minDist_irsCode`,
   `irs_rate_distance` and `irs_lambda_le_johnson_mds`, because instance resolution can never
   discharge it for symbolic parameters (unlike `[NeZero s]`, which fires on numerals) and so an
   instance argument only pushes a `rw`-then-`infer_instance` dance onto every caller — Probe H
   is now two clean lines. `minDist_irsCode`'s docstring drops "for **every** parameter choice"
   in favour of naming what is actually unconditional (divisibility, saturation) and records the
   machine-checked `ZMod 11`, `k = 1`, `s = 2` witness for why `0 < ⌊k/s⌋` is load-bearing.
   `irs_rate_distance`'s "unconditionally in the parameters" is likewise qualified, in both the
   docstring and the module header.
3. **F7 — signature unified.** `frs_is_subspaceDesign_gk16` now takes
   `Admissible (Finset.univ.map domain) s ω` like every sibling, dropping the `(L, hL_dom)` pair.
   The transport that used to be inlined in its proof is extracted as the reusable
   `ReedSolomon.Folded.Admissible.subset` (admissibility restricts along `L' ⊆ L`), so the
   superset direction a caller might want is available as a named lemma rather than a re-derivation
   — Probe K' exercises it. Net effect: seven fewer proof lines, one more reusable lemma, and no
   strength change in either direction.
4. **FW1 — migration lemma shipped.** `ListDecodable.listDecodable_of_ncard_le`: over a finite
   alphabet a bare `∀ y, ncard ≤ ℓ` bound gives `listDecodable`. Its docstring states plainly why
   the definition changed (the old shape was satisfied by an infinite point list, since
   `Set.ncard` returns `0` there) and that consumers whose bound comes from `Lambda` need neither
   this lemma nor `[Finite F]`.
5. **F3, F4, F5, F6, F12 — the documentation drift closed.** The renamed
   `extensionEncode_comp_algebraMap` and `mem_extensionCode_comp_algebraMap_iff` are now named
   correctly in the audit's D2.20 row, `papers/ABF26.md` and `papers/BCFW25.md`, and all three
   passages now state that the identity holds for an *arbitrary* presentation with the
   `φ_j(ψ x) = x · φ_j(1)` mechanism spelled out. `J`'s home is corrected to `Lemmas.lean` in the
   audit's D3.1 row and in `papers/Joh62.md` (which gains the missing `Lemmas.lean` bullet and
   loses the "`Jcap` lives beside `J`" claim). `papers/ABF26.md` now names `JohnsonBound.Jqℓ` /
   `JohnsonBound.Jcap` in the right namespace, writes the family as the paper does
   (`J_{q,ℓ}`, `J_q`, `J`), and lists the three code-family C3.3 instantiations. The audit's D2.13
   row is rewritten around the declarations that actually exist and the mechanism actually used
   (`Code.moduleInterleavedCodeEquiv` / `finrank_moduleInterleavedCode`, not the retired ad-hoc
   injection); D2.15 gains the rate and MDS clauses plus `Admissible.subset`; C3.3 records that
   the module-alphabet half is present and why the field wrapper cannot serve it.
   `papers/BCFW25.md`'s Mathlib-overlap bullet is retitled *resolved* and no longer names two
   nonexistent lemmas.
6. **F9, F10, F11 — the three remaining prose gaps.** The naming-divergence table in
   `coding-theory-conventions.md` gains rows for the three `*_lambda_le_johnson_mds`
   instantiations, `um_is_subspaceDesign_gk16`, and the two `*_rate_distance` equations.
   `Admissible`'s docstring records that Lean quantifies over *ordered* distinct pairs — both
   orders being consumed by the two branches of `admissible_foldedPoints_injective`'s
   `rcases le_total`. `um_is_subspaceDesign_gk16`'s docstring is restructured around all **three**
   absent source hypotheses, adding the previously unrecorded drop of GK16 §5.1's `t ≤ m` with the
   reason it is sound.

Re-validated after remediation: `validate.sh` green; `lake build` green; the eleven probes
re-run against the changed API, all green, plus the new Probe K'; and all 34 declarations
confirmed at exactly `[propext, Classical.choice, Quot.sound]` (`Admissible.subset` needs only
`[propext, Quot.sound]`).

## Remaining, deliberately not changed here

| Finding | Why |
|---|---|
| FW2 | The `Code.agree` ↔ `Code.disagreementCols` bridge and the `1/(2η√ρ)` vs `1/(2ηρ)` cross-reference belong to whichever of #701 / #717 merges **second**; writing them now would guess at the other PR's final names |
| FW3, FW4 | Owned by `feat/abf26-plan`: the PR-1.5 scope rows to correct, and the module-`IsMDS` decision, which belongs with #692's `IsMCA` generalisation of the same file |
