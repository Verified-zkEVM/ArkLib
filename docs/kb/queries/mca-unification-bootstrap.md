# MCA unification — reviewed execution plan (new PR on top of `main`)

**Status: S0–S6 EXECUTED + ADVERSARIALLY REVIEWED 2026-08-05, 7 commits on
`feat/mca-unification` (`5334b21c..5a51c7f0`), unpushed.** Full `lake build ArkLib` green;
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on `tensor_isMCAGenerator`,
`projectedCodeSubmod_moduleInterleavedCode_iff`, Lemmas 4.1/4.2/7.1, `mcaError`,
`isMCAGenerator_iff_mcaError_le`; regression probe (`scratchpad/regression_probe.lean`) shows
`IsMCA` at `A := F` is **`Iff.rfl`** vs the pre-PR definition, plus an x'-independence
mechanism probe. δᵣ(MC^⋈κ) = δᵣ(MC) **deferred** (real proof over
`possibleRelHammingDists`, needs `Nonempty κ`; consumer is S8/#610 only).

**Four-reviewer adversarial review (2026-08-05), all verdicts in:**
* **(i) Soundness: HOLDS, no refutations.** Def 3.14 faithfulness verified clause-by-clause
  against the PDF; probability skeleton has no hidden independence assumptions; reviewer
  *compiled* interleaved-MCA ⇒ plain-MCA at the same error, confirming the interleaved
  hypothesis is a strictly stronger **disclosed** repair of printed Lemma 4.4 (whose printed
  proof does not establish its printed statement — Eq (5) is verbatim the interleaved MCA
  event). Consumers citing "Lemma 4.4" must supply MCA-for-`C^⋈ℓ`. Pre-existing infelicities
  (ε ∈ ℝ≥0 vs [0,1]; `T = ∅` allowed but provably harmless) unchanged.
* **(ii) #610 fit: foundation right, "resolves #610" overstated.** The branch removes the
  obstruction that made #610's tight sorry *unprovable as stated*, but closes none of its
  sorries. Post-rebase #610 must: hand-port `vecMul`-unfolding proofs (statement-safe ≠
  proof-safe); restate `tensorGeneratorPi_isMCAGenerator` with per-factor **nested**
  interleaving hypotheses (+ a nested-vs-flat bridge); restate Thm 6.1 + `ε_MCA_MDS` at
  `ModuleCode`; prove the deferred δᵣ transfer (+ iterated form); Lemma 9.3 at interleaved RS
  stays a genuine paper gap. Merge traps: rename+content conflict on `ProximityGenerators`,
  modify/delete on `MCAGenerator`, and #610's stale `AffineGenerator` copy shares namespace +
  decl names with main's → silent duplicate-decl build failure. **#611: close as "subsumed
  and stale", NOT "superseded"** — its same-code weak lemma has strictly weaker hypotheses
  and remains the only fully paper-backed tensor route for the §9/RS chain.
* **(iii) abf26/prize: COMPATIBLE — bridge equation provable, no mathematical obstruction**
  (all six seams checked; `constrainedCode` is `LinearMap.range` of a linear map, so even the
  hardest Set-typed call site packages as a `ModuleCode`; size clauses are the same step
  function at ALL δ incl. truncation regime; `WordStack` vs `Fin 2 → ι → A` is rfl-level).
  **But the "delete epsMCA/mcaEvent" endgame is under-specified**: (1) δ-domain decision —
  RECOMMENDED: keep `epsMCA : ℝ≥0 → _` as a thin wrapper over `mcaError` + clamping lemma
  (abf26 genuinely evaluates at δ>1: `paper_criterion`, `MCAUpperWitness` has no `le_one`);
  (2) package Set-typed sites as ModuleCode + rewrite `Errors.lean:77-91` design note;
  (3) restate WHIR's two predicate bridges against `IsMCA (AffineLineGenerator F)`;
  (4) sequence after #505 absorbs main's drift + the `Probability`-namespace merge;
  (5) **do not delete/rename epsMCA before the prize repin** — `MCASafeClaim`/
  `MCAUnsafeClaim`/`winningSetSoundness_le_epsMCA_add` name it in statements (leaderboard
  extraction itself survives: keys only on `Security*Bound`).
* **(iv) Integration: fixed in `5a51c7f0`** — Lemmas 4.1/4.2 + `matrixMulCodewords`/
  `zeroExtend` transported to module alphabets (plan's S3 said so; had been left F-pinned);
  module docstring + stale MCA TODO cleaned. Remaining recorded debt: consumer files still
  name the distance arg `γ` (cosmetic), Stir sibling added to S7 list below.
  **KB `_generated` correction: `docs/wiki/generated-files.md` forbids committing
  `docs/kb/_generated/**` from feature PRs (workflow `kb-generated.yml` owns them) — both KB
  commits were DROPPED from the branch; the "stale on main" observation is explained by
  workflow-context generation, not neglect.**

Remaining: S7 (abf26 bridge, on #505) + S8 (#610/#611 coordination), refined per above.

Branch `feat/mca-unification`, worktree `/home/alh/ArkLib-mca-unify`, based on `origin/main`
@ `b12ea046` (Lean 4.31.0).

Supersedes the *decision* half of
[`mca-epsMCA-vs-isMCA-dedup-bootstrap.md`](mca-epsMCA-vs-isMCA-dedup-bootstrap.md) — that doc's
2-axis analysis stays the reference.

**Sequencing (owner decision, 2026-08-05):** this lands as its own PR on top of `main`. #610 /
#611 / #505 integrate onto it as they each become merge-ready. Consequently this PR stays on
`main`'s current `ProximityGap/` layout and does **not** adopt #610's `ProximityGenerator/`
directory rename.

---

## 1. Goal

One general-alphabet MCA notion on `main` such that:

1. **(unblocks BCGM25 Lemma 4.4 at the paper's tight error)** MCA becomes applicable to
   *interleaved* codes `C^κ ⊆ (Σ^κ)^n`, which is what the paper's own proof of Lemma 4.4 consumes.
   Today `IsMCA` is pinned to `LinearCode ι F` (`Σ = F`) and cannot state it, so the tight lemma is
   unreachable and #610/#611 pay a spurious `ℓ` factor.
2. **(retires the ABF26 duplicate)** `epsMCA`/`mcaEvent` on `feat/abf26-plan` becomes the
   `(A`-module alphabet, affine-line generator`)` instance of the unified notion, bridged by a
   theorem rather than by convention.

## 2. Verified this session (first-hand; supersedes earlier assertions)

Checked against the tree and `~/abf26-refs/BCGM25.pdf`, not inherited:

* **Paper is alphabet-general where it matters.** Def 3.2 makes `Σ` an `F`-vector space; Def 3.14
  (MCA) quantifies over `u₁…u_ℓ ∈ Σⁿ` for `C ⊆ Σⁿ`; Def 3.3 defines the `k`-interleaving `C^k` over
  `Σ = F^k`; Remark 3.4 warns against flattening `(F^k)ⁿ → F^{kn}`; Theorem 6.1 is stated for
  `C ⊆ Σⁿ` and its `ε_MCA` depends only on `n, |S|, ℓ, δ_C, η` — **not** on `Σ`. So the
  alphabet restriction is an ArkLib limitation, not a paper defect.
* **ArkLib state on `main`:** `IsMCA` / `IsMCAGenerator` at `ProximityGenerators.lean:88/98`
  (`ε_mca : I → ℝ≥0`, `Matrix.vecMul`, `LinearCode ι F`, distance argument named `γ : I`);
  Lemmas 4.1/4.2 in `MCAGenerator.lean`; Lemma 7.1 in `AffineGenerator.lean`.
  **All five target files are `sorry`-free on `main`** — any `sorry` we add is visible.
* **BCGM25 Lemma 4.4 exists on `main` in no form.** (`grep` hits for "Lemma 4.4" are AHIV22/STIR.)
  Neither #611's weak `ε + ℓ·ε′` nor #610's sorried tight version is on `main`.
* **Blast radius (`projectedWord`/`projectedCode`/`projectedCodeSubmod`)**: four files —
  `Basic/LinearCode.lean`, `ProximityGenerators.lean`, `MCAGenerator.lean`, `AffineGenerator.lean`.
  `projectedCode_linearCombination` has exactly two call sites (`MCAGenerator.lean:74`,
  `AffineGenerator.lean:58`), both needing `*` → `•`.
* `projectedCodeSubmod` over-demands `[Field F]`; `[Semiring F] [AddCommMonoid A] [Module F A]`
  suffices. `projectedWord`/`projectedCode` need no algebraic structure at all (their `F` is
  already a bare `Type*`), so give them their own `{A : Type*}` binder.
* `LinearCode_is_ModuleCode` (`LinearCode.lean:177`) is `rfl`, so `A := F` call sites survive.

### 2a. Corrections to the previous draft of this plan

1. **`ModuleCode.moduleInterleavedCode` already exists on `main`** —
   `ArkLib/Data/CodingTheory/InterleavedCode.lean:149`, i.e. BCGM25 Def 3.3 already generalised to
   module alphabets, with `mem_moduleInterleavedCode_iff` (row-wise membership). Do **not** build a
   new interleaving. This also sharpens the diagnosis: `main` already has the module-general
   interleaving and a module-general `ModuleCode`; it is only `IsMCA` that cannot be *applied* to
   them. (`InterleavedCode.lean` does not import `ProximityGenerators.lean`, so the new import
   direction is acyclic.)
2. **The tight Lemma 4.4 is not provable with the signature the previous draft implied.** See §3 —
   the `G′` hypothesis must be MCA **for the interleaving**, not for `MC`. This is the single most
   important correction; getting it wrong reproduces #610's unprovable `sorry`.
3. **Lemma 7.1's generalisation costs a fifth file.** `affineComb`/`linComb` live in
   `ArkLib/Data/CodingTheory/Prelims.lean:304` and are `Matrix.vecMul`-based over `ι → F`.
   Deliberately **deferred**: keep Lemma 7.1 at `A = F` in this PR (it survives with a
   `smul_eq_mul`-level fix), and generalise it in a follow-up. It is not on the Lemma 4.4 path.
4. **Sorry accounting.** The previous draft claimed "net −1 `sorry`". `tensor_of_MCA_is_MCA_tight`
   is not on `main`, so on `main` this PR is **net 0 `sorry`** and adds a proved lemma; the −1 is
   realised later when #610 rebases and deletes its `sorry`.
5. **The coincidence probe was not in the worktree.** It survives at
   `/tmp/claude-1000/-home-alh-ArkLib/1624fe08-…/scratchpad/unify.lean`. What it actually proves is
   three *clause* lemmas over a module alphabet (`pairJointAgreesOn_iff_forall_projected`,
   `not_pairJointAgreesOn_iff`, `close_clause_iff`) against `projectedCode` (the `Set` form).
   It does **not** assemble the event `iff`, does not touch the size clause, and does not reach the
   `iSup`. So S7 is real work, not glue. Copy it into the worktree before relying on it.

## 3. The crux: what BCGM25 Lemma 4.4 actually needs

Lemma 4.4's proof splits the tensor event by the law of total probability into Eq (4) and Eq (5).

* **Eq (4)** → MCA of `G` applied to the `x′`-dependent family `vᵢ := ∑_j G′(x′)_j u_(i,j) ∈ Σⁿ`.
  Sound as an ordinary MCA use, because MCA is worst-case over families and `x′` is fixed inside
  the expectation. Ordinary alphabet `Σ`.
* **Eq (5)** → the paper bounds
  `Pr_{x′}[∃T large ∧ ∃k∈[ℓ]×[ℓ′], u_k|T ∉ C|T ∧ ∀i∈[ℓ], (∑_j G′(x′)_j u_(i,j))|T ∈ C|T]`
  by `ε′_MCA(γ)`. Matching clause by clause, this is **exactly** MCA of `G′` for the
  **`ℓ`-interleaving `C^ℓ ⊆ (Σ^ℓ)ⁿ`** at the family `w_j := (u_(1,j),…,u_(ℓ,j))`:
  - combination clause: `(∑_j G′(x′)_j w_j)|T ∈ (C^ℓ)|T ⟺ ∀i, (∑_j G′(x′)_j u_(i,j))|T ∈ C|T`;
  - non-agreement clause: `∃j, w_j|T ∉ (C^ℓ)|T ⟺ ∃(i,j), u_(i,j)|T ∉ C|T`.

**Therefore:** Lemma 4.4's printed hypothesis ("`G` and `G′` have MCA for `C`") is weaker than its
proof uses. The faithful Lean statement must hypothesise `G′`'s MCA at the interleaving:

```lean
theorem tensor_isMCAGenerator
    (hG  : IsMCAGenerator G  ε  MC)
    (hG' : IsMCAGenerator G' ε' (ModuleCode.moduleInterleavedCode (κ := ℓ) MC)) :
    IsMCAGenerator (TensorGenerator_Explicit G G') (ε + ε') MC
```

Why this is the *right* reading rather than a weakening of the result: Theorem 6.1's `ε_MCA`
depends only on `δ_C`, and `δ_{C^κ} = δ_C` (Def 3.3's interleaved distance is the column-wise
Hamming distance), so for MDS generators the interleaved hypothesis is discharged by the *same*
Theorem 6.1 instance. The strengthening is invisible in the paper's applications and real in a
formalisation.

**Why the same-code version costs `ℓ`.** Without the interleaving you must pick, per `x′`, some row
`i₀` witnessing non-membership, and `i₀` depends on `x′` — so the family fed to `G′`'s MCA is not
fixed and you union-bound over `i ∈ [ℓ]`. That is precisely #611's / #610's proved weak lemma
`ε + ℓ·ε′`. With the interleaving, the family `w` depends only on `U`, so the `ℓ` disappears. This
is the whole reason unification is the only faithful route.

**Proof recipe for S5** (derived and checked on paper this session):
set `W x' i k := ∑_j G' x' j • U (i,j) k`; use `∑_{(i,j)} (G x i * G' x' j) • U (i,j) = ∑_i G x i • W x' i`;
case-split on `∃ i, projectedWord (W x' i) T ∉ projectedCodeSubmod MC T`:
* yes → `IsMCA G MC x (W x') δ` with the same `T`; bound by `hG` per fixed `x'`
  (`prob_split_uniform_sampling_of_equiv_prod` + `Pr_seq_le_of_forall_le`, as in #610's weak proof);
* no → `IsMCA G' (moduleInterleavedCode MC) x' w δ` with the same `T`, where `w j k i := U (i,j) k`
  — **`x'`-independent**; bound by `hG'` directly, no union bound.
Then `Pr_le_Pr_of_implies` + `Pr_or_le` + `add_le_add`.

## 4. Plan

Each step builds green and commits separately. `./scripts/validate.sh` at S3, S5, S6.

| # | step | files | done when |
|---|---|---|---|
| **S0** | Setup: copy this doc + `unify.lean` probe into the worktree; record baseline. | `docs/kb/queries/`, `scratchpad/` | baseline green recorded |
| **S1** | Generalise `projectedWord`/`projectedCode`/`projectedCodeSubmod`/`mem_projectedCodeSubmod_iff`/`projectedCode_linearCombination` to `ModuleCode ι F A`; `*` → `•`; weaken `[Field F]` → `[Semiring F]`. | `Basic/LinearCode.lean` | builds; `A = F` users unchanged |
| **S2** | Generalise `IsMCA`/`IsMCAGenerator` to `ModuleCode ι F A`; `Matrix.vecMul (G x) U` → `fun k => ∑ j, G x j • U j k`; add compat `vecMul_eq_smul_sum`; rename the distance argument `γ : I` → `δ : I` (collides with `mcaEvent`'s random scalar `γ : F`). | `ProximityGenerators.lean` | builds |
| **S3** | Repair fallout. Generalise Lemmas 4.1/4.2 (pure transport, should follow the alphabet). Keep Lemma 7.1 at `A = F`. | `MCAGenerator.lean`, `AffineGenerator.lean` | `lake build ArkLib` green, **0 new `sorry`** |
| **S4** | Interleaving bridge on the **existing** `ModuleCode.moduleInterleavedCode`: `projectedCodeSubmod_moduleInterleavedCode_iff` (`w|T ∈ (MC^⋈κ)|T ↔ ∀ k, (row k of w)|T ∈ MC|T`) — forward = row extraction, backward = assemble chosen rows. Plus `δᵣ(MC^⋈κ) = δᵣ(MC)` if cheap (downstream Thm 6.1 needs it). | `InterleavedCode.lean` or new | both directions proved, axiom-clean |
| **S5** | **BCGM25 Lemma 4.4 (tight)** with the interleaved `G′` hypothesis (§3). New file to minimise rebase conflict with #610/#611, which both touch `MCAGenerator.lean`. Docstring records the paper's implicit strengthening and why the same-code version costs `ℓ`. | new `ProximityGap/TensorGenerator.lean` | proved, axiom-clean, no `sorry` |
| **S6** | Value form the generator framework lacks: `mcaError G MC : I → ENNReal := fun δ => ⨆ U, Pr_{x ←$ᵖ S}[IsMCA G MC x U δ]` + `isMCAGenerator_iff_mcaError_le`. | `ProximityGenerators.lean` | builds; axiom-clean |
| **S7** | *(follow-up, on `feat/abf26-plan`)* Bridge `epsMCA C δ = mcaError (AffineLineGenerator F) C δ`: assemble the three clause lemmas, reconcile the size clause (`(S.card : ℝ≥0) ≥ (1-δ)*n` vs `(T.card : ℝ) ≥ n*(1-δ)`) and `iSup` over `WordStack A (Fin 2) ι` vs `Fin 2 → (ι → A)`; then delete `mcaEvent`/`epsMCA`. **Scope note (owner, 2026-08-05): the projected-code duplication itself is in scope too.** abf26 never defines a projection object — it restates `w\|T ∈ C\|T` structurally, as inline agreement clauses: `pairJointAgreesOn C S u₀ u₁` ⟺ `∀ j, (U j)\|S ∈ C\|S` (the probe's first lemma) and `mcaEvent`'s closeness clause ⟺ projected membership. S7 should re-express these through `projectedCode`/`projectedCodeSubmod`, retiring the representational duplicate, not only the `epsMCA` value. Measured blast radius on `feat/abf26-plan`: **9 files** consume `pairJointAgreesOn`/`mcaEvent` (`ProximityGap/{Errors,Basic,LineDecoding,InformationSetLowerBound,GrandChallenges}.lean`, `ToyProblem/{SoundnessBounds,Spec/ErasureDecoder,ConstrainedCode}.lean`, `Whir/MutualCorrAgreement.lean`) — a real refactor, plan it as its own pass. `InterleavedCode.jointAgreement` is a third structural sibling, already pinned by `exists_pairJointAgreesOn_iff_jointAgreement`; fold it into the same reconciliation. **Fourth sibling (adversarial review 2026-08-05): STIR's `combine_theorem` conclusion (`ArkLib/ProofSystem/Stir/Combine.lean:561-564`) inlines the same `jointAgreement` clause shape with per-index codes — add it to this reconciliation list.** | `ProximityGap/Errors.lean` + 8 consumers (#505 only) | bridge proved; value + representational duplicates retired |
| **S8** | *(follow-up, coordination)* #610 rebases: drop both tensor lemmas + the `sorry`, restate Theorem 6.1 at `ModuleCode ι F A`, discharge `hG'` at the interleaving via S4's `δᵣ` lemma. #611 closes as superseded. | — | #610 tight chain closed |

Wiki: no command/structure/blueprint change ⇒ no `docs/wiki/` update owed. Regenerate
`docs/kb/_generated/` (`scripts/kb/regenerate.py`) if any module is added or moved (S5 adds one).

## 5. Gotchas

* **`Matrix.vecMul` does not typecheck over a module** (needs a ring on the alphabet). This is the
  one forced behavioural change; do not try to preserve `vecMul`.
* **`InterleavedCode.lean` is `@[simp]`-heavy** on its abbrevs and accessors (`InterleavedSymbol`,
  `InterleavedWord`, `getRowWord`, `interleavedCodeSet`, `moduleInterleavedCode`). Expect `simp` to
  unfold the interleaving eagerly; prefer explicit `mem_moduleInterleavedCode_iff` rewrites.
* **Lemma 7.1 should survive S3 essentially unchanged.** Its counting
  (`proj_lincomb_ker_card_le`, `exists_avg_le`, `exists_dir_line_ge`) happens in the *coefficient*
  space `Fin s → F`, untouched. If it fights you, you generalised the wrong thing.
* At `A = F`, `c • x` and `c * x` are `rfl`-equal via `Mul.toSMul`; `simp [smul_eq_mul]` closes the
  two `projectedCode_linearCombination` call sites.
* **Do not add `[Fintype A]`/`[DecidableEq A]`** to the unified defs — `IsMCA` needs only
  `[AddCommMonoid A] [Module F A]`. (`δᵣ` lemmas in S4 will want `[DecidableEq A]`; keep it local.)
* **Do not adopt #610's `ProximityGap/` → `ProximityGenerator/` rename** (owner decision §0). #610
  will rebase; `git` rename detection carries most of it, conflicts land in the edited regions.
* `git stash` is unreliable in these nested worktrees — commit instead.

## 6. Acceptance criteria

1. `lake build ArkLib` green; **zero new `sorry`** (all five touched files are `sorry`-free on
   `main` — keep them that way).
2. `#print axioms` = `[propext, Classical.choice, Quot.sound]` on `tensor_isMCAGenerator`,
   `projectedCodeSubmod_moduleInterleavedCode_iff`, `mcaError`,
   `isMCAGenerator_iff_mcaError_le`, and Lemma 7.1.
3. A regression probe: `IsMCA` at `A := F` is propositionally the pre-PR definition (so #610/#611
   rebase against a semantics-preserving change on their axis).
4. A probe exhibiting the tight bound's mechanism: the case-(b) family `w` is `x'`-independent.
5. `lint-style.sh` no worse than `main` kind-by-kind; `check-imports`, `check-docs-integrity`,
   `kb/check_generated`, `lintWhitespace` pass.

## 7. Paper findings to raise with the BCGM25 authors

1. **Lemma 4.4's hypothesis is understated.** As printed it assumes `G, G′` have MCA for `C`, but
   the Eq (5) step applies `G′`'s MCA to the `ℓ`-interleaving `C^ℓ` (§3). Harmless for MDS
   generators via Theorem 6.1's `Σ`-independence + `δ_{C^ℓ} = δ_C`, but it should be stated.
2. **Theorem 9.2 has a genuine gap.** Its proof asserts "By Lemma 9.3, `G_d` has mutual correlated
   agreement for **any linear code** `C`", but Lemma 9.3 is stated only for `C := RS[F, D, k] ⊆ F^{|D|}`
   and §9 never mentions `Σ` or interleaving. The Lemma 4.4 application therefore needs MCA of
   `G_d` for *interleaved* RS, which the paper does not establish. After unification this becomes a
   **statable open hypothesis** instead of a hidden defect. Theorem 8.2 *is* fully unblocked, since
   Theorem 6.1 is alphabet-general.
3. Also note Def 3.3 defines interleaving only for `C ⊆ Fⁿ`, so iterated interleaving is not
   literally covered by the paper's definitions (immaterial here; ArkLib's
   `moduleInterleavedCode` is already general).

## 8. Cross-refs

* 2-axis analysis: [`mca-epsMCA-vs-isMCA-dedup-bootstrap.md`](mca-epsMCA-vs-isMCA-dedup-bootstrap.md)
* Review that surfaced the driver: `katy_mca_reviews/2026-08-01/README.md` §4.8–§4.9
* Paper: `~/abf26-refs/BCGM25.pdf` — Def 3.2/3.3, Remark 3.4, Def 3.14, Lemma 4.4, Thm 6.1,
  Lemma 9.3, Thm 9.2
* PRs: #596 MERGED (2026-08-04), #610 OPEN (`Katy/RScodeMCA`, renames the directory), #611 OPEN
  (`Katy/TensorLemma`, weak bound), #618 CLOSED
* Memory: `mca-formalization-dedup`, `katy-mca-prs-596-610-611`
