# R6 — `SubspaceDesign.lean` + `FoldedWronskian.lean` (ABF26 D2.16 / L2.17 / T2.18, GK16 Def 11 / Lem 12)

Reviewer: R6. Commit `ffa0733a`. All probes under
`(session-local probe) r6-*.lean`, compiled with `lake env lean` (no repo rebuild).

**Verdict: no CRITICAL, no HIGH. The two crown-jewel results are genuinely proven, axiom-clean,
faithful to their sources, and non-vacuous. 2 MEDIUM + 8 LOW.**

---

## Findings

### [MEDIUM] `subspaceDesign_tau_lower` needlessly narrows L2.17 from `∀ r ∈ ℕ` to `r ∈ Icc 1 s`; the identical proof gives `∀ r ≥ 1`

- **Where**: `ArkLib/Data/CodingTheory/SubspaceDesign.lean:139` (`CodingTheory.subspaceDesign_tau_lower`)
- **Source**: ABF26 Lemma 2.17 — *"If `C : F^k → (F^s)^n` is a τ-subspace-design code of rate ρ
  then `min_{r∈N} τ(r) ≥ ρ − 1/n`."* GG25 Lemma 2.16 — *"For any τ-subspace-design F_q-additive
  code of rate R, we must have `τ(r) ≥ R − 1/n` for all `r ∈ N`."*
- **What's wrong**: the Lean restricts the conclusion to `r ∈ Finset.Icc 1 s`. The `r = 0`
  exclusion is legitimate (verified, see clean bill), but the `r ≤ s` half is a pure
  weakening. The docstring itself concedes this ("`r > s` is dropped only because no in-tree
  consumer needs it … the proof below works verbatim for any `r ≥ 1` once `s ≥ 1` is known")
  — and there are **zero** in-tree consumers of `subspaceDesign_tau_lower` at all
  (`grep -rn "subspaceDesign_tau_lower" ArkLib/` outside the defining file: no hits).
- **Evidence**: `(session-local probe) r6-l217-gen.lean` — the *byte-for-byte identical proof body*
  with the binder changed to `(hs1' : 1 ≤ s) → ∀ r, 1 ≤ r → …` compiles clean (exit 0, no
  errors/warnings). Only two mechanical edits were needed (obtain `1 ≤ s` from the new
  hypothesis instead of from `Icc` membership).
- **Refutation attempt**: I looked for a step that secretly uses `r ≤ s` — the only uses of
  `hrs` are `hs1 : 1 ≤ s := hr1.trans hrs`; `hs_pos` (needed for `0 < s * card ι` in `hdiv`).
  Nothing else. Also checked whether `s = 0` could be admitted too: it can in principle
  (`s = 0 ⇒ C = ⊥ ⇒` the degenerate branch), but the proof computes `hs_pos` before the
  `by_cases`, so `1 ≤ s` is the honest minimal restructuring.
- **Suggested fix**: state `(hs : 1 ≤ s) : ∀ r, 1 ≤ r → τ r ≥ …` (or keep `Icc 1 s` as a
  `_of_mem_Icc` corollary). Update the module docstring's `min_r τ(r) ≥ ρ − 1/n` claim
  accordingly.

### [MEDIUM] T2.18's docstring records one source omission in forensic detail but silently omits a second, independent one (ABF26 D2.14 inter-orbit-only admissibility is insufficient)

- **Where**: `ArkLib/Data/CodingTheory/SubspaceDesign.lean:419–481`
  (`CodingTheory.frs_is_subspaceDesign_gk16`, hypothesis `hω_adm : Admissible L s ω`)
- **Source**: ABF26 Definition 2.14 (inter-orbit clause only: *"for α, β ∈ L² it holds that
  α·ωⁱ ≠ β for every 0 ≤ i < s"*, quantified over **distinct** pairs) and GG25 Definition 2.18
  (*"α₁,…,αₙ ∈ F_q distinct elements such that αᵢγᵗ ≠ αⱼ for all i ≠ j and t < s"*).
  Neither excludes `0 ∈ L`.
- **What's wrong**: `frs_is_subspaceDesign_gk16` consumes `ReedSolomon.Folded.Admissible`, which
  is a **deliberate strengthening** of ABF26 D2.14 (it adds the intra-orbit clause
  `α·ωⁱ ≠ α` for `0 < i < s`). That strengthening is **load-bearing for T2.18**: with the
  paper's literal D2.14 the theorem is FALSE even when `hω_gen` holds. The T2.18 docstring
  presents itself as a faithfulness audit record ("Source hypothesis restored (2026-07-21
  Phase-A merge audit)… the omission has been reported to the paper's authors"), lists
  `hω_adm : Admissible …` as if it were the paper's D2.14, and never mentions this second gap.
  The deviation is documented only in `ReedSolomon/Folded.lean`, and there only as a hedge
  ("would … silently weaken the FRS distance argument downstream (T2.18, T4.14)") — not as
  "T2.18 is false without it".
- **Evidence**: `(session-local probe) r6-zero-in-L-cex.lean`, **compiles clean**. It takes as a
  hypothesis exactly `frs_is_subspaceDesign_gk16` with `Admissible` replaced by ABF26 D2.14's
  literal inter-orbit clause (and `hω_gen` kept!) and derives `False`.
  Witness: `F = ZMod 5`, `ι = Fin 2`, `domain = (0, 1)`, `s = 3`, `k = 2`, `ω = 2`
  (`orderOf ω = 4 = |F| − 1`, so `hω_gen` holds; `hadm_paper` proved `by decide`).
  `A := span {enc X}` has `dim A = 1`; the block at the point `0` is identically zero
  (`hblock0 : finrank (A ⊓ ker proj 0) = 1`), the block at `1` is trivial
  (`hblock1 : … = 0`), so `Σ/n = 1/2` while `dim A · τ(1) = (k/n)/(s−1+1) = 1/3`.
  `arklib_admissible_fails` (also in the probe) confirms ArkLib's `Admissible` rejects this
  instance, i.e. the ArkLib strengthening is exactly the missing hypothesis.
- **Refutation attempt**: I tried to make the collapse harmless by choosing `A` differently
  and by taking `σ = 2` — those cases satisfy the bound; the failure is specific to a block
  whose whole `s`-orbit degenerates to a single point, which is precisely the multiplicity
  over-count that `hfinj` (injectivity of `(i,m) ↦ domain i · ω^m`) rules out. I also checked
  GK16 itself is *not* affected: GK16 §4.2 requires `F_q(α) = F_{q^r}` and `|S_α| = rt`, which
  excludes `α = 0`.
- **Suggested fix**: add a paragraph to `frs_is_subspaceDesign_gk16`'s docstring recording the
  second deviation with this counterexample (parallel to the `hω_gen` paragraph), and add the
  T2.18 row of the audit note. Nothing in the Lean needs to change — the statement is correct
  as it stands.

### [LOW] `pow_dvd_det_of_forall_mem_col_dvd` is matrix-generic but sits in the `Polynomial` namespace of a Wronskian file

- **Where**: `ArkLib/Data/Polynomial/FoldedWronskian.lean:103`
  (`Polynomial.pow_dvd_det_of_forall_mem_col_dvd`)
- **What's wrong**: the lemma is `{R} [CommRing R] {n} [DecidableEq n] [Fintype n]
  (M : Matrix n n R) …` — no polynomial anywhere; its own docstring says "Generic in the ring
  (used at `R := F[X]`)". It should be `Matrix.pow_dvd_det_of_forall_mem_col_dvd` and belongs
  under `ArkLib/ToMathlib/` (per AGENTS.md: "local extensions intended for upstreaming").
- **Evidence**: not a duplication — `loogle "|- _ ^ _ ∣ Matrix.det _"` → 0 hits;
  `loogle "|- _ ∣ Matrix.det _"` → only `Matrix.superFactorial_dvd_vandermonde_det`. So it is a
  genuine gap and a clean Mathlib candidate.
- **Suggested fix**: move to `ArkLib/ToMathlib/LinearAlgebra/Matrix/Determinant.lean` (new) in
  namespace `Matrix`.

### [LOW] Module-level `set_option linter.* false` suppresses real, actionable warnings

- **Where**: `ArkLib/Data/CodingTheory/SubspaceDesign.lean:49–51`
- **Evidence**: `(session-local probe) r6-nolinteropt.lean` (the file with the three `set_option`s
  commented out), compiled with the package's own lean options
  (`-Dlinter.mathlibStandardSet=true -DautoImplicit=false -Dlinter.style.longFile=1500
  -Dlinter.style.header=false`) reports:
  - `subspaceDesign_tau_lower` does not use `[DecidableEq ι]` (#4), `[DecidableEq F]` (#8);
  - `subspaceDesign_tau_lower` `[Fintype F]` (#7) should be `[Finite F]`
    (`LinearCode.singleton_bound_module` only needs `[Finite F]`);
  - `sum_rootMultiplicity_le_natDegree` does not use `[DecidableEq F]` (#3).
  `linter.unusedSectionVars` fires on nothing (the file has no section variables).
- **What's wrong**: these are real, fixable hypothesis-hygiene issues; disabling three linters
  at module scope also blanket-disables them for everything added to the file later.
- **Suggested fix**: drop the three `DecidableEq` instances, weaken `[Fintype F]` to
  `[Finite F]`, delete all three `set_option`s.

### [LOW] `hτ_nonneg : ∀ r, 0 ≤ τ r` is an ArkLib invention where a source-faithful guard exists

- **Where**: `ArkLib/Data/CodingTheory/SubspaceDesign.lean:138`
- **Source**: neither ABF26 D2.16/L2.17 nor GG25 Def 2.15/L2.16 asserts `τ ≥ 0`; GG25 constrains
  the *other* side (`τ : N → R_{≤1}`). GG25's proof instead begins *"Pick any non-zero codeword
  c …"*, i.e. it implicitly assumes the code is non-trivial.
- **What's wrong**: `hτ_nonneg` is used exactly once, in the `finrank C = 0` branch, i.e. purely
  to carry `C = ⊥`. It is genuinely needed *for that branch* (the docstring's `τ ≡ −1, n = 2`
  refutation of the unguarded statement is correct: `−1 ≥ 0 − 1/2` is false), so this is not a
  correctness defect. But `C ≠ ⊥` is closer to what GG25 actually assumes and imposes nothing
  on `τ`. Also, only `τ r` at the quantified `r` is ever used, so `∀ r, 0 ≤ τ r` is stronger
  than needed.
- **Evidence**: `(session-local probe) r6-l217-nonbot.lean` compiles clean: the same proof body with
  `hτ_nonneg` replaced by `(hCne : C ≠ ⊥) (hs1' : 1 ≤ s)` and the degenerate branch deleted.
- **Suggested fix**: either offer both forms, or weaken to `0 ≤ τ r` at the quantified `r`, and
  say in the docstring that `C ≠ ⊥` is the alternative (source-shaped) guard.

### [LOW] `ker_proj_eq_vanish_at` is advertised in "Main statements" but has zero consumers

- **Where**: `ArkLib/Data/CodingTheory/SubspaceDesign.lean:25, 87`
- **Evidence**: `grep -rn "ker_proj_eq_vanish_at" ArkLib/` → only the two lines above. Its
  docstring promises "this lets downstream proofs rewrite freely between the technical
  `ker(proj i)` form … and the paper's comprehension form", but neither `subspaceDesign_tau_lower`
  nor `frs_is_subspaceDesign_gk16` uses it (both work with `LinearMap.mem_ker` directly).
- **Suggested fix**: keep it (it *is* the D2.16 faithfulness witness) but say so honestly, or
  actually use it in the two proofs.

### [LOW] Module docstring states `min_r τ(r) ≥ ρ − 1/n` without the range restriction the theorem carries

- **Where**: `ArkLib/Data/CodingTheory/SubspaceDesign.lean:27–28` ("`min_r τ(r) ≥ ρ - 1/n`
  (**proved**, sorry-free)"). The declaration docstring does disclose the `[s]` narrowing, so
  this is a header/declaration inconsistency, not a fabrication. Fold in with the MEDIUM above.

### [LOW] Dated review-process metadata inside mathematical docstrings; dangling reference to "the audit's T2.18 row"

- **Where**: `SubspaceDesign.lean:33, 118, 132, 439, 460, 471`
- **Evidence**: `grep -rlE "20(25|26)-[0-9]{2}-[0-9]{2}" --include=*.lean ArkLib/` returns only
  `SubspaceDesign.lean` and `Data/Fin/Basic.lean` — this module is essentially the sole ArkLib
  file carrying "2026-06-10 re-review", "2026-07-21 Phase-A merge audit", "formerly an external
  admit; proved in-tree 2026-08-07" in docstrings. "see the audit's T2.18 row" gives no path,
  so `scripts/check-docs-integrity.py` cannot validate it.
- **Note**: this is a repo-convention/owner-preference call (CONTRIBUTING §Documentation
  Standards asks for title/summary/notation/references, not changelogs). The *substance* of
  each note is accurate (I verified the `hω_gen` and `r = 0` claims independently).
- **Suggested fix**: keep the mathematical content (counterexamples, hypothesis rationale),
  move the dates/audit-process narration to the KB audit file, and use a resolvable relative
  path if a KB link is kept at all.

### [LOW] `natDegree_comp_C_mul_X_le` re-derives what Mathlib's `comp_C_mul_X_coeff` gives directly

- **Where**: `ArkLib/Data/Polynomial/FoldedWronskian.lean:66`
- **Evidence**: Mathlib has `@[simp] Polynomial.comp_C_mul_X_coeff :
  (p.comp (C r * X)).coeff n = p.coeff n * r ^ n`
  (`Mathlib/Algebra/Polynomial/Eval/Degree.lean:107`), from which the `≤` bound (and the
  *equality* for `r ≠ 0`, which the docstring claims but the statement does not provide) is
  immediate. Not a duplication (Mathlib has no `natDegree_comp_C_mul_X_le`), so LOW.

### [LOW] T2.18 carries `L` + `hL_dom` where only `Admissible (univ.map domain) s ω` is used

- **Where**: `ArkLib/Data/CodingTheory/SubspaceDesign.lean:486–488`
- **What's wrong**: `Admissible L s ω` with `image domain ⊆ L` is strictly stronger than
  `Admissible (Finset.univ.map domain) s ω`, which is all `hadm` (line 550) needs. Paper-shaped
  (ABF26 writes `FRS[F, L, k, s, ω]`), so acceptable, but it does weaken the theorem for no
  gain, and the code itself is `frsCode domain k s ω` (indexed by `ι`, not `L`), so `L` plays no
  role in the conclusion.

---

## Clean bill

Everything below was checked and is **genuinely OK**.

**Axiom hygiene** (`(session-local probe) r6-axioms.lean`) — all exactly
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`:
`frs_is_subspaceDesign_gk16`, `subspaceDesign_tau_lower`, `IsSubspaceDesign`,
`ker_proj_eq_vanish_at`, `foldedWronskian_ne_zero_of_linearIndependent`,
`natDegree_foldedWronskian_le`, `pow_dvd_det_of_forall_mem_col_dvd`,
`X_pow_card_sub_one_sub_C_irreducible`, `natDegree_comp_C_mul_X_le`,
`LinearCode.singleton_bound_module`. Zero `sorry`/`admit`/`axiom` tokens in both files.

**D2.16 transcription** — ABF26 Def 2.16 quoted: *"for every r ∈ N and F-linear subspace A of C
with dim A ≤ r … `(Σ_{i∈[n]} dim Aᵢ)/n ≤ dim A · τ(r)`, where `Aᵢ := {a ∈ A : aᵢ = 0ˢ}`."*
The Lean matches on every point: `∀ r : ℕ`, `A ≤ C`, `finrank A ≤ r` (**≤**, not `=`),
division by `Fintype.card ι`, RHS `finrank A * τ r`. `Aᵢ = A ⊓ ker (LinearMap.proj i)` is
faithful: `ker_proj_eq_vanish_at` proves the carrier is `{a | a i = 0}`.
**GX13 check**: GX13's original notion *is* on the ambient/message space (a collection of
subspaces `H_i ⊆ F_q^m` with `Σ dim(W ∩ H_i)` small) — but ArkLib cites and transcribes
**ABF26 D2.16**, which is the code-side recast, and the T2.18 proof does the message-side lift
itself (`B := degreeLT ⊓ comap enc A`, `N i := B ⊓ comap enc (ker proj i)`, both dimension-
preserving via `finrank_eq_of_map_eq` + encoder injectivity). No mismatch, nothing downstream
is wrong.

**Rate convention** — ABF26 Def 2.5 quoted: *"the rate of C is `ρ(C) := log_{|Σ|}|C| / n`"*.
With `Σ = F^s`, `|C| = |F|^{dim_F C}` this is `dim_F C/(s·n)`; for FRS, `ρ = k/(s·n)` and
`s·ρ = k/n`, so `τ(r) = s·ρ/(s−r+1) = (k/n)/(s−r+1)` — exactly the Lean spelling. Boundary
values `τ(1) = ρ` and `τ(s) = s·ρ` check out. `Finset.Icc 1 s` is the right encoding of the
paper's `[s]`. The `(s − r + 1)` in the Lean `τ` elaborates in **ℝ** (confirmed via `hτval`),
not truncated ℕ subtraction.

**L2.17 `r = 0` exclusion** — correct: `finrank A ≤ 0` forces `A = ⊥`, so the design inequality
degenerates to `0 ≤ 0 · τ(0)`, constraining nothing. Both ABF26 L2.17 and GG25 L2.16 are
therefore literally false at `r = 0` for a `τ` with `τ(0) < ρ − 1/n`. GG25's own proof concedes
this ("We just need to prove the result for r = 1 since we can just take A of dimension at 1").

**L2.17 `hτ_nonneg` necessity** — the docstring's `τ ≡ −1, n = 2` refutation of the unguarded
statement is correct (`C = ⊥` makes all design inequalities `0 ≤ 0`; the claimed bound becomes
`−1 ≥ −1/2`, false). Recorded as LOW only because a more source-faithful guard exists.

**`LinearCode.singleton_bound_module`** — **new in this PR** (`Basic/LinearCode.lean:631`,
+87 diff), not pre-existing. Correct: `|F|^{finrank C} = |C| ≤ |A|^{n−(d−1)} =
(|F|^{finrank A})^{n−(d−1)}` via the pre-existing `singleton_bound` +
`Module.card_eq_pow_finrank`, then `Nat.pow_le_pow_iff_right` with `1 < |F|`. The ℕ-subtraction
edge is safe (`d = 0` ⇒ `n − (0−1) = n`, bound `finrank A · n`, true). In `subspaceDesign_tau_lower`
it is used at `A = Fin s → F` (`finrank = s`) and cast to `k ≤ s(n − d + 1)` under
`1 ≤ d ≤ n`, both established. **Metric consistency verified**: `Code.dist` here is the
*block* Hamming distance on `ι → (Fin s → F)`, matching the design sum's per-block dimensions.

**L2.17 proof chain** — verified by hand: `a := u − v` nonzero with `#{i : a i ≠ 0} = Δ(u,v) ≤ d`;
`A = span{a}` has `finrank 1 ≤ r`; `finrank (A ⊓ ker proj i) = [a i = 0]`; hence
`τ(r) ≥ #zeros/n ≥ (n−d)/n ≥ k/(sn) − 1/n`. Correct.

**T2.18 statement vs GK16 Theorem 14** — GK16 Thm 14 quoted; its counting identity
`(m−1)s ≥ r(t−s+1)·Σ_α dim(W ∩ H_α)` maps to the Lean's
`hS_nat : (s−σ+1)·Σᵢ dim(A ⊓ ker projᵢ) ≤ σ(k−1)` under `m ↔ k`, GK16-`s` ↔ `σ = dim A`,
`t ↔ s` (fold), `r ↔ 1`. Exact match.

**T2.18 `hω_gen` is LOAD-BEARING; the docstring's counterexample checks out** —
`(session-local probe) r6-omega-cex.lean` **compiles**: `refutes_unguarded` takes the theorem *with
`hω_gen` deleted* as a hypothesis and derives `False`. Witness `F = ZMod 17`, `ι = Fin 7`,
`domain = 1..7`, `s = 2`, `k = 3`, `ω = −1` (structurally the docstring's 𝔽₁₀₁ example, shrunk
to the smallest field admitting 7 points with `{α, −α}`-freeness). All other hypotheses
discharged in-probe (`hL_dom`, `hFn`, `hω_adm` by `decide`, `hω0`), and `hω_gen_fails` confirms
`orderOf(−1) = 2 ≠ 16`. `A = span{enc 1, enc X²}` has `finrank 2` (`hAfinrank`) and every block
subspace has `finrank 1` (`hblock`), giving `Σ/n = 1 > 6/7 = dim A · τ(2)`. GK16 Lemma 12 is
quoted and does require *"γ ∈ F* be a generator"* — so `hω_gen` is exactly the source's own
hypothesis, not an unlicensed hybrid. GG25 Thm 2.19 (`q > sn` only) is falsified by the same
witness (`q = 17 > sn = 14`), as the docstring claims.

**T2.18 non-vacuity in the contentful regime** — `(session-local probe) r6-nonvacuous.lean` **compiles**:
`F = ZMod 5`, `ι = Fin 2`, `domain = (1, 4)`, `s = 2`, `k = 3`, `ω = 2`. All hypotheses
discharged including `hω_gen : orderOf 2 = 4 = |F| − 1` and `Admissible`; `instance_holds`
applies `frs_is_subspaceDesign_gk16` directly. `contentful : 3 < 2 * card ι` (i.e. `k < s·n`),
and `tau_one_lt_one` shows `τ(1) = 3/4 < 1` (so the `1 ≤ τ r` trivial branch does **not**
cover `r = 1`) and `σ·τ(1)·n = 3/2 < 2 = σ·n` (so the conclusion at `r = 1, σ = 1` is strictly
stronger than the trivial per-block bound `dim Aᵢ ≤ dim A`). The docstring's own
`k ≥ s·|ι| ⇒ τ ≥ 1 on [1,s]` contentless-regime caveat is also correct (worst case `r = 1`:
`τ(1) ≥ 1 ⟺ k ≥ n·s`).

**T2.18 proof walk** — every danger point the brief flagged:
- *Trivial branches*: `1 ≤ τ r` (line 514) and `σ = 0` (line 518) are handled before the main
  branch; the surviving regime is exactly `r ∈ [1,s]`, `1 ≤ σ ≤ r`, `k < n(s−r+1)` — non-empty,
  see the compiled instance above.
- *`hns_q` split*: `s ≤ 1` uses `hFn` (`n·1 ≤ q − 1`); `s ≥ 2` derives `domain x ≠ 0` from the
  intra-orbit clause at `i = 1` and then embeds the `n·s` distinct folded points into
  `univ.erase 0`. Both correct. `hkq : k ≤ q − 1` follows from `hk_ns` + `hns_q`. ✓
- *`hmult` arithmetic `(i' : ℕ) + m < s` under ℕ subtraction*: `hσs : σ ≤ s` is established at
  **line 528**, well before `hmult` at line 682, and is in `omega`'s context together with
  `i'.isLt : i' < σ` and `hm : m < s − σ + 1`. No `σ > s` case can arise. ✓
- *`hfinj` coercion `ι × ℕ → ι × Fin s`*: `m < s − σ + 1` plus `1 ≤ σ ≤ s` gives `m < s`
  (`hms`), so `⟨m, hms⟩ : Fin s` is legitimate and `admissible_foldedPoints_injective` applies
  verbatim. The `n(s−σ+1)` points are genuinely distinct. ✓
- *`sum_rootMultiplicity_le_natDegree`*: correct (packs `rootMultiplicity a W` copies of each
  distinct `a ∈ S` into a sub-multiset of `W.roots`); safe even at `W = 0`.
- *`hSb` chain*: `S(s−r+1) ≤ S(s−σ+1)` uses `hS_nonneg : 0 ≤ S` and `hσr : σ ≤ r`;
  `S(s−σ+1) ≤ σ(k−1) ≤ σk` uses `0 ≤ σ`. All three facts are present; verified by hand. ✓
- *`hk1 : 1 ≤ k`*: correct (`k = 0 ⇒ degreeLT F 0 = ⊥ ⇒ frsCode = ⊥ ⇒ σ = 0`, contradicting
  the `σ = 0` branch already taken).
- *`hadm` transport*: `Admissible L s ω` + `image domain ⊆ L ⇒ Admissible (univ.map domain) s ω`
  — correct direction.

**GK16 Definition 11 / `foldedWronskian`** — GK16 Def 11 quoted: row `i` of `W_γ` is
`(P₁(γⁱX), …, P_s(γⁱX))`, i.e. **rows = twists, columns = polynomials**. The Lean
`Matrix.of fun i j => (P j).comp (C (ω ^ i) * X)` is the same orientation (and `det` is
transpose-invariant anyway). No normalisation difference. ✓

**GK16 Lemma 12 / `foldedWronskian_ne_zero_of_linearIndependent`** — GK16 Lemma 12 quoted:
*"Let m < |F| = q, let γ ∈ F* be a generator, and let P₁,…,P_s ∈ F_q[X]_{<m}. Then P₁,…,P_s are
linearly independent over F_q **iff** det W_γ ≠ 0."* Hypothesis match is exact:
`k ≤ card F − 1 ⟺ k < q ⟺ m < q`; `orderOf ω = q − 1 ⟺ ω generates F^×`;
`P j ∈ degreeLT F k`. ArkLib proves only the ⇒ direction and says so explicitly in the
docstring ("the direction needed by T2.18") — a faithful narrowing, not a mis-advertisement.
The **proof is real**: it is GK16 Appendix A's argument (quoted: `E(X) = X^{q−1} − γ`
irreducible, `X^q ≡ γX`, `P_j(X^{qʲ}) = P_j(X)^{qʲ}`, `Q(Y) = Σ αᵢ Y^{qⁱ}` of degree `≤ q^{s−1}`
vanishing on the whole span, `q^s ≤ q^{s−1}` absurd), with the `A_i`-common-factor step replaced
by taking the row dependency directly over `K` via `Matrix.exists_vecMul_eq_zero_iff`. No hidden
induction-assumes-conclusion, no off-by-one in the `Finset.card` step (`hcount` uses
`Finset.card_le_card_of_injOn` into `Q.roots.toFinset`, then `card_roots'`). Attempted
counterexamples all fail for structural reasons: `σ > k` makes `LinearIndependent` unsatisfiable;
`σ = 0` is handled (empty det `= 1`); `ω` of order `k` is excluded by `hω_gen`; small
characteristic is irrelevant (that is precisely why GK16 introduced the *folded* Wronskian).
ArkLib additionally **proves** `X^{q−1} − ω` irreducible (`X_pow_card_sub_one_sub_C_irreducible`),
which GK16 merely asserts ("which happens to be irreducible") — genuine added value, and the
proof (any irreducible factor of degree `d` gives `ω^d = 1`, so `(q−1) ∣ d ≤ q−1`) is correct.

**`natDegree_foldedWronskian_le`** — `σ × σ` det of entries of `natDegree ≤ k` has
`natDegree ≤ σ·k`: correct (Leibniz, `natDegree_sum_le` + `natDegree_prod_le`). Edge cases fine:
`σ = 0` gives `natDegree 1 = 0 ≤ 0`; zero entries give `natDegree 0 = 0 ≤ k`. Applied in T2.18
at `k − 1` with `natDegree < k`, sound (`natDegree < k ⇒ k ≥ 1`).

**`pow_dvd_det_of_forall_mem_col_dvd`** — statement is TRUE (induction on `t`, factoring `d` out
of one column at a time via `Matrix.det_updateCol_smul`); proof is correct. Not in Mathlib
(loogle, above). Only the placement is a finding.

**Duplication sweep (top priority per brief)** — no duplication found:
- Mathlib's only Wronskian is `Polynomial.wronskian a b = a·b′ − a′·b`
  (`Mathlib/RingTheory/Polynomial/Wronskian.lean`, for Mason–Stothers/FLT) — 2-argument, not a
  `σ × σ` determinant, and unrelated to the folded variant. `foldedWronskian` is **not** a
  specialization or generalization of it and should not be phrased as one.
- ArkLib has no other Wronskian (`grep -rni wronskian ArkLib/` → only the two PR files).
- No Mathlib `det`-divisibility lemma of this shape (loogle, above).
- `IsSubspaceDesign` has no ArkLib precursor (`grep -rn IsSubspaceDesign ArkLib/` → only this
  file).
- The FRS infrastructure (`Admissible`, `frsCode`, `frsEvalOnPoints`,
  `admissible_foldedPoints_injective`, `frsEvalOnPoints_domRestrict_injective`) is reused, not
  re-implemented.

**Style/integration** — no line exceeds 100 characters (checked with a UTF-8-aware counter;
a naive byte count is misleading here); 763 and 406 lines, both under the 1500 `longFile` cap;
both modules are imported from `ArkLib.lean` (lines 120 and 193), so CI builds them.
Naming follows `docs/wiki/coding-theory-conventions.md`
(`IsX` predicate `IsSubspaceDesign`; `<codeFamily>_<...>_<authors><year>` for
`frs_is_subspaceDesign_gk16`; helper lemmas `private`).

**Audit-doc claims** (`docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`,
rows `D2.16` / `L2.17` / `T2.18`) — all verified accurate: "proved in-tree 2026-08-07,
sorry-free, axiom-clean", the `ρ = k/(s·n)` correction, "the only consumer of the ω-generator
hypothesis" (confirmed: `hω_gen` is threaded to exactly one call site, line 643), and
"UM half deferred pending D2.19" (the theorem states only the FRS half and says so).
