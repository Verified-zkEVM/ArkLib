# R4 — `JohnsonBound/*` + `Basic/LinearCode.lean` (ABF26 §3)

Reviewer cluster `R4-johnson`. Repo `/home/alh/ArkLib-split-pr1` @ `ffa0733a`, base `origin/main`
@ `02d759d5`.

Probes (all compiled with `lake env lean` from the repo root, unmodified tree):

| probe | result |
|---|---|
| `(session-local) r4-dup.lean` | ✅ clean — `remap`/`piCongrRight`, `remap_hammingDist`/`hammingDist_comp`, `Jqℓ = J q (lFac·δ)` |
| `(session-local) r4-guardfree.lean` | ✅ clean — T3.2 proved **without** `_h_radicand` |
| `(session-local) r4-c33-content.lean` | ✅ clean — C3.3 instantiated: `Λ(C, 7/16) ≤ 32` at n=16,k=4,η=1/16 |
| `(session-local) r4-rs-witness2.lean` | ✅ clean — those hypotheses are satisfiable (RS[F,16 pts,deg<4] MDS, `finrank=4`, `minDist=13`, domain exists over `ZMod 17`) |
| `(session-local) r4-t32-content.lean` | ✅ clean — T3.2 instantiated `Λ(C,1/2) ≤ 2` (tight); `plotkin_card_le_ell` instantiated |
| `(session-local) r4-edge.lean` | ✅ clean — `Jqℓ q 0 δ = 0`; `Λ(C,0) ≥ 1`; `Jqℓ 2 2 ≠ J 2` |
| `(session-local) r4-linter.lean` | ✅ clean — **refutes** a suspected finding (see §Refuted) |

---

## HEADLINE (positive): the `(ℓ-1)/ℓ` factor is CORRECT, not a transcription error

This was the single biggest CRITICAL risk in scope and it is **clean**.

`ABF26.pdf` (build date 2026-04-08, page 12, Definition 3.1) prints, per a positional
`pdftotext -bbox` reconstruction of the glyph boxes:

> `J_{q,ℓ}(δ) = (1 − 1/q) · (1 − √(1 − (q/(q−1)) · (ℓ/(ℓ−1)) · δ))`

(numerator `ℓ` at y=355.27, denominator `ℓ−1` at y=363.33 ⇒ the printed fraction really is
`ℓ/(ℓ−1)`.) That printed form is **mathematically wrong**: `ℓ/(ℓ−1) > 1` makes `J_{q,ℓ} > J_q`,
i.e. a *finite* list budget would buy a *larger* radius than the `ℓ → ∞` limit, and at `q→∞, δ→1`
the radicand goes negative so `J: (0,1) → ℝ` is not even real-valued.

The Lean uses `(ℓ-1)/ℓ` (`Family.lean:75`). This is:

* what the classical literature says — **GRS12 Exercise 7.8** (`(pdftotext of ~/abf26-refs/) GuruswamiRS12.txt:7618`):
  > "Let `C` be a q-ary code with distance `d`, `L ≥ 1` and
  > `e < (1 − 1/q)(1 − √(1 − (q/(q−1)) · ((L−1)/L) · (d/n))) n`.
  > Then prove that `C` is `(e/n, L)`-list decodable."
  (Independently re-derived: Johnson gives `|B| ≤ θδ/(θδ − 2θρ + ρ²)`, `θ = 1−1/q`; solving
  `|B| ≤ ℓ` yields `ρ ≤ θ(1 − √(1 − (δ/θ)(1 − 1/ℓ)))`.  Cross-check at `q=2, δ=1/2` reproduces
  the textbook Hadamard bound `ℓ = 1/(4ε²)` exactly.)
* what the **authors' canonical `.tex` says today**: `/home/alh/ef-millenium/ef-millenium.tex:1343`
  has `\frac{\ell-1}{\ell}`, changed from `\frac{\ell}{\ell - 1}` by **Giacomo Fenzi in commit
  `c673766` ("fix"), 2026-06-13** — i.e. the paper authors themselves fixed the typo after the
  PDF in `~/abf26-refs/` was built.

The `Jqℓ` docstring documents this explicitly and correctly, including that the printed factor
"would have made [the Johnson denominator] negative" (verified: denominator
`= frac·δ_min·(1 − lFac)`, which is `−frac·δ_min/(ℓ−1) < 0` under the printed factor).
**No finding. This is a good catch by the PR author and should be preserved on any rebase.**

---

## Findings

### [MEDIUM] `johnson_bound_lambda_le_ell` is strictly weaker than ABF26 Thm 3.2, and the docstring's justification for the extra hypothesis is provably false
- **Where**: `ArkLib/Data/CodingTheory/JohnsonBound/Family.lean:398` (`CodingTheory.johnson_bound_lambda_le_ell`),
  docstring lines 385–393.
- **Source**: ABF26 Theorem 3.2 (`ef-millenium.tex:1351`):
  > "For any `C ⊆ Σ^n` with `|Σ| = q` it holds that `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`."
  The paper has **no** side condition.
- **What's wrong**: The Lean theorem adds
  `_h_radicand : q/(q-1) · (ℓ-1)/ℓ · (minDist C / n) ≤ 1`.
  The docstring justifies it with:
  > "at which radius the list-size-`ℓ` claim is **false** (e.g. a high-distance code can have
  > more than `ℓ` codewords within relative distance `1 - 1/q`)."

  That sentence is **false**, and is refuted by `plotkin_card_le_ell` **80 lines above it in the
  same file**: when the guard fails, `δ_min` exceeds the Plotkin radius by `ℓ/(ℓ-1)`, so the
  *whole code* has `≤ ℓ` words, hence `Λ(C, anything) ≤ |C| ≤ ℓ`. No such counterexample code
  exists. Sanity check: for `q=2, ℓ=3` the guard fails only when `δ_min > 3/4`, where classical
  Plotkin already gives `|C| ≤ δ/(δ−1/2) ≤ 3 = ℓ`.
- **Evidence**: `(session-local) r4-guardfree.lean` compiles clean; it proves
  `johnson_bound_lambda_le_ell_guardfree` — the paper's exact statement with **only** `2 ≤ ℓ` —
  by `rcases` on the guard and dispatching the failing branch through
  `Lambda_le_ncard` + `plotkin_card_le_ell`. ~45 lines, all ingredients already in-tree.
  Note `mds_johnson_lambda_le` (`Family.lean:723`, `789`) is *forced* to do exactly this case
  split itself, which is direct evidence the guard is a real cost, not a modelling choice.
- **Refutation attempt**: I first assumed the guard was forced because `J_{q,ℓ}` is undefined
  (imaginary) there and `Real.sqrt` truncation would silently inflate the radius to `1 - 1/q`.
  That is true about the *truncation*, but the resulting statement is still **true** — Plotkin
  carries it. I also checked whether `plotkin_card_le_ell`'s `2 ≤ B.card` / `2 ≤ card α`
  preconditions could fail: both degenerate cases give `|C| ≤ 1 ≤ ℓ` directly (handled in the
  probe). No obstruction found.
- **Suggested fix**: drop `_h_radicand` and inline the probe's proof; or, at minimum, delete the
  false "the claim is false there" sentence and replace it with "the theorem is also true there
  by `plotkin_card_le_ell`; the guard is kept to keep the proof in one branch".

### [MEDIUM] `JohnsonBound.remap` and its three lemmas duplicate Mathlib
- **Where**: `ArkLib/Data/CodingTheory/JohnsonBound/Expectations.lean:146` (`remap`),
  `:150` (`remap_injective`), `:158` (`remap_hammingDist`).
- **Source**: Mathlib `Equiv.piCongrRight`
  (`.lake/packages/mathlib/Mathlib/Logic/Equiv/Basic.lean:143`) and
  `hammingDist_comp` (`.lake/packages/mathlib/Mathlib/InformationTheory/Hamming.lean:120`).
- **What's wrong**: `remap σ` is *definitionally* `⇑(Equiv.piCongrRight σ)`; `remap_injective σ`
  is `(Equiv.piCongrRight σ).injective`; `remap_hammingDist` is
  `hammingDist_comp (fun i => (σ i : F → G)) (fun i => (σ i).injective)`.
  Per `docs/kb/…/feedback-no-duplication` and `CONTRIBUTING.md`, these should reuse Mathlib.
  (`remap_e`, `remap_d`, `remap_image_card` are genuine new content about `JohnsonBound.e`/`d` —
  those are fine, but they should be phrased over `Equiv.piCongrRight`.)
- **Evidence**: `(session-local) r4-dup.lean` — all three replacement proofs are `rfl` /
  `(Equiv.piCongrRight σ).injective` / `hammingDist_comp …` and compile clean.
- **Refutation attempt**: checked whether the `Fin n`-indexed, non-dependent shape blocks reuse —
  it does not (`piCongrRight` and `hammingDist_comp` are both dependent-family general). Checked
  whether `remap` needs to be a plain function rather than an `Equiv` coercion for the `Finset.image`
  uses — `⇑(Equiv.piCongrRight σ)` works identically.
- **Suggested fix**: delete `remap`/`remap_injective`/`remap_hammingDist`; restate `remap_e`/`remap_d`
  over `Equiv.piCongrRight`.

### [MEDIUM] `docs/kb/audits/…` §3 is stale in exactly the rows this PR fills
- **Where**: `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md:57–60`.
- **What's wrong**: at HEAD the table still says
  * Definition 3.1 → `present-but-different` … "ArkLib has the usual q-ary Johnson function,
    but **not the paper's full three-function family**" — but this PR adds `Jqℓ` and `Jcap`;
  * Theorem 3.2 → `present-but-different` … "rather than the exact paper packaging" — but this
    PR adds the exact paper packaging `johnson_bound_lambda_le_ell`;
  * Corollary 3.3 → **`missing`** … "Likely derivable, but not present as a named result" — but
    this PR proves it as `mds_johnson_lambda_le`;
  * Theorem 3.4 → "Depends on missing subspace-design infrastructure" — the PR adds
    `SubspaceDesign.lean`.

  The PR *rewrote the whole Section 2 table of this same file* (and updated the A.7 / B.1 rows),
  so leaving §3 untouched is an omission, not a scope decision. `AGENTS.md` requires docs to move
  with the PR. Net effect: the two headline theorems of the PR have **zero** references anywhere
  outside their own file, and the one index that would find them says they don't exist.
- **Evidence**: `sed -n '50,70p' docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`
  at `ffa0733a`; `grep -rn "mds_johnson_lambda_le\|johnson_bound_lambda_le_ell" ArkLib/ docs/` returns
  nothing outside `Family.lean`.
- **Refutation attempt**: checked `docs/wiki/coding-theory-conventions.md` and `docs/wiki/repo-map.md`
  (both touched by the PR) in case §3 was indexed there instead — `Jqℓ`/`Jcap` appear only as
  *naming examples*, not as status rows.
- **Suggested fix**: update the four §3 rows in the same PR.

### [MEDIUM] `LinearCode.IsMDS_iff_rate_distance'` is a zero-consumer restatement of the lemma directly above it
- **Where**: `ArkLib/Data/CodingTheory/Basic/LinearCode.lean:707` (`IsMDS_iff_rate_distance'`),
  vs `:667` (`IsMDS_iff_rate_distance`).
- **What's wrong**: the primed version differs only by writing `((rate LC : ℚ≥0) : ℝ)` where the
  unprimed one writes `(Module.finrank F LC : ℝ) / Fintype.card ι`; its entire proof is
  `rw [IsMDS_iff_rate_distance]` + a `simp [rate, dim, length]; push_cast; ring` coercion lemma.
  It has **no consumers** (`grep` finds exactly 1 hit = its own declaration). Two spellings of one
  lemma in one file, one of them dead.
- **Evidence**: `git diff origin/main...HEAD -- ArkLib/Data/CodingTheory/Basic/LinearCode.lean`;
  usage count via `grep -rn "IsMDS_iff_rate_distance'" ArkLib/` → 1.
- **Refutation attempt**: checked whether `mds_johnson_lambda_le` or anything in the next split
  (per the PR's own "next split" list in `docs/wiki/coding-theory-conventions.md`) uses the `rate`
  form — `mds_johnson_lambda_le` uses the **unprimed** one (`Family.lean:615`), and the docstring
  there explicitly says the `finrank` form is preferred "to match the upstream `IsMDS` signature".
  So the primed one is not even the form the author's own consumer wants.
- **Suggested fix**: drop `IsMDS_iff_rate_distance'`, or export the coercion fact
  `((rate LC : ℚ≥0) : ℝ) = finrank/card` as a standalone `rate_eq_finrank_div` lemma (that *is*
  reusable) and let call sites `rw` it.

### [LOW] `Jqℓ` re-defines the in-tree `JohnsonBound.J`; the bridge is proved inline but never exported. `Jcap` is dead.
- **Where**: `Family.lean:73` (`Jqℓ`), `:88` (`Jcap`); `JohnsonBound.J` at `Basic.lean:52`.
- **What's wrong**: `Jqℓ q ℓ δ = J q (((ℓ-1)/ℓ) · δ)` holds (for `q ≠ 0, 1`), so `Jqℓ` could have
  been a one-line wrapper of the existing `J`. The identity is *proved inside* the
  `mds_johnson_lambda_le` proof (`Family.lean:728-733`, `hJqℓ_eq`) but not exported as a
  `Jqℓ_eq_J` lemma, so a downstream consumer cannot reuse it. Similarly `Jcap δ = 1 - √(1-δ)` is
  exactly the LHS of the pre-existing `JohnsonBound.sqrt_le_J`, but no `Jcap_le_J` bridge is stated;
  `Jcap` has zero consumers and its only two lemmas (`Jcap_zero`, `Jcap_one`) evaluate it at `0`
  and `1`, both **outside** the paper's declared domain `(0,1)`.
- **Evidence**: `(session-local) r4-dup.lean` (last example) compiles the `Jqℓ = J q (lFac·δ)` identity;
  usage counts: `Jcap` → def + its 2 lemmas only.
- **Refutation attempt**: considered that a paper-shaped standalone definition is the documented
  convention (`docs/wiki/coding-theory-conventions.md:49` lists `Jqℓ`, `Jcap` as sanctioned
  paper-named functions) — so the *definition* is fine; what is missing is the bridge lemmas,
  which the convention doc does not excuse. Downgraded from MEDIUM to LOW on that basis.
- **Suggested fix**: export `Jqℓ_eq_J` and `Jcap_le_J` (the latter is `sqrt_le_J` verbatim).

### [LOW] Two docstring inaccuracies in `Family.lean`, one self-contradictory
- **Where**: `Family.lean:71` and `Family.lean:395-397`.
- **What's wrong**:
  1. `:71` — "For `ℓ = 2` this is the binary Johnson radius". It is not: `Jqℓ 2 2 δ = ½(1-√(1-δ))`
     whereas the binary Johnson radius is `J_2(δ) = ½(1-√(1-2δ))`. The `Jcap` docstring 15 lines
     later (`:83`) states the correct `J_2` formula, so the file contradicts itself. `ℓ = 2` is the
     *list-size-two* radius, unrelated to `q = 2`.
  2. `:395` — "The paper states the theorem for all `ℓ ∈ ℕ`; the case `ℓ = 1` is true but excluded
     here for convenience". Under Lean's `ℚ` division convention `(0-1)/0 = 0`, so
     `Jqℓ q 0 δ = 0`, and `Λ(C, 0) ≥ 1` for any nonempty `C` — i.e. the `ℓ = 0` instance is
     **false**, not merely inconvenient. (The paper's `J_{q,0}` is undefined, so this is a Lean-side
     encoding artifact, but the docstring as written implies `ℓ = 0` is fine.)
- **Evidence**: `(session-local) r4-edge.lean` compiles `Jqℓ 2 2 (1/2) = ½(1-√(1/2))`,
  `J 2 (1/2) = ½(1-√0)`, `Jqℓ q 0 δ = 0`, and `1 ≤ Lambda C 0` for `c ∈ C`.
- **Suggested fix**: replace (1) with "for `ℓ = 2` this is the list-size-2 Johnson radius"; in (2)
  say "`ℓ = 0` is excluded because `Jqℓ q 0 δ = 0` by `ℚ`-division convention and `Λ(C,0) ≥ 1`;
  `ℓ = 1` is true but excluded for convenience".

### [LOW] The `lin_shift_*` family is orphaned by the `remap` rewrite
- **Where**: `ArkLib/Data/CodingTheory/JohnsonBound/Expectations.lean:34` (`lin_shift_card`),
  `:43` (`lin_shift_e`), `:52` (`lin_shift_d`).
- **What's wrong**: their only consumer was `JohnsonBound.johnson_bound_lemma`
  (`Lemmas.lean:421`), which this PR rewrites to use `remap`. After the PR the three lemmas have
  **zero** consumers in the whole repo, and they are the only remaining `[Field F]` users in
  `Expectations.lean`. Dead code left behind by a refactor.
- **Evidence**: `grep -rn "lin_shift_e\|lin_shift_d\|lin_shift_card" ArkLib/` → only their own
  definitions and `lin_shift_e`/`lin_shift_d` calling `lin_shift_card`.
- **Suggested fix**: delete them, or keep with an explicit "`[Field F]` specialisation, superseded
  by `remap_*`" note.

### [LOW] `Family.lean`'s theorem names violate the naming convention this same PR introduces
- **Where**: `Family.lean:398` (`johnson_bound_lambda_le_ell`), `:598` (`mds_johnson_lambda_le`)
  vs `docs/wiki/coding-theory-conventions.md:14-42` (added by this PR).
- **What's wrong**: the doc mandates `<codeFamily>_<quantity>_<regime>_<authors><year>` for
  "statement-level theorems that bound an ε-error or list-size for a specific code family", with
  `lambda` listed as a `<quantity>` and `mds` as a `<codeFamily>`. The two headline theorems would
  be e.g. `general_lambda_johnson_joh62` and `mds_lambda_johnson_joh62`; neither carries the
  `<authors><year>` slot at all, despite both being cited to `[Joh62]`.
- **Evidence**: `sed -n '1,45p' docs/wiki/coding-theory-conventions.md`.
- **Refutation attempt**: checked whether the convention is scoped to the *next* split only — the
  doc says "In the current tree that layer is `JohnsonBound/Family.lean`, `SubspaceDesign.lean`,
  and the `ReedSolomon/` code families", i.e. it explicitly claims `Family.lean` follows it.
- **Suggested fix**: rename, or narrow the convention doc's claim.

### [LOW] Universe-monomorphic `{ι : Type}` / `{α : Type}` in the new §3 layer
- **Where**: `Family.lean:107` (`reidx_hammingDist`), `:398`, `:599`;
  `LinearCode.lean:668`, `:708`.
- **What's wrong**: fixed at `Type 0`, whereas `ListDecodable.Lambda`,
  `ListDecodable.closeCodewordsRel`, `ReedSolomon.code`, and the new `singleton_bound_module`
  (same PR, same file!) all use `Type*`. Nothing in the proofs needs `Type 0`
  (`Fintype.equivFin` is universe-polymorphic). Blocks consumers whose index type is not in `Type 0`.
- **Mitigation**: for the two `LinearCode.lean` lemmas the upstream `LinearCode.IsMDS`
  (`LinearCode.lean:297`) is itself `{ι : Type}`, so matching it is defensible; `Family.lean` has
  no such excuse.
- **Suggested fix**: `Type*` in `Family.lean`.

### [LOW] `mds_johnson_lambda_le` does not cover the paper's motivating case (interleaved RS), but says so
- **Where**: `Family.lean:598`, docstring `:586-592`.
- **Source**: ABF26 Cor 3.3 preamble: "Recalling that MDS codes (**which include the important
  class of interleaved Reed–Solomon codes**) …".
- **What's wrong**: the Lean is the `LinearCode ι F` (field-alphabet) instance only; IRS lives over
  the module alphabet `F^m`. Recorded as LOW rather than MEDIUM **only** because the docstring's
  "Scope vs the paper" paragraph states this explicitly and accurately, and no doc overclaims
  (the audit table — see the MEDIUM above — says nothing at all).

---

## Refuted / not reported (things I checked and could not make stick)

* **`Family.lean` is a fork of the existing Johnson development** — **NO, it is a genuine
  extension.** It `import`s `JohnsonBound/Basic` and consumes `johnson_bound`,
  `johnson_bound_lemma`, `JohnsonConditionStrong`,
  `johnson_condition_strong_iff_johnson_denom_pos`, `JohnsonDenominator`, `sqrt_le_J`,
  `min_dist_le_d`, `JohnsonBound.e`/`d`. Nothing is re-proved. The only re-definition is `Jqℓ`
  (LOW above), and even that is only a rescaling of `J`. **Definite verdict: extension, not fork.**
* **The PR narrowed the pre-existing Johnson bound** — **NO, the opposite.** `git diff` on
  `Basic.lean`/`Expectations.lean`/`Lemmas.lean` shows only `[Field F]` *removals*
  (`johnson_condition_weak_implies_strong`, `johnson_bound`, `johnson_bound_alphabet_free`,
  `e_ball_le_radius`, `min_dist_le_d`, `johnson_bound_lemma`) plus proof cleanups. Every statement
  is unchanged or strictly more general. No hypothesis was strengthened anywhere.
* **Consumer breakage from the generalizations** — impossible: `grep` shows the entire
  `JohnsonBound/` directory had **zero** consumers outside itself before this PR, and still does.
* **The `set_option linter.unusedFintypeInType/unusedDecidableInType false` at `Family.lean:54-55`
  hides unused instance arguments in the headline theorems** — refuted. `(session-local) r4-linter.lean`
  restates both signatures verbatim *without* the suppression and neither linter fires. (The
  file-wide suppression is also an established pattern: `SubspaceDesign.lean`, `ExtensionCodes.lean`,
  `HammingBallVolume.lean`, `ReedSolomon/{Folded,Interleaved}.lean` all do it.)
* **`plotkin_card_le_ell` is wrong / missing the `δ > 1-1/q` regime condition** — refuted. Its
  guard `q/(q-1)·(ℓ-1)/ℓ·δ > 1` is equivalent to `δ > (1-1/q)·ℓ/(ℓ-1)`, which *implies*
  `δ > 1-1/q`. Setting `D := q/(q-1)·δ`, the classical Plotkin bound `|C| ≤ δ/(δ-(1-1/q))` equals
  `D/(D-1)`, and the guard is exactly `ℓ > D/(D-1)`. The docstring's tightness witnesses check out
  (`[4,2,3]/𝔽₃`: `δ/(δ-2/3) = (3/4)/(1/12) = 9 = |C|`).
* **`singleton_bound_module` duplicates `singleton_bound_linear`** — refuted. The module version
  needs `[Finite F] [Finite A]` (it goes through `|C| = |F|^{finrank}`), while
  `singleton_bound_linear` works over any `[CommRing F] [StrongRankCondition F]`. Incomparable;
  both are used.
* **`IsMDS_iff_rate_distance` duplicates something in `Basic/MDSCode.lean`** — refuted.
  `MDSCode.lean` only has `Matrix.IsMDS` and the matrix↔code bridges; no real-valued
  rate–distance form exists. The ℕ-subtraction in `IsMDS` is safe (`finrank ≤ card ι` is proved
  and used via `Nat.cast_sub`).
* **`mds_johnson_lambda_le` is vacuous / hypotheses unsatisfiable** — refuted, see the two probes.
* **The `ℓ ≤ 1` branch of `mds_johnson_lambda_le` is a degenerate cheat** — checked the maths:
  `ℓ = ⌊1/(2ηρ)⌋₊ ≤ 1 ⟹ η > 1/(4ρ) ⟹ 1 - √ρ - η < 1 - s - 1/(4s²) < 0` since
  `max_{s∈[0,1]} 4s²(1-s) = 16/27 < 1`. Correct, and the paper's statement is equally degenerate
  there.
* **`Lambda`'s `Set.ncard` collapses to 0 on infinite lists** — true, but inherited from the
  pre-existing `listDecodable` (same `ncard` shape), and `Lambda_le_iff_listDecodable` makes them
  one notion. Not introduced by this PR; `Lambda_ne_top`'s docstring is honest about it.

---

## Clean bill (specifically checked, genuinely OK)

* **`Jqℓ` formula, character by character** vs ABF26 Def 3.1 — correct (see HEADLINE); matches
  GRS12 Ex. 7.8 and the authors' fixed `.tex`; the `(1 - 1/q)·(…)` outer parenthesisation and the
  `q/(q-1)` inner factor are both right (bbox-verified against the PDF glyph positions).
* **`Jcap`** = `1 - √(1-δ)` — exactly ABF26's `J(δ)`.
* **`johnson_bound_lambda_le_ell`** proves the paper's *conclusion* shape
  `Λ(C, J_{q,ℓ}(δ_min(C))) ≤ ℓ` over an **arbitrary finite alphabet `α`** and an arbitrary finite
  index `ι` — faithful to the paper's "any `C ⊆ Σ^n` with `|Σ| = q`". Not narrowed to
  linear/field codes. `Lambda` matches the paper's maximised `|Λ(C,δ)|` (sup over words).
* **Non-vacuity of T3.2**: `(session-local) r4-t32-content.lean` instantiates it at `q=2, n=4, δ_min=1, ℓ=2`
  giving `Λ(C, 1/2) ≤ 2`, which is **tight** (length-4 repetition code, `f = 0011`). The radicand
  guard is satisfiable across the whole interesting regime (it only bites past Plotkin).
* **Non-vacuity of `plotkin_card_le_ell`**: `(session-local) r4-t32-content.lean` instantiates it at
  `q=2, n=3, mDist=3, ℓ=3` (ambient 8 words).
* **`mds_johnson_lambda_le`** is ABF26 Cor 3.3 verbatim (`Λ(C, 1-√ρ-η) ≤ 1/(2ηρ)`, `η > 0`, ρ
  the `finrank/n` rate), and is genuinely non-vacuous: `(session-local) r4-c33-content.lean` derives
  `Λ(C, 7/16) ≤ 32` for a `[16,4]` MDS code, `(session-local) r4-rs-witness2.lean` shows such codes exist
  (`ReedSolomon.code dom 4`, `IsMDS`, `finrank = 4`, `minDist = 13`, domain exists over `ZMod 17`).
  The radius `7/16 = 0.4375` strictly exceeds the unique-decoding radius `13/32 = 0.40625`, and
  `32 ≪ |C| = |F|^4 ≥ 83521`, so the bound has real content in the list-decoding regime.
* **C3.3's proof maths independently re-derived**: `1/ℓ·(1-ρ) ≤ 2η√ρ + η²` with `ℓ = ⌊1/(2ηρ)⌋₊`
  reduces to `√ρ(1-ρ) ≤ 1` and (with the floor slack) to `s(1-s²) ≤ 1-2ηρ`, whose maximum
  `2/(3√3) ≈ 0.385 ≤ 1/2` is covered by the `2ηρ ≤ 1/2` branch condition. `domination_core` is
  the faithful Lean form of this.
* **`johnson_card_le_ell`** — the numeric core; uses the *average* distance `e B v`/`d B` (the
  standard Johnson double-counting form), and `mDist ≤ d B` is the correct direction for feeding
  in a minimum distance.
* **The T3.2 docstring's claim about `JohnsonConditionStrong` at the boundary** — verified by hand:
  denominator `= frac·δ_min·(1 - (ℓ-1)/ℓ) = frac·δ_min/ℓ > 0`, and the printed `ℓ/(ℓ-1)` factor
  would indeed have made it `< 0`.
* **`Field`-freeing of `johnson_bound_lemma`** via `remap` + `Equiv.swap` recentering: sound
  (`NeZero (card F)` derived from `2 ≤ card F`; `card (Fin (card F)) = card F` rewrite is correct).
* **`IsMDS_iff_rate_distance`** — correct; `Nat.cast_sub` guarded by the proved `finrank ≤ card ι`;
  the `k = 0` exclusion in `mds_johnson_lambda_le` correctly uses `Code.dist_le_card`
  (`Code.dist : ℕ`, so a singleton code has `dist = 0`, not `⊤`).
* **`ArkLib.lean` registration** — `JohnsonBound.Family` is imported at `ArkLib.lean:80`.
* **No `sorry` / no non-standard axioms** in any file in scope (`grep` clean; the build is green
  at `ffa0733a`).
