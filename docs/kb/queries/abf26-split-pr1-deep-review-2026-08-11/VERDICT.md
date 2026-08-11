# PR 701 — consolidated verdict (2026-08-11)

Head reviewed: `103ffe89a`. Merge base: `a4ac38e0e`. Ground truth: the pinned author TeX for
*Open Problems in List Decoding and Correlated Agreement* (`ABF26`), the cited source papers, the
unsplit `feat/abf26-plan` branch, and the external proximity-prize repository.

## Headline

**No blocker. No soundness defect. No false theorem. No new admit and no new axiom.** The PR is
sound and is a genuine long-term contribution. One HIGH and about fourteen MEDIUM findings, every one
mechanical: documentation accuracy, one regime-vacuity, one surplus hypothesis, and duplicated proof
bodies.

## Gate results

| Gate | Result |
|---|---|
| `validate.sh` | PASS — 4220 jobs, no `ArkLib/Data` non-sorry warnings, 347 umbrella imports, docs integrity and KB lint green |
| `validate.sh --lint` | PASS with **zero delta** — 729 style hits at base, 729 at head, identical multiset; **no hit lands on a line this PR adds**; all new files clean |
| `validate.sh --docs` | PASS — `ArkLib:docs` builds |
| `lake exe axiomsweep` | 8440 declarations across 348 modules, **0 non-standard axioms** |
| Headline theorems | every one exactly `[propext, Classical.choice, Quot.sound]` |
| New `sorry` | **none.** The only `sorry`-carrying declaration in any touched file is the pre-existing `Fin.sumCases`, which has **zero consumers** in either tree, so its `sorryAx` cannot propagate |
| New `axiom` / `autoImplicit` / `native_decide` | none |
| Docstring coverage on new files | 112/114 |
| Long-file cap | no file in this PR approaches 1500 lines; the sole over-cap file in the tree has a pre-existing opt-out |

## Review questions, answered

**Coverage against the unsplit branch is complete.** All 250 data-layer declarations absent here
partition cleanly: 148 in ten whole files belonging to later splits, 62 in stale pre-`#497`
rational-function work that `main` has already superseded, 2 advertised deletions, and 38 benign
residue (superseded primed lemmas, de-duplication replacements, dropped paper-shape wrappers, the
removed tautological erasure API, and dead zero-consumer declarations). **No accidental gaps, no
protocol or framework leakage, and no statement weaker here than on the unsplit branch.**

**Statements are correct and faithful.** A reverse audit from the sources toward the Lean found
nothing weaker, distorted, or illegitimately absent. Every departure from the printed paper is either
a documented strengthening or a repair of a place where the paper is provably false, each recorded
with a counterexample.

**Nothing is vacuous or weakened in a dangerous way.** Non-vacuity was established positively, by
compiling satisfying instances of the headline theorems. Two qualifications, both below: one
regime-vacuity (MEDIUM-1) and one benign hypothesis-strengthening of pre-existing STIR statements
(MEDIUM-4).

**Reuse is mostly exemplary** — `qEntropy` renormalises Mathlib's `Real.qaryEntropy` rather than
reimplementing it, so the whole continuity/monotonicity/concavity API transports by one division;
`disagreementCols` is net de-duplication. Against that, roughly 90 lines of duplicated *proof bodies*
and three Mathlib forks remain (MEDIUM-5 through MEDIUM-8, MEDIUM-12, MEDIUM-13).

**The external prize repository is safe.** `Lambda`'s move from `Set.ncard` to `Set.encard` runs in
the protective direction: `ncard` silently collapsed an infinite close-codeword set to `0`, which
would have made a safety claim satisfiable by junk over an infinite alphabet. At the finite instances
the prize uses, the two agree exactly, so previously certified figures still certify the same
propositions. The closed-ball convention is unchanged, and every prize-relevant declaration lies
inside the prize's own three-axiom whitelist. Note the prize cannot yet build against this branch at
all — its imports target the later splits — so build compatibility is assessable only there.

## Leaderboard-critical constants, explicitly verified

- `J_{q,ℓ}`'s `(ℓ−1)/ℓ` factor: checked against the pinned TeX, the published PDF, and
  Guruswami–Rudra–Sudra Exercise 7.8. The Lean follows the corrected TeX; the PDF's inverted
  `ℓ/(ℓ−1)` was **not** copied.
- `ABF26` Theorem 3.2 and Corollary 3.3 (`1/(2ηρ)`): match the TeX and are **proved in-tree**, not
  transcribed. Corollary 3.3 uses the paper's constant rather than the sharper classical
  `1/(2η√ρ)`, so downstream numeric anchors are not poisoned.
- Theorem 2.18's profile `τ(r) = s·ρ/(s−r+1)` on `[1,s]`, else `1`: re-derived from the `GK16`
  source; substituting it into the paper's Theorem 3.4 reproduces Corollary 3.5's printed radius and
  list size exactly, confirming it is the profile the paper's own numerics consume.

## Findings

Items marked **[fixed]** were remediated in this PR; see § *Remediation applied*.

### HIGH-1 — the Johnson-radius de-duplication was claimed complete but was not **[fixed]**

`docs/kb/papers/Joh62.md` recorded "reduce the three in-tree copies of the Johnson radius to one" as
**Done**, but two byte-identical definitions remained in the same namespace: `JohnsonBound.J'` in
`JohnsonBound/Lemmas.lean` and `JohnsonBound.J` in `JohnsonBound/Basic.lean`. It had gone from three
copies to two, not to one. `J'` was pre-existing, so this PR did not introduce the duplicate — but it
refactored this exact area and then asserted completion in newly committed documentation.

Correction to an earlier draft of this review, recorded because the error is instructive: `J'` was
first reported as having zero consumers. That was wrong. `johnson_e_div_ne_J` uses `J'` **unqualified**
in both its hypothesis and its conclusion, which a search for the qualified `JohnsonBound.J'` cannot
match. Moreover `Basic.lean` *imports* `Lemmas.lean`, so `J'` was the upstream definition and Basic's
`J` the downstream duplicate — the reverse of the initial diagnosis. The downstream copy typechecked
against the upstream one only because the two constants are delta-definitionally equal, which was the
real smell.

### MEDIUM-1 — characteristic-zero fields were silently excluded, making the multiplicity half of Theorem 2.18 vacuous over ℚ, ℝ and ℂ **[fixed]**

`ReedSolomon/Multiplicity.lean` guarded five declarations with the bare `k ≤ ringChar F`, and
`SubspaceDesign.lean` did the same for `um_is_subspaceDesign_gk16`. Since `ringChar F = 0` in
characteristic zero, that hypothesis forces `k = 0`, so `pow_dvd_of_eval_iterate_derivative_eq_zero`,
`umEvalOnPoints_domRestrict_injective`, `dim_umCode`, `dim_umCode_eq_min` and the headline theorem —
stated with only `[Field F]`, no finiteness — all degenerated to the trivial case over those fields.
Nothing was false, and the material was fully contentful in characteristic `p`.

Three reviewers found this independently. The sibling `ClassicalWronskian.lean` in the same PR
already used the correct disjunction at five sites, and `SubspaceDesign.lean` already injected
`Or.inr hchar` into it — so the weaker hypothesis was all the proofs ever needed. This was a
half-applied fix: an earlier session added the disjunction to the Wronskian criterion without
propagating it to the multiplicity layer.

### MEDIUM-2 — two shipped theorems carried a provably surplus `IsSystematic` hypothesis **[fixed]**

`extensionEncode_comp_algebraMap_of_isSystematic` and
`mem_extensionCode_comp_algebraMap_iff_of_isSystematic`, both advertised under *Main statements*,
assumed systematicity unnecessarily. For any presentation `φ_j(ψ x) = x · φ_j(1)`, so the `j`-th
coordinate row of an embedded message is the rescaling `φ_j(1) • v`; the forward direction follows by
scaling with `φ_j(1)⁻¹` at any `j` with `φ_j(1) ≠ 0`, and one such `j` exists because `1 ≠ 0`. Both
docstrings asserted the opposite, claiming the reverse direction is "where systematicity does real
work … it pins them to `0`". This is also an observation about the source: the remark following
`ABF26` Definition 2.20 states the identity only for systematic presentations.

### MEDIUM-3 — two docstrings described the superseded PDF rather than the pinned TeX **[fixed]**

`Probability/Combinatorial.lean` and `Probability/Instances.lean` stated that the proof of Lemma 6.12
applies Claim B.1 "exactly once", that the second counting step is "a plain pigeonhole" requiring
full injectivity, and that substituting a second Claim B.1 application would prove something strictly
weaker than the printed bound. The pinned TeX reads "Applying \Cref{claim:distinct} **again**" and
derives the printed bound from that second application; the unsplit branch's consumer does exactly
that. There is no pigeonhole step in the current TeX. The published PDF genuinely does use one
application plus a pigeonhole and prints the weaker `|Λ|/(|F| + |Λ| − 1)`; an earlier fix corrected
the wording toward the PDF and thereby away from ground truth.

### MEDIUM-4 — `listDecodable` gained a finiteness conjunct, strengthening pre-existing STIR hypotheses (accepted)

The definition moved from `∀ y, ncard ≤ ℓ` to `∀ y, Finite ∧ ncard ≤ ℓ`. Because it occurs only in
hypothesis position in the pre-existing STIR files, those statements are formally weaker. **Accepted**:
it is a genuine correctness fix, since the old definition was satisfied by an infinite point list
(`Set.ncard` returns `0` there), and it is a no-op under the `[Fintype F]` every consumer uses. Worth
a line in the PR description for the STIR and WHIR owners, and a `listDecodable_iff_ncard_le`
recovery lemma would make the transition one step.

### MEDIUM-5 to MEDIUM-8 — duplicated proof bodies (deferred)

Roughly 90 lines, none of them wrong. The folded-Reed-Solomon and multiplicity halves of
`SubspaceDesign.lean` are the same proof with three names swapped (~200 lines across several
blocks); `U.det ≠ 0` is hand-proved three times where `(bas.isUnit_det cb).ne_zero` suffices; the
base-change step is hand-proved three times where `Basis.sum_toMatrix_smul_self` with `map_sum`
gives it in two lines; and the `minDist C ≤ JohnsonBound.d B` block appears three times inside
`JohnsonBound/Family.lean`, two of them a fifteen-line exact textual match. Natural extractions are a
"lift a subspace through an injective encoder" lemma and a "root count implies `IsSubspaceDesign`"
lemma. These were missed by the earlier review because it audited declarations rather than proof
bodies.

### MEDIUM-9 — the KB catalog was not updated for ten new paper pages **[fixed]**

`docs/kb/index.md` was unchanged despite ten new non-stub paper pages and a new query directory,
against the contract in `docs/kb/README.md`. The series' primary paper was absent from the catalog.
`scripts/kb/lint.py` does not check this, which is why validation stayed green.

### MEDIUM-10 — KB paths appear inside Lean sources (deferred)

Five new occurrences, including two in `SubspaceDesign.lean` pointing at a dated review-artifact
directory. This is against the convention that Lean sources cite papers, not KB pages. Comparable
violations pre-exist elsewhere in the tree, so this is not unique to this PR.

### MEDIUM-11 — `ClassicalWronskian.lean` cited a source four times with no references section **[fixed]**

It also lacked *Main definitions* and *Main statements*. `CONTRIBUTING.md` requires the references
section, its sibling `FoldedWronskian.lean` has all four, and this file carries the multiplicity half
of Theorem 2.18.

### MEDIUM-12 and MEDIUM-13 — Mathlib forks and an unbridged Mathlib TODO (deferred)

`natDegree_comp_C_mul_X_le` is a four-line corollary of Mathlib's `natDegree_comp_le` and says so
nowhere; `sum_rootMultiplicity_le_natDegree` is restricted to `[Field F]` though the identical proof
compiles over `[CommRing F] [IsDomain F]`, which matters for an upstreaming candidate. Separately,
Mathlib's `Polynomial/Wronskian.lean` carries a literal TODO to define the Wronskian for an `n`-tuple
of polynomials; `classicalWronskian` is exactly that and agrees with Mathlib's two-argument
`wronskian` on the nose, but no lemma connects them, so Mathlib's `wronskian_*` API is unreachable at
`σ = 2`. Both Wronskian files are pure generic polynomial algebra yet sit outside `ToMathlib/`,
against the policy stated in one of their own docstrings. Relatedly,
`pow_dvd_of_eval_iterate_derivative_eq_zero` is the positive-characteristic complement of Mathlib's
`lt_rootMultiplicity_iff_isRoot_iterate_derivative` and lives in a Reed-Solomon namespace despite
saying nothing about Reed-Solomon codes.

### MEDIUM-14 — stacking drift for the later splits (partly fixed)

The unsplit branch's consumer of the folded-Reed-Solomon Theorem 2.18 passes an `ω ≠ 0` argument this
PR now derives internally, and ascribes the profile `(k/n)/(s−r+1)` where this PR concludes
`s · alphabetRate/(s−r+1)`. **This PR's form is the corrected one** — it tracks saturated dimension,
whereas the older form is right only in the unsaturated regime — so the consumer, not this PR, must
adapt; the bridge additionally needs `k ≤ s·|ι|`, which that consumer does not currently assume. A
`τ`-monotonicity lemma was missing; it is now supplied here so the later split need not reopen this
file. Remaining mechanical drift for those splits: two renames for the Claim B.1 lemma's
`tsum`-shaped versus `Pr`-shaped forms, and a two-line `intro` swap from an `Admissible` conjunct
reordering.

## Remediation applied

All changes keep every conclusion intact and only ever remove or weaken hypotheses.

1. **MEDIUM-1** — the characteristic guard became `ringChar F = 0 ∨ k ≤ ringChar F` across the five
   multiplicity declarations and the headline theorem, mirroring the sibling Wronskian file. The
   hypothesis was load-bearing in exactly one place, the unit-ness of `d!`; that step now splits on
   the disjunction, taking `CharZero` in the zero branch. The call site passing `Or.inr hchar` now
   passes `hchar` directly, and the docstring that called this "the sharp source condition" was
   corrected. A compiled probe witnesses contentfulness over ℚ: `finrank ℚ (umCode domQ 3 2) = 3` at
   `k = 3`, together with the saturated form, encoder injectivity, and the headline theorem — and the
   positive-characteristic path still works.
2. **MEDIUM-2** — the surplus hypothesis was dropped and both theorems renamed to
   `extensionEncode_comp_algebraMap` and `mem_extensionCode_comp_algebraMap_iff`. The proofs became
   shorter as well as more general. Both docstrings were rewritten around the `φ_j(ψ x) = x · φ_j(1)`
   identity, and the module docstring gained a ledger entry recording the source's surplus
   assumption, in the voice it already uses for comparable observations. `IsSystematic` itself and its
   coordinate form are retained as the paper-faithful API.
3. **MEDIUM-3** — both passages now describe two Claim B.1 applications, naming which lemma supplies
   each collision bound, and flag the TeX-versus-PDF divergence using the convention already used
   elsewhere in the tree. Prose only.
4. **HIGH-1** — the duplication is genuinely resolved, in the direction the dependency graph
   dictates: the upstream definition in `Lemmas.lean` is now named `J` and the downstream duplicate in
   `Basic.lean` is deleted, leaving one `JohnsonBound.J` with the same name, namespace and body. No
   statement changed. Two prose pointers stale-ified by the move, and the trailing clause in
   `Joh62.md` naming the old location, were corrected.
5. **MEDIUM-9** — `docs/kb/index.md` now lists all ten new paper pages with descriptions drawn from
   each page's own summary, plus the review directories.
6. **MEDIUM-11** — `ClassicalWronskian.lean` gained *Main definitions*, *Main statements* and
   *References*, formatted as in its sibling.
7. **MEDIUM-14** — `IsSubspaceDesign.mono_tau` was added: a `τ₁`-design is a `τ₂`-design for any
   pointwise-larger profile, since the design bound is monotone in `τ r`. Stated without a sign
   condition on either profile.

Re-validated after remediation: `validate.sh` green at 4220 jobs with the `ArkLib/Data` zero-warning
gate intact, and all fourteen touched or headline declarations confirmed at exactly
`[propext, Classical.choice, Quot.sound]`.

Deliberately **not** changed, so a later reader can distinguish deferral from oversight: MEDIUM-5
through MEDIUM-8 (proof-body de-duplication), MEDIUM-10 (KB paths in Lean sources), MEDIUM-12 and
MEDIUM-13 (Mathlib bridges and file relocation), and the residual consumer-side items of MEDIUM-14,
which belong to the later splits. MEDIUM-4 is accepted as a correctness fix and needs only a note to
the STIR and WHIR owners. One consequence of remediation to note: the coordinate form of
`IsSystematic` now has no consumer, its only two users having been generalised away.

## Source-side defects found

Each is guarded in the Lean already; they are recorded here for the paper's authors.

- **Theorem 2.18 omits the generator condition on `ω`** that `GK16`'s Lemma 12 requires; the Lemma is
  stated there for a generator of `F*`. Refuted as printed over `𝔽₁₀₁` with `s = 2`, `ω = −1`,
  `k = 3`.
- **Definition 2.14 permits `0` in the evaluation domain**, which makes Theorem 2.18 false even with
  the generator condition. Refuted over `ZMod 5` with domain `(0,1)`, `s = 3`, `k = 2`, `ω = 2`. The
  `GK16` construction excludes the zero point.
- **Lemma 2.17 is false at `r = 0`**, where the profile is unconstrained; a degenerate code with
  `n = 2` refutes it.
- Theorem 2.18 asks `char > k` while Definition A.7 asks `char ≥ k`, inconsistently in both the TeX
  and the PDF. The `≥` form is correct and is what the Lean takes.
- Smaller items: Definition 2.14 permits `ω = 1`, which breaks the folded distance formula (`ZMod 11`,
  `s = 2`, `k = 2`: true distance 4 against a predicted 5); Definition 2.5's minimum admits equal
  arguments; Definition 3.1 admits `ℓ = 0` and so a division by zero; Definition 2.13 tacitly assumes
  a divisibility.
- The published PDF's Definition 3.1 prints the inverted `ℓ/(ℓ−1)`; the TeX was corrected to
  `(ℓ−1)/ℓ`, and the Lean follows the corrected form.

## Unrelated to this PR

- `validate.sh --axioms` is red on `main` as well, from four newly tainted lattice declarations
  introduced upstream of this branch's merge base. A `main`-side baseline refresh is owed.
- `Probability/Combinatorial.lean` has no in-repo consumer yet. This is disclosed in its own module
  docstring, and its intended consumer lands in a later split.
