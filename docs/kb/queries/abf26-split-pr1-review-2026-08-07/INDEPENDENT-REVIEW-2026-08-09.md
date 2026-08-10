# PR #701 independent adversarial review — 2026-08-09

## Verdict

**Request changes.** No critical false theorem, vacuous headline theorem, proof cheat, new
`sorryAx`, or non-standard axiom was found in the complete current filesystem candidate.
Nevertheless, PR #701 is not ready to merge. The remaining findings affect delivery integrity,
the accuracy of ABF26 completeness claims, an exported list-decoding predicate, the meaning of
rate for module alphabets, and the generality and placement of reusable APIs.

Severity below is counted by finding cluster:

- **1 merge blocker**: the published branch and the locally validated candidate are different,
  the PR conflicts with current `main`, generated files violate repository policy, and the local
  index is not commit-coherent;
- **1 high**: ABF26 erasure-correction coverage is materially overclaimed;
- **5 medium**: infinite-alphabet `listDecodable`, module-alphabet rate, the scope of the MDS
  Johnson corollary, unnecessarily strong algebra assumptions, and a specialized/misplaced
  Hamming reindexing lemma;
- **4 low clusters**: the omitted `ell = 1` Johnson boundary, stale source-audit records,
  `coord` reducibility documentation, and citation formatting.

The formalized results that are actually present appear sound in the portions audited. The
corrected Johnson factor, folded-code admissibility strengthening, generator and degree
hypotheses in the GK16 argument, `r >= 1` repair to the subspace-design lower bound, folded-RS
block distance, extension/interleaving Hamming isometry, entropy reuse, probability results,
and Claim B.1 all survived fresh adversarial checks.

## Review target and state separation

This distinction is essential because the checkout contains pending review fixes.

| Object | Revision/state reviewed |
| --- | --- |
| Published GitHub PR | `Verified-zkEVM/ArkLib#701`, head `1d9d57dace42aa1cc1ccf86fdac419dfef610127` |
| PR base at review time | `main`; fetched `origin/main` was `5fea8abf971496f54bcca2b98c029581d5b31658` |
| Original merge base | `4f386913` |
| GitHub integration state | `mergeable: CONFLICTING`, `mergeStateStatus: DIRTY`, review required |
| Complete local candidate | Published head plus the staged and unstaged review fixes visible on 2026-08-09 |

Findings explicitly say whether they concern the published PR, the intended complete local
candidate, or the staging arrangement. A successful build of the complete filesystem does not
show that the Git index or the published branch is buildable.

## Method

The lead pass and three independent concurrent passes covered:

1. statement/reference fidelity against the current ABF author source in
   `~/ef-millenium/ef-millenium.tex` and the primary copies under `~/abf26-refs/`;
2. soundness, vacuity, edge cases, theorem assumptions, and axiom dependencies, including
   session-local compiled Lean probes;
3. reuse of existing ArkLib and Mathlib concepts, abstraction boundaries, universe behavior,
   namespace placement, and algebraic generality;
4. the published PR diff, current local fixes, generated-file policy, merge behavior against
   current `origin/main`, routine validation, documentation generation, import generation, and
   style-lint attribution.

The reference pass checked ABF26 L2.1; D2.2, D2.4-D2.5, D2.8, D2.13-D2.16, L2.17; the folded
half of T2.18; D2.19-D2.21; D3.1, T3.2, C3.3; D6.4/L6.5; Appendix A D6-D7; and Claim B.1. It
also checked the relevant supplied copies of GG25, GK16, GR08, BCFW25, GX13, and GW13/KSY14.
The original Joh62 paper was not present in the supplied reference tree, so the Johnson theorem
was checked against ABF26's statement and the in-tree combinatorial derivation, not independently
against Joh62.

No repository file was changed by the review passes themselves. This report is the requested
review artifact.

## Findings

### B1 — Merge blocker: the deliverable being validated is not the published PR

The published PR is still at `1d9d57da`; the fixes validated in the complete local worktree have
not been pushed. GitHub reports the PR as conflicting with current `main`.

The committed PR diff contains all four generated knowledge-base outputs:

- `docs/kb/_generated/declarations.json`;
- `docs/kb/_generated/dedup-report.md`;
- `docs/kb/_generated/lean-citations.json`;
- `docs/kb/_generated/references.json`.

This contradicts [`docs/wiki/generated-files.md`](../../../wiki/generated-files.md), which says
ordinary feature PRs must not commit `docs/kb/_generated/**`. A `git merge-tree` analysis against
current `origin/main` found textual conflicts only in `declarations.json`, `dedup-report.md`, and
`lean-citations.json`; `references.json` auto-merges but remains policy-invalid. Restoring all four
to `origin/main` removes this source of conflict.

The local review-fix staging is also not commit-coherent. `ArkLib.lean` and five new ToMathlib
modules are staged, while the removals/import rewires from their former source modules are
unstaged. In particular:

| Staged declaration | Duplicate still present in the indexed `HEAD` source |
| --- | --- |
| `Polynomial.natDegree_comp_C_mul_X_le` in `ToMathlib/Polynomial/CompositionDegree.lean` | `Data/Polynomial/FoldedWronskian.lean` |
| `Polynomial.X_pow_card_sub_one_sub_C_irreducible` in `ToMathlib/FieldTheory/Kummer.lean` | `Data/Polynomial/FoldedWronskian.lean` |
| `Polynomial.sum_rootMultiplicity_le_natDegree` in `ToMathlib/Polynomial/RootMultiplicity.lean` | `Data/CodingTheory/SubspaceDesign.lean` |

Committing the index alone would make the umbrella import encounter duplicate fully-qualified
declarations. The complete filesystem is coherent; the index is not.

**Required action:** restore generated KB output to `main`, stage each relocation and its old-site
removal/import rewire atomically, rebase, push the exact validated tree, and rerun validation on
the pushed commit.

### H1 — High: ABF26 D6.4/L6.5 erasure-correction coverage is overclaimed

The published PR description says `Erasure.lean` supplies `SupportsErasureCorrection` for ABF26
Definition 6.4 and proves `additive_code_supports_erasure_correction_grs12` for Lemma 6.5. The
current corrected file deliberately supplies neither declaration. Its module documentation says
that the algorithm, failure behavior, and cost model are not formalized, and the file proves only
the metric uniqueness statement `eq_of_consistent_with_erased`.

The distinction is substantive. In the ABF author source:

- D6.4 (`~/ef-millenium/ef-millenium.tex:2244`) requires a deterministic algorithm, correct
  recovery when the unique completion exists, failure otherwise, and an operation bound;
- L6.5 (`~/ef-millenium/ef-millenium.tex:2254`) says every additive code supports correction in
  `O((s*n)^3)` field operations.

The earlier cost-free existential predicate was provable for every code by classical choice, so
it encoded none of the reference's algorithmic content. Its local removal is correct. The
remaining uniqueness lemma is useful and sound, but is not D6.4 or L6.5.

The PR body is stale in other material respects as well: it claims exactly two new `sorry`s in
`SubspaceDesign.lean`, whereas the current results are proved, and its job/declaration/reviewer
statistics describe an earlier revision.

**Required action:** either formalize an appropriate algorithm/cost model and the additive-code
result, or mark D6.4/L6.5 missing and remove every PR/audit claim that they land in this split.

### M1 — Medium: `listDecodable` is vacuous on infinite alphabets

`ListDecodable.listDecodable` is exported without `[Finite F]` and uses `Set.ncard`:

```lean
def listDecodable (C : Code ι F) (r : ℝ) (ℓ : ℝ) : Prop :=
  ∀ y : ι → F, (closeCodewordsRel C y r).ncard ≤ ℓ
```

`Set.ncard` is zero for an infinite set. The following probe compiled in the current tree:

```lean
import ArkLib.Data.CodingTheory.ListDecodability

open ListDecodable

example : listDecodable (Set.univ : Code (Fin 1) ℚ) 1 0 := by
  intro y
  simp [closeCodewordsRel, relHammingBall, listDecodable]
```

Every radius-one list here is all of `ℚ`, so the mathematical list is infinite rather than
empty. `uniqueDecodable`, defined through `listDecodable`, inherits the defect. The declaration's
docstring claim that the cardinality is “a natural number anyway” is false at this generality.

The pending local change correctly defines the new `Lambda` using `Set.encard`; a separate probe
shows the same universal rational code has `Lambda = top`. All new bridges from `Lambda` to the
legacy predicate require `[Finite F]`, and all inspected STIR consumers use finite fields, so no
new headline theorem relies on the collapse.

**Required action:** make the legacy predicate honest—preferably through `encard`/an extended
bound, or by requiring finiteness at the declaration boundary. A warning on a proposition that is
false to its intended semantics is not enough.

### M2 — Medium: `LinearCode.rate` is not ABF26 rate for `ModuleCode` alphabets

ABF26 D2.5 defines

```text
rho(C) = log_(|Sigma|)(|C|) / n.
```

For an `F`-linear code over block alphabet `Sigma = F^s`, this is
`finrank_F(C) / (s*n)`. The polymorphic ArkLib declaration instead computes
`finrank_F(C) / n` for every `ModuleCode iota F A`.

This compiled counterexample makes the mismatch concrete:

```lean
import ArkLib.Data.CodingTheory.Basic.LinearCode

example : LinearCode.rate
    (⊤ : Submodule (ZMod 2) (Fin 1 → Fin 2 → ZMod 2)) = 2 := by
  rw [LinearCode.rate, LinearCode.dim, LinearCode.length,
    (Submodule.topEquiv :
      (⊤ : Submodule (ZMod 2) (Fin 1 → Fin 2 → ZMod 2)) ≃ₗ[ZMod 2]
        (Fin 1 → Fin 2 → ZMod 2)).finrank_eq]
  rw [Module.finrank_pi_fintype]
  simp
```

Here `n = 1`, the alphabet has cardinality four, and the code has cardinality four, so ABF26's
rate is `log_4(4) = 1`; the ArkLib API returns `2`.

This definition predates the PR, but the PR newly advertises generalized module alphabets and
maps D2.5 directly to `LinearCode.rate` in the audit and coding-theory conventions. That makes the
legacy meaning newly misleading. The subspace-design theorem explicitly uses the correct
`finrank/(s*n)` normalization, so no inspected theorem becomes false through this issue.

**Required action:** distinguish base-field dimension rate from alphabet-normalized rate in the
API and documentation. Reasonable options are to restrict the existing `rate` notation to
field-alphabet `LinearCode`, rename the current module quantity, or add a normalized finite-module
alphabet rate and use it for ABF statements.

### M3 — Medium: the theorem labeled ABF26 Corollary 3.3 is only a field-linear instance

`JohnsonBound.mds_johnson_lambda_le` is labeled “ABF26 Corollary 3.3” and “fully proven,” but
quantifies over `C : LinearCode iota F`. ABF26 states the corollary for every MDS code under its
arbitrary-alphabet definition and immediately names interleaved Reed-Solomon codes as an important
included class. Those codes have alphabet `F^m`, so the current theorem cannot express the
motivating instance.

The module docstring itself acknowledges that the non-field alphabet and general rate-distance
bridge are deferred. The underlying alphabet-generic Johnson theorem appears sound; the problem
is completeness labeling and the absent general-alphabet MDS bridge.

**Required action:** either generalize the MDS corollary to the paper's alphabet/cardinality
form—covering the module-alphabet/interleaved case—or consistently call the present theorem a
field-linear specialization and record Corollary 3.3 as partial.

### M4 — Medium: new foundational APIs retain unnecessarily strong algebra assumptions

Session-local probes compiled the exact proof bodies under these weaker assumptions:

| Declaration | Current assumption | Compiled sufficient assumption |
| --- | --- | --- |
| `ReedSolomon.mem_map_degreeLT_one_iff_mem_code` | `[Field F]` | `[CommSemiring F]` |
| `ReedSolomon.Folded.frsCode` and elementary membership/collapse API | `[Field F]` | definition needs the same ambient semiring structure as `frsEvalOnPoints` |
| `Polynomial.natDegree_comp_C_mul_X_le` | `[Field F]` | `[Semiring F]` |

The strong assumption on the shared encoder-collapse lemma unnecessarily forces both the folded
and multiplicity `s = 1`/`m = 1` corollaries to fields. `frsCode` is simply
`degreeLT.map frsEvalOnPoints`, and its documentation already says only ambient algebra is needed.

**Required action:** weaken code construction, membership, and collapse declarations; retain
fields only for distance, dimension, admissibility, Kummer, and other genuinely field-dependent
results.

### M5 — Medium: `reidx_hammingDist` is specialized and placed in the Johnson module

`CodingTheory.reidx_hammingDist` hardcodes an equivalence
`e : iota equiv Fin (Fintype.card iota)`. The same proof compiled for arbitrary finite index types
and `e : iota equiv iota'`. The lemma has four real consumers in `JohnsonBound/Family.lean`, so
this is not an unused-code inference.

Mathlib's nearby `hammingDist_comp` transports alphabet values through pointwise injections; it
does not transport the coordinate index. No existing arbitrary index-equivalence transport was
found in Mathlib or ArkLib.

**Required action:** generalize the signature and place the result with generic Hamming facts in
`Basic/Distance.lean` or a suitable ToMathlib module.

### L1 — Low: Theorem 3.2 omits the `ell = 1` boundary while claiming exact scope

The docstring for `johnson_bound_lambda_le_ell` says the result has no side condition “exactly as
in the paper,” then acknowledges that the paper includes `ell >= 1` while the Lean theorem assumes
`2 <= ell`. The missing `ell = 1` case is true and elementary: `J_(q,1)(delta) = 0`, and a
radius-zero list contains at most one distinct word.

**Required action:** add the boundary case or weaken the “exactly/no side condition” claim.

### L2 — Low: two source-audit records are stale

- `docs/kb/sources/GX13/metadata.yml` classifies GX13 as an article and says the bibliography has
  a different title. The primary source is a STOC 2013 proceedings paper and the current BibTeX
  entry is already corrected to `@inproceedings` with the matching title.
- `docs/kb/papers/GW13.md` says `SubspaceDesign.lean` still claims the derivative operation is
  missing. The current module says derivative evaluation exists; the missing item is the
  multiplicity-Wronskian analogue.

### L3 — Low: `ExtensionFieldPresentation.coord` is not the advertised abbreviation

`ExtensionCodes.lean` calls `coord` an abbreviation and says the abbreviation exists only for the
paper-shaped statement. The declaration is a `noncomputable def`. It is `rfl`-equal to
`Basis.coord`, but `def` and `abbrev` deliberately have different reducibility behavior.

**Required action:** make it an actual `abbrev` or describe it as a thin definition.

### L4 — Low: several new References sections do not follow project format

`CONTRIBUTING.md` requires
`* [Author Last Name, First Initial, *Title*][citation_key]`. Nonconforming new sections remain in:

- `Data/CodingTheory/ExtensionCodes.lean`;
- `Data/CodingTheory/JohnsonBound/Family.lean`;
- `Data/CodingTheory/ReedSolomon/Folded.lean`;
- `Data/CodingTheory/ReedSolomon/Interleaved.lean`;
- `Data/CodingTheory/ReedSolomon/Multiplicity.lean`;
- `Data/CodingTheory/SubspaceDesign.lean`;
- `Data/Polynomial/FoldedWronskian.lean`.

The BibTeX keys exist, so this is formatting rather than a dangling reference.

## Soundness and source-fidelity results that passed

The following are positive results of actual checks, not inferences from successful compilation:

- `Jqell` uses the corrected `(ell-1)/ell` factor. This matches the current author source and the
  standard monotonicity/limit behavior; the older PDF's inverted factor is a documented source
  defect.
- The Johnson proof handles both the nonnegative-radicand regime and the negative-radicand
  Plotkin corner. The headline theorem is not secretly conditional on the square-root guard.
- The MDS proof derives positive dimension/rate where it divides by the rate.
- Folded-RS minimum distance is a block-Hamming statement and uses injectivity of all folded
  evaluation points, rather than silently reasoning in the scalar metric.
- The strengthened `Admissible` predicate's intra-orbit and inter-orbit clauses are load-bearing.
  They rule out `omega = 1` and `0`-domain counterexamples admitted by literal ABF D2.14.
- The folded subspace-design proof derives `k <= |F|-1` before invoking the folded-Wronskian
  nonvanishing theorem; the generator hypothesis and degree restriction are not ornamental.
- The profile is the source-correct `k/n/(s-r+1)`, equivalently
  `s*rho/(s-r+1)` for `rho = k/(s*n)`.
- The `r >= 1` restriction in the L2.17 lower bound is necessary: the source's `r = 0` statement
  leaves `tau 0` unconstrained and is false.
- `lambda_extensionCode_eq_lambda_interleaved` is backed by a coordinatewise Hamming isometry,
  not only a cardinality coincidence.
- The multiplicity encoder uses ordinary iterated formal derivatives, matching ABF Appendix A
  under the documented characteristic condition.
- Claim B.1's fiber-counting/Cauchy-Schwarz proof, q-entropy normalization, Hamming-ball volume
  bridge, dot-product probability, uniform product probability, Schwartz-Zippel edge cases, and
  relative-distance/minimum-distance bridges checked out.
- The pending `Lambda` definition uses `Set.encard`, so infinite lists produce `top`; all bridges
  to the older `ncard` predicate carry finiteness.

Reuse checks also confirmed that q-entropy delegates to Mathlib, interleaving finrank is handled by
a general theorem rather than an RS-only proof, folded/multiplicity collapse proofs share one
encoder-generic lemma, erasure uniqueness reuses the generic disagreement theorem, and the new
Kummer/determinant/root-multiplicity/finite-dimensional/composition helpers have Mathlib-only
dependency direction with no exact Mathlib duplicate found.

## Axiom, admission, and vacuity validation

`#print axioms` probes were run for the headline declarations, including:

- `johnson_bound_lambda_le_ell` and `mds_johnson_lambda_le`;
- the RS Johnson consumer;
- `minDist_frsCode` and `frs_is_subspaceDesign_gk16`;
- folded-Wronskian nonvanishing;
- `subspaceDesign_tau_lower`;
- `lambda_extensionCode_eq_lambda_interleaved`;
- Claim B.1;
- dot-product and Schwartz-Zippel probability bounds;
- the Hamming-ball volume and q-entropy bridges;
- erasure uniqueness and minimum/relative-distance bridges.

Each reported only the standard dependencies
`[propext, Classical.choice, Quot.sound]`. No audited headline declaration depended on
`sorryAx`. Focused searches found no new `axiom`, `unsafe`, `native_decide`, or proof-term `sorry`
in this contribution. Pre-existing admits elsewhere in ArkLib and dependencies remain outside the
scope of this claim.

The principal compiled negative probes were:

1. infinite-alphabet `listDecodable` accepts an actually infinite list at bound zero;
2. module-alphabet `LinearCode.rate` can exceed one and differs from ABF's alphabet-normalized
   rate;
3. weaker-assumption versions of the encoder collapse, folded construction, and polynomial
   composition-degree lemma compile;
4. arbitrary coordinate-equivalence Hamming transport compiles.

These probes establish concrete semantic/API facts; they are not based on current-use searches.

## Build and integration validation

### Complete current local filesystem

| Check | Result |
| --- | --- |
| `./scripts/validate.sh` | Passed; project build completed with 4,202 jobs, `ArkLib/Data` zero-warning gate passed, imports current, docs integrity and KB lint passed |
| `./scripts/validate.sh --docs` | Passed; documentation build completed with 8,566 jobs |
| `./scripts/check-imports.sh` | Passed |
| `git diff --check origin/main...HEAD` | Passed |
| `git diff --check` | Passed |

### Current-main merge simulation

A temporary worktree was based on `origin/main` `5fea8abf`. The PR was merged without committing,
the generated files were restored to the main versions, and every pending local review fix except
the generated outputs was overlaid. This exact combined filesystem then passed:

| Check | Result |
| --- | --- |
| `./scripts/validate.sh` | Passed; 4,202 jobs |
| `./scripts/validate.sh --docs` | Passed; 8,574 jobs |

This shows that, once the generated-file conflicts are resolved according to policy, no current
source-level conflict or semantic build drift was found against today's `main`. It does not replace
validation of the eventual pushed commit. The temporary worktree was removed afterward.

### Style lint

The optional full-repository style lint is not green: it reports the existing 730-item backlog.
Targeted inspection of the changed/new Lean files found only previously existing issues in old
files (`DivergenceOfSets`, `SchwartzZippelCounting`, and `Probability/Instances`), and no style
errors in the new ABF or ToMathlib modules. Accordingly, this review does not claim that
`./scripts/validate.sh --lint` is globally clean; it claims no newly attributable style failure was
found in the new modules.

## Honest remaining formalization scope

The following are known partial or deferred items, not hidden theorem failures:

- the univariate-multiplicity half of ABF26 T2.18;
- an encoder-level extension-code abstraction and its systematic encoder equality;
- the Diamond-Posen minimum-distance equality;
- a general/module-alphabet MDS Johnson corollary covering interleaved RS;
- an algorithm and cost model for ABF26 D6.4/L6.5.

The last two become review findings because code/PR documentation currently describes the
corresponding paper items too strongly. The other items are acceptable staged scope only while
they remain explicitly marked partial/missing and later splits do not assume them as proved.

## Required remediation and re-review bar

Before approval:

1. produce one pushed, rebased, commit-coherent candidate and remove all generated KB output from
   the feature diff;
2. update the PR body to the exact pushed state, especially erasure coverage, sorry count,
   validation statistics, and partial results;
3. repair or appropriately restrict `listDecodable` so infinite sets cannot collapse to a zero
   list size;
4. distinguish base-field finrank rate from ABF alphabet-normalized rate throughout APIs, audits,
   and notation;
5. generalize the MDS Johnson corollary or label it consistently as the field-linear
   specialization;
6. weaken the identified algebra assumptions and move/generalize `reidx_hammingDist`;
7. fix the low documentation/reference issues and either cover `ell = 1` or state the restricted
   Johnson scope honestly;
8. rerun routine validation, docs validation, focused axiom probes, and current-main merge
   validation on the exact pushed commit.

Given the prize-facing use, successful compilation alone is not a sufficient re-review bar. The
final pass should re-check the public declaration statements, module docstrings, audit matrix, and
PR description together so that all four communicate the same formal scope.
