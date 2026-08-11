# PR 701 deep review — 2026-08-11

Independent pre-merge review of PR 701 (*ABF26 foundations and code families*, split 2/4) at head
`103ffe89a`, against merge base `a4ac38e0e`. This is a **later and broader** review than the record
in [`../abf26-split-pr1-review-2026-08-07/`](../abf26-split-pr1-review-2026-08-07/README.md), which
remains the immutable evidence for the earlier candidate `3c303efa`.

Eleven independent reviewers covered, in parallel and without seeing each other's findings: subspace
designs, the Wronskian/multiplicity layer, the Johnson family, the Reed-Solomon code families and
extension codes, the probability and entropy layer, regressions in the pre-existing `Basic/*` files,
declaration-level coverage parity against the unsplit branch, repo-wide hygiene and vacuity gates,
style/duplication/documentation, a reverse audit working from the paper sources toward the Lean, and
the impact on the external proximity-prize repository. Each was barred from reading the 2026-08-07
record until its own findings were formed, then cross-checked it.

## Contents

- [`VERDICT.md`](VERDICT.md) — consolidated verdict, gate results, findings, the paper-side defects
  found along the way, and the remediation applied in response.

## Outcome

Sound: no blocker, no false statement, no new admit or axiom, and no soundness defect. One HIGH and
about fourteen MEDIUM findings, all mechanical. The set agreed for this PR was remediated in-tree;
see `VERDICT.md` § *Remediation applied*. Findings deliberately deferred are listed there too, so a
later reader can tell a deferral from an oversight.

## Method notes worth reusing

- Non-vacuity was established **positively** — by compiling satisfying instances of the headline
  theorems — rather than by failing to refute them. Two findings were caught only this way.
- Claims of falsity required a **compiled** refutation before being reported.
- One reviewer error is recorded honestly in `VERDICT.md`: a `grep` for a *qualified* name
  (`JohnsonBound.J'`) structurally cannot match in-namespace uses of `J'`, which led to a
  "zero consumers" claim that was wrong. Prefer unqualified searches, or the elaborator, when
  arguing that a declaration is dead.
