# Continue the paper decoder with parallel workers

This checkpoint provides tower representations, executable zero/unit splitting, fiber
preprocessing, exact tower agreement recovery, support-based equation construction, and
easy-branch dispatch. It does **not** complete Milestone 1 or the paper decoder.

The symbolic branch in `HiddenDerivativeDecoder/Run.lean` returns
`symbolicBackendUnavailable`. `TowerBatch.restrictBases` is proved but is not yet called by
tower recovery. Inversion, materialization, partition accounting, and equation-check
certification remain open. No running-time theorem is claimed.

The target specification is the paper repository’s
[decoder formalization plan](https://github.com/quangvdao/rs-capacity-and-correlated-agreement/blob/156f14b4cf4b5231c6218c695c45cb86ee32ca8b/docs/decoder-formalization-plan-2026-09-11.md).
Read it if accessible; report inaccessible source material rather than inventing its contents.
The code contracts and deliverables below remain usable without that checkout.

## Launch a worker

Use one new ChatGPT conversation for each task below. Give it the repository
`quangvdao/ArkLib`, the exact foundation checkpoint SHA supplied by the coordinating
Codex task, this page, and one task page. Do not use a moving branch name as the base.

1. Ask the worker to inspect its available GitHub tools before promising a push.
2. If branch creation and file writes are available, create only its assigned branch
   from the supplied SHA. Never update the integration branch or force-push.
3. If those tools are unavailable, ask for a unified patch or complete changed files
   based on that SHA. The coordinator can apply and check them locally.
4. Return the result to the coordinating Codex task. Include the base SHA, branch,
   final commit SHA or patch, changed files, checks actually run, and remaining gaps.

A worker without a Lean environment must label its changes **uncompiled**. Connector
access alone does not establish that Lean builds or shell commands can run.

| Worker | Branch | Deliverable |
| --- | --- | --- |
| [A: inverse](inverse.md) | `quang/decoder-m1-inverse` | Computed tower inverse and coefficient materialization |
| [B: accounting](accounting.md) | `quang/decoder-m1-accounting` | Disjoint partitions and dimension bounds |
| [C: batching](batching.md) | `quang/decoder-m1-batching` | Product-tree batching in the actual recovery path |
| [D: equation checks](equation-checks.md) | `quang/decoder-m1-equation-checks` | Executable checks with semantic certification |
| [E: review](review.md) | None; read-only | Independent assessment of the checkpoint |

A–D can run independently. E can review the frozen checkpoint while they work.
Integration and full validation belong to the coordinator. Completing these tasks
alone does not establish correctness of the unfinished symbolic decoder.

## Shared instructions for every worker

Read repository `AGENTS.md` and relevant source before editing. All paths in task pages
are relative to `ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/` unless stated otherwise.
Own only the files assigned to you. Put required shared-file changes in a separate
suggested patch for the coordinator; do not commit them into your branch.

Use the repository module style (`module`, `public import`, `@[expose] public section`).
Keep files below 1500 lines. Add no `sorry`, new axioms, `native_decide`, or lint
suppressions. Proof-only algebraic closures and classical reasoning are acceptable;
executable code must not enumerate the field, extract geometric roots, use a supplied
inverse oracle, or fall back to exhaustive message enumeration. Do not change the paper,
dependencies, build configuration, generated umbrella, or unrelated modules. Do not
claim asymptotic costs without a proved cost model.

When Lean is available, build your modules with `lake build <Module.Name>` and exercise
nontrivial examples. Before commit or push follow the repository-required
`./scripts/validate.sh --axioms` gate; stage new files first so source checks see them.
Do not build API docs. If the environment cannot run the gate, return a patch and explain
which checks remain for the coordinator instead of claiming a verified commit.

## Collect and integrate

The coordinator fetches each returned SHA, checks that its merge base is the supplied
checkpoint and its changed files obey ownership, reviews the full diff, then integrates
one task at a time. Re-run affected checks after integration and the full validation
gate before publishing the combined result. Keep each worker's limitations in the
checkpoint report until evidence resolves them.
