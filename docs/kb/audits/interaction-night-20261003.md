# Interaction-security theory run, October 3, 2026

## Contract and clock

The user authorized the [general-theory contract](../../design/interaction-security-night-contract.md)
after reviewing its definitions, scope, ambitious targets, review requirements and PR sizing.
The mathematical targets are G1 (ordinary soundness), G2 (knowledge composition), and G3
(state-restoration knowledge soundness). Supporting examples do not count as their completion.

Start: 2026-10-03 00:56:52 America/New_York / 04:56:52Z.
Six-hour checkpoint: 06:56:52 local / 10:56:52Z.
Expansion freeze: 07:26:52 local / 11:26:52Z.
Deadline: 08:56:52 local / 12:56:52Z.

The earlier premature launch was interrupted with a clean worker tree. Its stopped timer does
not govern this run. The active clock is recorded in `/tmp/arklib-night-20261003/timing.json`;
the local timer writes checkpoint/freeze/deadline markers and never kills a build.

## Baseline and ownership

ArkLib baseline: `ace55c3e29da1fc55a321378ada55ea4f7ed8790`.
Research baseline: `c3e715d23a05a01ae1f7e6b0421d873476ec3f00`.
Supported pins: Lean 4.34.0, VCVio `d7089e46d69e07640fa23b5ae6b1b966f1d4b949`,
PolyFun `3710d71b28404a151b8d1f0ce080ea448778dec0`.
Origin: `https://github.com/Verified-zkEVM/ArkLib.git`.

| Owner | Worktree / branch | Work |
|---|---|---|
| Main orchestrator | `ArkLib` / `research/cy-interaction-theory` | Contract, notes, PR operations |
| Main orchestrator | `ArkLib-interaction-night` / `work/interaction-night-20261003` | G3 investigation, integration, final validation |
| Sol High worker A | `ArkLib-local-rbr` / `feat/native-local-rbr` | G1 and actual Sumcheck application |
| Sol High worker B | `ArkLib-witness-transport` / `feat/native-witness-transport` | G2 and named backward extraction |
| Independent reviewer | `ArkLib-interaction-review` / `review/interaction-night-20261003` | Statement/read-back and code review |

All paths are under `/Users/quangdao/Documents/Lean`. The unrelated
`ArkLib-runtime-soundness` worktree is outside scope. Workers do not push, open PRs, merge, or
edit one another's files. The main orchestrator reviews and owns acceptance.

Project build outputs are private copies. Dependencies use the existing exact-revision shared
cache. All run-owned Lean/Lake writes are serialized through
`/tmp/arklib-night-20261003/with-build-lock.py`. VCVio, PolyFun and Mathlib revisions/origin URLs
were inspected; PolyFun has only the cache manager's untracked `.lean-deps-immutable` marker,
not a source change. No dependency reset or upgrade is authorized merely to pass a check.

## Live theorem status

| Target | Status | Required next evidence |
|---|---|---|
| G1: generic ordinary soundness | Assigned, unproved | Literal public statement and actual native executor induction |
| G2: knowledge composition | Assigned, unproved | Literal relation/witness seam and native composition statement |
| G3: restoration security | Source/API investigation, unproved | Source-faithful query game and fresh-response/ancestor probability lemma |

No implementation theorem or code PR is claimed at launch. Public names must use clear
cryptographic terminology; an abstraction's representation does not justify inscrutable names.

## Review, validation and publication evidence

The pre-launch mathematical proposal received an independent ordinary review. That is not a
blind read-back or an implementation verdict. New principal Lean types will receive a fresh
blind read-back, followed by the orchestrator's comparison against the contract and sources.
Each substantive code PR also requires source/axiom/API checks and full repository validation.

Expected substantial code PRs: G1 with Sumcheck; G2 with its native composition proof; G3 with
the quantitative restoration theorem. Aim for roughly 500-1500 changed lines per PR, preserving
important coherent smaller results. No definitions-only micro-PRs and no merging into main.

Validation commands, exact revisions, reviewer verdicts, PR links and incomplete obligations
will be added here as evidence becomes available. The final report distinguishes checked partial
theory from completion of G1/G2/G3 and records any pending CI or validation.
