# Second interaction-security run: evidence and progress

Status: active. The [authorized contract](interaction-security-next-night-contract.md)
controls scope; no main theorem is declared complete by this progress record.

## Run and ownership

- Start: October 3, 2026, 17:34:15 UTC.
- Six-hour checkpoint: 23:34:15 UTC.
- Deadline: October 4, 01:34:15 UTC (October 3, 21:34:15 America/New_York).
- Root orchestrates and integrates. Workers use gpt-6-sol at high reasoning effort.
- Integration: `integration/interaction-second-night-20261003`, initially ArkLib main
  `ace55c3e29da1fc55a321378ada55ea4f7ed8790` plus prior reviewed integration
  `b2ec8214150121c00f2d4ec468f72f1be34d8f22`.
- VCVio worker: `feat/expected-fresh-query`, worktree `VCVio-expected-query`.
- Native restoration worker: `feat/randomized-state-restoration`, worktree
  `ArkLib-randomized-restoration`.
- Merkle worker: `feat/native-merkle-terminal-batch`, worktree `ArkLib-merkle-terminal`.
- Builds serialize shared dependency writes; each project has private build outputs.
- No main merges are authorized. Substantial PRs and checkpoint pushes are authorized.

## Validated merged-upstream baseline

VCVio PR 823 merged at 17:31:21 UTC as
`d606eab018ab87bf4a0a6ac7b6d2da4fedfa53b0`. Current execution baseline is
`bc3433e3c94a85ff5b70a00109cf74394ad5c401`, also containing PR 820.
The ArkLib migration changes its exact VCVio pin and four uses of renamed binding-security
identifiers in the Ajtai proof. The binding experiment and mathematical proof are unchanged.

- Integration migration commit: `31ca1b19d`.
- Worker migration cherry-pick: `324fd0bf3`.
- Contract commit: `a9f7757aa`; pushed integration head verified remotely.
- Full `./scripts/validate.sh --axioms`: passed in 159.8 seconds after the name migration
  and line-length repairs. Production build, compile-time clients, runtime checks, source
  policy, documentation checks, and axiom regression all passed.
- Axiom audit: 18,341 declarations, 933 modules, 286 existing sorry-tainted declarations,
  zero nonstandard-axiom-tainted declarations; no regression.
- Independent ordinary review found no issue in the dependency/name migration.
- Dependency revisions and origin URLs match the manifest. The only untracked entry in
  the new VCVio cache checkout is the cache manager's `.lean-deps-immutable` metadata.

## Early statement review

The initial independent reviewer checked the proposed interpreter and native definitions
before being reassigned to the Merkle workstream. This is an ordinary review, not a blind
read-back, and is not a final verdict on the eventual theorems. It requires actual cached
expectation, returned failure with retained log/cache, independent uncached private draws,
finite-support treatment of infinite key domains, and exact native phase handoff.
That worker cannot independently approve its own later Merkle implementation.

The Merkle design uses one native public root emission per sequential commitment. Each
checkpoint is recorded at that step. A proposed grouping of all roots into one public move
was rejected pending a stronger causal refinement proof; final transcript equality alone
would not certify commitment-time extraction.

## Current proof frontier

At this checkpoint, native scalar and closed-output randomized execution equations have
passed a targeted source check. Root has checked the finite expected-charge union assembly
in scratch. The main expected cached-query theorem, native expected knowledge bound, and
Merkle security transfer remain in progress. Their eventual acceptance requires exact
revision-specific validation, independent statement read-back, and contract comparison.
