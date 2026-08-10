# Implementation Plans

Plans for refactors that are proposed, in flight, or recently landed, where the design rationale is
worth more than the diff and a future reader needs to know what was decided and why.

The operational split:

- `docs/wiki/` explains how to work in the repo.
- `docs/skills/` holds reusable cross-cutting workflows.
- `docs/kb/` holds durable knowledge about external papers.
- **this directory** holds plans for specific pieces of work in this repo.

## Contract

- One page per piece of work. State its **status** in the first line: proposed, in progress, landed,
  or abandoned — and keep that line honest, since a stale plan is worse than no plan.
- Every load-bearing claim carries a `file:line` citation or a reproduction command. A plan that
  cannot be checked cannot be reviewed.
- Separate what is **machine-checked** from what is **argument**. Say which is which explicitly.
- Record the open decisions that need a human, and mark the ones that must be answered before work
  starts.
- When a plan lands, either delete it or mark it landed and leave it as the design record. Do not
  leave a proposal looking live after the work is done.

## Pages

- [`computable-cwss-extractors.md`](computable-cwss-extractors.md) - making the CWSS extractor
  engines computable by giving the extractor **leaf witnessings** (the witness-only
  reduction-of-knowledge extractor interface; statement attribution stays with the verifier as
  `PureForm` data). **Landed** (2026-08-10, `tr/computable-extractors`) across ten milestones: the
  CWSS surface now has **0** noncomputable definitions, against the baseline's 20; the escape ×
  guarded composition theorem that was a `sorry` is proved; and the migration shim is deleted, so
  there is one layer again, under the original names. The design record stays; the living
  regression gate for the notion's shape is
  `ArkLib/OracleReduction/Security/TranscriptTree/NonVacuity.lean`.
