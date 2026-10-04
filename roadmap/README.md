# Area roadmaps

This folder tracks ongoing development by area, following the direction discussed in
[issue #608](https://github.com/Verified-zkEVM/ArkLib/issues/608). The
[root roadmap](../ROADMAP.md) is the project-wide index. Area pages record current source,
active branches or PRs, proof gaps, and the next useful step.

## Current pages

| Area | Page |
|---|---|
| Interaction theory and legacy migration | [Interaction migration](interaction-migration.md) |
| Sumcheck and Spartan | [Sumcheck and Spartan](proof-systems/sumcheck-spartan.md) |
| Merkle commitments | [Merkle commitments](commitments/merkle-trees.md) |

These are the initial populated areas, not complete coverage of ArkLib. Add a page when an area's
status and next steps can be checked against source. Use [the template](TEMPLATE.md); do not create
empty pages for every prospective project. Other areas remain indexed in the root roadmap until
contributors supply their maintained pages.

## Maintenance

- Update the affected area page in the same PR as a material implementation or status change.
  The PR author proposes the update and reviewers check it alongside the code.
- Record a date and source revision. Separate merged results, proved results in open PRs, and
  planned work. Link active PRs and name their authors or responsible contributors when verified.
- Keep mathematical exposition and literature in the blueprint and research notes. Keep
  architecture in the design suite. Link to those owners instead of duplicating them here.
- Preserve one implementation sequence per area. The interaction sequence remains in
  [the design roadmap](../docs/design/05-roadmap.md); its area page owns migration readiness.
- After a tracked scope is completed and its PRs merge, move its page into `done/`, record the
  final revision and remaining out-of-scope work, and repair incoming links. A merged component
  does not mean an entire research area is complete. Create `done/` when there is a completed page.
- When a PR is superseded or closed, remove it from the active list and preserve any useful
  history in a linked result record. Do not leave closed branches as the next implementation step.
