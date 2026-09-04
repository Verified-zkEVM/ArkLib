# Source Metadata

Each paper may have a source metadata directory under:

- `docs/kb/sources/KEY/`

The minimal committed artifact is usually:

- `metadata.yml`

Optional additional artifacts include:

- extracted plaintext or markdown;
- a local PDF when redistribution is acceptable;
- source-specific notes for reviewers or agents.

Non-paper sources may also have a directory here when their provenance materially affects an
ArkLib development. Such a directory should use a stable source name and explain why it is not a
BibTeX-keyed paper record. For example,
[`rs-ld-mca/PERMISSION.md`](rs-ld-mca/PERMISSION.md) records the permission and commit-level
provenance for an external Lean formalization adapted by the all-rate Reed-Solomon project.

The metadata should record:

- source URL;
- source type;
- version/provenance notes;
- whether a local artifact is committed.

A permission record must distinguish a project-owner attestation from direct grantor evidence and
must not infer a license merely because a source repository is public.
