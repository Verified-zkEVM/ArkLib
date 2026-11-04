# Blueprint and Citations

Use this page when a change is paper-driven, adds a new reference, or changes long-lived
formalization structure.

## Source Of Truth

- [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) is canonical for style, docstrings, naming,
  and citation policy.
- `blueprint/src/` contains blueprint sources; `leanblueprint web` refreshes `blueprint/lean_decls`.
- `blueprint/web/` and `blueprint/print/` are outputs.
- [`../kb/README.md`](../kb/README.md) holds per-paper pages and formalization status.
- [`../../BACKGROUND.md`](../../BACKGROUND.md) explains the underlying theory, compares ArkLib's
  oracle reductions with the literature, and lists the standard references. Per-paper detail
  belongs in the KB, not there.

## When To Reach For The Blueprint

- New proof systems or other substantial formalization efforts.
- Paper-driven API or design work that spans several files.
- Changes that need shared references, BibTeX entries, or published docs.

For substantial contributions, discuss the blueprint-first workflow described in
[`../../CONTRIBUTING.md`](../../CONTRIBUTING.md).

## Citation Workflow

1. Cite papers by citation key, for example `[BCIKS20]`, only in the top-level Lean module
   docstring. Keep URLs and paper-specific locators there too; declaration docstrings state the
   mathematics and relevant hypotheses directly.
2. Give the module docstring a `## References` section and brief provenance. Link to the KB
   paper page or audit for paper-specific statement/version mappings, coverage and gaps.
3. Add the matching BibTeX entry to `blueprint/src/references.bib`.
4. For durable paper context, create or update `docs/kb/papers/KEY.md` for the same citation key.
   Leave stub-only paper pages and source metadata to the main-branch KB workflow.
5. Prefer public paper titles, venues, DOIs, or URLs in shared docs rather than pointing readers
   to private or local notes.

## Knowledge Base Mapping

Lean declarations describe the mathematics independently of a source's numbering or revision.
The same result can occur in several papers; the KB records those correspondences, and the
wiki routes contributors to them.

- `blueprint/src/references.bib` is the bibliographic source of truth.
- `docs/kb/papers/KEY.md` is the preferred repository-local landing page for a cited paper key.
- `docs/kb/sources/KEY/metadata.yml` records source provenance and optional local artifacts.
- `docs/kb/_generated/lean-citations.json` is the generated map from Lean files to cited keys.
  Do not commit `_generated` changes from feature PRs.

## Build And Publish Checks

For a local preview of the docs + blueprint website:

```bash
DISABLE_EQUATIONS=1 ./scripts/build-web.sh
```

The nondefault `ArkLibBlueprint` library imports dependency declarations cited only by the
blueprint, including the abstract binary tower. It keeps those references available to
`checkdecls` without adding them to the production `ArkLib` import graph or default build.
For a direct declaration check, run:

```bash
lake build ArkLib ArkLibBlueprint
lake exe checkdecls blueprint/lean_decls
```

If blueprint output matters and `leanblueprint` is missing:

```bash
python3 -m pip install leanblueprint
```

### Continuous integration

[`.github/workflows/ci.yml`](../../.github/workflows/ci.yml) renders the blueprint PDF and HTML
on a separate read-only runner using the pinned TeXLive action. Its artifact contains only the
rendered PDF, web directory and generated `blueprint/lean_decls`; it contains no Lean build
cache. The required `build` job checks rendering success explicitly, then runs the normal Lean
validation and `lake exe checkdecls blueprint/lean_decls` against its existing `ArkLibBlueprint`
build. Rendering or declaration failures block the build check on PRs and merge groups too.

On trusted main pushes, the pinned
[`leanprover-community/docgen-action`](https://github.com/leanprover-community/docgen-action)
generates API documentation from that same Lean build in an isolated `docbuild` project.
A following step adds `ArkLibBlueprint:docs`, since the action selects only default-target API
facets. The local preview builds `ArkLib:docs` then `ArkLibBlueprint:docs` sequentially for the
same coverage; both facets update shared indexes.

The read-only build assembles the rendered blueprint and API pages under `home_page/` and
uploads the site. A separate Pages-privileged job deploys it only after a successful main push.
PR-head jobs receive neither Pages nor OIDC write permission.

### Blueprint LaTeX gotchas

These break the PDF build (and therefore the whole publish workflow):

- Math in `\section`/`\subsection` titles reaches hyperref's PDF bookmarks, where
  commands such as `\cong` raise a fatal `Improper alphabetic constant`. Wrap any
  math in a title with `\texorpdfstring{$...$}{plain-text fallback}`.
- Every `@key{...}` in `blueprint/src/references.bib` must be unique; a duplicate
  key makes BibTeX error out and leaves all citations unresolved.
- Only use macros that are defined in `blueprint/src/macros/`.
