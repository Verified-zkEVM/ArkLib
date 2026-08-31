# Blueprint and Citations

Use this page when a change is paper-driven, adds a new reference, or changes long-lived
formalization structure.

## Source Of Truth

- [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) is canonical for style, docstrings, naming,
  and citation policy.
- `blueprint/src/` contains blueprint sources.
- `blueprint/web/` and `blueprint/print/` are outputs.
- `BACKGROUND.md` is a lightweight reference list, not the detailed theory source.

## When To Reach For The Blueprint

- New proof systems or other substantial formalization efforts.
- Paper-driven API or design work that spans several files.
- Changes that need shared references, BibTeX entries, or published docs.

For substantial contributions, discuss the blueprint-first workflow described in
[`../../CONTRIBUTING.md`](../../CONTRIBUTING.md).

## Citation Workflow

1. Cite papers in Lean docstrings by citation key, for example `[BCIKS20]`.
2. Give the Lean file a `## References` section in its module docstring.
3. Add the matching BibTeX entry to `blueprint/src/references.bib`.
4. For durable paper context, create or update `docs/kb/papers/KEY.md` for the same citation key.
   Leave stub-only paper pages and source metadata to the main-branch KB workflow.
5. Prefer public paper titles, venues, DOIs, or URLs in shared docs rather than pointing readers
   to private or local notes.

## Knowledge Base Mapping

- `blueprint/src/references.bib` is the bibliographic source of truth.
- `docs/kb/papers/KEY.md` is the preferred repository-local landing page for a cited paper key.
- `docs/kb/sources/KEY/metadata.yml` records source provenance and optional local artifacts.
- `docs/kb/_generated/lean-citations.json` is the generated map from Lean files to cited keys.
  Do not commit `_generated` changes from feature PRs.

## Build And Publish Checks

For a local preview of the docs + blueprint website:

```bash
DISABLE_EQUATIONS=1 lake build ArkLib:docs
./scripts/build-web.sh
```

If blueprint output matters and `leanblueprint` is missing:

```bash
python3 -m pip install leanblueprint
```

### Continuous integration

Publishing to GitHub Pages is handled by [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml),
which delegates to the maintained [`leanprover-community/docgen-action`](https://github.com/leanprover-community/docgen-action)
rather than a hand-rolled TeX/pygraphviz setup. The action runs after CI's Lean
build on the same runner, so blueprint validation and documentation publishing
reuse the existing `.lake` build instead of compiling the project again. It
builds the API docs via doc-gen4 (in an isolated `docbuild` project, the layout
recommended by [doc-gen4](https://github.com/leanprover/doc-gen4)), builds the
blueprint with `leanblueprint pdf` + `leanblueprint web`, runs
`lake exe checkdecls blueprint/lean_decls` to confirm every `\lean{...}`
declaration exists, and deploys the static `home_page/` (with `docs/` and
`blueprint/` copied in). Pull requests run a validation-only build (blueprint +
`checkdecls`, no deploy), so LaTeX and declaration errors are caught before they
reach `main`.

### Blueprint LaTeX gotchas

These break the PDF build (and therefore the whole publish workflow):

- Math in `\section`/`\subsection` titles reaches hyperref's PDF bookmarks, where
  commands such as `\cong` raise a fatal `Improper alphabetic constant`. Wrap any
  math in a title with `\texorpdfstring{$...$}{plain-text fallback}`.
- Every `@key{...}` in `blueprint/src/references.bib` must be unique; a duplicate
  key makes BibTeX error out and leaves all citations unresolved.
- Only use macros that are defined in `blueprint/src/macros/`.
