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
4. Prefer public paper titles, venues, DOIs, or URLs in shared docs rather than pointing readers
   to private or local notes.

## Build And Publish Checks

```bash
DISABLE_EQUATIONS=1 lake build ArkLib:docs
./scripts/build-web.sh
```

If blueprint output matters and `leanblueprint` is missing:

```bash
python3 -m pip install leanblueprint
```
