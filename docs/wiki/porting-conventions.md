# Porting Conventions

This page covers code ported into ArkLib from another snapshot or branch, such as the
Reed–Solomon port tracked by [issue #907](https://github.com/Verified-zkEVM/ArkLib/issues/907).
A ported file follows every rule in [`CONTRIBUTING.md`](../../CONTRIBUTING.md). The rules below
cover what porting adds: where the record of the port lives, and how to keep that record out of
the library's public surface.

The criteria come from the maintainer review of the #962–#991 port batch. Each one is a rule a
reviewer checks, with the check that finds violations.

## Where port history goes

The library documents the mathematics that is present now. It does not document how the code
got there.

- **Module docstrings** hold a title, an overview of the present API, `## Main statements`, and a
  `## References` section of citation-key bullets. They do not record:
  - the source snapshot or revision;
  - source file paths or old declaration names;
  - which statements are unchanged, generalized, weakened, or dropped;
  - what is deferred or not ported.
- **Declaration docstrings** state the declaration itself. They do not compare it with a source
  statement ("the source assumed `0 < d`", "this is the source's `foo`"). They do not attribute it
  to a numbered result of a paper ("BCHKS Lemma 3.1", "the paper's formulation"). Paper
  attribution belongs in the module's `## References` section. `CONTRIBUTING.md` allows a
  declaration docstring to name a source only when the statement depends on which formulation is
  meant.
- **Port history lives in** the port ledger
  ([`docs/design/reed-solomon-port.md`](../design/reed-solomon-port.md) and its correspondence
  appendix [`docs/design/reed-solomon-port-correspondence.md`](../design/reed-solomon-port-correspondence.md))
  and in the pull request description. The appendix holds the declaration-by-declaration notes
  per destination file.
- **Acceptance tests** in `ArkLibTest/` may derive a source-shaped statement from the ported one,
  to show that nothing was lost. The test comment says what the statement is ("the special case
  `w = 1`", "the form with the guard `D ≤ n - 2`"). The test's name describes the mathematics,
  not `source_*`.

Check: search module and declaration docstrings for `Ported from`, the snapshot hash, `source`,
`unchanged`, `deferred`, `not ported`, and `Lemma`/`Theorem` followed by a number.

## Names

- Name every declaration, private helpers included, for what it states. `CONTRIBUTING.md`
  already forbids author-year suffixes and paper numbering. For ports this also rules out:
  - paper-author acronyms (`johnsonBCHKS`, `bchks_source_lower`);
  - a paper's variable names used as API names (`johnsonE0`, `johnsonESharp`);
  - `source`/`paper` markers (`source_selectedTrace`).
- Acronyms are words: `Bchks`, never `BCHKS`, and only when no semantic name exists.
- Words like "source space" and "source monomial" are fine when they name the domain of a map.

## Module layout

- Lay modules out by the present API, not by the source tree. A directory or file that only
  mirrors the source layout, with no object of its own, goes to the module that owns the objects
  it is about. The example from the review: `RatePartition/*` exposed only `partitionSupport_*`
  declarations, so those results belong in `PartitionSupport/`.
- Put a generic result with its generic owner. A joint-kernel lemma about matrices goes to the
  linear-algebra layer, not to the protocol-specific module that first used it.
- Retire a source module when existing APIs cover every declaration and it has no distinct present
  API or production consumers. Record the mappings and downstream guidance in the port history.
  Do not add aliases, theorem wrappers, or duplicate acceptance tests solely to fill the unit.
- Concrete instances without a production consumer go to `ArkLibTest/`. Examples are table rows
  and results with hard-coded parameters such as `n = 2 ^ 16`. The generic API they instantiate
  stays in `ArkLib/`.

## Documentation coverage

- Every public definition has a docstring, and so does every public theorem that is part of the
  advertised API. This includes:
  - membership characterizations (`mem_foo`);
  - `_apply` and coordinate lemmas of named maps and matrices;
  - nonvanishing lemmas (`foo_ne_zero`).
  One sentence stating the characterization is enough.
- Cite papers by citation key (`[BCPZZ26]`), never by authors and title in running text. The key
  must have an entry in `blueprint/src/references.bib`
  (see [`blueprint-and-citations.md`](blueprint-and-citations.md)).

## Line length

The limit is 100 **characters**, enforced by Mathlib's `linter.style.longLine`. The repository
enables it through `linter.mathlibStandardSet` in `lakefile.toml`, so `lake build` rejects a longer
line. Count characters, not UTF-8 bytes. A line with `≤`, `→` or subscripts can exceed 100 bytes
while staying within the limit.

## Review checklist for a port PR

1. The module docstring has no port history (see [Where port history goes](#where-port-history-goes)).
2. No declaration docstring compares with the source or cites a numbered paper result.
3. No declaration name has a paper acronym, a paper variable name, or a `source`/`paper` marker.
4. Every public definition has a docstring, and so do membership, `_apply` and API theorems.
5. Every paper is cited by a key that is in `references.bib`.
6. The module layout follows the present API, and concrete instances are in `ArkLibTest/`.
7. The PR diff contains only its own slice. A stacked PR says what it is stacked on and is rebased
   once its parent lands.
8. The ledger row and the correspondence appendix record the port history.
