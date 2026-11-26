# The protocol specification site

This directory builds a website about the protocol specification prototype in
`docs/design/interaction-layer/prototypes/Specs/` and its decision record, D10
(`docs/design/interaction-rebuild/D10-protocol-specifications.md`). The site is written in
[Verso](https://github.com/leanprover/verso)'s manual genre, the format of the Lean reference
manual.

Lean computes or checks everything on the site when the site builds:

- Each code excerpt is the highlighted source of a named declaration, with hovers and, in tactic
  proofs, the proof state after each tactic. A renamed or deleted declaration fails the build.
- Each protocol figure is what Lean computes from the example specification: the JSON skeleton, the
  folded figure, and the expanded figure at several sizes. The page draws the figure from that data
  and, on load, checks its own port of Lean's printer against every string Lean computed.
- Each accessor path in the transcript view (`tr⟦sumcheck, 1, g⟧`) is elaborated on a transcript of
  its specification. The build fails if Lean rejects one, and the page shows the type Lean gave it.
- Each theorem in a `{theorems}` table must exist and must depend only on `propext`,
  `Classical.choice` and `Quot.sound`. A theorem that uses `sorryAx` fails the build.
- Each size table counts the lines of its files, and the benchmark table is read from
  `docs/design/interaction-layer/prototypes/out/bench.md`.

## Build

The site requires ArkLib by path and shares the root's package directory, like `docbuild/`. Build
ArkLib's prototype library first, then the site:

```bash
lake build ArkLibPrototypes
```

```bash
cd specsite && lake build specsite && .lake/build/bin/specsite --output _out --without-html-single
```

The site is in `specsite/_out/html-multi/`, one page per section. Replace `--without-html-single`
with `--with-html-single --without-html-multi` to write the whole site as one page into
`specsite/_out/html-single/` instead. Read the site one page per section. The single page is about
8 MB and has about 150,000 elements, and each time the table of contents opens or closes the
browser restyles all of them. The page therefore responds slowly, most of all on a phone. Serve
either with any static server, for example:

```bash
python3 -m http.server 8765 --directory specsite/_out/html-multi
```

`./build.sh` runs these steps and fails on any warning. The first build of an excerpt runs
`lake build +Module:highlighted` in `specsite/highlight/` for that module, which elaborates the
module again with SubVerso; later builds reuse the result.

## Layout

| Path | Contents |
|---|---|
| `SpecSite.lean` | The root: the title page and the list of chapters |
| `SpecSite/Overview.lean` | What the site shows, the four protocols, one round as written |
| `SpecSite/Language.lean` | The specification language |
| `SpecSite/Protocols.lean`, `SpecSite/Protocols/` | Sum-check, Spartan, FRI, and the branching example |
| `SpecSite/Proofs.lean` | The proof kit, its instances, the bridge and the claims |
| `SpecSite/BeforeAfter.lean` | Today's sum-check next to its specification |
| `SpecSite/Design.lean` | D10, the design record |
| `SpecSite/Cost.lean` | Line counts and elaboration times |
| `SpecSite/Adopting.lean` | How the site is built, and what adopting the specifications takes |
| `SpecSite/Data.lean` | The example specifications that the protocol widget shows |
| `SpecSite/Tables.lean` | The size tables |
| `SpecSite/Meta/` | The site's own blocks (below), and in `Accessors.lean` the accessor rule that the protocol block checks |
| `assets/protocol.js`, `assets/specsite.css` | The protocol widget's script and the site's styles |
| `highlight/` | The Lake project from which excerpts load highlighted source |

## Writing a page

A chapter is a Lean module that starts with `#doc (Manual) "Title" =>`, followed by an optional
metadata block with the chapter's tag:

```
#doc (Manual) "Sum-check" =>
%%%
tag := "sumcheck"
%%%
```

`SpecSite.lean` includes each chapter with `{include 0 SpecSite.Chapter}`. Inside a chapter, `#`
starts a section and `##` a subsection. Verso's markup is close to Markdown: paragraphs, `*` lists,
`` `code` ``, `_emphasis_`, `*bold*`, and `[text](url)` links. A description list item is a line
`: Term` followed by a blank line and its body indented by two spaces. `$`x^2`` is inline math and
`$$`…`` is display math. `{ref "tag"}[text]` links to a chapter or section by its tag.

A chapter that uses the site's blocks or Lean names opens three namespaces after its imports:

```
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open SpecSite
```

`Verso.Genre.Manual.InlineLean` provides `{name}`, and `SpecSite` provides the blocks below.

### Lean names

`` {name}`Specs.sumcheck_tree` `` prints a name with its signature and docstring on hover. The build
fails if the name does not resolve. To show a shorter text, give the full name as an argument:
`` {name Specs.Kit.RoundSound}`RoundSound` ``. The site's own blocks take names as arguments and
resolve them the same way. Write names in full (`Specs.Fri.friSpec`, not `friSpec`): a short name
that matches in two open namespaces is ambiguous, and the block then stops reading its arguments.

### The site's blocks

| Block | Shows |
|---|---|
| `{decl Specs.sumcheckRound}` | The source of one or more declarations, highlighted, with a caption that links to the lines on GitHub. `+statement` cuts each declaration after its top-level `:=`. `-docs` drops the doc comments. |
| `{protocols SpecSite.sumcheck SpecSite.fri}` | The protocol widget for one or more examples from `SpecSite/Data.lean`. |
| `{theorems Specs.sumcheck_tree Specs.Claims.sumcheckSpec_contract}` | A table of theorems with their source lines and axioms. Fails the build on `sorryAx` or a nonstandard axiom. |
| `{sizes SpecSite.prototypeSizes}` | A table of line counts for a `SizeTable` from `SpecSite/Tables.lean`. |
| `{bench}` | The benchmark table from `prototypes/out/bench.md`. |
| `:::card "Title" (n := "1") (status := "fixed")` … `:::` | A numbered decision record with a status badge: `fixed`, `partial` or `open`. |
| `::::stats` … `::::` holding `:::stat "6 + 12 lines"` … `:::` | A row of headline numbers, each with a sentence. |
| `::::columns` … `::::` holding `:::column "Today" (tone := "before")` … `:::` | Two columns side by side on a wide screen, one above the other on a narrow one. `tone` is `before`, `after` or empty and colors the column's title. |

Verso's own `:::table +header` takes a list of rows, each row a list of cells:

```
:::table +header
* * Case
  * Size
* * sum-check
  * n = 8
:::
```

### Adding a protocol to the widget

1. Write the specification in `prototypes/Specs/Examples/`.
2. Add an `Example` to `SpecSite/Data.lean`: its key, title, skeleton, the skeletons at a few
   more sizes for the page's check of its unrolling, and the specification as a term in `spec`,
   written with full names. The protocol block checks that the term has the example's skeleton and
   elaborates each accessor path of the transcript view against it.
3. Show it with `{protocols SpecSite.yourExample}`.

## Checks before a commit

- `./build.sh` succeeds with no warnings.
- The widget's line under each figure is green on every page that has one. It reports whether the
  page's port of Lean's printer reproduced every formula and figure that Lean computed, and whether
  the page computes the same accessor paths that Lean elaborated.
