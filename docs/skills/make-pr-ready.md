# /make-pr-ready

Use this workflow to get a branch into shape before opening or finalizing a pull request.
It is a general checklist skill that chains the project's contribution guidelines, lint cleanup,
and citation generation into one pass.

## Goal

Leave the branch in a state where every contribution guideline is met, no Lean warnings remain,
and citation metadata is regenerated and consistent — so the PR can be opened without follow-up
churn.

## TODO List

Work through these in order. Do not stop until every item is complete.

### 0. Establish the real PR base

- Verify that `origin` is the repository that owns the PR base before trusting `origin/main`.
  Contributor checkouts often use a personal fork as `origin`, whose `main` may lag the canonical
  repository even after `git fetch origin main`. Inspect the PR with
  `gh pr view <number> -R <canonical-owner>/<repo> --json baseRefName,headRefName`, compare the
  configured remote URL, and fetch the canonical base into a separate tracking ref when needed
  (for example `canonical/main`). Use that canonical ref for all scope and `_generated/`
  comparisons below.
- Fetch the selected canonical base first (`git fetch origin main` when `origin` is canonical),
  then compute scope and `_generated/` drift against its remote-tracking ref, not local `main`.
  The local `main` ref can be many commits stale (e.g. you branched, then the canonical `main`
  advanced via merges you never pulled). Diffing `main...HEAD` against a stale local `main`
  inflates the file list and can report phantom `_generated/` drift that actually matches the
  remote. With a canonical `origin`, use `git diff --stat origin/main...HEAD` for scope and
  `git diff --quiet origin/main...HEAD -- docs/kb/_generated/` for the CI guard's real view;
  otherwise substitute the canonical tracking ref selected above.
- **Also account for uncommitted work.** `origin/main...HEAD` (three-dot) only shows *committed*
  changes; a make-pr-ready pass often runs with staged/working-tree edits still in flight (e.g. a
  half-finished file). Those appear only in `git diff HEAD` (or `git diff origin/main`, two-dot).
  Compute the real PR surface as the **union** of `git diff --stat origin/main...HEAD` (committed)
  and `git diff --stat HEAD` (uncommitted), and audit/lint every file in that union — not just the
  committed ones. The whole-tree view is `git diff --stat origin/main`.
  - **An empty three-dot diff does not mean there is nothing to review.** A branch can sit exactly
    at the base (`git rev-parse HEAD origin/main` prints the same SHA) with the entire PR staged
    but not yet committed — the normal state when the work was just finished. Then
    `origin/main...HEAD` is empty and `git diff origin/main` (two-dot) *is* the whole PR. Confirm
    which case you are in with that `rev-parse` before concluding the scope is empty.
- **Check for an in-progress merge before trusting any of the above.** Run
  `cat .git/MERGE_HEAD 2>/dev/null`. If it exists, the author is mid-merge with the resolution
  staged, and the union formula **over-reports badly**: every file the base changed since the
  merge-base shows up as if this branch authored it. On a real run this attributed an entire
  directory reorganization, a new README, and several doc pages — about 50 files, all of them
  `origin/main`'s own work — to the branch, and produced a deleted-path list containing renames the
  branch never made. When `MERGE_HEAD` is present, confirm it is the canonical base
  (`git merge-base --is-ancestor $(cat .git/MERGE_HEAD) origin/main`, and
  `git log --oneline $(cat .git/MERGE_HEAD)..origin/main` should be empty), then use the **two-dot**
  `git diff origin/main` as the single authoritative PR surface — worktree versus base is exactly
  what the PR will contribute once the merge is committed. Derive the deleted/renamed list the same
  way: `git diff --name-status -M origin/main | awk '/^[DR]/ {print $2}'`. Sanity-check the
  conclusion on one file: if `git ls-tree origin/main <dir>` and `git ls-files <dir>` agree but
  `git ls-tree HEAD <dir>` differs, that directory is the base's work, not the branch's.
  More generally, whenever the worktree is the thing being shipped, two-dot `git diff origin/main`
  is the formula that cannot over- or under-report; reach for the union only when you specifically
  need to separate committed from uncommitted work.
- **Separate your own work from a merged-in sibling branch.** If this branch has merged another
  in-flight feature branch (e.g. `foo-infra`), the `origin/main...HEAD` scope will include files
  that are **byte-identical** to that sibling branch's PR. Detect them with
  `git diff --quiet origin/<sibling-branch> HEAD -- <file>` (clean = owned by the sibling PR). Do
  **not** audit or "fix" those files here: it is redundant with the sibling PR and any edit invites
  a merge conflict. Scope the audit/lint/warning-fix work to files this branch actually authored or
  extended (differs from both `origin/main` and the sibling branch).
- **Test for committed `_generated/` drift explicitly — a clean `git status` does not rule it out.**
  If the branch committed regenerated outputs, the working tree is clean and nothing in the default
  `validate.sh` complains, yet CI's first job fails. One line settles it, and it belongs in step 0:

  ```bash
  git diff --stat origin/main HEAD -- docs/kb/_generated/   # any output = the guard will fail
  ```

- **If `_generated/` drift is already committed** (the branch committed regenerated outputs, not
  just dirtied the working tree), `git checkout origin/main -- docs/kb/_generated/` stages a
  *revert*, and you must **commit it** for the guard to pass — the guard compares the committed
  branch tip to `main`, so an uncommitted revert leaves HEAD still drifted. After staging the
  revert, `git diff --cached --stat` shows huge index-vs-HEAD numbers for `_generated/` — that is
  the size of the revert, **not** new drift; do not panic. Confirm the post-commit guard view with
  `git diff --cached --quiet origin/main -- docs/kb/_generated/` (must be clean).
- **Report stray planning/scratch `.md` files — do not stage them, and do not delete them.** A
  Markdown plan, design note, or working-notes file (`PLAN.md`, `NOTES.md`, `scratch/*.md`, an
  agent handoff/TODO dump) is a working artifact, not repo documentation, and should not land in
  the PR. It is also the author's live working state, so this step is **detect-and-report only**:
  never `git add`, `git commit`, `git stash`, `git rm`, or delete one. Stashing hides work the
  author may still be using; deleting destroys it; and either way the call is theirs. List the
  candidates:

  ```bash
  git diff --name-only --diff-filter=A origin/main...HEAD -- '*.md'   # newly-added, committed
  git status --short -- '*.md'                                        # staged / untracked
  ```

  Subtract the curated docs a PR may legitimately add (`docs/kb/papers/`, `docs/kb/sources/`,
  `docs/wiki/`, `docs/skills/`, `blueprint/`, and top-level pages like
  `README`/`ROADMAP`/`CONTRIBUTING`) — a real `docs/kb/papers/<KEY>.md` or `docs/wiki/` page stays.
  For anything left that reads as a working plan, **warn the user**, naming each file and whether
  it is untracked, staged, or already committed, and let them decide. Leave untracked plans
  untracked and staged ones staged; just do not carry them into a commit you make on the author's
  behalf. Prevention lives upstream of this step: write scratch manifests and experiments under
  `/tmp` rather than as root-level planning files, so a plan surfacing here means that rule was
  bypassed — worth saying out loud.

  **Stripping the plan file is only half the job.** Lean docstrings written alongside it almost
  always cite it (`see \`PLAN.md\` §3.K`), and those citations become dead the moment the file is
  dropped. Step 4 below sweeps for them; do not consider the strip done until that sweep is clean.

### 1. Follow the contribution guidelines

- Read [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) in full and make sure every changed file
  follows it. Check at least:
  - **Naming**: files `UpperCamelCase.lean`, types/structures `UpperCamelCase`, functions/terms
    `lowerCamelCase`, theorems/proofs `snake_case`, acronyms treated as words, American English
    spelling, and the theorem-naming logic (`_of_`, `left`/`right`, `ext`/`iff`/`inj`/`mono`).
  - **Symbol naming**: translate statements into names with the standard symbol dictionary;
    standardize on `≤`/`<`, avoid `≥`/`>` in statements.
  - **Variable conventions**: match the Mathlib-style variable roles (e.g. `R`/`M`/`G`/`F` for
    algebraic carriers, `i`/`j`/`k` for indices).
  - **Syntax and formatting**: lines under 100 chars, 2-space indent, spaces around `:`/`:=`/infix
    operators, `fun x ↦` over `λ`, `where` syntax for instances/structures, `by` at end of line,
    aligned `calc`, no empty lines inside definitions/proofs, prefer `<|`/`|>` over parentheses.
  - **File headers**: Apache 2.0 copyright/license/authors block at the top of every new file.
  - **Documentation**: module docstring (`/-! ... -/` with title, summary, notation, references)
    on each file; `/-- ... -/` docstrings on every definition and major theorem; sectioning
    comments where helpful.
  - **Normal forms, transparency, deprecation**: respect the standard-form, `def`/`abbrev`/
    `irreducible`, and `@[deprecated ...]` policies when relevant to the diff.
- Verify with `./scripts/validate.sh` (add `--lint` for style linting and `--docs` for docstring
  checks). Fix anything it flags.
  - If you added or removed `ArkLib/**.lean` files, run `./scripts/update-lib.sh` **and then
    `git add ArkLib.lean`**: the import check (`check-imports.sh`) uses `git diff --quiet`
    (working tree vs index), so a regenerated-but-unstaged `ArkLib.lean` still reports
    "Import file is out of date".
  - `--docs` runs the full `doc-gen4` site build (`bibPrepass` + per-module pages), which is
    memory- and disk-heavy and may be killed (exit 137) or fill the disk in constrained
    environments. That failure is about the doc *renderer*, not your docstrings/citations —
    verify those directly (every decl has a `/-- … -/`; citation keys resolve in
    `references.bib`; the `kb` regeneration below is consistent) and note the `--docs` limitation
    rather than churning on it.
  - `--lint` (`lint-style.sh`) reports **repo-wide pre-existing** style debt — hundreds of
    `ERR_*` lines in files you did not touch. Do **not** try to clear all of it; scope style
    fixes to your changed files (lint them individually with
    `python3 scripts/lint-style.py <your-files>`). **Line length is codepoints, not bytes**: these
    files are dense with multi-byte Unicode math (`ℓ₂²`, `∑`, `·ᵥ`, `c̄ⱼ`), so `awk length` / naive
    byte counts over-report by 2–3× and can invent dozens of phantom "over-100" lines. Trust
    `lint-style.py` and the Lean `linter.style.longLine` (both count codepoints); if in doubt verify
    with Python `len(line)`, never `awk`/`wc -c`. Otherwise treat the **default** `validate.sh`
    (build + Data warning budget + `check-imports` + `check-docs-integrity` + `kb/lint`) as the
    real gate. Capture its true exit with `rc=$?` on its own line — a trailing
    `… ; echo "EXIT $?"` reports the `echo`'s exit (always 0) and masks a failing validate. Piping
    has the same trap: `./scripts/validate.sh | tail -40` reports `tail`'s exit and truncates the
    failure detail (kb lint errors print near the end). Run it as
    `./scripts/validate.sh > validate.log 2>&1` with `rc=$?` on the next line, then grep the log.
  - The **Data warning budget** fails on any non-`sorry` warning under `ArkLib/Data/`. A
    toolchain/Mathlib bump commonly introduces **deprecation** warnings (e.g.
    `X has been deprecated: Use Y instead`) — fix these by switching to the suggested name.
- Confirm the eventual PR title/description will follow the
  `<type>(<scope>): <subject>` convention (imperative, lowercase, no trailing dot) and includes
  motivation, contrast with previous behavior, and issue references.

### 2. Fix Lean warnings

- Follow the [`fix-lean-warnings.md`](fix-lean-warnings.md) skill end to end for every changed
  `.lean` file: check with `ReadLints` / `lake env lean path/to/File.lean`, fix by safety order,
  re-check after each batch, and do not stop until `ReadLints` is clean and the file still builds.

### 3. Generate citations correctly

- Make sure every paper cited in a Lean docstring uses a citation key (e.g. `[BCIKS20]`), each
  citing file has a `## References` section, and every key has a matching BibTeX entry in
  `blueprint/src/references.bib` (see the citation policy in
  [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) and the workflow in
  [`../wiki/blueprint-and-citations.md`](../wiki/blueprint-and-citations.md)).
- **Do not commit `docs/kb/_generated/` changes in a feature PR.** The CI job's first step,
  "Reject generated KB updates in PRs" ([`ci.yml`](../../.github/workflows/ci.yml)), fails the
  build if your branch's `docs/kb/_generated/` differs from `main` in **any** way — and a
  **deletion counts as a diff** just like a modification or addition. These files are refreshed
  only on `main`, by [`kb-generated.yml`](../../.github/workflows/kb-generated.yml), which opens an
  `automation/kb-generated-*` PR after merge. The guard runs before the Lean build, so a stray
  `_generated/` diff blocks CI before the build even starts (and removing the files does **not**
  help — the directory must match `main` exactly).
- You may regenerate the derived metadata **locally to check consistency** — do not hand-edit it —
  but **revert the `_generated/` outputs before committing** so the directory matches `main`:

  ```bash
  python3 ./scripts/kb/sync_from_bib.py          # writes docs/kb/_generated/references.json
  python3 ./scripts/kb/extract_lean_citations.py # writes docs/kb/_generated/lean-citations.json
  # ... inspect for consistency, then:
  git checkout origin/main -- docs/kb/_generated/ # restore to main's state; do NOT stage these
  ```

  If your branch has already diverged in `docs/kb/_generated/` (drift, an accidental delete, or a
  regenerate that got committed), restore it the same way: `git fetch origin main` then
  `git checkout origin/main -- docs/kb/_generated/`, and commit so the guard passes.

  **Expect the local regenerate to surface drift that is not yours.** `main`'s `_generated/` is
  refreshed only after merge, so it routinely lags `main`'s own sources: the regenerated diff will
  mix your new citations with citation edges from recently-merged PRs whose refresh has not landed.
  Read the diff to confirm *your* keys resolve, attribute the rest, and revert the whole directory
  regardless — a bigger-than-expected diff is not evidence your revert failed.
- Confirm the regenerated files are consistent (no dangling keys, no missing entries), but stage
  **only** your source changes plus any scaffolded `docs/kb/papers/` / `docs/kb/sources/` pages
  (those are *not* under `_generated/` and are allowed in feature PRs) — never the `_generated/`
  outputs.
- `kb/lint.py` does **not** verify that every cited key has a BibTeX entry. Check for dangling
  keys yourself: grep each `[KEY]` used in docstrings against `blueprint/src/references.bib` and
  add any missing entry (then regenerate). A key can be "present-looking" but actually a different
  paper — confirm the entry's title/authors match the citation, not just that the key exists.
- Know the `kb/lint.py` severity split: a **paper page whose `bibkey` has no BibTeX entry** is an
  *Error* (fails `validate.sh`), while a **cited key with no paper page** is only a *Warning*.
  Fix the warning too: `python3 scripts/kb/scaffold_paper.py <KEY>` scaffolds
  `docs/kb/papers/<KEY>.md` + `docs/kb/sources/<KEY>/metadata.yml` from the bib entry — then
  replace the TODO sections with real content (what the paper is, what ArkLib uses, touchpoint
  modules) before staging; a page of TODOs is reviewer bait.
- A validate/kb failure is not necessarily yours: it can be **pre-existing on `main`** (e.g. a kb
  paper page merged before its BibTeX entry). Attribute it (`git show origin/main:<file>`), but
  fix it in your PR anyway if cheap — it blocks *your* CI regardless of who introduced it.
- Also check for **duplicate BibTeX keys**: `grep -oE '^@[a-z]+\{[^,]+' blueprint/src/references.bib
  | sort | uniq -d`. Neither `kb/lint` nor the sync script flags a key defined twice (the JSON dict
  silently collapses it), but it is real bib cruft a reviewer will hit. Keep the better-formatted
  entry and delete the other.
- Docstrings must cite **papers, not internal planning documents**. Phrases like "per §1.2 of the
  X plan" pointing at an out-of-repo design doc are dead references the day the PR merges — restate
  the design rationale directly in the docstring and cite the underlying paper with a `[KEY]`
  (e.g. `[NOZ26, Lemma 8]` for a specific result).
- Also check the **reverse direction — orphan entries**: a BibTeX key (and/or a scaffolded
  `docs/kb/papers/<KEY>.md` + `docs/kb/sources/<KEY>/` page) that **no** `[KEY]` in any `.lean`
  docstring or blueprint `.tex` actually cites. `kb/lint` passes on these (they are internally
  consistent), but they are cruft a reviewer will question — especially a kb page whose
  `related_modules` frontmatter points at files that do not cite it. For each orphan, decide with
  the author whether to (a) wire it in as a real `[KEY]` citation in the relevant file (+ a
  `## References` section), or (b) remove it: drop the bib entry and `git rm` the
  `papers/<KEY>.md` + `sources/<KEY>/` pages. After removing, grep tracked files for any markdown
  link to the deleted page (`check-docs-integrity.py` fails on a broken link).
- If you **moved or renamed** any `.lean` file, regeneration does **not** fix hand-maintained
  `docs/kb/papers/*.md` pages (they are scaffolded once, then curated) — their curated links and
  `related_modules` frontmatter still point at the old path. Step 4 sweeps for these; run it rather
  than relying on `check-docs-integrity.py`, which only sees Markdown *links* and never inspects
  frontmatter. Running `kb/regenerate.py` after adding a new cited key also **scaffolds** a new
  `docs/kb/papers/<KEY>.md` + `docs/kb/sources/<KEY>/`; stage those too.

### 4. Clean up references to what the branch removed

**Do not gate this whole step on file deletions.** Only the *path* sweep below needs a deleted,
moved, or renamed file. The **declaration**, **status-flip**, **docstring-section** and
**planning-code** sweeps that follow are unconditional whenever a refactor renames or removes
*declarations*, *table rows*, or *docstring sections* — which happens constantly on branches that
touch no file at all. On a real run `git diff --name-status -M` returned **zero** deleted paths
while the branch had removed six top-level declarations and cut a chain table from 12 rows to 9;
every one of the 24 confirmed findings came from the un-gated sweeps, and an agent that read the
old opening sentence as a gate would have skipped the entire step with a green `validate.sh`.

Do this near the end of the pass — step 0's plan-file strip and step 1's refactors both create
deletions.

If this branch deletes, moves, or renames **any** file, sweep the whole library for references to
the old path and fix them.

**Assume nothing catches this for you.** Coverage is much thinner than it looks:

- `lake build` catches stale `import` lines — and *only* those. A path named in a docstring, a
  comment, or a Markdown file is invisible to it.
- `check-imports.sh` regenerates `ArkLib.lean` from `git ls-files`, so the deletion must be
  **staged** (`git rm <path>`, or `git add -A -- <path>` after an `rm`). A file deleted in the
  working tree but still in the index keeps its `import` line and fails the build instead.
- `check-docs-integrity.py` checks **only** inline Markdown links (bracketed text followed by a
  parenthesised path), and **only** in `AGENTS.md`, `scripts/README.md`, and `docs/**/*.md` (minus
  `_generated/`). Note it resolves links inside backticks too, so do not write a literal
  link-shaped example in prose — it will be chased and reported broken. It does **not** see:
  bare or backticked paths anywhere, `.lean` docstrings, `blueprint/**`, `.github/**`, or the
  top-level `README.md` / `CONTRIBUTING.md` / `ROADMAP.md` / `BACKGROUND.md`.
- `kb/lint.py` does **not** validate the `related_modules:` paths in `docs/kb/papers/*.md`
  frontmatter. A module listed there can be long gone and lint still passes.

Net effect: **a branch can carry dozens of dead path references with a fully green
`./scripts/validate.sh`.** Only the sweep finds them.

Enumerate every path the branch removes — committed, uncommitted, and rename sources:

```bash
{ git diff --name-status -M origin/main...HEAD; git diff --name-status -M HEAD; } \
  | awk '/^[DR]/ {print $2}' | sort -u > /tmp/deleted-paths.txt
```

Then sweep the tracked tree for each one. Match the path, the dotted module name, and the bare
basename (relative Markdown links and prose usually mention only the basename):

```bash
while read -r p; do
  [ -e "$p" ] && continue                      # skip paths a later commit restored
  pats=(-e "$p" -e "$(basename "$p")")
  case "$p" in *.lean)
    mod="$(printf '%s' "${p%.lean}" | tr '/' '.')"
    pats+=(-e "${mod//./\\.}($|[^.A-Za-z0-9_])")   # boundary-anchored: see trap 1
  esac
  hits="$(git grep -nE "${pats[@]}" -- . ':!docs/kb/_generated' ':!ArkLib.lean')"
  [ -n "$hits" ] && { echo "### stale refs to $p"; printf '%s\n' "$hits"; echo; }
done < /tmp/deleted-paths.txt
```

Three false-positive traps, the first two of which fire routinely on this repo's refactors:

1. **File promoted to a same-named directory** (`Hachi/Gadget.lean` → `Hachi/Gadget/`). A plain
   `git grep -F ArkLib.Commitments.Functional.Hachi.Gadget` prefix-matches every live
   `import ...Hachi.Gadget.Core` and reports the whole new folder as stale. That is why the module
   pattern above is anchored with `($|[^.A-Za-z0-9_])`. Never sweep module names with bare `-F`.
2. **Basename collision with a surviving file.** Deleting `Hachi/Escape.lean` while
   `CoordinateWiseSpecialSoundness/Escape.lean` still exists makes every bare `` `Escape.lean` ``
   mention ambiguous. Before touching a basename-only hit, run `git ls-files | grep <basename>`:
   if a namesake survives, the prose may be correctly pointing at it — read the surrounding
   sentence and decide, do not bulk-delete.
   The degenerate case is `README.md` / `index.md`: deleting one directory's README makes the
   basename half of the pattern return every README cross-link in the repo — on a real run, two
   deleted READMEs produced ~60 hits, none of them real. Drop the basename pattern entirely for
   these names and match the full path only.
3. **This file matches its own examples.** Hits in `docs/skills/make-pr-ready.md` are the sample
   paths quoted above, not stale references. Same for any changelog or migration note that
   deliberately records an old path.

For each **confirmed** stale reference, pick a disposition — never just delete the line and move on:

1. **Moved or renamed** → repoint to the new path (and fix the link text, which usually still
   spells the old name).
2. **Content absorbed into a sibling** → repoint to the sibling and reword the sentence so it
   describes what is actually there now.
3. **Genuinely gone** → remove the reference, including the clause that introduced it. A stranded
   "see also" with its target excised reads worse than no cross-reference.
4. **Pointing at a scratch plan stripped in step 0** → **never** repoint it; that file never
   existed on `main`, so the reference was born dead. Restate the reasoning inline in the docstring
   and cite the underlying paper with a `[KEY]`. This is the same rule as the "cite papers, not
   internal planning documents" bullet in step 3 — the strip is what makes it urgent.

Then check the places a path grep structurally cannot reach:

- `docs/kb/papers/*.md` — `related_modules:` frontmatter (unlinted; also verify the entries still
  make sense after a move, not just that they resolve).
- `blueprint/src/**/*.tex` — `\texttt{ArkLib/...}` path mentions, plus `\lean{Decl.Name}` refs to
  declarations that died with the file. Only `./scripts/validate.sh --site` checks the latter.
- [`../wiki/repo-map.md`](../wiki/repo-map.md) — the structure map goes stale on *every* move,
  rename, and delete, and nothing verifies it.
- `.github/workflows/*.yml` — path config such as `upstream_path:` silently no-ops when its target
  disappears rather than failing.
- Non-Lean assets living under `ArkLib/` (generated overview HTML, diagrams) — they escape both the
  Lean build and the Markdown link check.

**Dead *declaration* names outlive dead paths, and nothing catches them at all.** A refactor that
renames or splits a theorem leaves every prose mention of the old name behind: `lake build` only
checks names in *code*, so a backticked `` `foo_bar` `` in a docstring, a kb page, or `repo-map.md`
can name something that has not existed for months. On a real run this was the single largest
finding class — a chain certificate advertised under a name that lost its `Escape` suffix, an escape
event under a name that was never defined, a commitment field cited as a lemma, an upstream instance
that does not exist in the pinned dependency, and a composed-event helper under an entirely wrong
namespace. Sweep it: extract the backticked lower/UpperCamelCase identifiers from every docstring
the branch touched, and for each one check it resolves as a declaration —

```bash
DECL='(def|theorem|lemma|abbrev|structure|instance)'
MOD='(noncomputable |protected |private )*'
git grep -nE "^[[:space:]]*${MOD}${DECL}[[:space:]]+<name>([[:space:]]|\(|\{|:|$)" -- 'ArkLib/**'
```

Note `git grep -E` is POSIX ERE: `\b` and `\s` are unreliable, so anchor with `[[:space:]]` and an
explicit trailing class as above, or the sweep silently reports everything as missing. For a
namespaced name (`A.B.c`), grep finds only the leaf, so confirm the full path really resolves with a
throwaway probe instead of trusting the grep:

```bash
printf 'import ArkLib.<Module>\n#check @<Full.Declaration.Name>\n' > /tmp/probe.lean
lake env lean /tmp/probe.lean
```

**The probe's own `unknown identifier` is ambiguous** — it fires both for a genuinely dead
declaration and for *your* wrong guess at the namespace, and the two look identical. A docstring is
read in its file's `open` context, so a backticked `` `Foo.bar` `` may be correct there while
unresolvable from the root. Before reporting a name as dead, find where it is actually declared
(`git grep -nE '^[[:space:]]*(structure|def|theorem) <leaf>' -- 'ArkLib/**'`, then read the
enclosing `namespace`) and re-probe with the full path. On a real run this made a live structure
field look like a dead reference.

**Sweep the *un*-sorrying direction too — proving something out orphans status prose.** Step 4
instinctively hunts for things the branch *deleted*, but a branch that *finishes* a proof leaves
just as many false sentences behind, and no check catches them. When a branch takes a file from
sorried to proven, grep the tree for prose still calling it a `skeleton` / `sorried` / `WIP` /
`(**sorried**)` / "not yet proven". On a real run the branch proved `Guarded.lean` out (2 sorries
→ 0) and updated three files to say so, while a fourth still described the same file as "the only
composition machinery it consumes is `Guarded.lean`'s skeleton". Note `skeleton` is this repo's
sorriedness marker, not a neutral word — treat every occurrence as a status claim:

```bash
git grep -nE 'skeleton|sorried|\(\*\*sorried\*\*\)|still open|not yet proven' -- 'ArkLib/**' \
  | grep -iE '<file-or-decl-the-branch-proved-out>'
```

**Deleting a docstring *section* strands cross-file pointers to it by name.** A `/-! ## TODO … -/`
or `## References` block removed from one module is invisible to every checker, yet other modules
say "see the `TODO` blocks in `Foo.lean`". On a real run one deleted TODO block broke pointers in
two sibling Lean files *and* a `docs/kb/audits/` page. Whenever a diff removes a named docstring
section, grep for prose naming it, and prefer **restoring a trimmed section** over deleting three
pointers — the pointers usually exist because the work is still open:

```bash
git grep -nE '`?TODO`? (block|section)|see the .*(TODO|References)' -- 'ArkLib/**' 'docs/**'
```

**Dangling row/link numbers hide behind three spellings.** After cutting rows from a table, grep
for `row N`, `row-N`, and `row&nbsp;N` (and the `rows N–M` forms, en-dash *and* hyphen). A sweep
written as `grep -E 'row 1[0-2]|row&nbsp;1[0-2]'` silently missed a live `row-11` reference in a
page footer. Also check the **reverse legend direction**: deleting the last row that carried a
status leaves a legend entry defining a status no data uses — and its text usually names the row
number that was just deleted.

**Bare internal planning codes are as dead as the plan file that defined them.** Step 0 strips plan
*files* and step 3 forbids citing them, but the *codes* survive every automated check and every path
grep, because they are not paths: `milestone F2.0`, `design D5`, `Phase-G`, `(B4)`, `(D12 / R6)`,
`sorried F5`, `filling F7`, `**(S1)**`, `**(C-1)**`. Once the plan is gone they are unresolvable
noise. Sweep and delete them, keeping the substance (`(σ₋₁-twisted, design D5)` → `(σ₋₁-twisted)`)
and re-anchoring the disclosure to a paper locator (`[NOZ26] §4.5`) or plain prose
("closing this gap") rather than the internal process:

```bash
C='(B|C|D|E|F|G|M|R|S)-?[0-9]+(\.[0-9]+)?'
git grep -nE "milestone|prototype|design [DG][0-9]|Phase-[A-Z]|§[0-9]+ [A-Z][0-9]|\b${C}\b" \
  -- ArkLib/ blueprint/src/
grep -rnE "[^A-Za-z_]${C}[^A-Za-z_0-9.]" --include='*.lean' ArkLib/   # \b-free fallback, see below
```

**Do not require the code to open a parenthesis.** An earlier version of this sweep matched only
`\(CODE\)`, and on a real run it missed two of the four sites present: `` (whence `harity₂`, D5) ``
(parenthesized, but the code is not the first token) and `(§10 R3)` (a section-plus-code pair). Match
the bare code with word boundaries instead, then eyeball the hits.

The bare-code pattern is noisy by construction, so filter rather than narrow: expect `Array.prototype`
in vendored HTML/JS, `(L9)`/`(L11)`-style *paper* lemma tags, and math like `(S-1)·(D - dY)`. Paper
section references (`§4.5`, `Figure 3`, `[NOZ26] Lemma 8`) are exactly what step 4 tells you to
re-anchor *to* — never strip those. And remember `git grep -E` does not honor `\b`: if a code is
present but the git grep comes back empty, re-run with plain `grep -rn --include='*.lean'` before
concluding the file is clean.

**Hand-maintained dashboards drift silently and loudly.** A status page under `ArkLib/` (this repo
has `Hachi/hachi-overview.html`) hard-codes file counts, per-file `sorry` counts, row spans, and a
status legend; none of it is generated, so all of it rots. Recompute every number from ground truth
before believing it — `sorry` counts from the build log
(`grep -c 'declaration uses .sorry.'` per file, which agrees with a comment-stripped source scan)
and file/umbrella counts from `git ls-files` — then check the page against itself: the totals it
prints must equal the sum of its own data table, every `status` value used in the data must appear
in the legend, and any "rows N–M" claim must match the rows actually carrying that status (a single
row with a different status in the middle makes a range wrong — enumerate rather than assume). On a
real run this page was understating open `sorry`s by 40%, was three files and one umbrella behind,
and used a status with no legend entry.

**A name that still resolves can still be dead.** The sweeps above find names with no declaration.
They cannot find a declaration whose *name* encodes a migration that is over: after the shim layer
was deleted, `Verifier.treeSpecialSoundWith.old_of_new` and `Verifier.specialSound.old_of_new` still
compiled and still had accurate statements, but nothing in the tree defined what "old" or "new"
meant. Same for docstring prose that narrates the library's own history rather than its content —
"the classical version had to *invent*", "the statement that used to sit behind X's `sorry`", "the
certificate is **now** proved", "no longer existential", "as before the carrier change". None of it
is checkable by a reader of the merged tree. Sweep for it on any branch that finishes a refactor:

```bash
git grep -nEi "used to |no longer|formerly|previously|the old |is now |now \*\*|the classical (version|form|notion|reading)|\bshim\b|migration" -- ArkLib/
```

Then keep the fact and drop the history (`used to be the fundamental sorried obligation` → `is the
fundamental composition obligation`). Filter out the ordinary senses first — "used to define",
"the goal is now", and protocol-level "the old target" are not findings.

**Re-derive any number or span a subagent reports.** Counts and row ranges are exactly where
parallel reviewers disagree with each other and with the source; two reviewers of the same page
returned different totals, and one asserted a chain spanned rows 1–9 when its own definition's
docstring said rows 1–12. Settle each from the declaration, not from the report.

**Do not "fix" `docs/kb/_generated/`.** `declarations.json` and `lean-citations.json` still index
the deleted path; that is expected. Regenerating and committing them trips the CI guard described in
step 3. Leave them at `main`'s state;
[`kb-generated.yml`](../../.github/workflows/kb-generated.yml) refreshes them after merge.

Finish by re-running `./scripts/update-lib.sh` (then `git add ArkLib.lean`) and
`./scripts/validate.sh`, and re-run the sweep itself — repointing one reference can introduce
another stale path.

### 5. Suggest skill improvements

- After completing the pass, tell the user whether this skill could be improved: any new recurring
  guideline gap, a missing or stale step, a better ordering, or a check worth adding. Follow the
  Maintenance Rule in [`README.md`](README.md) and update this file if the improvement is likely to
  help the next agent.

## Persistence Rule

Only consider the PR ready when:

1. `./scripts/validate.sh` (with `--lint` / `--docs` as appropriate) succeeds.
2. `ReadLints` is clean for every changed `.lean` file.
3. Citation metadata is consistent, and `docs/kb/_generated/` matches the PR base exactly (step 3
   — it is checked locally, never committed).
4. The deleted-file sweep in step 4 comes back clean — no reference anywhere in the tree points at
   a path this branch removed. A green `validate.sh` does **not** imply this.
5. You have reported any suggested improvements to this skill.
