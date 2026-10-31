# /make-pr-ready

Use this workflow to prepare a branch before you open a pull request, or before it merges. Apply
it to the contribution that the user names. Keep the scope of the user, and do not change
unrelated work.

## Goal

When you finish, the contribution is ready for review:

- The names and the docstrings agree with the mathematics.
- The statements agree with their sources, and the claims agree with the axiom output.
- The proofs are clear and have no known performance problem.
- The branch has no non-`sorry` warnings in `ArkLib/` and no warnings in the tests.
- The citations are correct, and `docs/kb/_generated/` is the same as on the base.
- The prose follows the [writing standard](../wiki/writing.md).
- A draft description exists.

A pull request can be open for review with admissions if its description lists them. Before it
merges, it must add no `sorry`, no `admit`, and no new `sorryAx` dependency relative to the base.
The closure of a different admission does not cancel a new admission. A baseline update can record
a closure or a rename of existing debt, but it cannot permit new debt. This pass does not give
permission to fill unrelated admissions.

## Steps

Do the steps in order. Steps 0 to 2 can find problems that change the rest of the pass. Step 5
comes near the end, because the refactors of the earlier steps can delete files and declarations.
The [gotchas](#gotchas) at the end record the failures of earlier runs. Read them before your first
pass.

### 0. Find the scope of the branch

Run the scope script against the canonical base. The script handles three cases that make a plain
`git diff origin/main...HEAD` wrong. These cases are uncommitted work, a merge in progress, and a
deleted file that a later change restores.

```bash
git fetch origin main
python3 scripts/pr-scope.py summary --base origin/main
```

Then do these steps:

1. If the script warns that `origin` is not the canonical repository, fetch the canonical
   repository into a different remote. Give that base to each later command, for example
   `--base canonical/main`. The `main` branch of a fork can be many commits old.
2. If the script warns that a merge is in progress, make sure that `MERGE_HEAD` is the base.
   `git log --oneline MERGE_HEAD..origin/main` must print nothing. In this case the script
   compares the work tree with the base.
3. Use the "Changed files" section as the scope of all later steps. This section includes staged
   and unstaged work. A branch can be at the base with all of its work staged.
4. If the branch merged a different feature branch, remove the files of that branch from the
   scope. If `git diff --quiet origin/<sibling-branch> HEAD -- <file>` succeeds, the sibling pull
   request owns the file. Do not audit or change that file in this pass.
5. If the section for `docs/kb/_generated/` lists a change, the first CI job fails. Run the
   restore command that the script prints, and commit the result. The command restores the files
   of the merge base, not the files of `origin/main`.
6. Report each file in the section for Markdown working files to the user. Say whether the file
   is untracked or added. Do not stage, stash, commit, or delete these files, because they are
   the working state of the author. Scratch manifests and experiments belong under `/tmp`,
   outside the contribution.
7. Stage each file in the section for other untracked files that the pull request needs.

A Lean docstring often refers to a plan file. When the plan stays out of the pull request, that
reference is dead. Step 5 finds these references.

### 1. Follow the contribution guidelines

Read [`CONTRIBUTING.md`](../../CONTRIBUTING.md) in full, and make sure that each changed file
follows it. A green build does not check these rules, so check them yourself:

1. **Names**: apply the [naming conventions](../../CONTRIBUTING.md#naming-conventions) and the
   symbol dictionary. A name must state the actual contract. Preservation is not commutativity,
   and `≤` is not `<`. Do not put paper numbers or planning codes in a name. Update each caller
   when you rename a declaration, as the [compatibility policy](../../CONTRIBUTING.md#compatibility-policy)
   requires.
2. **Syntax and headers**: check the line length, the indentation, the operator spaces, and
   `fun x ↦`. Each new file needs the license header.
3. **Docstrings**: each file has a module docstring. Each definition and main theorem has a
   declaration docstring. A declaration docstring states the claim, the important hypotheses,
   and each abbreviation. A reader must not need the paper to understand it. Put external
   citations, URLs, and paper locations only in the module docstring. The module docstring
   describes the actual scope and the gaps.
4. **Reuse**: find repeated arguments and existing library facts. Move each general lemma to the
   module of its mathematics. Keep the strength, the hypotheses, and the axiom boundaries of each
   theorem. Test the public interface with a real caller and satisfiable hypotheses.
5. **Computability**: apply the [computability policy](../../CONTRIBUTING.md#computability), and
   use [`make-computable.md`](make-computable.md) to sort the blockers. Protocols and functions
   that calculate values must run. From an ordinary caller, run concrete examples with known
   results. Include success, failure, and boundary cases, and record the results. An admitted
   body can produce code that panics.
6. **Performance**: measure before you change a proof for speed. Use the build timings or the Lean
   profiler to find the slow declaration and tactic. Compare the times on the same workload. Do
   not expand a stable terminal `simp` into a `simp only` list. A shorter proof is not always
   faster.

Then run the validation, and keep its exit code:

```bash
./scripts/validate.sh > validate.log 2>&1
rc=$?
```

A pipe into `tail`, or an `echo $?` on the same line, hides a failure. If you added or deleted a
file under `ArkLib/`, run `./scripts/update-lib.sh` and `git add ArkLib.lean` first. Use `--docs`
only when you change how the documentation builds. It builds the documentation of each dependency.

### 2. Audit statements, claims, and overlap

A green build does not find a wrong statement or a false claim. Do these checks on each headline
declaration that the branch adds or changes:

1. Do the checks in [Statement Correctness](../../CONTRIBUTING.md#statement-correctness). Record
   the result of each check for the description.
2. In a probe file outside the repository, state each headline theorem as an `example`. Try
   `trivial`, `simp`, `decide`, `aesop`, and `exact?` on it, and read each proof that you get.
   Ignore a proof by the audited theorem or by a lemma that the branch adds for it. `exact?` finds
   these lemmas too. If a different proof does not use the main hypotheses or lemmas, report the
   statement as probably too weak. If it uses an existing library theorem, report a possible
   reuse.
3. For each admission that the branch adds, check that its statement is true. Evaluate small
   instances with `decide` or `#eval` where the types permit it. Report each admission that you
   could not check.
4. Make sure that each hypothesis of a headline theorem is necessary. The unused-variable linter
   finds only a hypothesis that the proof never mentions. If your tools include the Lean
   language server tool `lean_minimal_hypotheses`, run it on the theorem. If not, and the proof
   is fast, remove the hypothesis in a probe copy and build the copy again. Also compare each
   hypothesis with the source. A missing hypothesis, for example a query bound, can make a
   theorem false or vacuous.
5. List each claim in the planned title and description, for example "proves", "sorry-free", or
   "as stated in the paper". For each claim, run `#print axioms` on the declaration that it names.
   A claim of "no admissions" requires an output with only `propext`, `Classical.choice`, and
   `Quot.sound`. A file without `sorry` can depend on an admission in an imported declaration.
6. Search the open pull requests for the same declarations and files:

   ```bash
   gh pr list -R Verified-zkEVM/ArkLib --state open --search "<declaration or file name>"
   ```

   Report each open pull request that changes the same declarations. Do not change the branch of a
   different pull request.

### 3. Fix warnings and admissions

1. Follow [`fix-lean-warnings.md`](fix-lean-warnings.md) for each changed `.lean` file. Fix the
   source, and do not add a linter suppression. A deprecation warning gives the new name. Use it.
2. Compare the admissions and `scripts/axiom_baseline.json` with the base, including the
   uncommitted changes:

   ```bash
   python3 scripts/source-trust-audit.py --base-ref origin/main
   ./scripts/validate.sh --axioms
   ```

   Examine each new obligation, not the net count. A new declaration can depend only on
   `propext`, `Classical.choice`, and `Quot.sound`. Reject custom axioms, `sorryAx`, and
   native-compiler trust. Existing debt does not permit new debt.
3. The baseline has an empty `sorry` list. Its admitted entries are reviewed solicited proofs,
   each linked to a tracking issue. Remove a proved entry from `solicited` in the same pull
   request. Adding an entry requires maintainer review. No declaration outside `solicited` may
   depend on an entry. See [`scripts/README.md`](../../scripts/README.md).

### 4. Check the citations

1. Put each external citation, URL, and paper location in the module docstring. Keep a short
   mathematical statement in each declaration docstring. Put a detailed map from statements to
   paper versions in the knowledge base. Cite papers, not planning documents.
2. Give each cited paper a citation key such as `[BCIKS20]`, and give the module docstring a
   `## References` section. Each key must have an entry in `blueprint/src/references.bib`. Read
   the entry, because a key can exist and name a different paper.
3. `kb/lint.py` does not find a key without an entry, so search for each key yourself. Also find
   duplicate keys, because the scripts keep only one copy of each:

   ```bash
   grep -oE '^@[a-z]+\{[^,]+' blueprint/src/references.bib | sort | uniq -d
   ```

4. Find each orphan: a BibTeX entry or a `docs/kb/papers/` page that no file cites. Ask the author
   to cite it or to remove it. If you remove a page, remove each link to it.
5. For a paper that the contribution adds or extends, add a substantive page with
   `python3 scripts/kb/scaffold_paper.py <KEY>`. Replace each TODO before you stage the page. Do
   not try to clear the existing backlog of coverage warnings.
6. Do not commit a change to `docs/kb/_generated/`. The first CI job compares the head with the
   merge base of the branch and `main`. It fails on any difference, and a deletion is a
   difference. You can regenerate the files to check them. Then restore them from the merge base:

   ```bash
   python3 ./scripts/kb/sync_from_bib.py
   python3 ./scripts/kb/extract_lean_citations.py
   git restore --source="$(git merge-base origin/main HEAD)" --staged --worktree -- docs/kb/_generated/
   ```

   The regenerated files also contain changes from recent merges, because `main` updates them only
   after a merge. Make sure that your keys resolve, and then restore the whole directory.

A failure in `kb/lint.py` can come from `main`. Find its source with `git show origin/main:<file>`.
If the fix is small, include it, because the failure also stops your CI.

### 5. Remove references to what the branch removed

Do each sweep that applies, even if the branch deletes no file. A renamed declaration or a deleted
table row also leaves stale references. A green `./scripts/validate.sh` does not find them:

- `lake build` finds only a stale `import`.
- `check-docs-integrity.py` finds only a broken Markdown link in `AGENTS.md`, `scripts/README.md`,
  and `docs/`. It does not read a path in backticks, a Lean docstring, `blueprint/`, `.github/`, or
  the top-level pages.
- `kb/lint.py` does not read the `related_modules:` list of a paper page.

**Paths.** Find each reference to a deleted, moved, or renamed path:

```bash
python3 scripts/pr-scope.py stale-refs --base origin/main
```

Each output line gives the deleted path, the kind of match, and the matching line. The script
searches all tracked files except `docs/kb/_generated/` and `ArkLib.lean`. It uses these kinds of
match:

- **Path**: the full path.
- **Module**: the dotted module name of a Lean file. The search anchors the end of the name. Thus
  a live import of `Hachi.Gadget.Core` does not match the deleted module `Hachi.Gadget`.
- **Basename**: the file name. If a tracked file has the same name, the kind names that file. Read
  the sentence before you change the line, because it can refer to the surviving file.
- **Parent and basename**: the parent directory and the name, for a common name such as
  `README.md` or `index.md`. A search for the common name alone gives only noise.

A match in this skill file can be an example path. A changelog entry or a migration record can also
keep an old path on purpose. Give each real stale reference one of these dispositions:

1. The file moved: change the path and the link text.
2. A different file contains the content: refer to that file, and change the sentence to describe
   it.
3. The content is gone: remove the reference and the clause that introduced it.
4. The reference is to a plan file outside the pull request: do not refer to a different
   file. Write the reasoning in the declaration docstring, and put the citation in the
   module docstring.

Then examine the places that the script does not read:

- The `related_modules:` list of each page in `docs/kb/papers/`.
- The `\texttt{ArkLib/...}` paths in `blueprint/src/`.
- [`repo-map.md`](../wiki/repo-map.md), which each move or rename makes stale.
- The paths in `.github/workflows/*.yml`. A missing path can make a step do nothing without an
  error.
- Files under `ArkLib/` that are not Lean files, such as HTML overview pages.

**Declaration names.** The build checks names only in code. List the backticked identifiers in
each docstring and Markdown page that the branch changes. For each name, find its declaration:

```bash
git grep -nE '^[[:space:]]*((noncomputable|protected|private) )*(def|theorem|lemma|abbrev|structure|instance)[[:space:]]+<leaf>([[:space:]]|$)' -- 'ArkLib/**'
```

Use `[[:space:]]`, because `git grep -E` does not support `\b` or `\s` reliably. For a name with a
namespace, the search finds only the last component. Confirm the full name with a probe file
outside the repository:

```bash
printf 'import ArkLib.<Module>\n#check @<Full.Declaration.Name>\n' > /tmp/probe.lean
lake env lean /tmp/probe.lean
```

An `unknown identifier` error can mean a dead name or a wrong namespace in your probe. A docstring
uses the `open` namespaces of its file. Find the `namespace` of the declaration, and try again
before you report the name.

For each declaration that the branch renames or deletes, also search the blueprint. Only
`./scripts/validate.sh --site` checks the `\lean{...}` names. A stale name fails the declaration
check on `main` after the merge:

```bash
git grep -nF '<Old.Declaration.Name>' -- blueprint/src
```

**Status text.** When the branch proves a file or a declaration, search for text that still calls
it open. In this repository, "skeleton" means "contains admissions":

```bash
git grep -nE 'skeleton|sorried|still open|not yet proven' -- 'ArkLib/**' 'docs/**'
```

**Sections and rows.** When the branch deletes a named docstring section such as `TODO` or
`References`, search for text that refers to it. If the work is still open, restore a shorter
section. When the branch deletes table rows, search for `row N`, `row-N`, and `row&nbsp;N`. Also
search for ranges with a hyphen or an en dash. Make sure that each status in a legend still has a
row.

**Planning codes.** Remove each code from a plan outside the repository, such as `milestone F2.0`,
`design D5`, `Phase-G`, or `(B4)`. Keep the mathematical content of the sentence:

```bash
C='(B|C|D|E|F|G|M|R|S)-?[0-9]+(\.[0-9]+)?'
git grep -nE "milestone|design [DG][0-9]|Phase-[A-Z]|${C}" -- ArkLib/ blueprint/src/
```

The pattern also finds paper lemma tags and mathematical expressions, so read each match. A paper
location such as `§4.5` or `[NOZ26] Lemma 8` is correct in a module docstring.

**History text.** A declaration name or a docstring describes the present code, as rule C3 of the
writing standard requires. Examples of history text are `old_of_new`, "used to", "no longer", "is
now proved", and "as before the change". The writing check in step 7 finds the common words. Keep
the fact, and remove the history.

**Status pages.** A page under `ArkLib/` that a person maintains, such as
`Hachi/hachi-overview.html`, contains counts that no script updates. Calculate each count again
from the source. The totals must equal the sum of the table. Each status in the data must be in the
legend.

Do not change `docs/kb/_generated/`. Its files still index the deleted paths.
[`kb-generated.yml`](../../.github/workflows/kb-generated.yml) updates them after the merge.

Finish with `./scripts/update-lib.sh`, `git add ArkLib.lean`, and `./scripts/validate.sh`. Then do
the sweeps again, because a changed reference can introduce a new stale path.

### 6. Draft the pull request description

Complete the [pull request template](../../.github/pull_request_template.md) with the results of
the earlier steps. Write the draft to a file outside the repository, and give it to the user. Do
not edit the description of an open pull request unless the user asks for it.

- **Formalized statements**: the source comparison from step 2.
- **Admissions and axioms**: the admission changes from step 3 and the axiom output from step 2.
- **Validation**: each command that you ran, and the output of `git rev-parse HEAD`.
- **Breaking changes**: the renamed and deleted declarations from step 5.
- **Known gaps**: the differences from the source that step 2 found and that stay open.
- **Related work**: the overlapping pull requests from step 2.

### 7. Check the writing

Check the prose that the branch adds or changes against the [writing standard](../wiki/writing.md).
This prose includes docstrings, comments, Markdown, commit messages, the title, and the
description:

```bash
python3 scripts/check-writing.py --base origin/main
python3 scripts/check-writing.py --stdin description < /tmp/pr-description.md
git log --format=%B origin/main..HEAD | python3 scripts/check-writing.py --stdin commits
python3 scripts/check-pr-title.py '<type>(<scope>): <subject>'
```

The first command reports only problems in the lines that the branch adds. Read each sentence
before you change it, because a match is not always an error. The scripts find only the measurable
rules. Then read the changed text one time for the other rules. These rules include one topic for
each sentence, the active voice, and the claims rules C1 to C8.

### 8. Suggest skill improvements

Tell the user whether this skill needs a change: a new recurring gap, a missing or stale step, a
better order, or a new check. Follow the Maintenance Rule in [`README.md`](README.md), and update
this file if the change can help the next agent.

## Persistence Rule

Do not call the pull request ready to merge until each of these conditions is true:

1. `./scripts/validate.sh` succeeds, and each changed `.lean` file meets the warning budgets.
2. The checks in step 1 are complete. Each performance claim has a measurement.
3. The statement audit in step 2 is complete. Each claim in the title and the description agrees
   with the `#print axioms` output for the declaration that it names.
4. The branch adds no admission and no admitted debt. Each new declaration depends only on the
   three standard axioms, and a baseline change does not hide a new obligation.
5. Each protocol and each function that calculates a value produces code and has runtime evidence.
   Each noncomputable mathematical definition has a documented reason.
6. The citations are consistent, and `docs/kb/_generated/` is the same as on the base.
7. The sweeps in step 5 find no stale reference.
8. A draft description from the template exists, and the writing check of step 7 is complete.
9. You reported your suggested improvements to this skill.

## Gotchas

These failures happened on real runs of this skill. Most of them passed a green validation.

- **Merge in progress**: the three-dot comparison gave the branch about 50 files from the base. The
  files included a directory reorganization and renames that the branch never made.
- **Empty three-dot diff**: a branch was at the base with all of its work staged. Then
  `git rev-parse HEAD origin/main` prints the same commit two times.
- **Fork as `origin`**: the `main` branch of a fork was many commits behind the canonical
  repository after `git fetch origin main`. The scope then contained the changes of the base.
- **No deleted files**: a branch deleted no file, but it removed six declarations and three table
  rows. All 24 stale references came from the sweeps that do not need a deleted file.
- **Common file names**: two deleted `README.md` files gave about 60 basename matches. None of them
  were real.
- **File to directory**: `Gadget.lean` became the directory `Gadget/`. A search for the module
  name without an end anchor matched each import of `Gadget.Core`.
- **Namesake files**: after the deletion of `Hachi/Escape.lean`, text about `Escape.lean` could
  refer to `CoordinateWiseSpecialSoundness/Escape.lean`.
- **Declaration names in prose**: these were the largest class of stale references on one run. The
  class included a certificate under an old suffix and an event that was never defined. It also
  included a field that the text called a lemma, a missing instance of the pinned dependency, and
  a helper in a wrong namespace.
- **Probe namespaces**: a probe in a wrong namespace made a live structure field look dead.
- **Proved files**: a branch proved `Guarded.lean` and updated three files. A fourth file still
  called it a skeleton.
- **Deleted sections**: one deleted `TODO` section broke the pointers in two Lean files and in a
  page under `docs/kb/audits/`.
- **Row numbers**: a search for `row 1[0-2]` did not find the text `row-11`.
- **Planning codes**: a search that required a parenthesis before the code did not find
  `` (whence `harity₂`, D5) `` or `(§10 R3)`.
- **Status pages**: one overview page reported 40% fewer open admissions than the build. It was
  three files behind and used a status that its legend did not define.
- **Subagent numbers**: two reviewers of the same page reported different totals. Calculate each
  count again from the source.
- **Inherited admissions**: a pull request advertised files without `sorry`. Their theorems
  depended on admitted framework definitions.
- **Line length**: `lake exe lint-style` counts Unicode code points. `awk length` and `wc -c` count
  bytes and report false long lines.
- **Restoration from `origin/main`**: a review found this failure, not a run. `main` refreshed the
  generated files after the branch started. A restoration from `origin/main` copies the new files
  into the branch, and the CI check then fails.
- **Restored generated files**: after you stage the restoration of `docs/kb/_generated/`,
  `git diff --cached --stat` shows large numbers. They measure the restoration, not new drift.
- **Unstaged deletion**: `check-imports.sh` builds `ArkLib.lean` from `git ls-files`. Stage each
  deletion, or the import stays and the build fails.
