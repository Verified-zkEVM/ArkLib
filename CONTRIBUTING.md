## Contributing to ArkLib

Contribute a definition, proof, test, or documentation change. The [roadmap](ROADMAP.md) describes
current work and planned directions. The [open
issues](https://github.com/Verified-zkEVM/ArkLib/issues)
include bugs, formalization tasks, and documentation requests. Issues labeled `good first issue`
or `help wanted` are suitable starting points.

Some true external results have statements in the library and proofs left open for contributors.
[Issue #1352](https://github.com/Verified-zkEVM/ArkLib/issues/1352) explains these solicited proofs.
The [wiki](docs/wiki/README.md) describes repository commands and conventions.
[AGENTS.md](AGENTS.md) gives the entry points for agent workflows.

## Before You Start

### Set Up and Validate

On a new clone, download the build cache. Then run the full validation:

```bash
lake exe cache get
./scripts/validate.sh
```

For a change to proofs or admissions, also run `./scripts/validate.sh --axioms`.
The [quickstart](docs/wiki/quickstart.md) explains the checks and optional build targets.
Use [uv](https://docs.astral.sh/uv/getting-started/installation/) for the Python commands in the
writing workflow. Those commands select Python 3.12 and do not install a project package.

### Check for Overlap

Before starting a formalization, search open pull requests and issues for the same target:

```bash
gh pr list -R Verified-zkEVM/ArkLib --state open --search "<paper key or topic>"
gh issue list -R Verified-zkEVM/ArkLib --state open --search "<paper key or topic>"
```

If an open PR covers the same declarations, ask its author whether the work is active.
Do not duplicate active work. If you open a PR for the same target, link the earlier PR and
explain how your work relates to it.

If the earlier PR appears abandoned and its author does not reply, you can ask a maintainer
whether to proceed. A maintainer may waive the overlap rule. This creates no response deadline
or obligation for maintainers.

### Reuse Existing Definitions

Search ArkLib and its dependencies before adding a definition. Generalize an existing definition
when it almost meets the need. Explain why a separate definition is necessary if generalization
would change the intended concept. Do not add an `alias` only to match a paper's presentation.

A new abstraction needs a consumer, such as a theorem or protocol. Include that consumer or link
the issue or PR that will add it.

### Large Contributions

For a large formalization, we strongly encourage a
[blueprint](https://github.com/PatrickMassot/leanblueprint) before you write the Lean code.
Describe the results, key definitions, assumptions, and intended proof structure. Include the
sources, dependency graph, and unresolved design choices.

Open an issue or discussion for the proposal. Discuss the blueprint before starting the
implementation.

## Pull Request Guidelines

### Title Format

Use this format:

```text
<type>(<optional-scope>): <subject>
```

**Types:**

* `feat`: A feature or formalized result
* `fix`: A defect correction
* `doc`: Documentation
* `docs`: Documentation, as an alternative to `doc`
* `style`: Formatting
* `refactor`: A change to the organization or interfaces
* `test`: Tests and acceptance examples
* `chore`: Maintenance
* `perf`: A performance improvement
* `ci`: CI workflows and checks

**Subject:**

Write a short subject that names the change. Use an imperative phrase, such as "add the FRI folding
round". A noun phrase for the result, such as "soundness of the FRI folding round", is also correct.
Do not use "added" or "adds".

Keep ordinary words lowercase. Preserve the capitalization of names such as `FRI`. Do not end the
subject with a period. Use the scope when it helps identify the affected component.

For a breaking change, put `!` before the colon:
`refactor(binius)!: remove the legacy folding API`.
Both `doc: clarify the contribution process` and `docs: clarify the contribution process` are valid.

### Description

Use the [PR template](.github/pull_request_template.md). Keep the description proportional to the
change. Omit sections that do not apply rather than inventing formalization claims for a prose edit.
Give the reader the information needed to assess the contribution:

- State the problem, the change, and its purpose.
- Identify headline declarations. Compare each statement with its source and explain differences
  in hypotheses, conclusions, scope, or generality.
- List admissions added or closed. Give the axiom output for each headline theorem.
- State the validation commands, their results, and the commit or exact diff they cover.
- Identify breaking changes, renamed declarations, and affected callers.
- Link related issues, the base of a stack, and overlapping work.
- Describe known gaps and the parts of a source that remain outside the formalization.

Keep claims in the title and description consistent with the code and evidence.
A successful build does not establish source fidelity or axiom cleanliness.

### Size and Stacking

Give each PR one topic. Separate mechanical changes from mathematical changes when a reviewer can
review and validate each one independently.

Use a stack for contributions that need several dependent PRs. Each PR must build and pass its
validation against its stated base. Name that base in the description.
ArkLib permits squash and rebase merges. It does not permit merge commits.
The [CI mapping](docs/wiki/quickstart.md#ci-mapping) explains automatic checks on feature-base PRs
and when manual dispatch is necessary.

### Writing

The [writing guide](docs/wiki/writing.md) offers advice for documentation, docstrings, comments,
commit messages, PR and issue text, and review comments. Use it to improve clarity and precision.
Leave clear, correct text alone, even if it does not follow a rule or the checker reports it.

Use the [writing workflow](docs/skills/write-technical-prose.md) when drafting or revising prose.
Keep claims, hypotheses, uncertainty, requirement strength, and established technical terminology
intact. Compare a revised paragraph with the original in context. The vocabulary helps resolve
ambiguity; it does not prohibit other meanings when their context is clear.

### Tool-Assisted Contributions

Authors remain responsible for content produced with an AI agent or another tool:

- Read the headline statements and the full description before requesting review.
- Keep temporary plans, handoff notes, and session logs out of the contribution.
- Replace inaccessible planning codes with the maintained source or an explanation.
- Describe the current library in reference documentation. Explain the change in the commit or
  PR description.
- Coordinate concurrent tool runs so they do not open competing PRs for the same target.

A prose task does not itself authorize a comment, PR, or merge.
Agents must keep the user's task scope and publication instructions.

## Merge Requirements

### Review and Merge Readiness

You can open a PR for review with unfinished proofs if its remaining admissions and validation
status are clear. Before merging into `main`, it must introduce no new `sorry`/`admit` or additional
`sorryAx` debt relative to the canonical base. Closing one gap does not offset a new admission
elsewhere. Updating `scripts/axiom_baseline.json` cannot authorize new debt. Baseline changes record
verified closures or renames of debt at the base.

The baseline's `sorry` list is empty. Its only admitted entries are *solicited proofs*: true,
faithfully stated external results whose research-sized proofs remain open for contributors. A
solicited entry requires review and a tracking issue linked from its docstring. The entry must stay
a leaf. No declaration outside the solicited list may depend on it.

A PR that proves a solicited result removes its entry. [`scripts/README.md`](scripts/README.md)
states the exact rules that
`lake exe axiomsweep --check` enforces.

New declarations may depend only on a subset of Lean's three standard axioms:
`propext`, `Classical.choice`, and `Quot.sound`. Do not introduce custom axioms, `sorryAx`,
or native-compiler trust dependencies. Solicited proofs are not an exception for new
declarations.

Merge readiness also requires `./scripts/validate.sh` to pass: resolve all linter/style issues,
all production non-`sorry` warnings, and all test warnings. Fix the source. Do not suppress linters.
For proof changes, run `./scripts/validate.sh --axioms` and review the source-admission and baseline
diffs against `main`. That review must cover admissions in examples and default arguments, which
may not appear as exported declarations.

### Statement Correctness

A build cannot find a wrong statement, and a proof of a wrong statement has no value. Before you
request a merge, do these checks on each headline definition and theorem:

1. Compare the statement with its source. Record each difference in the description and in the
   paper page of the [knowledge base](docs/kb/README.md).
2. Make sure that the hypotheses can all be true at the same time. An acceptance test in
   `ArkLibTest/` gives the evidence.
3. Check that the conclusion expresses the intended restriction. For an error bound, give permitted
   parameters where it is below one. If a predicate must reject some inputs, include a rejected
   case.
4. Make sure that a definition has no degenerate case that hides an error. Examples are an
   `else True` branch and an empty relation.
5. Make sure that each hypothesis is necessary, or say in the docstring why it stays.
6. Try `trivial`, `simp`, `decide`, `aesop`, and `exact?` on each headline theorem, and read each
   proof that you get. A proof by the theorem itself, or by a lemma that the pull request adds for
   it, gives no evidence. If a proof does not use the main hypotheses or lemmas, the statement is
   probably too weak. A proof by an existing library theorem shows a possible reuse, not a weak
   statement.

An admitted statement must be true. A false admitted statement lets a proof derive any claim. Before
you admit a statement, check small cases or try to find a counterexample.

### Acceptance Tests

Keep compile-time examples and regression tests in `ArkLibTest/`, mirroring production paths.
`lake test` builds them, and `./scripts/validate.sh` runs the test target with a zero-warning
budget.
Stage new tests before validation. Production modules must not import tests. Both trees share the
source-style policy and build-time lint plugin. See [ArkLibTest/README.md](ArkLibTest/README.md).

Use acceptance examples with satisfiable hypotheses that exercise the claimed behavior. When an
error bound is intended to be nontrivial, include an instance with error below one. Exercise a
boundary or a necessary hypothesis when that distinguishes the intended statement from a weaker one.

### Computability

Make definitions computable wherever possible. Protocols, provers, verifiers, encoders,
decoders, samplers, and anything whose purpose is to run a program or compute a value must
be executable. Carry the necessary representations, decision procedures, and witnesses as data.
Do not replace an algorithm with classical choice. If the current interface lacks that data,
redesign it or provide a verified executable implementation before calling the contribution
merge-ready.

Purely mathematical objects used in statements and proofs may remain `noncomputable` when
there is a concrete reason. Mark those declarations individually and explain the blocker in
the module overview. Avoid blanket `noncomputable section` declarations that hide accidental
code-generation failures. Where executable data has a mathematical view, prove their agreement.

Check code generation from a caller outside any `noncomputable section`. Then execute small concrete
cases with independently known results, including relevant failure or boundary cases.

Neither removing the keyword nor an axiom-clean theorem establishes executability: admitted bodies
can compile to a panic. Executable specifications permit tests that can expose mistaken or vacuous
declarations. Those tests complement satisfiable hypotheses and correctness proofs. Executability
alone does not establish either property. Follow [the computability
workflow](docs/skills/make-computable.md) when an audit finds a blocker.

## Style and Naming Guidelines

We aim to follow the [Lean community's contribution
guidelines](https://github.com/leanprover-community/leanprover-community.github.io/tree/lean4/templates/contribute).
`./scripts/validate.sh` runs ArkLib's source-policy gate, and `lake build` rejects linter
suppressions. Neither gate permits exceptions. The
[quickstart](docs/wiki/quickstart.md#lean-source-policy-checks) describes both gates.
If a proof needs a larger elaboration budget, make it cheaper instead.

### Naming Conventions

The [Mathlib-style naming
conventions](https://leanprover-community.github.io/contribute/naming.html)
below are the repository standard. Consistent names give readers and tools predictable search
terms within ArkLib and across Lean libraries. Use established mathematical terminology and
namespace structure rather than introducing local synonyms.

* **Files**: `UpperCamelCase.lean` (for example, `BinarySearch.lean`).
* **Types and Structures**: `UpperCamelCase` (for example, `MonoidHom`, `Visualizer`).
* **Functions and Terms**: `lowerCamelCase` (for example, `binarySearch`, `isPrime`).
* **Theorems and Proofs**: `snake_case` (for example, `add_comm`, `list_reverse_id`).
* **Acronyms**: Treat as words (for example, `HtmlParser` not `HTMLParser`).
* **Prop-valued Classes**: Use `UpperCamelCase`. If the class is an adjective, use the `Is` prefix
  (for example, `IsCompact`, `IsPrime`). If it is a noun, no prefix is needed (for example, `Group`,
  `TopologicalSpace`).
* **Spelling**: Use American English for declaration names (for example, `analyze` not `analyse`,
  `color` not `colour`).
* **Dot Notation**: Use namespaces to group related definitions (for example, `List.map`). This
  enables dot notation (for example, `l.map f`) when the type is known. Use manual dot notation for
  logical connectives and equality (for example, `And.intro`, `Eq.refl`, `Iff.mp`).
* **Axiomatic Names**: Use standard names for properties: `refl`, `symm`, `trans`, `comm`, `assoc`,
  `inj` (injective), `congr`.
* **Identifiers**: 
    * Use namespaces for logical properties (for example, `And.comm`, `Or.intro`).
    * Use descriptive names for arithmetic/algebraic properties (for example, `mul_comm`,
      `add_assoc`).
* **No paper items in names**: name a declaration for what it says, never for where it came from.
  No author-year suffix (`..._gk16`), no numbering (`lemma_4_3`, `claimA2_...`, `thmA2`), and no
  internal planning code (`milestone_F5`, `design_D5`). Source labels can change when a paper is
  revised or another source is added. A label does not describe the mathematical statement. Cite the
  source in the module docstring's `## References` section instead (see
  [Citation Standards](#citation-standards)). State the chosen mathematical formulation directly in
  the declaration docstring. Keep brief provenance in the module docstring and paper-specific
  statement/version mappings in the KB.

### Theorem Naming Logic

* **Hypotheses**: Use `_of_` to separate hypotheses. List them in the order they appear (for example,
  `lt_of_succ_le` means "less than *follows from* successor less equal").
* **Variants**: Use `left` or `right` to describe which argument changes or is relevant (for
  example, `add_le_add_left`).
* **Structural Lemmas**:
    * `ext`: For extensionality (`∀ x, f x = g x → f = g`).
    * `iff`: For bidirectional implications.
    * `inj` / `injective`: For injectivity results.
    * `mono` / `antitone`: For monotonicity.
* **Induction/Recursion**:
    * `induction_on` / `recOn`: Use when the value comes before the constructions (motive eliminates
      to Prop / Type).
    * `induction` / `rec`: Use when the constructions come before the value.
* **Predicates**: Generally use prefixes (for example, `isClosed_Icc` not `Icc_isClosed`).
  Exceptions include property suffixes like `_inj`, `_mono`, `_injective`, `_surjective`.
* **Match the mathematical contract**: distinguish preservation (`map_add`, `map_smul`) from
  commutativity, and a `≤` bound from a `<` bound. For inverse laws, check the composition order.
  A name describing the composed operations can explain a round-trip identity better than a
  left/right-inverse label. When improving an existing public name, update every caller (see the
  [compatibility policy](#compatibility-policy)).

### Variable Conventions

We follow Mathlib style, adapted for algebraic code. The conventions below reflect repository usage.
Read adjacent declarations when a role is unclear.

* `u`, `v`, `w`, ...           : Universes
* `α`, `β`, `γ`, ...            : Generic types (in non-algebraic contexts)
* `R`, `M`, `G`, `F`, ...       : Algebraic carrier types (rings, modules,
  groups, fields). Prefer these names in algebraic declarations such
  as `variable {R : Type*} [Semiring R]`
* `a`, `b`, `c`, ...            : Propositions
* `x`, `y`, `z`, ...            : Elements of a generic type
* `h`, `h₁`, ...                : Assumptions / hypotheses
* `p`, `q`                     : Polynomials or predicates (disambiguate by
  type and surrounding context)
* `m`, `n`, `k`, ...            : Natural numbers
* `i`, `j`, `k`, ...            : Indices into vectors, lists, or `Fin n`
  (these may be `ℕ`- or `ℤ`-valued). The convention describes the indexing
  role, not the underlying type.
* `s`, `t`, ...                : Sets or lists

### Symbol Naming Dictionary

When translating theorem statements into names, we use standard mappings for symbols:

**Logic**
| Symbol | Name | Symbol | Name | Symbol | Name |
|---|---|---|---|---|---|
| `∨` | `or` | `∧` | `and` | `¬` | `not` |
| `→` | `of` / `imp` | `↔` | `iff` | `∃` | `exists` |
| `∀` | `all` / `forall` | `=` | `eq` | `≠` | `ne` |

**Sets and Lattices**
| Symbol | Name | Symbol | Name | Symbol | Name |
|---|---|---|---|---|---|
| `∈` | `mem` | `∉` | `notMem` | `⊆` | `subset` |
| `∩` | `inter` | `∪` | `union` | `\` | `sdiff` |
| `≤` | `le` | `<` | `lt` | `⊥` | `bot` |
| `⊤` | `top` | `⊔` | `sup` | `⊓` | `inf` |

**Algebra**
| Symbol | Name | Symbol | Name | Symbol | Name |
|---|---|---|---|---|---|
| `+` | `add` | `*` | `mul` | `^` | `pow` |
| `-` | `neg` / `sub` | `⁻¹`| `inv` | `/` | `div` |
| `∑` | `sum` | `∏` | `prod` | `•` | `smul` |

Use `≤` (`le`) and `<` (`lt`) in theorem statements. Use `≥` (`ge`) or `>` (`gt`) only when
the argument order makes them necessary.

### Syntax and Formatting

* **Line Length**: Keep lines under 100 characters.
* **File Length**: Keep each source file at or below 1500 lines. Divide a longer file into
  modules.
* **Indentation**: Use 2 spaces for indentation.
* **Headers**: Start every file with the copyright block, crediting ArkLib Contributors and naming
  the authors. Do not add a separate AI-attribution line. List only the credited authors on the
  `Authors:` line. A file under `ArkLib/` then follows the module-system shape:
  ```lean
  /-
  Copyright (c) 2026 ArkLib Contributors. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Author Name
  -/
  module

  public import ArkLib.Data.Foo
  public import Mathlib.Bar

  /-!
  # Module docstring
  -/

  @[expose] public section
  ```
* **Imports**: Group imports at the top of the file.
* **Module system**: every file under `ArkLib/` uses Lean's module system (issue #795), so a new
  one must too. The shape is `module` after the copyright block, `public import` for every import,
  then the module docstring, then `@[expose] public section`, as in the header above. Mark
  metaprograms (delaborators, unexpanders, elaborator helpers) `meta`, and use
  `public meta import` for their `Lean.*` and `Qq` dependencies. When a proof needs to unfold a
  definition a dependency did not expose, add `import all M` naming the module that *declares* it.
  Do not write a per-declaration `@[expose]` while the blanket section is present, and do not reach
  for `backward.privateInPublic`. Files under `ArkLibTest/` stay classic on purpose. The
  error-to-fix table in [`docs/wiki/module-system.md`](docs/wiki/module-system.md) covers the
  common failures and their fixes.
* **Operators**: Put spaces on both sides of `:`, `:=`, and infix operators. Place them before a
  line break rather than at the start of the next line.
* **Hypotheses**: Prefer placing hypotheses to the left of the colon (for example, `(h : P) : Q`)
  rather than using arrows (`: P → Q`) when the proof introduces them.
* **Functions**: Prefer `fun x ↦ ...` over `λ x, ...`.
* **Instances**: Use the `where` syntax for defining instances and structures.
* **Binders**: Use a space after binders (for example, `∀ x,` not `∀x,`).
* **Tactic Mode**: Place `by` at the end of the line preceding the tactic block. Indent the tactic
  block.
* **Calculations**: In `calc` blocks, align relations.
* **Empty Lines**: Avoid empty lines *inside* definitions or proofs.
* **Delimiters**: Avoid parentheses where possible. Use `<|` (pipe left) and `|>` (pipe right) to
  reduce nesting. Avoid using `;` to separate tactics unless writing short, single-line tactic
  sequences.
* **Error Messages**: In custom error or trace messages, surround interpolated data with backticks
  (inline) or place it on a new indented line.

### Normal Forms

We aim for consistent representations of equivalent statements:
* **Standard Forms**: Use established normal forms (for example, `s.Nonempty` instead of `s ≠ ∅`) to
  enable dot notation and consistency.
* **Inequalities with Bottom/Top**:
    * In assumptions, use `x ≠ ⊥`, which is easier to check.
    * In conclusions, use the strict bound `⊥ < x`, which is easier to apply.
    * Similarly for top: `x ≠ ⊤` in assumptions, `x < ⊤` in conclusions.

### Tactic Mode & Performance

* **Expose the mathematical structure**: Prefer proofs whose intermediate statements and named
  helper lemmas make the argument visible. If the same induction, extensionality argument, cast,
  or normalization step recurs, look for a missing lemma in the module that owns the underlying
  definition.
* **Use automation on well-scoped goals**: `simp`, `aesop`, `grind`, `omega`, `linarith`, and
  `nlinarith` are all acceptable. They are best used as terminal steps, or after an explicit
  transformation that leaves a clear goal. Avoid using broad automation as an intermediate step
  before a tactic that depends on a particular goal shape.
* **Profile before rewriting for speed**: For a slow proof, use Lean's profiler to locate the
  expensive declaration and tactic. Then consider narrower imports, fewer local hypotheses,
  `simp only`, `grind only`, `linarith only`, or `nlinarith only`, or replace repeated search with
  a reusable structural lemma. Do not perform repository-wide mechanical tactic substitutions
  without measured evidence. Check before/after measurements before claiming a speedup, and
  distinguish import/loading cost from proof elaboration. Keep a short, stable proof when the
  measurements do not reveal a performance problem.
* **Stable terminal `simp` calls**: Keep a short, stable terminal `simp` unless a change improves
  stability or measured performance. A long `simp only [...]` list can hide key lemmas and
  complicate
  renames. Mathlib explains
  [squeezing simp
  calls](https://leanprover-community.github.io/contribute/style.html#squeezing-simp-calls),
  [nonterminal
  simplification](https://leanprover-community.github.io/extras/simp.html#non-terminal-simps),
  and [profiling slow proofs](https://leanprover-community.github.io/extras/speedup.html).
* **Comments**: Use `--` for inline comments and `/- ... -/` for block comments.

### Transparency and API Design

* **Definitions (`def`)**: By default, `def` creates `semireducible` definitions. Tactics such as
  `rw` and `simp` do not usually unfold these definitions without an instruction. Prefer `def` for
  most definitions.
* **Abbreviations (`abbrev`)**: Creates `reducible` definitions that are always unfolded. Use this
  for type synonyms or lightweight aliases where the underlying term should be exposed.
* **Irreducible**: Use `irreducible` (or `structure` wrappers) to seal API boundaries when the
  internal implementation details should not leak.

### Compatibility Policy

ArkLib makes no backward-compatibility guarantees and does not promise deprecation periods. This
holds in particular until the [migration](ROADMAP.md#priority-replace-the-legacy-layer) from the
legacy layer (`ArkLib/OracleReduction/`) to the interaction layer (`ArkLib/Interaction/`) is
complete. [README.md](README.md#two-layers) describes both layers.

When you rename or remove a declaration, update every caller in the same PR.
Avoid keeping the old name as a `@[deprecated]` alias without a concrete reason. For example, a
downstream project can need time to migrate. State that reason in the PR.

### Documentation Standards

Every definition and major theorem should have a docstring.

* **Module Docstrings**: Each file should start with a `/-! ... -/` block containing a title,
  summary, notation, and references.
* **Sectioning Comments**: Use `/-! ### Title -/` to structure large files into sections. These
  appear in the generated documentation.
* **Declaration Docstrings**: Use `/-- ... -/` above definitions and major theorems. State the
  object's meaning or theorem's claim, with the relevant hypotheses and any shorthand needed to
  understand it. Keep the explanation concise and self-contained. A reader should not need a
  paper, a planning document, or proof-development history to understand the declaration.
  Internal Lean declarations may be cross-referenced by name.
* **Syntax**:
    * Use backticks for Lean names: `` `List.map` ``.
    * Use LaTeX for math: `$ f(x) = y $` (inline) or `$$ \sum_{i=0}^n i $$` (display).
* **Tactic Documentation**: Complete and self-contained descriptions for tactics.

### Citation Standards

Lean files should be self-contained descriptions of the mathematics. Their declarations should
remain understandable when a reference is revised or renumbered, or when the same definitions
and theorems appear in several sources. The wiki and KB provide the paper-specific mappings.
The mathematical API should not depend on a particular paper's organization or labels.

In Lean sources, external references belong only in the top-level module docstring (`/-! ... -/`).
This includes bibliographic citations, URLs, and paper-specific theorem/lemma numbers, sections, or
figures. Keep module provenance brief. Link to the corresponding `docs/kb/papers/KEY.md` page or
audit for detailed statement/version correspondence, generalizations, and remaining gaps.
Declaration and section docstrings focus on the mathematics.

When referencing papers in the module docstring:

* **Use citation keys in text**: Reference papers with citation keys like `[ACFY24]` rather than
  full titles or URLs.

* **Include a References section**: Each file that cites papers should have a `## References`
  section in its docstring header:
  ```lean
  ## References
  
  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]
  * [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
      for Reed-Solomon Codes*][BCIKS20]
  ```
  Format: `* [Author Last Name, First Initial, *Title*][citation_key]`.

* **Add BibTeX entries**: All academic papers must have entries in `blueprint/src/references.bib`.
  When adding a new paper, add the BibTeX entry, use the citation key in your Lean file, and list it
  in the References section.

* **Non-academic references**: Implementation references (GitHub repos, specifications) may include
  URLs directly in the module docstring and typically do not need BibTeX entries.

## Code of Conduct

ArkLib follows the principles of the [Mathlib Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md).

Project participation includes contributions, issues, and discussions. Participants agree to the
code of conduct. Treat other contributors with respect. You can report unacceptable behavior to the
maintainers.

## Licensing

Like many other Lean projects, ArkLib is licensed under the terms of the Apache License 2.0 license. The full license text can be found in the [LICENSE](LICENSE) file.

By contributing to ArkLib, you agree that your contributions will be licensed under this same license. Ensure you are comfortable with these terms before submitting contributions.
