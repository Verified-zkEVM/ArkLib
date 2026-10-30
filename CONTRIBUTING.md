## Contributing to ArkLib

We enthusiastically welcome contributions to ArkLib!

Whether you are fixing bugs, improving documentation, or adding new formalizations, your input is valuable. We particularly encourage contributions that address:

* **Active formalizations:** The [ROADMAP](ROADMAP.md) lists what is complete, what is in progress, and the planned directions, with links to the tracking issues.
* **Open Issues:** Please see the [list of open issues](https://github.com/Verified-zkEVM/ArkLib/issues) for bugs, requested features, and specific formalization tasks. Issues tagged as `good first issue` or `help wanted` are great places to start.
* **Solicited proofs:** Some true external results are stated in the library with their proofs deliberately left open for contributors; see [issue #1352](https://github.com/Verified-zkEVM/ArkLib/issues/1352).
* **Documentation:** Start with [AGENTS.md](AGENTS.md) for the one-screen guide, then the [wiki](docs/wiki/README.md) for commands, conventions and workflows.

If you are interested in contributing but unsure where to begin, please get in touch.

### Large Contributions

For substantial contributions, such as a new proof system, we strongly encourage the development of a [blueprint](https://github.com/PatrickMassot/leanblueprint) first.

* **What is a Blueprint?** A blueprint is a document that outlines:
    * The contents of the formalization.
    * The proposed formalization strategy in Lean (key definitions, theorems, assumptions).
    * A dependency graph relating all intermediate results to the final desired result.
    * References to relevant literature.
    * Potential challenges and design choices.
* **Why a Blueprint?** This helps align the contribution with the project's structure and goals *before* significant coding and proving effort is invested. It facilitates discussion and feedback from maintainers and the community. It also makes it easier to manage large efforts in a distributed way.
* **Process:** Please open a new discussion or issue to propose your planned contribution and discuss the blueprint before starting implementation.

## Pull Request Guidelines

We follow the specific convention for pull request titles and descriptions used by the Lean community.

### Title Format
The title should follow the format:
```
<type>(<optional-scope>): <subject>
```

**Types:**
* `feat`: New feature
* `fix`: Bug fix
* `doc`: Documentation changes
* `style`: Formatting, missing semicolons, etc.
* `refactor`: Code refactoring
* `test`: Adding missing tests
* `chore`: Maintenance
* `perf`: Performance improvements
* `ci`: CI workflow changes

**Subject:**
* Use imperative, present tense ("change" not "changed" or "changes").
* Do not capitalize the first letter.
* No dot (.) at the end.

### Description
The description should include:
* Motivation for the change.
* Contrast with previous behavior.
* References to issues (e.g., `Closes #123`).

### Review and Merge Readiness

A PR may be opened for review with unfinished proofs, provided its remaining admissions and
validation status are clear. Before merging into `main`, it must introduce no new `sorry`/`admit`
or additional `sorryAx` debt relative to the canonical base. Closing one gap does not offset a
new admission elsewhere. Updating `scripts/axiom_baseline.json` cannot authorize new debt;
baseline changes record verified closures or renames of existing debt.

The baseline's `sorry` list is empty. Its only admitted entries are *solicited proofs*: true,
faithfully stated external results whose research-sized proofs are left open for contributors.
A solicited entry is added only after review, names a tracking issue that its docstring links,
and must stay a leaf: no declaration outside the solicited list may depend on it. A PR that proves
one removes its entry. [`scripts/README.md`](scripts/README.md) states the exact rules that
`lake exe axiomsweep --check` enforces.

New declarations may depend only on a subset of Lean's three standard axioms:
`propext`, `Classical.choice`, and `Quot.sound`. Do not introduce custom axioms, `sorryAx`,
or native-compiler trust dependencies. Solicited proofs are not an exception for new
declarations.

Merge readiness also requires `./scripts/validate.sh` to pass: resolve all linter/style issues,
all production non-`sorry` warnings, and all test warnings. Fix the source rather than suppressing
linters. For proof changes, run `./scripts/validate.sh --axioms` and review the source-admission
and baseline diffs against `main`, including admissions in examples or default arguments that
may not appear as exported declarations.

## Style and Naming Guidelines
We aim to adhere to the [Lean community's contribution guidelines](https://github.com/leanprover-community/leanprover-community.github.io/tree/lean4/templates/contribute).
The default validation command runs ArkLib's Lean-native source-policy gate. You can run its
text-and-import checks directly with `lake exe lint-style`. The normal `lake build` also loads a
Lean syntax-tree plugin that rejects linter suppressions; neither gate supports exceptions. The
text gate is an independent, fail-closed backstop. It rejects `set_option` for the `linter`, `pp`,
`profiler` and `trace` option families and for the elaboration budgets `maxHeartbeats`,
`maxRecDepth` and `synthInstance.*`, anywhere in the source, including comments. If a proof needs a
larger budget, make it cheaper instead (see [Tactic Mode & Performance](#tactic-mode--performance)).
`nolint` attribute heads are also reserved in active code and literal bodies. Put policy examples
in `scripts/LintStyleFixtures`, which is outside the library-source closure; policy-like quoted
identifiers and syntax quotations are reserved for the same reason.

### Acceptance Tests

Keep compile-time examples and regression tests in `ArkLibTest/`, mirroring production paths.
`lake test` builds them, and `./scripts/validate.sh` runs the test target with a zero-warning budget.
Stage new tests before validation. Production modules must not import tests; both trees share the
source-style policy and build-time lint plugin. See [ArkLibTest/README.md](ArkLibTest/README.md).

Use acceptance examples with satisfiable hypotheses that exercise the claimed behavior. When an
error bound is intended to be nontrivial, include an instance with error below one. Exercise a
boundary or a necessary hypothesis when that distinguishes the intended statement from a weaker one.

### Computability

Make definitions computable wherever possible. Protocols, provers, verifiers, encoders,
decoders, samplers, and anything whose purpose is to run a program or compute a value must
be executable. Carry the necessary representations, decision procedures, and witnesses as data;
do not replace an algorithm with classical choice. If the current interface lacks that data,
redesign it or provide a verified executable implementation before calling the contribution
merge-ready.

Purely mathematical objects used in statements and proofs may remain `noncomputable` when
there is a concrete reason. Mark those declarations individually and explain the blocker in
the module overview; avoid blanket `noncomputable section` declarations that hide accidental
code-generation failures. Where executable data has a mathematical view, prove their agreement.

Check code generation from a caller outside any `noncomputable section`, then execute small
concrete cases with independently known results, including relevant failure or boundary cases.
Neither removing the keyword nor an axiom-clean theorem establishes executability: admitted
bodies can compile to a panic. Executable specifications allow testing and other validation
that can expose mistaken or vacuous declarations; they complement satisfiable hypotheses and
correctness proofs rather than establishing those properties by themselves. Follow
[the computability workflow](docs/skills/make-computable.md) when an audit finds a blocker.

### Naming Conventions

The [Mathlib-style naming conventions](https://leanprover-community.github.io/contribute/naming.html)
below are the repository standard. Consistent names give readers and tools predictable search
terms within ArkLib and across Lean libraries. Use established mathematical terminology and
namespace structure rather than introducing local synonyms.

* **Files**: `UpperCamelCase.lean` (e.g., `BinarySearch.lean`).
* **Types and Structures**: `UpperCamelCase` (e.g., `MonoidHom`, `Visualizer`).
* **Functions and Terms**: `lowerCamelCase` (e.g., `binarySearch`, `isPrime`).
* **Theorems and Proofs**: `snake_case` (e.g., `add_comm`, `list_reverse_id`).
* **Acronyms**: Treat as words (e.g., `HtmlParser` not `HTMLParser`).
* **Prop-valued Classes**: Use `UpperCamelCase`. If the class is an adjective, use the `Is` prefix (e.g., `IsCompact`, `IsPrime`). If it is a noun, no prefix is needed (e.g., `Group`, `TopologicalSpace`).
* **Spelling**: Use American English for declaration names (e.g., `analyze` not `analyse`, `color` not `colour`).
* **Dot Notation**: Use namespaces to group related definitions (e.g., `List.map`). This enables dot notation (e.g., `l.map f`) when the type is known. Use manual dot notation for logical connectives and equality (e.g., `And.intro`, `Eq.refl`, `Iff.mp`).
* **Axiomatic Names**: Use standard names for properties: `refl`, `symm`, `trans`, `comm`, `assoc`, `inj` (injective), `congr`.
* **Identifiers**: 
    * Use namespaces for logical properties (e.g., `And.comm`, `Or.intro`).
    * Use descriptive names for arithmetic/algebraic properties (e.g., `mul_comm`, `add_assoc`).
* **No paper items in names**: name a declaration for what it says, never for where it came from.
  No author-year suffix (`..._gk16`), no numbering (`lemma_4_3`, `claimA2_...`, `thmA2`), and no
  internal planning code (`milestone_F5`, `design_D5`). Such a name drifts the moment the source is
  renumbered, revised, or joined by a second citation, and it tells a reader nothing the statement
  does not. Cite the source in the module docstring's `## References` section instead (see
  [Citation Standards](#citation-standards)). State the chosen mathematical formulation directly in
  the declaration docstring. Keep brief provenance in the module docstring and paper-specific
  statement/version mappings in the KB.

### Theorem Naming Logic

* **Hypotheses**: Use `_of_` to separate hypotheses, listed in the order they appear (e.g., `lt_of_succ_le` means "less than *follows from* successor less equal").
* **Variants**: Use `left` or `right` to describe which argument changes or is relevant (e.g., `add_le_add_left`).
* **Structural Lemmas**:
    * `ext`: For extensionality (`∀ x, f x = g x → f = g`).
    * `iff`: For bidirectional implications.
    * `inj` / `injective`: For injectivity results.
    * `mono` / `antitone`: For monotonicity.
* **Induction/Recursion**:
    * `induction_on` / `recOn`: Use when the value comes before the constructions (motive eliminates to Prop / Type).
    * `induction` / `rec`: Use when the constructions come before the value.
* **Predicates**: Generally use prefixes (e.g., `isClosed_Icc` not `Icc_isClosed`). Exceptions include property suffixes like `_inj`, `_mono`, `_injective`, `_surjective`.
* **Match the mathematical contract**: distinguish preservation (`map_add`, `map_smul`) from
  commutativity, and a `≤` bound from a `<` bound. For inverse laws, check the composition order;
  a name describing the composed operations often makes a round-trip identity clearer than a
  left/right-inverse label. When improving an existing public name, update every caller (see the
  [compatibility policy](#compatibility-policy)).

### Variable Conventions

We follow Mathlib style, adapted for algebraic code. The conventions below
reflect actual usage across the repository; please consult adjacent files
when in doubt.

* `u`, `v`, `w`, ...           : Universes
* `α`, `β`, `γ`, ...            : Generic types (in non-algebraic contexts)
* `R`, `M`, `G`, `F`, ...       : Algebraic carrier types (rings, modules,
  groups, fields) — preferred over `α`, `β` in algebraic declarations such
  as `variable {R : Type*} [Semiring R]`
* `a`, `b`, `c`, ...            : Propositions
* `x`, `y`, `z`, ...            : Elements of a generic type
* `h`, `h₁`, ...                : Assumptions / hypotheses
* `p`, `q`                     : Polynomials or predicates (disambiguate by
  type and surrounding context)
* `m`, `n`, `k`, ...            : Natural numbers
* `i`, `j`, `k`, ...            : Indices into vectors, lists, or `Fin n`
  (these may be `ℕ`- or `ℤ`-valued; the convention is about the indexing
  role, not the underlying type)
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

> **Note**: In adherence with mathlib, we standardize on `≤` (`le`) and `<` (`lt`). Avoid `≥` (`ge`) and `>` (`gt`) in theorem statements unless necessary for argument ordering.

### Syntax and Formatting

* **Line Length**: Keep lines under 100 characters.
* **Indentation**: Use 2 spaces for indentation.
* **Headers**: Start every file with the copyright block, crediting ArkLib Contributors and naming
  the authors. A file under `ArkLib/` then follows the module-system shape:
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
* **Operators**: Put spaces on both sides of `:`, `:=`, and infix operators. Place them before a line break rather than at the start of the next line.
* **Hypotheses**: Prefer placing hypotheses to the left of the colon (e.g., `(h : P) : Q`) rather than using arrows (`: P → Q`) when the proof introduces them.
* **Functions**: Prefer `fun x ↦ ...` over `λ x, ...`.
* **Instances**: Use the `where` syntax for defining instances and structures.
* **Binders**: Use a space after binders (e.g., `∀ x,` not `∀x,`).
* **Tactic Mode**: Place `by` at the end of the line preceding the tactic block. Indent the tactic block.
* **Calculations**: In `calc` blocks, align relations.
* **Empty Lines**: Avoid empty lines *inside* definitions or proofs.
* **Delimiters**: Avoid parentheses where possible. Use `<|` (pipe left) and `|>` (pipe right) to reduce nesting. Avoid using `;` to separate tactics unless writing short, single-line tactic sequences.
* **Error Messages**: In custom error or trace messages, surround interpolated data with backticks (inline) or place it on a new indented line.

### Normal Forms

We aim for consistent representations of equivalent statements:
* **Standard Forms**: Use established normal forms (e.g., `s.Nonempty` instead of `s ≠ ∅`) to enable dot notation and consistency.
* **Inequalities with Bottom/Top**:
    * In **assumptions**, use `x ≠ ⊥` (easier to check).
    * In **conclusions**, use `⊥ < x` (more powerful result).
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
* **Do not squeeze stable terminal `simp` calls by default**: Replacing a short terminal `simp`
  with a long `simp only [...]` list can obscure the important lemmas and make renames more
  disruptive. Squeeze when it improves stability or produces a measured performance benefit.
  This follows Mathlib's guidance on
  [squeezing simp calls](https://leanprover-community.github.io/contribute/style.html#squeezing-simp-calls),
  [nonterminal simplification](https://leanprover-community.github.io/extras/simp.html#non-terminal-simps),
  and [profiling slow proofs](https://leanprover-community.github.io/extras/speedup.html).
* **Comments**: Use `--` for inline comments and `/- ... -/` for block comments.

### Transparency and API Design

* **Definitions (`def`)**: By default, `def` creates `semireducible` definitions. These are usually not unfolded by tactics like `rw` and `simp` without explicit instruction. This is preferred for most definitions to keep terms manageable.
* **Abbreviations (`abbrev`)**: Creates `reducible` definitions that are always unfolded. Use this for type synonyms or lightweight aliases where the underlying term should be exposed.
* **Irreducible**: Use `irreducible` (or `structure` wrappers) to seal API boundaries when the internal implementation details should not leak.

### Compatibility Policy

ArkLib makes no backward-compatibility guarantees and does not promise deprecation periods. This
holds in particular until the [migration](ROADMAP.md#priority-replace-the-legacy-layer) from the
legacy layer (`ArkLib/OracleReduction/`) to the interaction layer (`ArkLib/Interaction/`) is
complete; [README.md](README.md#two-layers) describes both layers.

When you rename or remove a declaration, update every caller in the same PR. Keeping the old name
as a `@[deprecated]` alias is discouraged: add one only with a concrete reason, such as a
downstream project that needs time to migrate, and say so in the PR.

### Documentation Standards

Every definition and major theorem should have a docstring.

* **Module Docstrings**: Each file should start with a `/-! ... -/` block containing a title, summary, notation, and references.
* **Sectioning Comments**: Use `/-! ### Title -/` to structure large files into sections. These appear in the generated documentation.
* **Declaration Docstrings**: Use `/-- ... -/` above definitions and major theorems. State the
  object's meaning or theorem's claim, with the relevant hypotheses and any shorthand needed to
  understand it. Keep the explanation concise and self-contained: a reader should not need a
  paper, a planning document, or proof-development history to understand the declaration.
  Internal Lean declarations may be cross-referenced by name.
* **Syntax**:
    * Use backticks for Lean names: `` `List.map` ``.
    * Use LaTeX for math: `$ f(x) = y $` (inline) or `$$ \sum_{i=0}^n i $$` (display).
* **Tactic Documentation**: Complete and self-contained descriptions for tactics.

### Citation Standards

Lean files should be self-contained descriptions of the mathematics. Their declarations should
remain understandable when a reference is revised or renumbered, or when the same definitions
and theorems appear in several sources. The wiki and KB provide the paper-specific mappings;
the mathematical API should not depend on a particular paper's organization or labels.

In Lean sources, external references belong only in the top-level module docstring (`/-! ... -/`).
This includes bibliographic citations, URLs, and paper-specific theorem/lemma numbers, sections,
or figures. Keep module provenance brief and link to the corresponding `docs/kb/papers/KEY.md`
page or audit for detailed statement/version correspondence, generalizations, and remaining gaps.
Declaration and section docstrings focus on the mathematics.

When referencing papers in the module docstring:

* **Use citation keys in text**: Reference papers with citation keys like `[ACFY24]` rather than full titles or URLs.

* **Include a References section**: Each file that cites papers should have a `## References` section in its docstring header:
  ```lean
  ## References
  
  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]
  * [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
      for Reed-Solomon Codes*][BCIKS20]
  ```
  Format: `* [Author Last Name, First Initial, *Title*][citation_key]`.

* **Add BibTeX entries**: All academic papers must have entries in `blueprint/src/references.bib`. When adding a new paper, add the BibTeX entry, use the citation key in your Lean file, and list it in the References section.

* **Non-academic references**: Implementation references (GitHub repos, specifications) may include
  URLs directly in the module docstring and typically do not need BibTeX entries.

## Code of Conduct

To ensure a welcoming and collaborative environment, ArkLib follows the principles outlined in the [mathlib Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md).

By participating in this project (e.g., contributing code, opening issues, commenting in discussions), you agree to abide by its terms. Please treat fellow contributors with respect. Unacceptable behavior can be reported to the project maintainers.

## Licensing

Like many other Lean projects, ArkLib is licensed under the terms of the Apache License 2.0 license. The full license text can be found in the [LICENSE](LICENSE) file.

By contributing to ArkLib, you agree that your contributions will be licensed under this same license. Ensure you are comfortable with these terms before submitting contributions.
