## Contributing to ArkLib

We enthusiastically welcome contributions to ArkLib!

Whether you are fixing bugs, improving documentation, or adding new formalizations, your input is valuable. We particularly encourage contributions that address:

* **Active formalizations:** Please see the list of active formalization efforts and their blueprints.
* **Open Issues:** Please see the list of open issues for bugs, requested features, and specific formalization tasks. Issues tagged as `good first issue` or `help wanted` are great places to start.
* **Roadmap Goals:** We maintain a [ROADMAP](ROADMAP.md) outlining the planned direction and major goals for the library.
* **Documentation:** Documentation is actively being worked and will be available as soon as possible.

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

## Style and Naming Guidelines
We aim to adhere to the [Lean community's contribution guidelines](https://github.com/leanprover-community/leanprover-community.github.io/tree/lean4/templates/contribute).
Our [linting script](`./scripts/lint-style.sh`) helps enforce some aspects of these guidelines.

### Naming Conventions

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

### Variable Conventions

* `u`, `v`, `w`, ... : Universes
* `α`, `β`, `γ`, ... : Generic types
* `a`, `b`, `c`, ... : Propositions
* `x`, `y`, `z`, ... : Elements of a generic type
* `h`, `h₁`, ...     : Assumptions/Hypotheses
* `p`, `q`, `r`, ... : Predicates and relations
* `m`, `n`, `k`, ... : Natural numbers
* `i`, `j`, `k`, ... : Integers
* `s`, `t`, ...      : Sets or Lists

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

> **Note**: Mathlib and ArkLib standardize on `≤` (`le`) and `<` (`lt`). Avoid `≥` (`ge`) and `>` (`gt`) in theorem statements unless necessary for argument ordering.

### Syntax and Formatting

* **Line Length**: Keep lines under 100 characters.
* **Indentation**: Use 2 spaces for indentation.
* **Headers**: Use standard file headers including copyright, license (Apache 2.0), and authors.
  ```lean
  /-
  Copyright (c) 2024 Author Name. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Author Name
  -/
  ```
* **Imports**: Group imports at the top of the file.
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

* **Squeezing Simp**: Do not "squeeze" terminal `simp` calls (replacing `simp` with `simp only [...]`) unless necessary for performance or stability. Un-squeezed `simp` is often more readable and robust to minor library changes.
* **Comments**: Use `--` for inline comments and `/- ... -/` for block comments.

### Transparency and API Design

* **Definitions (`def`)**: By default, `def` creates `semireducible` definitions. These are usually not unfolded by tactics like `rw` and `simp` without explicit instruction. This is preferred for most definitions to keep terms manageable.
* **Abbreviations (`abbrev`)**: Creates `reducible` definitions that are always unfolded. Use this for type synonyms or lightweight aliases where the underlying term should be exposed.
* **Irreducible**: Use `irreducible` (or `structure` wrappers) to seal API boundaries when the internal implementation details should not leak.

### Deprecation Policy

* **Renaming**: If you rename a declaration, please ensure you fix any breakage this causes. If that is not possible, keep the old name as a deprecated alias to avoid breaking downstream code immediately.
  ```lean
  @[deprecated (since := "YYYY-MM-DD")] alias oldName := newName
  ```
* **Removal**: For removals, provide a message explaining the transition.
  ```lean
  @[deprecated "Use `better_theorem` instead" (since := "YYYY-MM-DD")]
  theorem old_theorem ...
  ```

### Documentation Standards

Every definition and major theorem should have a docstring.

* **Module Docstrings**: Each file should start with a `/-! ... -/` block containing a title, summary, notation, and references.
* **Sectioning Comments**: Use `/-! ### Title -/` to structure large files into sections. These appear in the generated documentation.
* **Declaration Docstrings**: Use `/-- ... -/` above definitions.
* **Syntax**:
    * Use backticks for Lean names: `` `List.map` ``.
    * Use LaTeX for math: `$ f(x) = y $` (inline) or `$$ \sum_{i=0}^n i $$` (display).
* **Tactic Documentation**: Complete and self-contained descriptions for tactics.

### Citation Standards

When referencing papers in Lean docstrings:

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

* **Non-academic references**: Implementation references (GitHub repos, specifications) may include URLs directly and typically don't need BibTeX entries.

## Code of Conduct

To ensure a welcoming and collaborative environment, ArkLib follows the principles outlined in the [mathlib Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md).

By participating in this project (e.g., contributing code, opening issues, commenting in discussions), you agree to abide by its terms. Please treat fellow contributors with respect. Unacceptable behavior can be reported to the project maintainers.

## Licensing

Like many other Lean projects, ArkLib is licensed under the terms of the Apache License 2.0 license. The full license text can be found in the [LICENSE](LICENSE) file.

By contributing to ArkLib, you agree that your contributions will be licensed under this same license. Ensure you are comfortable with these terms before submitting contributions.
