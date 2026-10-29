# Writing Standard

This page sets the standard for English prose in ArkLib. The standard adapts the writing rules of
ASD-STE100 Simplified Technical English (STE), Issue 9. STE makes technical text short, literal,
and difficult to misread. The adaptation keeps those rules and adds rules for mathematical text.

The terms that ArkLib prose uses, and the words to avoid, are in
[`writing-vocabulary.md`](writing-vocabulary.md).

## Scope

The standard applies to prose that a person or an agent writes for the project:

- Markdown files, which include root guides, `docs/`, skills, and READMEs
- Lean module docstrings, declaration docstrings, and comments
- Commit messages
- Pull request bodies, issue bodies, and review comments.

The standard applies to all authors in the same way. Reviewers and tools cannot check a rule that
depends on who wrote a text.

Apply the standard to the text that you add or change. A pull request does not have to rewrite
text that it does not touch.

The standard does not apply to:

- Lean code, formulas, commands, and other code
- Quoted text, for example a quotation from a paper or a verbatim error message
- Titles of papers, documents, and other works
- Generated files, the bibliography, and license text.

## Text types

STE gives different limits to two types of text. Identify the type of your text before you
apply the rules.

| Type | Function | Examples in ArkLib | Sentence limit |
|---|---|---|---|
| Procedural | Tells the reader what to do | Skills, `AGENTS.md`, checklists, and numbered steps | 20 words |
| Descriptive | Gives information | Docstrings, comments, wiki and KB pages, commit, PR, and issue bodies | 25 words |

Do not put procedural and descriptive items in the same list.

## Rules

Each rule names the STE rule that it adapts. The label *ArkLib* marks a rule that has no STE
source. Reviewers cite a rule by its identifier, for example "S1".

### Words

- **W1.** Use the most common word that gives the correct meaning. (STE 1.1)
- **W2.** Use the terms in [`writing-vocabulary.md`](writing-vocabulary.md) only with their listed
  meanings. (STE 1.3, 1.5, 1.8, 1.12)
- **W3.** Use one term for one concept in a text. Do not change between synonyms to vary the
  text. (STE 1.11, 9.4)
- **W4.** Write a multi-word noun with no more than three words. Use "of", "for", or "on" to
  divide a longer group. (STE 2.1)
- **W5.** If an established term has more than three words, write it in full the first time. Then
  use its abbreviation: "mutual correlated agreement (MCA)". (STE 2.2)
- **W6.** Do not use phrasal verbs, for example "set up", "carry out", "figure out", or "point
  out". Use a single verb. (STE 9.3)
- **W7.** Do not use Latin abbreviations, for example "e.g.", "i.e.", "etc.", "cf.", or "resp.".
  Write the English words. (STE GR-6)
- **W8.** Use American English spelling. (STE 1.14)
- **W9.** Use gender-neutral language. For a person whose pronouns you do not know, use "they".
  (STE GR-7)

### Verbs

- **V1.** Use the simple present, simple past, simple future, imperative, and infinitive forms.
  Do not use the perfect or the progressive forms. (STE 3.2, 3.4)
  Write "this pull request adds", not "this pull request has added". After a modal verb, keep the
  perfect form when it carries a hedge: "the build may have failed".
- **V2.** Use the "-ing" form only in a technical noun, for example "folding", "batching", or
  "ring switching". Do not start a clause with an "-ing" form. (STE 3.5)
- **V3.** Use the active voice. Make the agent the subject: a declaration, a tactic, a tool,
  the prover, or "we". (STE 3.6)
- **V4.** Use the passive voice only when the agent is unknown or not relevant. A past participle
  that gives a state is not passive voice: "`C` is closed under addition". (STE 3.3, 3.6)
- **V5.** Use a verb, not a noun, to describe an action. Write "the verifier queries the oracle",
  not "the verifier performs a query to the oracle". (STE 3.7)
- **V6.** After "prove", "show", "assume", and "make sure", write "that". (STE GR-1)

### Sentences

- **S1.** Write procedural sentences of no more than 20 words. Write descriptive sentences of no
  more than 25 words. Count words as [Word count](#word-count) specifies. (STE 5.1, 6.3)
- **S2.** Give each sentence one topic. Give each procedural sentence one instruction, unless two
  actions occur at the same time. (STE 4.1, 5.2, 6.1)
- **S3.** If an instruction has a condition, write the condition first: "If the build fails, read
  the log." (STE 5.4)
- **S4.** Write instructions in the imperative. Do not write "you must" before an instruction
  unless the instruction is important for correctness. (STE 5.3)
- **S5.** Do not omit articles, subjects, or verbs to make a sentence shorter. Do not use
  contractions. (STE 4.2, 4.5)
- **S6.** Connect related sentences with words such as "and", "but", "then", "thus", and "as a
  result". (STE 4.4)
- **S7.** Make sure that each pronoun refers to one noun. After "this" or "these", write the
  noun: "this lemma", not "this". (STE GR-3, GR-4)
- **S8.** Use a note only to give information. Do not put an instruction in a note. (STE 5.5)

### Paragraphs

- **P1.** Give each paragraph one topic. Start the paragraph with a sentence that states that
  topic. (STE 6.4, 6.5)
- **P2.** Write no more than six sentences in a paragraph. (STE 6.6)
- **P3.** Give information gradually. Define a term or a notation before you use it. (STE 6.1)

### Lists

- **L1.** Use a vertical list for three or more items, steps, or conditions. (STE 4.3)
- **L2.** Introduce a list with a sentence or a clause that ends with a colon. Make sure that
  each item completes that sentence or clause. (STE 4.3)
- **L3.** Start each item with an uppercase letter. Use the same punctuation at the end of all
  items in a list. Do not end an item with a semicolon. (STE 4.3)
- **L4.** Use a numbered list for steps that occur in a sequence. (STE 5.2)

### Punctuation

- **U1.** Do not use semicolons in prose. Write two sentences. (STE 8.1)
- **U2.** Do not join two clauses with a dash. Write two sentences. (*ArkLib*)
- **U3.** Use a hyphen to join words that modify a noun as one unit: "round-by-round soundness".
  (STE 8.2)
- **U4.** Use parentheses to give an abbreviation, an explanation, a reference, or an
  alternative. (STE 8.3)
- **U5.** Use bold text only for the term in a definition or the label of a list item.
  (*ArkLib*)

### Word count

Count words as STE does, with extensions for technical text (STE 8.4 to 8.7). Each of these
elements counts as one word:

- A number, or a number with its unit
- An abbreviation, for example "MCA" or "RS"
- A code span, for example a Lean name or a command
- A formula in `$...$` or `$$...$$`
- A citation key, for example `[BCIKS20]`
- A hyphenated word
- A quotation, a title, or a proper noun
- Text in parentheses.

The text in parentheses also counts as a separate sentence. In a vertical list, the colon ends
the introductory sentence, and each item counts as a separate sentence.

### Claims

STE controls the form of a text. These rules control what a text claims. They come from the
review of ArkLib pull requests and have no STE source.

- **C1.** State only what the code establishes. If a result depends on an admission (`sorry`) or
  on an extra hypothesis, say so. (*ArkLib*)
- **C2.** Keep the strength of each claim. Do not remove a hypothesis or a qualifier, and do not
  change "can" to "does". Do not add a fact that the source does not give. (*ArkLib*)
- **C3.** Describe the present state of the library. Do not describe its history with words such
  as "now", "no longer", "previously", or "new". (*ArkLib*)
- **C4.** Do not refer to internal planning codes, plan files, or session notes. A reader of the
  merged tree cannot find them. (*ArkLib*)
- **C5.** Do not use words that claim quality without evidence, for example "robust",
  "seamless", "comprehensive", or "powerful". Give the measurement or the reason. (*ArkLib*)
- **C6.** Do not write "clearly", "obviously", or "trivially" in place of an argument. Give the
  reason or the name of the lemma. (*ArkLib*)
- **C7.** Make each point one time. Do not end a text with a summary of that text. (*ArkLib*)
- **C8.** In Lean files, put paper references only in the module docstring, as
  [`CONTRIBUTING.md`](../../CONTRIBUTING.md#citation-standards) specifies. (*ArkLib*)

The history of a change belongs in the commit message and the pull request body. Rule C3 applies
to the library, not to the description of a change.

### Mathematical conventions

Mathematical text has conventions that STE does not cover. These conventions are permitted:

- "Let", "fix", and "suppose" at the start of a statement introduce notation. They are not
  instructions, so rule S4 does not apply to them.
- "We" refers to the author and the reader together, for example in a proof sketch.
- A word can be a technical noun and a technical verb when the field uses both forms, for
  example "bound" and "query". STE permits a word that is in both categories.
- In prose, write "if and only if". In a formula, use `↔`.

## Examples

These examples show the rules on ArkLib text. The text in the first column is quoted, so it is
exempt from the rules.

| Before | After | Rules |
|---|---|---|
| "This lemma, which is crucially used in the main theorem, shows that folding preserves proximity; i.e., close words fold to close words." | If $f$ is $\delta$-close to $C$, then the fold of $f$ is $\delta$-close to the folded code. The soundness theorem uses this lemma. | U1, W7, C5, S2 |
| "This PR has refactored the proximity-error API and leverages a new abstraction to seamlessly unify the four definitions." | This pull request replaces the four proximity-error definitions with one definition that takes the error notion as a parameter. | V1, C5, W1 |
| "Make sure the base is fetched and, if there's a merge in progress, use the two-dot diff instead since three-dot over-reports." | 1. Fetch the canonical base. 2. If a merge is in progress, use `git diff origin/main`. | S2, S3, S5, L4 |
| "Now uses the shared lemma (previously inlined)." | Applies the triangle inequality for the Hamming distance. | C3 |
| "Fixed lints; bumped baseline." | Update the axiom baseline for the renamed lemmas. | U1, S5 |

## Relation to ASD-STE100

This standard keeps the STE rules in sections 2 to 6, 8, and 9, with these changes:

| STE part | Change in ArkLib |
|---|---|
| Rules 1.1 to 1.4, the dictionary | Replaced. Rule W1 and the ArkLib vocabulary replace the STE dictionary, which does not cover mathematics. |
| Rules 1.5 to 1.13, technical nouns and verbs | Kept. The ArkLib vocabulary lists them for this subject field. |
| Rule 3.6, active voice | Adapted for the mathematical conventions above. |
| Rule 4.3, punctuation of list items | Adapted. Rule L3 requires the same punctuation for all items. |
| Rule 8.6, word count | Extended to code spans, formulas, and citation keys. STE counts a formula as one word. |
| Section 7, safety instructions | Not used. ArkLib text has no safety instructions. |

ASD owns the copyright and the trademark of ASD-STE100. This page gives the ideas of the STE
rules in its own words and with its own examples. It does not reproduce the text, the examples,
or the dictionary of the standard. ArkLib text is not certified STE text, and this page does not
claim compliance with STE. To read the full standard, request a free copy from
[ASD](https://www.asd-europe.org/standards-specifications/simplified-technical-english/download-asd-ste-100).
