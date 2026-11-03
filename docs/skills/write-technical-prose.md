# /write-technical-prose

Use this workflow when drafting or revising ArkLib documentation, comments, docstrings, commit
messages, PR text, issue text, or review comments. Use it for short comments as well as long guides.
Work on the text the user requested. Writing review does not authorize unrelated source changes
or publication.

## Read the local requirements

Read the [writing standard](../wiki/writing.md) and [vocabulary](../wiki/writing-vocabulary.md).
Read the relevant section of [CONTRIBUTING.md](../../CONTRIBUTING.md) for the contribution or text
being prepared. The guide owns the requirements. This skill explains how to apply them.

Treat existing prose as material to assess, not a style to preserve automatically. Use STE's
writing principles to correct defects. Keep established identifiers, quotations, and technical
meanings accurate. Consult the official standard when a rule's source or a word's approval matters.
Do not invent a dictionary approval or claim full STE conformance from a linter result.

## Establish the facts

Read the source needed for the claims in the passage. A theorem name or a successful build alone
does not establish a mathematical claim. Inspect the statement, its hypotheses, and the relevant
proof or axiom evidence. Use the [statement audit](../../CONTRIBUTING.md#statement-correctness)
when preparing a mathematical contribution for review.

For a PR description, distinguish the change, the checks actually run, and the remaining gaps.
Keep output instructions separate from repository facts. A request for a draft does not establish
a PR's status, approval, or CI result. State those facts only when the source provides them.

For a review comment, identify the affected code or statement and explain the consequence.
For reference documentation, describe the interface or result that exists in the reviewed source.
Do not substitute a session history for that explanation.

If the source does not support a claim, narrow or remove the claim. Preserve uncertainty when the
evidence is incomplete. A prose task does not by itself require a new proof, build, or experiment.

## Draft and revise

Choose procedural or descriptive writing from the passage's purpose. Start with the result,
problem, or action the reader needs. Develop one topic in each paragraph. Add headings, lists,
and examples when they make the text easier to use.

Revise the text for direct verbs, clear actors and antecedents, consistent terms, and short
sentences. Introduce unfamiliar concepts before using them. Remove empty praise and repetition.
Keep instructions distinct from explanations and optional advice.

Compare every mathematical rewrite with its source. Keep the hypotheses, quantifiers, negations,
error terms, exceptional cases, and direction of implication. Preserve time and requirement
strength: "may have failed" does not mean "failed", and "recommended" does not mean "required".
A shorter expression is useful only when it keeps the intended meaning.

Do not let a writing rule change standard terminology. A rule can conflict with a term or language
pattern that is standard in cryptography research and engineering, computer science, or mathematics.
In that case, keep the standard form and apply the rules to the rest of the passage. Repository
habit alone does not make a wording standard.

Use the vocabulary to resolve ambiguous terms, not to erase valid technical meanings.
"Complete the template" does not claim protocol completeness. A protocol statement and a theorem
statement need different qualifiers only when the context could confuse them.

## Use the checker when available

If `scripts/check-writing.py` exists in this checkout, use it as an editing aid:

```bash
uv run --no-project --python 3.12 python scripts/check-writing.py path/to/document.md
uv run --no-project --python 3.12 python scripts/check-writing.py --stdin description < /tmp/pr-description.md
```

For changed prose, pass the actual review base to `--base`. A stacked PR can have a feature branch
as its base. Do not assume that every PR targets `main`.

Read each finding before editing. Counts and grammar patterns are approximations. Correct real
defects, retain accurate technical expressions, and report a recurring checker defect with an
example. Do not rewrite a correct claim merely to make the checker quiet.

The checker does not establish clarity, source fidelity, dictionary compliance, or permission to
publish. If it is absent, do the same reading pass manually. Keep the writing standard applicable.

## Read the final text before handoff

Read the complete affected passage after the last edit. Confirm that its structure is useful and
its claims still agree with the source. Check any links or references that the edit changes.
A good sentence can still be wrong in its paragraph.

Return or save the requested text. Publish it only when the user's instructions authorize that
action. If the task includes a commit or push, run the validation required by the contribution
workflow first. Report material evidence gaps without adding a standard disclaimer to every text.
