# /write-technical-prose

Use this workflow for ArkLib documentation, comments, docstrings, commit messages, PR and issue
text, and review comments. Work within the user's requested scope. A prose task does not authorize
publication or unrelated source changes.

1. **Read the source before stating a claim.** Use [CONTRIBUTING.md](../../CONTRIBUTING.md) for
   contribution requirements, including the [statement audit](../../CONTRIBUTING.md#statement-correctness).
   Inspect the relevant definitions, hypotheses, proofs, and test evidence. For a PR description,
   distinguish what changed, which checks actually ran, and what remains uncertain.
2. **Start with what the reader needs.** State the problem, result, or action first. Develop one
   topic per paragraph. Use the [writing guide](../wiki/writing.md) and
   [vocabulary](../wiki/writing-vocabulary.md) when they help; their advice is not a conformance test.
3. **Revise real problems.** Identify a clarity or accuracy problem before changing a passage.
   Keep established technical terms, hypotheses, uncertainty, and requirement strength. Repository
   habit alone does not justify unclear wording.
4. **Compare complete passages.** Read the old and new paragraphs side by side in context.
   Check that the revision keeps the meaning, conditions, and scope, and explain why it is clearer.
   Read the final passage and check any changed links or references.
5. **Leave correct text alone.** If `scripts/check-writing.py` is available, you can use it for
   optional editing suggestions. Read each suggestion in context; it does not establish clarity,
   technical accuracy, or STE conformance. Do not change clear, correct text to silence it.

The [quickstart](../wiki/quickstart.md) describes repository commands.
If the task includes a commit or push, run the validation required by the contribution workflow.
