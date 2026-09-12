# Launch, validate and integrate a decoder workstream

Use this procedure for one group or one bounded subtask from [workstreams](workstreams.md).
The coordinator maintains the [task board](README.md#current-task-board).

## Before launch

Read repository `AGENTS.md`, [verified status](status.md), and [shared contracts](contracts.md).
Check available GitHub and Lean capabilities before promising a branch, compilation, or push.
GitHub connector access alone does not provide a Lean environment.

The source baseline is `3c67cb3fa669985b2add6c5d080a3060c4728789`. A launch should normally use a
newer immutable commit containing this plan and any accepted interfaces. The coordinator supplies
that exact launch SHA, paper revision/excerpts, and dependency commits. Do not work against a
moving branch name or assume that a proposed shared record already exists.

Use a separate checkout/worktree and writable build directory for each active implementation
group. Reuse dependency caches according to workspace policy, but never run concurrent builds
writing the same artifacts. Documentation below does not allocate machines or start agents.

## Assignment template

Copy this block and fill every field before dispatch:

```text
Group/subtask:
Repository: quangvdao/ArkLib
Exact launch base SHA:
Exact interface/dependency SHAs:
Paper revision and available excerpts:
Assigned branch:
Lead and independent reviewer:
Owned production/test/doc files:
Existing files explicitly transferred, if any:
First bounded executable deliverable:
Required theorem statement and assumptions:
Decisive example or failure case:
Acceptance checks:
Remaining dependencies and conditional obligations:
```

Only create or update the assigned worker branch. Do not update the integration branch or
force-push. Keep shared-file changes in a separate proposal unless ownership was transferred.
Do not create overlapping generic algebra representations or expand into another group silently.

## Implement and validate

1. Build a concrete small producer and prove that its result comes from its input.
2. Exercise a nontrivial case that would expose an omitted branch or weakened hypothesis.
3. Build affected production modules and compile their test clients.
4. Export namespaced runtime `run` functions; have the integration owner register them in the
   appropriate executed suite. `lake test` compiles test libraries; an unused `main` is not execution.
5. Stage new production sources so repository source checks and generated imports see them.
6. Follow `AGENTS.md` before committing or pushing. For decoder proofs, use the full gate below.

```bash
./scripts/validate.sh --axioms
```

This checks the project, acceptance clients, warning/source policy, runtime suites, imports,
documentation and axiom regression. The coordinator owns generated `ArkLib.lean`; do not hand-edit
it. In a standalone worker checkout the coordinator may authorize generated-import staging solely
for validation, keeping it outside the worker-owned commit. Record that validation-only diff.
Do not build API docs, change dependency pins, or update the axiom baseline to hide regressions.

If Lean is unavailable, return an explicitly **UNCOMPILED** patch or complete owned files. Include
all checks actually run and exact remaining gaps. Do not claim verification or push a verified
checkpoint. A separate validation worker can repair and certify the patch in a real checkout.

## Handoff template

```text
Group/subtask and assigned branch:
Exact base and dependency SHAs:
Final commit SHA, or UNCOMPILED patch and SHA-256:
Changed files and ownership exceptions:
Executable entrypoint and theorem names:
What runs, and what is specification/reference only:
Commands/checks actually completed and results:
Principal axiom output:
Executed cases and what they distinguish:
Conditional assumptions still requiring other producers:
Known defects, unrun checks and next smallest task:
```

An uncompiled patch is an implementation proposal, not an accepted proof. An isolated successful
example is not general coverage. Separate implemented, locally verified, integrated and accepted
status in every report.

## Coordinator integration

1. Verify the base/dependencies, full diff and owned-file scope.
2. Review the theorem statements and executable call graph against the assigned contract.
3. Integrate one coherent verified slice, resolving shared interfaces centrally.
4. Regenerate and stage the umbrella and register actual runtime tests.
5. Run affected checks and the full required validation gate before publication.
6. Obtain independent review of substantive statement/algorithm changes.
7. Update the task board with the integrated commit, evidence, and remaining obligations.
8. Publish the checkpoint and supply its immutable SHA to dependent groups.

Keep one integration owner for the top-level run, final correctness, dependency pins and public
reader map. Add reviewers and validators as author volume increases; avoid making one compiler
operator the bottleneck for many uncompiled ChatGPT patches.

## Completion gates

- **Slice:** concrete executed producer, correct theorem, meaningful example, clean required checks.
- **Group:** every declared output contract discharged; conditional dependencies instantiated.
- **Decoder milestone:** concrete constructors compose with recovery and produce exact output on
  the named branch; a passing test demonstrates that branch rather than fallback.
- **Whole decoder:** all eight paper procedures, both selection modes, supported-field construction,
  global coverage, public success/exactness and algorithm correspondence are verified together.

Only mark genuinely completed work accepted. A typed unavailable error, caller-supplied solver,
assumed candidate coverage, empty placeholder family, or renamed reference algorithm does not
close the final gate.
