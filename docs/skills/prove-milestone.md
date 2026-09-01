# /prove-milestone

Use this workflow to discharge one Hachi milestone named by a row, subprotocol, milestone code, or
file in
[`hachi-overview.html`](../../ArkLib/Commitments/Functional/Hachi/hachi-overview.html). The goal is
not merely to make Lean accept existing statements. First establish that the statements encode the
intended protocol and theorem; then make every proof obligation tractable; only then fill the proof
bodies without changing what they mean.

This workflow is deliberately stricter than [`discharge-lemmas.md`](discharge-lemmas.md). A Hachi
milestone is complete only when its paper contract, definitions, public theorem, package, and
composition seam agree and its entire proof-obligation closure is constructive and `sorry`-free.

## Invocation contract

Require an unambiguous target such as “row 8 / paired sumcheck rounds”, “F7”, or
`Sumcheck/Rounds.lean`. If the requested name selects several dashboard entries, resolve the
smallest semantic subprotocol that has its own input relation, output relation, verifier, and CWSS
certificate; ask only if two materially different scopes remain.

Treat the dashboard as an index and status report, not as the specification. Establish the target
from all of these sources:

- the exact version of the primary paper cited by the code, especially the referenced definition,
  figure, equations, lemma, bounds, and surrounding qualifications;
- the target Lean files and their imports, docstrings, exported package, and consumers;
- the seam table and sorry provenance in `Hachi/Composition.lean`;
- `docs/kb/papers/NOZ26.md` and relevant `docs/kb/audits/`;
- the generic ArkLib definitions of the claimed security notion and composition operator.

The paper is primary. Repository notes explain intent and known deviations but cannot establish
paper faithfulness by themselves. Record the paper version and page/figure/equation references. If
the primary source is unavailable, do not declare Stage 1 complete.

If the user's requested approach contradicts the repo's verified design notes (e.g. a directed
reuse or restructuring that a KB analysis argues against), surface the conflict as an
explicit scope question with a recommendation *before* Stage 1 design work, and record the user's
decision in the scope manifest; do not silently follow either side.

## Global invariants

Maintain these invariants throughout the task:

1. Preserve unrelated and pre-existing work. Start with `git status --short`, record the initial
   diff and untracked files in scope, and never reset, overwrite, or silently absorb user changes.
2. Keep a target-closure ledger. Include the milestone's semantic definitions, proof declarations,
   helper lemmas, exported package, and the immediate composition seam. Do not count unrelated
   Hachi sorries as part of the target, but do expose any target theorem that transitively depends
   on them.
3. Use the exact primary-source claim as the comparison point. Label every deliberate deviation as
   a strengthening, weakening, repair, generalization, or implementation-only representation
   choice, and justify the direction needed for soundness and completeness.
4. Never make a theorem easier by silently strengthening an input relation, weakening an output
   relation, shrinking the challenge space, adding a false/unmotivated hypothesis, or moving a
   verifier check into an assumption.
5. Make the remaining `sorry` count in the target closure monotonically decrease after the Stage 2
   freeze. Do not move, rename, hide, or replace a gap with another trust mechanism.
6. Do not use `native_decide`, a new `classical`/`Classical.*` shortcut in the milestone's own
   proofs, `axiom`, `admit`, `Lean.ofReduceBool`, an unsafe/opaque proof surrogate, or a theorem
   whose transitive axiom set contains `sorryAx`. Do not introduce project axioms. ArkLib's
   accepted **axiom-clean** baseline — the standard the proven QuadEval milestone meets — is
   exactly `{propext, Classical.choice, Quot.sound}` (Mathlib's foundational axioms);
   `Classical.choice` arriving through Mathlib or through an unmodified generic combinator (e.g.
   `ReduceClaim.verifier_coordinateWiseSpecialSoundWith`, which every CWSS milestone reuses) is
   acceptable and need not be eliminated; eliminating it from an individual theorem is sometimes
   possible by reproving constructively or routing around a choice-using combinator, but it is not
   required. Confirm each target declaration's `#print axioms` is a subset of that baseline with no
   `sorryAx` and no project axiom; call such a result "axiom-clean against the baseline", not
   "axiom-free".
7. Use a fresh independent reviewer when subagents are available. Give reviewers the raw paper
   section, Lean files, and current artifacts, not the intended verdict or a proposed fix.

Keep scratch manifests and experiments under `/tmp`, not as new root-level planning files. Promote
new, durable paper findings to `docs/kb/` when they materially change ArkLib's understanding of the
paper.

## Required artifacts

Maintain these artifacts during the run, in the conversation or in temporary files:

- **scope manifest** — target, source files, declarations, imports, consumers, and initial dirty
  state;
- **milestone contract** — paper-to-Lean comparison with exact source references;
- **audit ledger** — findings, severity, resolution, and evidence;
- **proof DAG** — every `sorry`, its dependencies, plan, difficulty, and status;
- **semantic-freeze manifest** — the Stage 2 definitions, declaration signatures, attributes,
  instances, imports, package wiring, and allowed proof-body locations;
- **verification log** — per-proof builds, axiom output, scoped searches, final build, and semantic
  review.
- **skill-improvement log** — end-of-run evidence, candidate edits, decisions, applied changes, and
  validation of the revised skill.

Do not use a prose plan as a substitute for typechecking. Each stage has an explicit exit gate.

## Stage 1 — establish the right formalization

This stage may change definitions, theorem statements, abstractions, hypotheses, and file
boundaries. It must end with the intended API fully stated and typechecking, with intentional proof
holes marking all remaining work.

### 1. Reconstruct the paper contract independently

Before accepting the current Lean design, write a compact contract covering:

| Contract item | Questions to answer |
| --- | --- |
| Claim | What exact correctness, soundness, CWSS, or reduction statement is claimed? |
| Data | What are the public statement, witness, messages, challenges, responses, and commitment data? |
| Protocol | What is sent or sampled in each round, from which space and distribution, and in what order? |
| Acceptance | Which checks run at runtime, and which facts belong to the input or output relation? |
| Extraction | What accepting transcript shape is assumed, what witness/escape is returned, and with what arity/error? |
| Parameters | What degree, norm, cardinality, non-emptiness, distinctness, and field/ring assumptions are required? |
| Composition | What exact relation enters this seam, what relation leaves it, and what data is retained or dropped? |

Translate every row into the corresponding Lean declaration or mark it missing. For relation
changes, state an equality, equivalence, or containment and verify that its direction is the one the
security argument needs. “Looks analogous” is not evidence.

### 2. Run an adversarial formalization audit

Audit from several angles:

- **Faithfulness:** compare quantifier order, indices, dimensions, challenge type and distribution,
  transcript shape, verifier checks, bounds, exceptional/escape cases, and conclusion. Check the
  exact paper verifier, not just an easier relation with a similar name.
- **Security notion:** unfold enough of `coordinateWiseSpecialSound`, guarded verification,
  challenge-tree structure, and package composition to confirm that the formal theorem expresses
  the claimed extraction guarantee.
- **Abstraction quality:** determine whether one declaration mixes distinct mathematical seams,
  whether a paper concept has been encoded twice, or whether a large target should be split at a
  semantic boundary. Keep bridges as statement reshaping; do not conceal protocol work inside one.
- **Hypothesis minimality:** classify every explicit and typeclass hypothesis as a paper premise,
  a representation requirement, a downstream composition requirement, or a proof artifact. Trace
  its use and, in a scratch example, try removing or weakening it. An important paper assumption
  that Lean never uses is also a warning that the theorem may be too weak.
- **Vacuity and countermodels:** try boundary and small cases. Check that challenge spaces and
  relations are inhabited where intended, the verifier is not definitionally always rejecting,
  witnesses carry the claimed information, an impossible hypothesis is not proving everything,
  and the extractor conclusion is not true for an irrelevant reason.
- **Connectivity:** confirm that the audited theorem is the theorem stored in the exported
  `CWSSPackage`/`GCWSSPackage`, that the package exposes the audited relations and verifier, and that
  `Composition.lean` consumes that package at the advertised seam. A correct unused theorem does
  not discharge a milestone.

Apply these Hachi-specific attacks whenever the target can reach the relevant seam:

- Recompute the transitive proof closure through generic CWSS/scalar/guarded composition code and
  planned prerequisites. A row with one local `sorry` can still depend on missing or sorried
  generic machinery.
- For every zero-round adapter, require the exact forward/completeness direction as well as the
  CWSS pullback direction, or document the precise asymmetric containment that is intended. Prove
  stack/unstack and encoding round trips; an empty or overly strong output relation can make the
  pullback theorem meaningless.
- For every `Bool` guard such as a round, final, or trace check, establish `check = true ↔` the
  advertised paper equations and an honest-acceptance lemma before proving soundness. An
  always-false sorried check makes accepting-tree obligations vacuous.
- When an escape event points at `LiftCom.Collision`, trace the required shortness proof for both
  colliding openings back through every relation. A point-evaluation check does not by itself imply
  coefficient/range shortness.
- For table and polynomial encodings, require explicit capacity inequalities, index equivalences,
  padding behavior, reconstruction laws, degree bounds, and the inequalities connecting digit
  bounds to public shortness parameters.
- Audit every division or derived omitted value for a nonzero denominator. In particular, a fixed
  partial-evaluation pivot must not be assumed nonzero for all evaluation points.
- Do not quantify over an arbitrary basis table, packing map, commitment reinterpretation, or
  escape conversion and then use unstated algebraic laws. State and justify independence,
  round-trip, commutation, bound, and escape-validity laws at the right abstraction boundary.
- Treat corrected Lemma 10 as an explicit protocol repair, not a proof of the paper's printed
  uniform-vector protocol. Treat the row-11 `Z`-packing pullback as a known open soundness gap until
  an authorized repair replaces it.
- Re-audit a “proven” dependency when its documented relation or bound is only a containment or a
  modeling generalization of the paper and becomes load-bearing for the target.
- For escape-threaded links, audit the **escape event**, not the relations: the certificate keeps
  ordinary `relIn`/`relOut` and concludes `esc stmt tree ∨ extraction succeeds`. Two things carry
  the content. First, the event must be *honest* — never mentioning the extractor or acceptance
  (`ChallengeTree.EscapeEvent` documents why such an event trivializes any certificate) — and
  *tight*, firing only where extraction genuinely fails; a statement-only event like "some
  collision of this commitment exists" is honest yet worthless because it fires almost everywhere.
  Second, use the **named** form (`…SoundWith`, not its `∃`-closure), so the extraction algorithm
  stays in the statement. Require the constructive anchor — the explicit witness assembler and its
  membership theorem (the `mkWitness`/`mkWitness_mem` pattern) — to be public, named, and cited by
  the module docstring as the auditable content.

Produce a concrete non-vacuity certificate: at least one honest symbolic instance/transcript or
small Lean example, plus a trace showing which verifier checks constrain which output-relation
facts. Use explicit mathematical counterexamples when useful, but do not use `native_decide`, even
for experiments. Independently search ArkLib and Mathlib before adding abstractions or hypotheses.

### 3. Correct the skeleton

Resolve every material audit finding now:

- repair definitions and theorem statements rather than compensating in proofs;
- split the subprotocol only at mathematically meaningful interfaces with explicit relations;
- remove unused or unjustified hypotheses, and add a missing premise only when it belongs to the
  paper or an explicitly approved repair;
- state all useful representation/equivalence/containment and sanity lemmas;
- wire the exact public theorem into the package and its immediate composition consumer;
- give every major definition and theorem a docstring with precise paper references and disclose
  every deliberate divergence.

Keep already-correct proofs. Use `sorry` only for genuine remaining proof bodies. Build each
affected file after statement changes so the skeleton, package, and seam elaborate together.
Every data-bearing definition—encoding, relation data, verifier, protocol spec, extractor,
statement conversion, or witness construction—must be implemented. Never use `sorry` to fabricate
data and then prove propositions about that fabricated value.

If the paper claim appears false or under-specified, do not silently repair it. Isolate the failing
claim, produce the smallest rigorous counterexample or missing obligation possible, distinguish a
faithful model from candidate repairs, and obtain a repair decision unless the target already names
an approved corrected variant. A dashboard entry marked as an open gap is not discharged by
assuming the missing implication.

### 4. Repeat until stable

Alternate a builder pass with an adversarial reviewer pass. After each pass, update the contract
and ledger, fix findings, rebuild, and restart the clean-pass count. Exit Stage 1 only after two
consecutive passes find no new material error or actionable improvement: one paper/cryptographic
semantics pass and one Lean abstraction/API/composition pass.

Stage 1 is complete only when:

1. every contract item maps to final Lean declarations with a justified correspondence;
2. no known vacuity, false seam, silent paper deviation, unnecessary hypothesis, or unjustified
   abstraction remains;
3. all intended definitions, theorem statements, helper statements, packages, and seam wiring
   elaborate together;
4. every remaining proof obligation is an explicit, inventoried `sorry` in a proof body.

## Stage 2 — develop a feasible proof architecture

This stage may add, generalize, split, relocate, or restate helper lemmas, but every such change must
remain faithful to the Stage 1 contract. Finish all proof-interface design before freezing.

### 1. Inventory exact goals and dependencies

Use `rg` to locate textual placeholders, then use Lean diagnostics/build warnings to distinguish
proof terms from comments and to inspect the elaborated goals. Include sorries in local helpers,
structure fields, package certificates, and imported target-specific prerequisites. Build a DAG and
plan leaf obligations first.

For each obligation record:

- declaration, file, exact type, local context, and hypotheses actually available;
- mathematical argument and the invariant or normal form that makes it work;
- existing ArkLib/Mathlib lemmas to reuse, with checked names and instantiated types;
- any intermediate lemma, generalization, induction motive, extensionality principle, or coercion
  normalization required;
- likely Lean proof steps, expected fragile points, and a fallback route;
- dependencies and a 1–10 difficulty rating with evidence.

Use the scale honestly: 1 is a direct one- or two-minute proof; 5 is involved but bounded work with
known mathematics and APIs; 6 or above means the current hole is not ready for the proof phase; 10
is day-scale or research-level work. No hole may enter Stage 3 at 6 or above.

### 2. Materialize the proof architecture

Search before inventing. Check candidate lemmas with scratch `#check`/`example` declarations and use
`exact?`, `apply?`, `rw?`, or `simp?` as exploration aids. Add every necessary top-level
intermediate lemma now, in its natural module, with its final statement and a `sorry` proof. Prefer
small reusable mathematical facts over protocol-specific duplication, but do not generalize beyond
a clear use.

When a scratch spike file `import`s the target module (the efficient way to develop proofs against
the real definitions), run `lake build <module>` first: `lake env lean` type-checks a file but does
not refresh the imported `.olean`, so definitions you just added to the target read as unknown
identifiers until you rebuild it. Two other pervasive Hachi mechanics: `lake build` (not `lake env
lean`) runs the style linters, so check long lines with `lake env lean -Dlinter.style.longLine=true`;
and pure index/algebra helpers over the cyclotomic-ring variable block trigger `unusedSectionVars`
for `[NeZero q]`/`[IsCyclotomic Φ]` — silence it with `omit [NeZero q] [IsCyclotomic Φ] in` placed
*before* the docstring (between docstring and declaration it is a parse error). Beware: this lint
does **not** fire on `sorry`-bodied declarations, so a clean sorried skeleton can still hide
unused section variables that surface only when the real proof lands; audit each frozen
statement's section-variable usage before the freeze, or expect lint-forced `omit` signature
narrowings afterwards and record them as explicit freeze amendments.

Split a hard hole until each resulting obligation is independently below 6. Splitting is legitimate
only when the helpers express real intermediate facts and do not merely restate the original goal,
assume its difficult premise, or form a dependency cycle. If an obligation cannot be brought below
6 without changing protocol semantics, return to Stage 1; if the mathematics itself is missing or
false, report the blocker rather than manipulating the rating.

### 3. Adversarially validate feasibility

Give a fresh reviewer the current skeleton and proof DAG. Ask it to attack each rating by checking
theorem names and orientations, universes and typeclasses, finite-index casts, induction motives,
algebraic side conditions, hidden classical reasoning, circular dependencies, and whether the
proposed conclusion really follows. Require proof spikes for the riskiest step and any disputed
rating. A plausible paragraph without an elaborated critical step is not enough.

Revise and repeat until every objection is either fixed or refuted with Lean/math evidence and two
consecutive feasibility passes introduce no new helper or rating of 6 or above.

### 4. Freeze the semantics

Build the complete sorried skeleton, then create a semantic-freeze manifest and copy the scoped
files to a fresh `/tmp/prove-milestone-<target>/stage2-baseline/` directory. Record:

- every declaration name and full type, binder order, attributes, instance priority, and namespace;
- all definitions, relations, verifiers, protocol specs, structures, notation, and imports;
- package fields and composition wiring;
- the exact allowed proof-body placeholders;
- captured `#check @fully.qualified.name` output for every target declaration and `#print` output
  for each frozen data-bearing definition, relation, verifier, and package constructor;
- scoped file hashes/diffs, initial user changes, `sorry` locations, and a successful build log.

Do not commit merely to create the freeze. From this point onward, only the bodies of inventoried
proof declarations may change. If anything else is needed, explicitly return to Stage 1 or 2,
re-run their exit gates, and create a new freeze.

## Stage 3 — discharge the frozen proof obligations

Work through the proof DAG from leaves to public certificates. Bodies that were already verified
*verbatim* (same statement, same context) in a Stage 2 spike file may be transcribed one file at a
time, with steps 3–7 run after each file; everything else proceeds one `sorry` at a time:

1. Re-open its exact goal and follow the reviewed plan.
2. Replace only that proof body. Proof-local `have` statements are allowed; new top-level helpers,
   attributes, imports, instances, definitions, or statement changes are not.
3. Run `lake env lean path/to/File.lean` immediately. Do not accumulate unverified edits.
4. Recount target-closure proof placeholders and require a strict decrease. Check that no `admit`,
   `constant`, axiom, or renamed surrogate appeared.
5. Diff against the Stage 2 baseline. Reject every change outside allowlisted proof bodies, including
   “harmless” binder, hypothesis, relation, verifier, package, or import edits.
6. Run the forbidden-construct scan over the changed proof and run `#print axioms` for the proved
   declaration. It must not contain `sorryAx` or a project-defined axiom, and its axiom set must
   stay within the baseline of invariant 6 (`{propext, Classical.choice, Quot.sound}`).
7. Mark the DAG entry proved only after the local build, freeze check, and axiom check pass.

Prefer explicit, maintainable kernel-checked arguments and existing library lemmas. Automation is
acceptable when it produces an ordinary auditable proof term and passes the axiom audit; it is not
evidence that the theorem has the intended meaning.

If the plan fails, stop editing that proof. Diagnose whether the issue is a missing helper (return
to Stage 2), a wrong statement/definition (return to Stage 1), or merely a tactic/API detail (revise
the proof plan without altering the freeze). Never make a frozen theorem easier in place.

After the last local hole is removed, audit `#print axioms` for every new or changed theorem, the
milestone's exported certificate, and its package-facing theorem. Also check imported lemmas on
which the public certificate depends: a locally sorry-free wrapper around `sorryAx` is not a proven
milestone.

Stage 3 is complete only when the target closure contains no `sorry`/`admit`, every source diff is
freeze-compliant, every scoped file builds, and all axiom/construct checks pass.

## Stage 4 — independently verify that the right result was proved

Perform a clean-room review from the primary paper and the frozen contract, preferably with a fresh
reviewer who is not shown the implementation rationale. Re-check:

- the exact claim, quantifier order, hypotheses, dimensions, bounds, transcript structure, and
  extraction conclusion;
- message/challenge order, challenge space and distribution, verifier acceptance predicate, and
  guarded-versus-relational checks;
- equality/equivalence/containment directions at both seams;
- non-vacuity and representative boundary cases;
- that the public theorem is installed in the advertised package and the package is the one used by
  composition;
- that no stronger assumption or weaker conclusion entered after the contract was written;
- that the final theorem and all target-specific dependencies are free of `sorryAx`, new classical
  shortcuts, forbidden constructs, and new axioms, and stay within invariant 6's axiom baseline.

Compare the final `#check` and frozen-definition `#print` outputs with the Stage 2 captures; require
exact matches. Source review remains necessary because elaborator output is a backstop, not a
license to modify semantically relevant syntax.

Try to falsify the result, not merely explain why it seems reasonable. Require two consecutive
clean independent audits. If either audit finds a material mismatch or improvement, return to
Stage 1, update the audit ledger, rebuild the skeleton, redo the proof architecture and semantic
freeze, and re-prove the affected obligations. Do not patch around the finding in Stage 4.

## Final validation and handoff

Once the clean-room review is clean:

1. Run each changed Lean file directly, then `./scripts/validate.sh`; its source-policy gate is
   repository-wide and exception-free. Run the relevant `ReadLints` checks, add `--docs` when Lean
   docstrings or documentation changed, and run `git diff --check`.
2. Re-run the target-closure placeholder scan and the complete axiom manifest.
3. Update `hachi-overview.html` only from verified source facts: file status, exact genuine `sorry`
   count, milestone description, and “proven” claim. Do not erase a known paper deviation or open
   gap. Re-run documentation integrity checks after documentation changes.
4. Update `Composition.lean` provenance, Hachi module docstrings, and `docs/kb/` when their factual
   account changed. If the milestone introduces or extends use of a citation key, complete the
   citation workflow (`blueprint/src/references.bib` entry + `docs/kb/papers/` page, per
   `docs/wiki/blueprint-and-citations.md`) — the KB linter in `validate.sh` enforces both. Never
   hand-edit generated `ArkLib.lean` or derived site output (regenerate via
   `./scripts/update-lib.sh` after `git add`-ing new files).
5. Run the self-improvement pass below before writing the final report.

## Self-improvement pass

Run this pass exactly once at the end of every invocation, after all milestone work and verification
that can be completed. Run it even when the milestone ends at a legitimate false-claim, missing-
authority, or external-blocker exception. This pass is part of the task: do not merely suggest
improvements for a future agent. Apply every accepted, in-scope improvement to this canonical skill
file before the final response.

### 1. Derive candidates from evidence

Review the scope manifest, audit ledger, stage restarts, invalidated proof ratings, reviewer
findings, verification failures, and user corrections. Identify places where this skill was
ambiguous, incomplete, stale, inefficient, too permissive, or missing a reusable Hachi-specific
check. Do not infer a workflow defect merely because the targeted mathematics was hard.

For each candidate record:

| Field | Required content |
| --- | --- |
| Evidence | The concrete event, failure, or repeated friction observed during this run |
| Generality | Why another Hachi milestone is likely to encounter it |
| Proposed edit | The exact instruction to add, remove, tighten, or reorganize |
| Risk | Possible overfitting, contradiction, excess cost, or loss of useful freedom |
| Decision | Apply, reject as one-off, or defer because it needs user authority |

Accept a candidate only when it is supported by the run, likely to recur, materially improves
correctness or efficiency, and is consistent with `AGENTS.md`, the user's constraints, and the
maintenance rule in `docs/skills/README.md`. Prefer tightening or simplifying an existing
instruction over appending a duplicate. Do not add task-specific theorem names, transient line
numbers, a success story, or a changelog unless they encode a stable class of failure.

### 2. Apply accepted improvements

Patch `docs/skills/prove-milestone.md` in the same run. Preserve its name, four-stage architecture,
semantic-freeze guarantee, constructive proof policy, and completion gates unless the user
explicitly changes them. Keep the file below 500 lines and remove superseded wording so the skill
does not grow monotonically. Do not modify milestone source files during this meta-pass.

If no candidate meets the acceptance rule, make no cosmetic edit. Explicitly report that no
durable improvement was found and give the evidence considered. “No change” is preferable to an
unsupported self-modification.

### 3. Validate the revised skill

Re-read the complete skill rather than only the edited hunk. Check for contradictory stage gates,
broken links, duplicated rules, weakened safety requirements, line-count growth, and instructions
that would cause an infinite loop. Run documentation integrity and `git diff --check`. When the
edit materially changes behavior and subagents are available, give a fresh agent the revised skill
and a realistic Hachi target as a forward test; revise again if that test exposes a defect.

Do not recursively run a new self-improvement pass because this pass edited the skill. Fix direct
validation defects within this same pass, then stop after the revised skill validates.

### 4. Report the self-improvement

Include a **Skill self-improvement** section in the final response. List the evidence-backed
candidates, which edits were applied and where, which candidates were rejected or deferred and why,
and the validation run on the revised skill. Do not call the overall invocation complete before
this report and the accepted edits both exist.

Report:

- the target and exact paper contract conclusion;
- definitions/statements changed before the freeze and why;
- the final proof DAG with ratings and statuses;
- hypotheses removed, retained, or added, with justification;
- semantic-freeze compliance;
- `#print axioms` results for the public declarations;
- validation commands and results;
- dashboard/documentation updates;
- skill-improvement candidates, applied edits, rejected/deferred candidates, and skill validation;
- any remaining out-of-scope sorries or upstream trust assumptions, clearly separated from the
  discharged milestone.

Do not call the milestone complete unless all four stage gates pass. The only legitimate terminal
exception is a demonstrated false/under-specified paper claim or a required repair decision outside
the authorized scope; report that as a formalization finding, not as a successful proof.
