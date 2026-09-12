# AR-3A / AR-3B semantic acceptance contract

This refines the corresponding slices in [the landing plan](01a-foundation-pr-plan.md).
The [naming contract](01b-type-tree-rename-cutover.md) and
[core claim design](02-oracle-reduction-core.md) remain in force. These are acceptance
requirements, not a statement that validation has already passed.

## AR-3A: signatures are not executions

Use the existing `PFunctor` carrier through `OracleSpec.toPFunctor` and
`OracleSpec.ofPFunctor`; do not introduce another packed-signature record solely to change
terminology. Preserve independent query and response universes where the upstream API does.

`TypeTree.accessAt` computes the available signature from an initial signature, an oracle
decoration, and a real `FreeM.Cursor`. It includes terminal cursors: a send followed by `done`
still leaves an oracle that the terminal verifier can query. A node decoration alone has a
unit-valued leaf and cannot serve as the only access API.

`AccessDecoration.build` is a derived presentation. Arbitrary values of `AccessDecoration`
are not certificates that their queries are authorized. The restriction/rebuild theorem must
connect that presentation to `accessAt`; generic restriction laws for arbitrary decorations
are not sufficient.

A cursor proves a syntactic occurrence, not reachability under a strategy. Run-derived resource
availability belongs to execution and the later full-prefix/artifact work. AR-3A must not infer
that every cursor is realizable, that every oracle payload type is inhabited, or that a
structural prefix supplies concrete messages.

Public values choose continuations. Hidden oracle payloads do not. Equal branch projections
therefore give equal available signatures, but do not imply equal handlers or equal verifier
results. A query can distinguish payloads when the declared interface permits it. Conversely,
a non-faithful interface must not silently become a projection to its underlying representation.

Signature extension uses disjoint query slots. Equal query/response types do not make two
resources identical. Stable identity, sharing, aliasing, and ideal guarantees remain AR-4B;
AR-3A's sum tags route queries; AR-4B's `NamedContext` and `OracleModel` track names and promises.

### Required AR-3A tests

- A public branch selects distinct oracle message types and their matching interfaces.
- A test actually attempts an unavailable query and fails; the same query is accepted after
  the send. A comment beside a type equality is not a negative canary.
- A terminal cursor retains the last sent message's query slot.
- A derived query uses both an initial resource and a new same-signature message, with correct
  answers under the explicit handler.
- Distinct hidden representation data with equal interface behavior yield the same handler.
- Cursor composition and restriction/rebuilding use PolyFun's actual cursor operations.
- Non-default, independently chosen query and response universes elaborate.

## AR-3B: authoring visibility and runtime visibility differ

The prover may choose and remember concrete message values. The verifier authoring API must
not receive those values at oracle nodes. Merely erasing payloads from the output path does
not repair a verifier that already inspected them while running.

Use PolyFun's local syntax and strategy substrate. The execution adapter may receive a
concrete oracle payload to extend its handler, but must pass only the declared queries to the
verifier continuation. Public messages, including query-dependent challenges, remain genuine
structural branches. The verifier's terminal output family is branch-indexed, not indexed by
hidden representation data.

Input oracle behavior is supplied as an arbitrary pure `QueryImpl`, not restricted to an
honest object. Prover messages are values of their declared message types, including any ideal
slot refinements. Neither quantifier should be silently changed to simplify an interpreter.

### Receive phases, terminal effects, and the schedule

AR-3A records access before a move. AR-3B distinguishes that boundary from the verifier's
post-receive computation. At an oracle send, the adapter first receives the concrete message,
then extends the handler, then runs the verifier's query computation. The verifier computation
has the extended query signature but no concrete-message argument. This allows immediate
oracle checks without either leaking the payload or postponing all checks to a later round.

The single-run schedule follows PolyFun's ordinary paired runner:

- at a public prover-owned node, verifier effects run after receiving the public value and
  use the unchanged source signature;
- at an oracle prover-owned node, verifier effects run after receipt and use the extended
  source signature, without seeing the concrete payload;
- at a verifier-owned public node, verifier effects run before emitting the chosen move;
- at a terminal leaf, the accumulated source signature remains available and the terminal
  action runs exactly once after the paired runner returns it.

Do not invent a dummy public round to run a terminal query, and do not model the terminal
statement as a function of the environment alone. Monadic continuation construction must not
silently move effects across any of the boundaries above. A richer authoring language with
arbitrary local binds would require its own order-preserving execution law.

A single-run erasure law must hold at the `OracleComp` level before an ambient handler is
chosen. Test a stateful ambient handler so that reordered or duplicated queries are observable.
Do not invoke `LawfulCommMonad` to hide a schedule mismatch. General sequential security,
state restoration, world traces, terminal faults, and run-derived claim closing remain in
their named later slices.

A projected public path and verifier result is not the full verifier observation history.
In particular, it omits the order and answers of local oracle queries. Name that projection
`publicResult`, not a complete verifier view or a trace artifact. Behavioral opacity means
that equal interface answers give equal verifier continuations; it does not mean that all
messages with the same structural branch must produce the same answers.

### Required AR-3B tests

- Run a mixed public/oracle tree with a query-dependent public challenge.
- Preserve a nontrivial private prover output without giving it to verifier construction.
- Query both the initial handler and sent messages, including after a final oracle send.
- Exercise effects immediately after both public and oracle receives.
- Reject a verifier continuation that tries to bind an opaque payload directly.
- Use a non-faithful oracle interface, rather than only the default whole-object interface.
- Check the exact ambient-query order and multiplicity using a stateful interpreter.
- Exhibit the erasure equation for the actual exported executor, not a separate toy runner.

## PR and validation boundary

AR-3A is additive to current `main`. AR-3B is a separate dependent PR; neither changes legacy
`OracleReduction`, dependency pins, source-policy exceptions, or the axiom baseline. Examples
belong in `ArkLibTest`, not the production umbrella. Regenerate the umbrella mechanically.

The focused Interaction acceptance workflow compiles production and test modules on stacked
feature-base PRs with the existing source-policy plugin and zero-warning budgets. It restores
but does not publish the shared build cache and uses a read-only token. It supplements the
full main-target validation/axiom gate; it does not replace it.

Each PR must report the exact validated head and distinguish static inspection, successful
Lean compilation, acceptance tests, and the full validation/axiom gate. An open draft or a
started CI job is not evidence that a formalization is complete. The records remain provisional
until the Sumcheck and legacy-correspondence checkpoints exercise them.
