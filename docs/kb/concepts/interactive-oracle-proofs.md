# Interactive oracle reductions: the legacy API

This page explains the prover, verifier and oracle interfaces in
[`OracleReduction/Basic.lean`](../../../ArkLib/OracleReduction/Basic.lean).
Read it when following a protocol written using `ProtocolSpec`, `Prover`,
`OracleVerifier` or `OracleReduction`.

The newer framework lives in `ArkLib/Interaction/`. Its protocols use trees and
native prover continuations. The [interaction design guide](../../design/README.md)
explains that framework. The two APIs coexist; a security theorem for one does not
by itself prove a theorem about the other.

## What a reduction produces

A reduction turns one claim into another. The verifier's output need not be an
accept/reject bit: it can be a smaller statement for the next protocol to check.

```text
Public input statement + input oracles
                 |
      prover messages and verifier challenges
                 |
      verifier checks the transcript through its allowed interface
                 |
         rejection OR output statement + output oracles
```

The prover also receives a private input witness and may produce a private output
witness. The input and output relations say when those statements, oracles and
witnesses are valid. They are separate from the algorithms. Returning an output
statement does not itself prove that its relation holds.

An interactive oracle proof is the special case with a Boolean output, no output
oracles and a trivial output witness. A reduction can instead leave an oracle
claim for a later protocol to discharge.

## The protocol schedule and transcript

[`ProtocolSpec n`](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean)
fixes `n` communication steps. Each step has a direction and a message type:

- `.P_to_V`: the prover sends a message.
- `.V_to_P`: the verifier sends a challenge.

The schedule need not alternate. Here `n` counts individual communication steps,
not necessarily pairs of messages and challenges. The schedule is fixed in
advance; it is not a branching protocol tree.

`MessageIdx` and `ChallengeIdx` select the respective steps. A `FullTranscript`
contains the value sent at every step. Its `messages` and `challenges` projections
separate the two directions.

The schedule records types, not the verifier's access to their contents. That
access is determined by the verifier type and the `OracleInterface` instances.

## Where the prover's private state lives

`Prover` contains a family of private state types, `PrvState i`, with one type
before each step and one after the last step. These types may differ by step.

| Field | Role |
| --- | --- |
| `input` | Build the initial state from the input statement and witness. |
| `sendMessage` | Use the current state to compute a message and the next state. |
| `receiveChallenge` | Compute a function that consumes the challenge and returns the next state. |
| `output` | Compute the prover's output statement and witness from its final state. |

Both `sendMessage` and `receiveChallenge` are oracle computations. In particular,
`receiveChallenge` has result type `Challenge → PrvState`, not just `PrvState`.
The executor runs that computation and applies its returned function to the
challenge. The private state is not part of the public transcript.

The prover's output statement supports composition of honest provers. The
verifier still determines its own output; completeness requires their statements
to agree. `ProverInteraction` and `ProverInteractionWithOutput` are smaller
interaction interfaces, but readers should inspect the particular security game
rather than assume every game uses them.

`OracleProver` uses the same prover machinery. Its input includes the full values
of the input oracles, and its output includes full values for the output oracles.
This is different from the oracle verifier's restricted query access.

## What the verifier can see

An ordinary `Verifier` receives the public input statement and the full
transcript. Its `verify` operation returns `OptionT (OracleComp oSpec) StmtOut`:
it may query the ambient oracles and either return a statement or reject.

An `OracleVerifier` receives the public input statement and the challenges. It
accesses input oracles and prover messages through queries, using this signature:

```text
oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)
  |           |                |
ambient    input oracles    message oracles
```

`oSpec` describes the shared ambient queries. It does not supply their answers or
probability distribution. An implementation supplies that behavior when the
computation is interpreted.

An `OracleInterface Data` specifies a query type, a response type for each query,
and how a value of `Data` answers the query. A polynomial interface might permit
only evaluation at a point; a vector interface might permit reading an index.
Having a polynomial as the message's underlying value does not grant the oracle
verifier direct access to its coefficients.

`OracleVerifier.NonAdaptive` is a restricted form: the input statement and
challenges determine its lists of input and message queries before their answers
are received. The general oracle verifier may choose later queries based on
earlier answers.

## How output oracles are carried forward

`OracleVerifier.outputOracle` chooses one of two representations. Its output
statement and its output oracle family are distinct parts of the result.

**Retain existing oracles.** `OracleOutputEmbedding` selects an input oracle or a
prover-message oracle for each output oracle:

- `embed` is an injection from output indices into input and message indices.
- `hEq` proves that the selected source has the required output data type.
- `outputInterface_heq` proves agreement of the query interfaces as well.

The last condition matters: equal data types alone do not establish that two
interfaces expose the same queries and answers. This representation selects
existing sources; it does not compute a new derived oracle.

**Compute a derived oracle on demand.** `OracleOutputSimulation` supplies:

- `simulateOutputQuery`, which answers each output query using input and message
  queries;
- `materializeOutput`, which describes the corresponding full output values for
  the mathematical relations;
- `simulateOutputQuery_eq`, which proves those two descriptions agree.

A downstream computation can therefore query a derived oracle without first
materializing its complete value. `OracleVerifier.simulateOutputQuery` handles
both representations through one interface.

`OracleVerifier.toVerifier` supplies full input and message values to answer the
restricted queries. It then pairs an accepted output statement with the
materialized output oracles. This defines the bundled semantics used by the
legacy security interface; it does not give additional access to the authored
oracle-verification program.

## Example: retaining a prover's vector

As an illustration of the types, consider a two-step reduction with a public
field element `s`. The prover sends a vector `v` of a fixed positive length, and
the verifier sends an index `j` into that vector. Give the vector a read-at-index
oracle interface.

The oracle verifier receives `s` and the challenge `j`. It can query the message
oracle at `j`, check that the answer equals `s`, and reject if it does not. On
success, suppose it returns `(j, s)` and keeps the vector as an output oracle.

The output embedding maps the sole output index to the sole prover-message
index using `Sum.inr`. The output data type is the same vector type, so `hEq` is
reflexive; the output and message use the same read interface, so interface
coherence is reflexive too. A later verifier can query that same vector at another
index without receiving the whole vector as a public value.

This example describes the interface and the check, not a security theorem. To
turn it into a claimed reduction, one must also specify its input and output
relations and prove the corresponding security property. In particular, passing
one sampled coordinate check does not establish an arbitrary property of the
whole vector.

## Definitions, execution and security are separate

| Layer | What to inspect |
| --- | --- |
| [Basic](../../../ArkLib/OracleReduction/Basic.lean) | The types of participants, reductions and oracle interfaces. |
| [Execution](../../../ArkLib/OracleReduction/Execution.lean) | How messages, challenges, private state and verification are run. |
| [Basic security](../../../ArkLib/OracleReduction/Security/Basic.lean) | Completeness, soundness and knowledge-soundness games. |
| [Round-by-round security](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) | Intermediate-state and extraction conditions at individual challenges. |

`Prover.runToRound` returns an actual transcript prefix and private state.
`Reduction.run` runs the prover through the schedule, obtains its output, then
runs verification on the completed transcript. Challenges are represented as
queries during execution; the security experiment supplies their sampling rule
and the ambient oracle implementation. Logged variants retain oracle-query logs
in addition to the transcript. These logs and the communication transcript are
different objects.

For completeness, the honest prover should take a valid input to a valid output
and agree with the verifier's statement. For ordinary soundness, an adversarial
prover should rarely turn a false input into a valid output. Knowledge soundness
instead specifies an extractor and what input witness it must recover from a
successful output. None of these properties follows just from constructing a
`Reduction` or `OracleReduction`.

Some legacy composition, extraction and context-transport theorems still contain
admissions. [Issue #676](https://github.com/Verified-zkEVM/ArkLib/issues/676) tracks
that work. Check a theorem's dependencies before treating it as proved. The
[native framework status](../../design/00-current-status.md) records the separate
results under `ArkLib/Interaction/`.

## Further reading

- [Oracle interfaces](../../../ArkLib/OracleReduction/OracleInterface.lean): how
  concrete data becomes query access.
- [Vector IORs](../../../ArkLib/OracleReduction/VectorIOR.lean): the vector-message
  specialization.
- [BCS16](../papers/BCS16.md): the original vector-IOP reference and its ArkLib
  formalization status.
