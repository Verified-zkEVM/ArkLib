# Interaction framework roadmap

**Status date: 2026-10-29.** This page lists the remaining design and implementation work for
ArkLib's interaction layer (`ArkLib/Interaction/`). The
[current-status page](00-current-status.md) records what has landed and the supported dependency
versions. Protocol-level status, including the legacy-layer protocol developments, is on the
public [roadmap](../../ROADMAP.md), which also states the
[migration plan](../../ROADMAP.md#priority-replace-the-legacy-layer): feature parity, ports with
a proved equivalence, then deletion of the legacy layer. The design documents define the model: see the
[oracle-reduction core](02-oracle-reduction-core.md),
[oracle execution and security games](03-adversarial-oracle-execution.md), and
[oracle-elimination compiler](04-oracle-elimination-compiler.md).

**Status terms:** *proposed* means designed but not started; *conditional* means do the work only
when a real client demonstrates the need. Every item on this page is open. The
[current-status inventory](00-current-status.md) lists the landed modules and theorems with their
hypotheses.

## Scope and contracts

Continue from the ordinary paired runner and the interaction-layer results listed in
[current status](00-current-status.md). Preserve the prover's actual continuation, its private
memory, declared oracle access, and the order of effects. Do not add a second executor or a separate
prover-state machine.

The exact tree, access, closing, and effect-order contracts belong to the
[access and execution contract](01c-access-execution-contract.md) and
[oracle-reduction core](02-oracle-reduction-core.md). Persistent state, the adversary's view,
security events, and fault accounting belong to
[oracle execution and security games](03-adversarial-oracle-execution.md). The first verifier
composition result uses a boundary that returns data and has no pending action. If a protocol needs
an effect at that boundary, represent it as a protocol move or prove the local effect-order law.

For Sumcheck, the final equality between the original polynomial oracle and the claimed value stays
in the output oracle relation; it is not an extra final verifier query.

## Interaction-layer protocol clients

[Current status](00-current-status.md#interaction-layer-security) records which protocols use the
interaction layer and which of its certificates still lack a protocol client. A legacy-layer assembly does not
port a protocol.

1. **Efficient Sumcheck and legacy correspondence.** Optimize the Boolean multilinear case using
   CompPoly evaluation tables, with proved message/update algorithms and separately stated costs.
   The computable general prover alone makes no efficiency claim. Extend the single-round
   legacy correspondence to relate the complete legacy-layer and interaction-layer security games;
   do not treat the interaction-layer result as silently proving the legacy declarations.
2. **An interaction-layer knowledge client.** Instantiate `KnowledgeCertificate` for a protocol with a
   nontrivial witness, for example a committed or hidden polynomial. State the witness relation
   explicitly and connect the certificate to the actual verifier through
   `SamplesChallenges` or `FreshVerifier`.
3. **FRI slice.** Use a derived virtual oracle view and prove a two-way bridge to the established
   legacy presentation.
4. **Spartan-like slice.** Use a fresh prover message and prove the corresponding two-way bridge.
5. **Broader migration.** Port further FRI, Spartan, Plonk, BCS and Nova protocols one at a time.
   Keep the legacy security namespace until each migrated protocol has its own proved
   correspondence.

For each slice, record the exact statement, oracle interface, prover information, success event,
and error bound. A protocol's use of the generic API is evidence for that client; it does not
automatically prove every legacy equivalence.

## Rewinding and compiled-protocol security

**Rewinding knowledge soundness.** Tracked in
[issue #1410](https://github.com/Verified-zkEVM/ArkLib/issues/1410). The protocol-free rerun
engine and tree finder belong in VCVio. ArkLib supplies a legacy-layer instance, an interaction-layer instance in
which one run executes the strategies against a verifier replaying a challenge script, and the
consumers (special soundness, coordinate-wise special soundness, Hachi). The issue records the
decisions: a fixed private tape, expected and truncated run-count bounds, and public-coin
verifiers only.

**From state restoration to compiled protocols.** The interaction-layer state-restoration theorem
bounds the restoration game for the interaction-layer verifier. Fiat–Shamir and BCS still need bridges that state their
entropy, salt, replay, budget and loss assumptions, and a concrete interaction-layer verifier realization
with its terminal witness relations for each protocol. The
[security chapter](03-adversarial-oracle-execution.md#5-state-restoration) specifies the targets.
A causal query-trace interface and a reusable conditioning facade were not needed for the
state-restoration proof; add them upstream only when one of these bridges requires them.

## Extractor efficiency repair

The unbounded-game and measured-operation contracts have landed. The remaining steps are
proposed. The near-term contracts
belong to [the efficiency chapter](03a-extractor-efficiency.md); complete execution and
computational-model decisions belong to [the execution-backend chapter](03b-extractor-execution.md).
Each implementation PR starts from current `main` or its explicit prerequisite branch; keep
dependency upgrades separate.

| Step | Deliverable | Acceptance evidence |
|---|---|---|
| Algebraic execution backend (E3a) | Proposed route, replaceable: build a generic algebraic execution backend for the PolyFun/VCVio quantitative layer | Executable code type with semantics for field operations, indices, control and storage; gate on realizing one real FRI fold-consistency check with proved output agreement and execution bound |
| Complete execution bounds (E3) | Required later for efficient-extraction claims: add `knowledgeSoundnessWithin` using the algebraic backend or another adequately reviewed execution model | Quantitative realization, explicit representations, charged pure computation, termination/access proof, and a documented review of primitive adequacy; no claimed standard-machine correspondence |
| Complete FRI extractor certificate | Certify all local work of FRI's same named extractor | Bound view preparation, scan/control/storage and interpolation, retain early rejection, combine with `knowledge_soundness_with`, and derive a polynomial envelope under the protocol constraints |
| Toy decoding certificate | Add the measured eager Toy decoder and terminal certificate | Equality with the existing extractor on all inputs, measured agreement/interpolation/re-encoding/materialization, and the unchanged `certifiedExtractorError` |
| Toy round-by-round certificate | Certify Toy round-by-round execution | Per-stage budgets for the actual available prefixes, exact extractor identities and the existing per-round error guarantees |
| Uniform families (E7) | Deferred: add uniform family corollaries when a consumer fixes the policy | One packed family realization and polynomial for fixed backend/boundary/contracts, with explicit parameter growth and representation policy |

Complete execution bounds are required before ArkLib claims efficient extraction without
qualification. Their prerequisites (the interaction-layer soundness contracts, their composition, and
a measured-stage conjunction with an acceptance example) have landed. No probability theorem
waits for them. The algebraic backend is the proposed route; another execution model with a
reviewed adequacy argument can replace it. Complete execution bounds consume the chosen backend
and the measured contract's same-program bridge. The complete FRI certificate and the Toy decoding
certificate consume them and can be developed independently; the Toy round-by-round certificate
follows the Toy decoding certificate. The backend's real FRI check is the gate before scaling it
to the complete extractor. The formal gain over the measured contract is that every piece of pure
computation is charged through the backend; the primitive model's adequacy is reviewed, not proved
against a standard machine.

Uniform families wait for a consumer and an explicit parameter-growth policy. They use the
corresponding concrete certificates and must not infer uniformity merely from parametric Lean
definitions. Update public summaries and protocol audits with each concrete FRI or Toy
certificate, marking whether it supplies operation counts, algebraic execution bounds or bit-time
bounds; those documentation updates do not wait for uniform families.

Protocol code stays in ArkLib; generic cost/realization combinators belong upstream. Use the
existing arithmetic layer rather than importing FRI-specific access instructions into Toy.
The generic algebraic code type belongs in PolyFun; a temporary `ArkLib/ToCompPoly` backend
must name its upstream destination and removal condition if upstream landing would delay the work.
Retain compatibility names with precise docstrings while adding the resource-certified public
theorems. A Caliper field/kernel pilot and bit-machine refinements are later clients, not
prerequisites for a complete claim relative to the explicit algebraic model.

For each of these steps, run the normal repository validation, the axiom regression gate for axiom-clean
theorems, and the relevant existing compiled extractor clients. Extend acceptance tests with the
failure modes in the efficiency chapter. Runtime fixtures check implementation behavior; the
kernel-checked bounds and realization establish the resource claim. Update current status only
when results land, and make public summaries match the strongest completed layer.

## Oracle elimination

### Oracle-elimination compiler

Build the compiler only after the ordinary security, runtime, query-trace, and extraction results
needed by its passes exist. Follow the interfaces and pass order in
[04-oracle-elimination-compiler.md](04-oracle-elimination-compiler.md): represent ideal oracle
guarantees, assign backends, plan reads, lower and transport claims, then prove concrete Merkle and
homomorphic adapters. Carry soundness, extraction, privacy, query costs, and running time through
each pass. Do not fill unsupported backend capabilities with placeholder guarantees.

### Merkle adapter

The first Merkle backend adapter adapts VCVio's existing shared-ROM execution and extractability
theorem to ArkLib's declared oracle interface. Its prerequisites have landed: the named-context
and source-routing API (#864), the persistent runtime (#884), terminal outcomes (#886), and the
access and query-budget evidence (#1238). The adapter itself has not started. Do not restate the
VCVio security game in ArkLib. This adapter supplies one backend capability; it does not by
itself prove the full Fiat–Shamir, BCS, or compiler theorem.

## Conditional upstream work

Use upstream PolyFun or VCVio only for a demonstrated client need. VCVio's runtime and
failure-to-return support are already available. The missing generic trace transducer, certified
query-log bridge, reusable conditioning, or error-bearing reduction API should be added at its
owning repository when an ArkLib proof needs that exact capability. Operational
`DynSystem.Prefix` concatenation is needed only if a client cannot use ordinary monadic sequencing.
Any temporary adapter must name the upstream destination, have a deletion condition, and disappear
when the upstream API lands.

If a real protocol needs an effect at an intermediate boundary, first express it at an explicit
interaction node. If that cannot preserve the protocol, prove the local effect-order law or propose
the smallest coherent PolyFun extension. If a suffix tree needs a dependency not represented by
the interaction's public choices, document that client and propose the needed upstream change. Do
not assume global effect commutativity and do not create a second ArkLib executor to work around
either limitation.

## Delivery rules

- Give each implementation PR one main theorem or API as its focus. Include the laws, acceptance
  examples, and documentation needed to use that result.
- Begin the next step while the current PR runs validation or CI, using isolated build outputs.
  Merge in dependency order after validation and independent review. After a dependency merges,
  bring the next PR onto the updated `main` and verify that the change was preserved.
- Reuse a supported upstream API before adding another wrapper or executor. Put reusable additions
  in the library that owns them; remove temporary ArkLib adapters when the upstream API lands.
- Use a real protocol or security theorem to test each foundational API. Keep the legacy namespace
  until each migrated protocol has a proved correspondence.
- Keep dependency bumps separate from theorem changes. Add no new `sorry` and run the repository's
  required validation before commit.
- Update [00-current-status.md](00-current-status.md) when a result lands.

Use names and docstrings that a cryptographer can understand without knowing the internal Lean
representation. State who chooses the prover, what the verifier observes, which event is bounded,
and how the error depends on the assumptions. Have an independent reviewer explain the principal
theorem in those terms and compare it with the intended game. Treat a failed proof as evidence about
the theorem or its assumptions, not as a reason to hide a stronger claim behind a weaker name.
