# Fiat-Shamir protocol interfaces and salt parameters

The exact eager/lazy equivalence in
`DuplexSponge/Execution/LazySampling.lean` covers arbitrary programs over the duplex-sponge
oracle and preserves the returned observations, including logs the program returns.

## Construction scope

ArkLib implements the basic random-oracle Fiat–Shamir transform and the CO25 overwrite-duplex
transform. This page describes their protocol interfaces, byte serialization, and completeness
results. The implementation correspondence for the overwrite duplex is separate from its
ideal-model security analysis.

## Application interface

`FiatShamir/Protocol.lean` defines `InteractiveProver`, `InteractiveVerifier`, and
`InteractiveProtocol`. The prover has input initialization and round algorithms but no terminal
output. The verifier consumes the original statement and full transcript and returns a Boolean
decision. `NonInteractiveArgument` exposes ordinary function fields:

- `prover : Statement → Witness → OracleComp oSpec NARGString`
- `verifier : Statement → NARGString → OracleComp oSpec Bool`

For applications, use `InteractiveProtocol.fiatShamir` from `Protocol/Canonical.lean` or
`InteractiveProtocol.duplexSpongeFiatShamir` from `Protocol/DuplexSponge.lean`. Both return a
`NonInteractiveArgument`; the `InteractiveProver` and `InteractiveVerifier` namespaces expose
the individual algorithms. These algorithms return a NARG string and acceptance decision,
without computing or returning a reduced statement or witness.

The established reduction-based constructors and security proofs remain available.
`InteractiveProver.toReductionProver` adds a dummy terminal `(true, ())` output for that proof
interface; NARG-string generation does not execute it. `InteractiveVerifier.toReductionVerifier`
embeds the Boolean computation without adding queries, retaining rejection as `some false`.
`InteractiveProtocol.toReduction` bundles these views. In the reverse direction,
`Prover.toInteractiveProver` forgets terminal output and `Verifier.toInteractiveVerifier` maps
an aborting Boolean verifier's abort to rejection.

`InteractiveProtocol.run` delegates to the established round executor, preserving query order
without executing a terminal prover output. `InteractiveProtocol.toReduction_verdict` proves
that the compatibility execution is exactly `some` applied to this Boolean computation.
The DSFS generator likewise delegates to the existing message algorithm, retaining its optimized
termination and permutation query routing.

The exact computation laws `InteractiveProver.compileFiatShamir_eq_sendMessage` and
`InteractiveVerifier.compileFiatShamir_eq_verify`, and their DSFS counterparts
`InteractiveProver.duplexSpongeFiatShamirPayload_sendMessage` and
`InteractiveVerifier.duplexSpongeFiatShamirPayload_verify`, identify the application algorithms with
the compatibility compilers. They preserve oracle effects, not just returned values. Existing
security theorems apply to the explicit compatibility views under their original hypotheses;
changing the return interface does not remove sampling, codec, round-shape, or oracle assumptions.

### Canonical byte NARG strings

`DSFSTypedNARGString pSpec U δ` is the typed NARG string: the salt paired with the
prover messages, before byte serialization. `DSFSNARGString` is its public byte representation,
`ByteArray`. Verifier messages are reconstructed and are not included in either representation.
The public `InteractiveProtocol.duplexSpongeFiatShamir`
compiler takes an explicit `Serializer (DSFSTypedNARGString pSpec U δ)` before its salt sampler.
Its prover serializes the typed NARG string; its verifier parses the whole input and rejects failure
before issuing any oracle query. The `...Payload` algorithms expose the structured internal view.
`Serializer` supplies byte serialization and parsing with correctness laws. `Codec` supplies
protocol-message encoding into sponge units and decoding of sponge output into verifier messages.
These are separate interfaces; an existing `Serde` instance without correctness laws is not
sufficient for serialization.

`Data/Encoding/Serializer.lean` formally requires and proves:

- `deserialize (serialize value) = some value` (round-trip correctness).
- Successful parsing implies `serialize value = input` (canonical acceptance).
- Encodings are prefix-free. Consequently, appending any nonempty suffix to a complete encoding
  yields `none`, even if the suffix could otherwise make an encoding of a different value.

The first two laws imply injectivity and rejection of every byte array outside the encoding's
image. All validity conditions must live in the payload type: use a subgroup type for subgroup
membership, or a subtype for a canonical range. `Serializer.subtype` checks a decidable
predicate during parsing; it does not silently assume that an arbitrary curve-point type has
subgroup membership. `vector`, `ofFixedSize`, and `ofEquiv` supply executable construction helpers.

**Implementation guidance:** lengths and counts read from bytes are untrusted.
Check them against remaining input and resource limits before indexing, allocation, iteration,
or arithmetic that could overflow. The abstract serializer laws do not prove memory/time bounds or
check ordering. Fixed-length formats can avoid transmitted counts entirely.

`Protocol/Serialization.lean` proves exact verifier correspondence on valid encodings, rejection
of malformed and trailing-byte inputs, and preservation of honest execution and completeness.
`NonInteractiveArgument/Legacy/Serialization.lean` transports adaptive soundness and knowledge soundness to byte
inputs, preserving query budgets, query logs, and extractor oracle permissions.
`Protocol/SerializationSecurity.lean` exposes these transfers for decision-facing arguments;
malformed inputs reject without queries and cannot increase the failure probability. Serialization-induced ambiguity is excluded;
this does not assert general cryptographic non-malleability.

## Salt parameters

The salt-bearing transformations are `fiatShamirSalted` and `duplexSpongeFiatShamir`.
The core `Prover.fiatShamir`, `Verifier.fiatShamir`, and `Reduction.fiatShamir`
remain in `FiatShamir/Basic.lean`; their fixed-table and shared-random-oracle completeness
theorems live in `FiatShamir/Completeness.lean`. Fork callers that previously passed a salt
length to `fiatShamir` now use `fiatShamirSalted`, with unchanged argument order and wire format.
The application-facing `InteractiveProver`, `InteractiveVerifier`, and `InteractiveProtocol`
`fiatShamir` methods take a `Serializer` and produce or consume `ByteArray`. Their
`fiatShamirTyped` counterparts retain the internal salt/message tuple. Malformed and trailing-byte
inputs reject before oracle queries. `InteractiveProtocol.fiatShamir_completeness` combines exact
random-oracle completeness with `NonInteractiveArgument.serialize_completeness_iff`;
serialization adds no error.
`fiatShamirSalted_completeness` preserves arbitrary completeness error with shared lazy uniform
round functions, an initially empty cache, stateless ambient oracles, and any ambient-only salt
sampler. Its proof in `Canonical/RandomOracleCompleteness.lean` establishes equality of honest
output distributions by conditioning on the salt and reusing the core random-oracle theorem.
`fiatShamirSalted_perfectCompleteness` additionally permits arbitrary fixed-function distributions;
that stronger oracle generality applies only to zero completeness error.
`ProtocolSpec.MessagesUpTo.completeMessages` converts an early prefix containing every prover
message; upstream `MessagesUpTo.toMessages` converts the complete round prefix.

Both salt-bearing transformations take a salt-length parameter and an ambient-only salt sampler.
The sampler is invoked once per NARG string. Its result has type `Vector U saltLength` and is reused for all rounds.
Canonical FS includes it in each random-oracle key; DSFS absorbs it once before the rounds.

`FiatShamirNARGString pSpec U saltLength` packages salt metadata alongside `pSpec.Messages`.
This is transport packaging, not a change to the application statement, relation, witness, or
interactive message family. An empty salt contributes no encoded symbols. Length zero is the
same construction, obtained by parameter instantiation; it has no separate compiler or public
security theorem family. Use `pure #v[]` when the zero-length sampler should make no queries.

The canonical compatibility entry points (CO25 Construction 3.17) live in
`FiatShamir/Canonical.lean` and `FiatShamir/Canonical/`, with namespace `CanonicalFS`.
Its generic abstract-salt
`compileFiatShamir` is an internal encoding adapter used by the DS-to-FS security bridge.
The state-restoration API takes the original verifier, input language or relation, and a separate
salt type. An SR prover returns `((x, τ), messages)`; its moves query the existing
`srChallengeOracle (StmtIn × Salt) pSpec` interface. The product here is query context, not the
IP statement space. Transcript reconstruction uses `(x, τ)`, verification receives only `x`,
and an SR extractor receives `x` and `τ` as separate arguments. The canonical FS
premises therefore use the original language and relation directly. No salted-verifier wrapper
is needed. The named SR prover types accept a private sampling interface explicitly; the standard
security predicates instantiate it with `unifSpec`. False-acceptance and extraction-failure
probabilities, query counts, and final security bounds are preserved by the FS/SR execution proofs.

`InteractiveProof/IP.lean` and `NonInteractiveArgument/NARG.lean` specialize these notions to Boolean acceptance, no ambient IP oracles,
and extractors with private randomness only. `OracleReduction/Salt.lean` remains a separate
transformation that inserts salts into protocol messages; the SR game here uses one salt in
every verifier-message query.

The sampler has type `OracleComp oSpec (Vector U saltLength)` and cannot inspect the statement,
witness-bearing prover state, or public FS oracle. The ZK experiments instantiate it with fresh
uniform private coins. Merely invoking an arbitrary ambient sampler once does not establish
uniformity. Canonical perfect-completeness, soundness and knowledge-soundness entry points have
explicit salt-length parameters. DSFS preserves terminal-work omission and the forward-only
honest verifier interface.

`DuplexSponge/Security/Completeness.lean` owns the public perfect-completeness endpoint,
re-exported by `Security/Salted.lean`. The theorem permits a stateless ambient handler and any
ambient-only salt sampler; it preserves the exact zero-error guarantee.

The public-coin view is `Reduction.honestVerifierView impl prover stmt wit`; HVZK uses
`Reduction.honestVerifierZeroKnowledge impl prover relation error`. Verifier messages are
independent uniform samples from the protocol's finite nonempty message spaces. The OR round
runner reveals each message only at its turn, and returns the statement and full transcript.
The final verifier check is neither an argument nor executed; acceptance is not a condition
of the view. In blueprint notation use `View_IP(P, x, w)`, with the protocol and ambient-oracle
handler specified in context. This specializes CO25 Definition 7.2 to its public-coin case;
it does not model general private-state verifier strategies. DSFS uses only private uniform
coins for the IP prover. Do not add unused verifier parameters to the view or its downstream
security statements merely to reproduce the paper's general notation.

Use `oSpec` for the ambient/shared oracle interface. Standard security games provide a separate
`unifSpec` for private prover coins; custom samplers remain inside reduction helpers. See
[the private-sampling lemmas](../../ArkLib/Security/PrivateCoins.lean) for routing and transcript rules. Instantiating `oSpec`
with `unifSpec` does not make the
interface prover-only: the usual handler supplies fresh coins per call, without exposing
one party's sampled coins to the other. In the SR game, the verifier-message oracle is a
separate interface. The generic SR initialization and stateful handler do not by themselves
ensure uniform sampling or repeatable answers.

After changing this surface, run `./scripts/validate.sh --axioms`. Do not introduce new axiom or
admission debt; native-compiler trust is never allowlisted.

## Extracted overwrite duplex correspondence

`Data/Hash/DuplexSponge/CapacityInitialization.lean` defines `capacityInit`, matching
current Spongefish capacity seeding: zero rate, encoded session identifier at the
start of capacity, zero remaining capacity, cursors zero and rate. This is separate
from ideal-hash `start` and rate-absorbed initial objects.
`Data/Hash/DuplexSponge/Deterministic.lean` interprets the existing chunk implementations
with one shared permutation. The adjacent development workspace
`/Users/maker/code/sigma/duplex-hax-bridge` checks extracted production loops against
these definitions, including arbitrary finite byte traces. Its README records the
trusted permutation and the reviewed, unextracted generic initialization dispatcher.
This construction correspondence does not transfer the ideal-model security claims.
