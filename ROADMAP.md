# Roadmap

ArkLib develops executable proof-system specifications and Lean proofs of completeness and
security. Shared ring-switching phases and their DP24/Binary Basefold composite are proved.
The next deliveries are native Flock protocols, the fused FRI-Binius opening route, and native
knowledge extraction and cryptographic compilation for concrete consumers.

The [ring-switching tracker](https://github.com/Verified-zkEVM/ArkLib/issues/1286) owns
implementation progress and dependencies. The [interaction roadmap](docs/design/05-roadmap.md)
owns framework contracts. Use [open issues](https://github.com/Verified-zkEVM/ArkLib/issues) for
assignments and [CONTRIBUTING.md](CONTRIBUTING.md) for the development and review process.

## Flock in ArkLib

Upstream Flock's reusable mathematics and circuit library, define its native prover and verifier,
and prove the security and correspondence needed by leanerVM. Keep field choices, circuit sizes,
bases and domains explicit, so other applications can instantiate the same results.

The implementation plan covers both the reference-paper construction and leanVM's Frobenius-map
variant. leanerVM supplies its concrete fields, BLAKE2s circuit and VM linkage. The
[Flock consumer tracker](https://github.com/Verified-zkEVM/leanerVM/issues/3) records the profile
contracts, source correspondence and acceptance checks. Native execution/security correspondence
and full committed extraction remain proof obligations.

## Reusable ring switching

Deliver algebra and claim-conversion results with proved Binius, Hachi and reference-Flock
instances. Each instance identifies the source it preserves, the claims it produces and the
assumptions required for its security bound. This makes reuse testable at the protocol boundary.

The common mathematics supports independent packing/opening algebras and ranks, representations
and commitment models. The shared head, product-sumcheck continuation and terminal phases provide
perfect completeness and worst-case round-by-round knowledge soundness under their declared
premises. DP24 instantiates these phases and composes with Binary Basefold. Hachi has its own
trace-head conformance result; native reference-Flock conformance remains work.

Reuse the shared protocol for consumers with matching messages, guards, samplers and endpoints.
The [consumer guide](docs/wiki/ring-switching-consumers.md) records the concrete interfaces and
remaining native-Flock obligations; the [concept page](docs/kb/concepts/ring-switching.md)
explains the construction. Pure conformance alone does not establish commitment binding or a
downstream opening theorem. Each concrete security instance must discharge its sampler, binding
and honest-coverage premises. The conversion to ordinary knowledge soundness remains admitted.

## Binius opening arguments

The ring-switching route followed by a black-box Binary Basefold opening is on main. Binary
Basefold's core interaction, query verifier and full protocol have perfect completeness and
worst-case round-by-round knowledge soundness, proved without local admissions. The concrete
ring-switching composite uses this backend and preserves its input relation and challenge ledger.

The fused FRI-Binius core and full protocol remain to be formalized. Preserve the production
schedule and prove rejecting behavior, completeness and the intended knowledge guarantees.
Keep these round-by-round results distinct from ordinary knowledge soundness through the
admitted generic bridge. The
[Binius tracker](https://github.com/Verified-zkEVM/ArkLib/issues/893) owns follow-up progress;
Flock's Frobenius variant can develop independently.

## Native security and cryptographic compilation

Use the proved CompPoly-backed honest Sumcheck prover and its specification correspondence
for native clients. Measure and optimize its actual workloads, and supply the remaining
client-specific certificates. Exercise the native typed-interaction execution and security
interfaces in small FRI and Spartan clients before migrating their larger protocol assemblies.

Instantiate the native extraction and composition contracts for actual protocol clients, then
connect them to concrete opening arguments, Merkle commitments and Fiat–Shamir transcripts.
For Flock's leanVM instance, this includes one shared WHIR opening and the deployed chain with
proof of work.

The [framework design](docs/design/03-adversarial-oracle-execution.md) specifies execution,
security games and resources. The [compiler design](docs/design/04-oracle-elimination-compiler.md)
specifies how oracle guarantees become commitment and opening obligations. Their
[protocol dependencies](https://github.com/Verified-zkEVM/ArkLib/issues/1286)
are tracked together with the consumers.

## Other protocol and commitment directions

- [FRI](ArkLib/ProofSystem/Fri/) has an executable specification with perfect and noisy-input
  completeness, soundness, and a certified straightline knowledge extractor with explicit
  resource bounds. Its native typed-interaction migration is a separate direction.
  [Batched FRI](ArkLib/ProofSystem/BatchedFri/) and [STIR](ArkLib/ProofSystem/Stir/) retain
  incomplete component or assembly obligations.
- Complete [Spartan](ArkLib/ProofSystem/Spartan/) and prove correspondence for its native
  migration.
- Extend [KZG](ArkLib/Commitments/Functional/KZG/) and
  [Hachi](ArkLib/Commitments/Functional/Hachi/) under their declared assumptions, including
  recursive opening and trace handoffs.
- Develop zero knowledge, the algebraic group model, pairing-based systems, Plonk,
  Twist/Shout, IVC folding and a mechanized PCP theorem as concrete clients require them.

## Supporting mathematics and implementation

[Coding theory](ArkLib/Data/CodingTheory/) and [polynomial theory](ArkLib/Data/MvPolynomial/)
supply the algebraic bounds consumed by protocol proofs. Computable polynomial representations,
field implementations and NTT kernels belong in
[CompPoly](https://github.com/Verified-zkEVM/CompPoly); local bridges live in
[ToCompPoly](ArkLib/ToCompPoly/). Generic probability, oracle games and resource accounting
belong in [VCVio](https://github.com/Verified-zkEVM/VCVio), and interaction structure in
[PolyFun](https://github.com/Verified-zkEVM/PolyFun).

Prove optimized algorithms agree with their specifications, exercise honest and rejecting runs,
and measure the actual workloads. Use each checkout's [manifest](lake-manifest.json) and the
[validation workflow](docs/wiki/quickstart.md).

## Completion evidence

Each delivery names its theorem, hypotheses, concrete consumer and transitive axiom report.
Keep mathematical security, native correspondence, execution tests and compiled implementation
claims distinct. The [axiom regression gate](docs/wiki/quickstart.md#filling-a-sorry-or-work-that-must-stay-axiom-clean)
tracks remaining admissions; a successful build or a deleted declaration alone does not close
a proof obligation.
