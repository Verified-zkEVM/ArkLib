# Interaction-layer rebuild: design records

The rebuild replaces the current interaction layer (`ArkLib/Interaction/`) with a new
interaction layer built on one protocol tree and a lens signature. The generic theory lives
in PolyFun under `PolyFun/Interaction/TwoParty/Lens/`; the ArkLib specialization lives under
`ArkLib/Interaction/Core/`. The legacy layer (`ArkLib/OracleReduction/`) stays in place for the
protocols that still use it.

The first milestone has three parts: an embedding of the legacy layer into the interaction
layer, Sumcheck written in the interaction layer, and a proof that the new Sumcheck is
equivalent to the embedded legacy Sumcheck at a stated observation (record D8).

Each record below states one design decision precisely enough to approve before the code that
implements it is written. Lean blocks in the records are marked "intended, not existing": they
specify work and are not evidence that a declaration exists or that a theorem is proved.

## Fixed premises

Every record assumes the following commitments.

- Challenges never change the shape of the rest of the protocol, in plain or oracle protocols.
  Public prover messages may. Oracle messages never do.
- Nothing rejects early. The interaction runs every round and every composed stage; the verifier
  decides once, at the end.
- Verifiers are public-coin and passive: a sampler draws the challenges, and a decision runs
  after the interaction. Private-coin verifiers are out of scope.
- Fiat–Shamir applies to plain protocols only. Oracle protocols reach a non-interactive argument
  through BCS; nothing hashes a whole oracle message.
- Generic theory lives in PolyFun and ArkLib specializes it. No lens is used as a runtime
  conversion between two tree types.
- The current interaction layer is reference material only. No compatibility shims are added.

## Order of work

| PR | Repository | Content |
|---|---|---|
| PolyFun PR P | PolyFun | Adds the lens-based two-party API: signatures, uniform effect slots, run, composition, iteration, swap, and the transcript ledger |
| VCVio PR R | VCVio | Moves the PolyFun pin to P's merge revision |
| ArkLib PR A | ArkLib | Adds the new core: signatures, passive verifiers, oracle families, composition, security definitions; bumps VCVio to R |
| ArkLib PR B | ArkLib | Embeds the legacy layer and proves execution correspondence and security transfers |
| ArkLib PR C | ArkLib | Writes Sumcheck in the interaction layer and proves it equivalent to the embedded legacy Sumcheck |
| ArkLib PR D | ArkLib | Ports the remaining oracle and security support and tests, then removes the current interaction layer |
| PolyFun PR P-clean | PolyFun | Removes the superseded two-party API |
| VCVio PR R-clean | VCVio | Moves the PolyFun pin to P-clean's merge revision |
| ArkLib PR E | ArkLib | Moves the VCVio pin to R-clean's merge revision, closing the dependency chain |

The order is P, R, A, B, C, D, P-clean, R-clean, E. The first milestone's mathematics is
complete when C merges.

## Records

| Record | Owns | Implemented by | Status |
|---|---|---|---|
| [D0](D0-tree-and-transcripts.md) | One protocol tree `FreeM P PUnit`, the lens signature into `rolePoly`, and the two transcript types `Path` and `PathAlong` | P | Proposed: awaiting maintainer approval |
| [D1](D1-signatures-and-shape.md) | Plain and oracle positions, their signatures, and the rule that challenges and oracle payloads cannot select shape | A | Proposed: awaiting maintainer approval |
| [D2](D2-ownership-and-universes.md) | Ownership read from the signature, the universe ledger, and role-free metadata | P, A | Proposed: awaiting maintainer approval |
| [D3](D3-transcript-indexed-state.md) | Which data is indexed by the full transcript, the verifier view (a fibre over the shape path), or the shape path | P, A | Proposed: awaiting maintainer approval |
| [D4](D4-paired-run-and-passive-verifier.md) | Uniform effect slots, the two run schedules and their exchange, the legacy slot correspondence, zero rounds, swap, and the passive verifier | P, A, B | Proposed: awaiting maintainer approval |
| [D5](D5-composition.md) | Sequential composition, its run laws, prefix decomposition, the end-decided composed verifier, and iteration | P, A | Proposed: awaiting maintainer approval |
| [D6](D6-oracle-access.md) | Oracle families along a completed path, the output oracle map (which may read the statement and the verifier view), and query routing | A, D | Proposed: awaiting maintainer approval |
| [D7](D7-security-definitions.md) | Security experiments, adversary classes, admissibility, node-indexed errors, and transfer obligations | A, B, C, D | Proposed: awaiting maintainer approval |
| [D8](D8-legacy-equivalence-observation.md) | The common observation for legacy equivalence and the Sumcheck equivalence statement | B, C | Proposed: awaiting maintainer approval |
| [D9](D9-quantum-provers.md) | Which parties may be quantum, the quantum prover type, adversary models for the security notions, and what transfers to quantum provers | A (model argument); post-milestone quantum track | Proposed: awaiting maintainer approval |

A record is committed and approved before the PR that implements it starts: D0, D2, D4 and D5
before P; D1–D7 before A; D8 before B's execution theorem and before C.

## Terms

- **Legacy layer:** `ArkLib/OracleReduction/`, with fixed-length `ProtocolSpec n`.
- **Current interaction layer:** the frozen code under `ArkLib/Interaction/` and
  `ArkLib/ProofSystem/Sumcheck/Interaction/`, which the rebuild replaces.
- **Interaction layer:** the rebuilt layer under `ArkLib/Interaction/Core/`.
- **Focal party / counterpart:** the two participants of a PolyFun two-party run. In ArkLib the
  prover is focal and the verifier's sampler is the counterpart.
