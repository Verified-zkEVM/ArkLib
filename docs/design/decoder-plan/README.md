# Complete the paper decoder

This is the current coordination hub for the Reed–Solomon paper decoder on
`quang/rs-capacity-and-correlated-agreement` in `quangvdao/ArkLib`.
It replaces the completed A–E worker assignments and earlier decoder sprint notes.

The verified source baseline is
[`3c67cb3fa669985b2add6c5d080a3060c4728789`](https://github.com/quangvdao/ArkLib/commit/3c67cb3fa669985b2add6c5d080a3060c4728789).
The finite-tower foundation milestone is complete. The full symbolic decoder is not:
`HiddenDerivativeDecoder.symbolicDecode` still returns `symbolicBackendUnavailable`.

Read the [verified status](status.md), then the [shared contracts](contracts.md),
[workstream assignments](workstreams.md), and [launch and acceptance workflow](workflow.md).
The contracts describe required semantics; proposed new Lean records are not frozen or implemented yet.

## Target and scope

Implement and prove correctness of the paper's eight procedures:
`ExactHiddenDerivativeDecode`, `RecoverAgreement`, `FirstOrderNormCandidates`,
`PairedCandidates` in both selection modes, `FastRegularTaylorFamily`, `SplitZeroUnit`,
`PreprocessFiber`, and the dedicated `ZerothOrderDecode`.

The final theorem concerns the actual executable program and the existing `ExactOutput` predicate.
Valid input/options, with a supplied explaining equation or a valid support certificate, must
produce the complete duplicate-free agreement list. A theorem about successful runs alone is
insufficient. Constructor coverage and solver correctness must be proved for concrete producers.

Termination, algebraic invariants, and correspondence with the named algorithms are in scope.
Arithmetic, bit, RAM, and native running-time bounds are not. This exclusion does not authorize
replacing Newton doubling, the norm decomposition, paired selection, or Rojas with another program.
MCA/proof-system development and paper edits are outside these worker assignments.

The paper-side specification is `docs/decoder-formalization-plan-2026-09-11.md` and the Taylor
construction is `appendices/decoder-taylor.tex` in `quangvdao/rs-capacity-and-correlated-agreement`.
At launch the coordinator supplies an immutable paper revision or accessible excerpts. Report
inaccessible sources; do not invent paper details. The ArkLib plan records implementation status,
while the paper defines the mathematical target.

## Current task board

No new group is assigned or running merely because it appears here. Branch names in the workstream
reference are reservations for future launches, not claims that remote branches exist.

| ID | Work | State | First action |
| --- | --- | --- | --- |
| I0 | Shared Lean interface freeze | Ready; coordinator-owned | Agree on the records and compile representative producer/consumer clients before cross-group integration |
| G01 | Function-field algebra and multivariate gcd | Unassigned; independent slice ready | Arithmetic, multivariate gcd, exact division and descent |
| G02 | Full squarefree decomposition | Unassigned; independent slice ready | Labelled decomposition over a certified computational field |
| G03 | Taylor geometry | Unassigned; independent slice ready | Projection and good-fiber specification with executed small case |
| G04 | Taylor local algebra and lifting | Unassigned; independent slice ready | Monic quotient over the existing box ring |
| G05 | Taylor reconstruction | Unassigned; independent slice ready | Division-free shift and degree-bounded injectivity |
| G06 | First-order norms | Unassigned; norm slice ready | Polynomial multiplication matrix and actual norm |
| G07 | Explicit fields | Unassigned; independent slice ready | Center-field adapter and general-extension construction interfaces |
| G08 | Rojas producer | Unassigned; feasibility slice ready | System-to-perturbation construction tied to its input |
| G09 | Higher-order selection | Unassigned; independent slices ready | Direct chart system and separate expander foundation |
| G10 | Dedicated zeroth-order decoder | Unassigned; interpolation slice ready | Prescribed interpolation backend/refinement and integer guards |
| I1 | Integration and independent review | Continuous coordinator responsibility | Accept compiled slices; maintain this board and obligation ledger |

At each launch record the lead, exact branch/base, owned files, first deliverable and acceptance
check here or in the corresponding group section. Record explicit dependency commit SHAs as they land.
Do not substitute a moving branch name for an agreed interface revision.

## Parallel organization

The ten groups support a proposed team of roughly 20–30 authors and reviewers once interfaces
stabilize. This is a staffing proposal, not a measured optimum or a tool-concurrency promise.
Split a group only when another worker has an independent deliverable and separate file ownership.
Each group needs compilation capacity; uncompiled patches otherwise accumulate at integration.

Start G01, G02, G03, G04, G05, G07 and G08 on their generic first slices. G06 can build norms before
its universal-agreement loop is ready. G09 can develop direct-system mathematics and the expander
in parallel. G10 can begin interpolation without waiting for the differential Taylor constructor.

| Consumer milestone | Required groups and already available components |
| --- | --- |
| Dedicated zeroth-order exact decoder | G10 + ordinary normalization from G01 + G07; reuse quotient Newton and recovery |
| Closed first-order exact decoder | G03–G05 Taylor + G01/G02/G06 norm pipeline + G07; reuse tower preprocessing/materialization/recovery |
| General-order all-subsets exact decoder | Taylor + G07 fields + G08 Rojas + G09 direct-system capture; reuse common recovery |
| Complete paper decoder | Both higher-order selections, global separant/center loop, supplied-equation and certified-support success, public theorem and algorithm correspondence |

Rojas production and the expander spectral certificate need early feasibility checkpoints.
More integration workers cannot remove those mathematical dependencies.

## Coordination ownership

The coordinator owns shared contracts, top-level dispatch and correctness, public reader maps,
umbrella generation, runtime-suite registration, dependency pins, and this task board.
Groups own the source areas in [workstreams](workstreams.md); existing source owners remain read-only
until an explicit transfer. An independent reviewer checks statements and algorithm correspondence.

Completion has separate stages: proposed, assigned, implemented, locally verified, integrated,
and accepted. Only the last stage closes a work package. See [workflow](workflow.md).

## Superseded records

Completed A–E assignments and their patch provenance remain in
[the foundation checkpoint's history](https://github.com/quangvdao/ArkLib/tree/3c67cb3fa669985b2add6c5d080a3060c4728789/docs/design/decoder-workers).
Earlier [algebraic-machine planning](https://github.com/quangvdao/ArkLib/blob/3c67cb3fa669985b2add6c5d080a3060c4728789/docs/design/rs-algebraic-machine-plan.md),
[bit-cost planning](https://github.com/quangvdao/ArkLib/blob/3c67cb3fa669985b2add6c5d080a3060c4728789/docs/design/rs-bit-cost-backend.md),
and [continuation logs](https://github.com/quangvdao/ArkLib/blob/3c67cb3fa669985b2add6c5d080a3060c4728789/PROGRESS.md)
are historical evidence, not active instructions. Their source implementations remain available.
A commit-pinned historical URL is immutable; current coordination lives only in this directory.
