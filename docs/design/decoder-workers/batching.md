# Worker C: execute batched tower agreement recovery

Read [shared instructions](README.md). Use the supplied checkpoint SHA and branch
`quang/decoder-m1-batching`.

## Owned files

Create `AgreementRecovery/BatchedTower.lean` and
`AgreementRecovery/BatchedTowerCorrectness.lean`, with corresponding new tests.
Do not edit `Tower.lean`, `TowerBatch.lean`, `ComponentScan.lean`, or dispatcher files.
Expose an adapter so the coordinator can switch callers after review.

## Deliverable

Integrate `TowerBatch.restrictBases` into the actual live-component recovery path.
At each received coordinate, share a remainder tree across current base moduli for
common coefficient/residual polynomials, then perform the fiber operations and split
components. Retire components after k agreements and preserve their sample positions.
Repeated moduli, empty lists, and branches with different fiber moduli must work.
A dead batching call, singleton batching of each component, or batching unrelated
polynomials does not meet the requirement. Explain where the common data comes from
and how the runtime reuses it across live components.

Prove a refinement to the existing tower scan and derive exact represented-family
recovery and coverage-based `ExactOutput`. Preserve observable output order if claiming
list equality; otherwise state and prove the appropriate membership equivalence and
retain deduplication. Base-field descent and final agreement filtering remain mandatory.

## Starting points and acceptance

Read `AgreementRecovery/TowerBatch.lean`, `ComponentScan.lean`, `Tower.lean`, and
`TowerCorrectness.lean`. `restrictBases` is already proved correct but currently unused
by the runtime scan. Review how component coefficient restrictions preserve common
ancestor data before designing a batch state.

Acceptance requires executable batched code, compiled refinement and exactness proofs,
and tests with several live components, duplicate moduli, early stopping, extension-only
roots, and final agreement rejection. Provide the actual call path showing remainder-tree
use. Make no asymptotic claim merely from the presence of a product tree.
