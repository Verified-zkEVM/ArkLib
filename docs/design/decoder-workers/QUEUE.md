# Paper decoder task queue

This queue tracks integration of the ChatGPT worker outputs based on
`1c5ee56ae5e082ab966322813715a5855801a9ad`. The original worker pages are frozen assignment
specifications. Consult this queue before launching more work.

## Current integration

| Task | State | Result or next action |
| --- | --- | --- |
| A: inverse/materialization | Accepted after local completion | Unit completeness, geometric equivalence, elimination/reference equality, and materialization proved; executable tests and full gate pass. |
| B: partition accounting | Accepted after repair | Exact split dimensions, disjointness, preprocessing bound and ramified fixture pass. |
| C: batched recovery | Accepted after repair | Actual product-tree scan, exactness and distinct-fiber runtime fixtures pass. |
| D: equation checks | Accepted after repair | Reflection and compact-row kernel proofs; nonvacuous certified construction passes. |
| E: independent review | Resolved | Prime-field contract and guard tests repaired; independent integration audit completed. |

## Milestone 1 closeout

A–E are integrated and the complete `./scripts/validate.sh --axioms` gate passed on
2026-09-11. This closes the foundation milestone: computed unit inversion, rational coefficient
materialization, exact/disjoint splitting and dimension accounting, ramified preprocessing,
real batched recovery, nonvacuous successful support construction, and easy-branch exactness.
The axiom scan checked 37,636 declarations in 1,571 modules with no new taint. Existing
repository admission debt is unchanged; the new principal proofs use only standard Lean axioms.

The top-level symbolic branch still returns `symbolicBackendUnavailable`. Closing Milestone 1
does not close the complete paper decoder.

## Next implementation queue

Box truncation and its executable commutative ring compile. Finite nilpotent inverse correction
and mixed-term tests also compile; the remaining Taylor construction is still queued. Scope later interfaces against
the integrated revision before dispatching them.

| Priority | Work package | Dependencies and acceptance |
| --- | --- | --- |
| Done | Complete A and audit Milestone 1 | All foundation gates pass; independent review complete. |
| 2 | Regular Taylor constructor: projection and good fiber | Concrete finite-grid projection, resultant-certified fiber, and regular-locus coverage. |
| 2 | Regular Taylor constructor: truncated algebra and lifting (box ring implemented; nilpotent correction implemented) | Actual nonreduced arithmetic, Bezout/Newton inverse, algebraic and differential correction branches. Coordinate interfaces with projection work. |
| 2 | First-order norm producer foundations | Function-field component splitting, computed norms and characteristic-safe full squarefree decomposition. Integrates after Taylor and materialization. |
| 2 | Rojas producer feasibility slice | Actual system-to-resultant/perturbation construction, independent of the existing downstream extraction interface. No solver oracle. |
| 3 | Explicit extension fields and prefixes | Computed field models and irreducibility; needed by the higher-order solver and center setup. |
| 3 | Higher-order all-subsets integration | Direct affine systems, nonsingular wanted-point coverage, concrete Rojas outputs, and common recovery. |
| 3 | Explicit expander selection | Executed Gabber–Galil graph, spectral certificate, padding/labels and independent-selection proof. |
| 4 | Global driver and public exactness | Execute the separant loop and instantiate all constructors; remove candidate-coverage premises from the public decoder theorem. |

No task may replace a named paper algorithm with enumeration or a supplied output oracle.
No running-time formalization or paper citation update is included in this queue.
