/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Coordinates
import ArkLib.ProofSystem.RingSwitching.Packing.Polynomial
import ArkLib.ProofSystem.RingSwitching.Packing.Relations
import ArkLib.ProofSystem.RingSwitching.Packing.Batching
import ArkLib.ProofSystem.RingSwitching.Packing.Multiplier
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Completeness
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Knowledge
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Quirky
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Security
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarFamily.Security
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarFamily.Execution
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.FullFamilyOpening
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.ScalarOpening
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.Accounting
import ArkLib.ProofSystem.RingSwitching.Packing.Opening
import ArkLib.ProofSystem.RingSwitching.Packing.Profile
import ArkLib.ProofSystem.RingSwitching.Packing.General

/-!
# Coordinate packing and evaluation-claim reductions

The coordinate core has independently based commutative algebras `P` and `E` over `B`.
A finite basis of `P` packs a family of `B`-polynomials into one `P`-polynomial; a finite
basis of `E` decomposes the family's evaluation values. Transposing those coordinates is
an exact linear equivalence. Neither a field/domain condition nor an embedding between
`P` and `E` is needed for the packing algebra.

`Polynomial.lean` proves both polynomial packing inverses. `Relations.lean` proves that
an entire family of claimed evaluations is equivalent to the corresponding packed slice
claims. `Batching.lean` supplies separation laws for two fixed distinct families, with
finite-domain hypotheses on the power/equality strategies. A compatible challenge algebra
`C` may receive the packed values; injectivity of `P → C` is required when transporting
separation, independently of the forward algebraic identity.

## Protocol boundaries

The generalized note [RSG] starts from a full family of public evaluations and derives
slices publicly. A checked-slice variant adds a prover message and verifies its coordinates
against that public family. `FullFamily/` implements this checked-message reduction to a
sumcheck relation, retaining the same oracle statements. `PackedCommitment` records that relation
and honest coverage; functionality is a separate premise used by the randomized knowledge bound.
The phase proves actual execution and perfect completeness for every initial state. Its
fixed-prefix knowledge theorem yields the averaged contract under the explicit binding premise.
`ScalarHead/` implements the preceding scalar-claim head for [DP24]
and [BRW26], including their different table layouts and Flock's quirky interpolation/equality
weights. Its original-source reconstruction, actual execution, completeness, and zero-error
knowledge contracts are proved independently of the later family certification. `ScalarFamily/`
composes the two actual heads, preserving both guards and the exact extractor/knowledge state.
Its completeness also applies to finite-list commitments; list/OOD probability bounds remain
separate from the exact-functional specialization.

`Tail/` implements the actual degree-two product-sumcheck rounds and terminal value check.
`FullFamilyOpening` and `ScalarOpening` compose the corresponding heads with that tail, ending
exactly at the same commitment's `evalRel` over `C`. Their state-aware completeness uses the base
commitment; fixed-prefix knowledge uses explicit functionality, finite-domain challenges, and
injective compatible `P → C` transport for the family head. Each tail challenge has error
`2 / Fintype.card C`; the batching challenge keeps its strategy error. The terminal adds no
challenge. `Accounting.lean` proves their exact sum is batching error plus `m * (2 / |C|)`.
The empty loop directly reaches the same terminal check. `Opening.lean` fixes a downstream
argument's input to that same `evalRel` and composes actual reductions using supplied worst-case
contracts. Its completeness wrapper states the guarded and shared-state seam requirements.
Concrete tests close both public pipelines through a checked polynomial oracle.

The legacy DP24 pipeline in this folder uses `RingSwitchingProfile`: one extension `L`,
a tensor-style carrier, two explicit embeddings, and two coordinate directions. With its
reconstruction conventions, rows recover the original partial values and columns retain
packed values for batching. `General.lean` assembles that pipeline with a downstream opening;
its final leaf has ring-valid completeness and zero-error knowledge proofs. The batching/loop
leaves and old general knowledge-composition pathway retain separate proof obligations.

Hachi [NOZ26, §3.1] uses a distinct deterministic trace head on monomial coefficients at
subfield-valued points. It needs the scaled trace identity, unit cancellation, and the actual
norm-conditioned commitment interpretation. `Commitments/Functional/Hachi/TraceHead/` supplies
that actual head, honest committer coverage, completeness and CWSS into the existing ring-opening
relation. It uses the fixed subring's ring structure and the actual `psi` basis, without the
unproved external field identification. The quotient-ring construction in sibling `Lift/`
is another protocol family.

## Main modules

* `Coordinates.lean` — independent finite-free algebras and faithful coordinate transpose.
* `Polynomial.lean` — coefficient packing/unpacking and the public multilinear multiplier.
* `Multiplier.lean` — actual multiplication-matrix evaluator, MLE correctness and action count.
* `Relations.lean` — full-family and slice relations, ring-valid read-back, and C-valued batching.
* `Batching.lean` — singleton, power, equality-fold, and reindexed separation strategies.
* `PackedCommitment.lean` — actual oracle relation and honest coverage, with separate functionality.
* `ExactCommitment.lean` — the exact-functional specialization and polynomial-oracle example.
* `FullFamily/` — checked slice message, actual execution, state-uniform completeness, and
  fixed-prefix knowledge soundness of the reduction to a sumcheck claim.
* `ScalarHead/` — scalar reconstruction, concrete DP24/Flock layouts and quirky interpolation,
  actual one-message execution, completeness and zero-error knowledge.
* `ScalarFamily/` — actual scalar/family append, guarded extraction, execution and completeness.
* `Tail/` — product sumcheck, terminal check and actual family/scalar pipelines to `pc.evalRel`.
* `Opening.lean` — same-commitment downstream contract and actual guarded append assembly.
* `FinalAlgebra.lean` — the legacy public-multiplier evaluation and terminal residual identity.
* `Profile.lean`, `Prelude.lean` — legacy carrier vocabulary, polynomial table layout,
  sumcheck relations, and the concrete tensor profile.
* `Spec.lean`, `BatchingPhase.lean`, `SumcheckPhase.lean`, `General.lean` — the existing
  scalar-input packing pipeline and its security proof boundary.

See the KB concept `docs/kb/concepts/ring-switching.md` and the model/coverage audit before
choosing a commitment or security adapter. Exact functionality, list/OOD selection, and
short-collision escape are different assumptions; an identity polynomial oracle only
witnesses an algebraic interface.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24]
* [Bünz, B., Rothblum, R., and Wang, W., *Flock: Fast Proving for Batch Boolean
  Computations*][BRW26]
* [*Ring switching, generalized*][RSG]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields*][NOZ26]
-/
