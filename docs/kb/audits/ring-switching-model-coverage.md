# Ring-switching models and coverage

This audit compares the algebra, relations, and security boundaries of the ring-switching
literature with ArkLib. It distinguishes implemented modules, proposed abstractions, and
admitted statements requiring correction. It is not a merge verdict or a completion claim.
The [concept page](../concepts/ring-switching.md) is the shorter entry point.

## Sources and version scope

Hashes pin the inspected content even when a URL later serves a revision. PDF creation metadata
is not a publication date. Page numbers below are one-based and match printed pages.

| Source | PDF version evidence | Relevant pages |
|---|---|---|
| [DP24](https://eprint.iacr.org/2024/504) | 50-page PDF; metadata 2025-09-22. The landing page reports a later 2026-05-14 revision. | §2.5 pp.18–19; Definitions 2.8–2.10 p.21; Construction 3.1 p.24; Theorem 3.5 pp.27–28; Hashcaster correspondence p.10. |
| [Ring switching, generalized](https://github.com/leanEthereum/leanVM-b/blob/main/misc/ring-switching-generalized.pdf) | 3-page note; metadata 2026-07-01; credits Lev Soukhanov and `[[alloc]init]`, without an author byline. | Full-family reduction p.1; soundness, multiplier evaluation, and extension remark p.2. |
| [Flock](https://eprint.iacr.org/2026/1329) | 45-page PDF; metadata 2026-06-28, matching the ePrint received date. | Appendix B pp.36–40; list/OOD security Appendix C pp.40–44. |
| [Hachi](https://eprint.iacr.org/2026/156) | 33-page PDF; metadata 2026-01-30, matching the ePrint received date. | §3.1 pp.11–13; §3.2 p.14; Figure 4/Lemma 9 p.20; §4.5 p.26. |
| [HMZ25](https://eprint.iacr.org/2025/199.pdf) | Web-served 31-page PDF headed 2025-02-10; the landing page separately reports a 2026-05-21 revision. | Exceptional sets: §2.1 p.7, Definition 2/Proposition 2; ring-switching construction: §4 pp.17–26. |

SHA256 of the first four inspected PDFs:

```text
DP24: 9e8f30b7994e6f4cec6df76f45fd7520c9bc5b8c8c3d99212f0567bc7045de77
RSG: 54124239a011c8c6abcaf9732f46e5d9b7348495b140b5625f36a73398a76d1a
Flock: 2d2756e77cc164f1ed8f3535ea719c7554e8c48be2f0130bac5fddb6594dfcda
Hachi: c7c98591c2576ecd8403d22e63861cb322d2995b0a88f0bc234f161afd5e6a15
```

DP24 is ArkLib's citation key; Flock and the generalized note cite the later publication as
DP26. The key alone does not select a PDF revision. The HMZ locators identify the inspected
February version rather than asserting a comparison against the latest revision.

## Reconciliation with current main

The implementation review uses main `66f3d089a41704597f54d641b78254d2a8f361f8` and the
pending composition stack #885 (`d513d5a7977680b4b3cf88fe6c5c937b23ffa46d`) and #887
(`c37a66264740a816d8a7e6b8639b8fe13f3a72bb`). Both dependency PRs were still open at the
last review; building on their commits does not mean they have merged. The earlier #615
snapshot is `e5b94f4dfe19cd4e4463088482de723758cc1038`.

The new work uses current `Packing/` ownership rather than restoring the draft's older
`Generic/` hierarchy. Recent changes affect both the mathematics and integration:

- #715 corrected Binius's Boolean-table encoder. The actual commitment uniqueness proof
  uses that encoder and its code-distance relation.
- #849 supplies ring-valid Boolean uniqueness. Polynomial transport and final evaluation
  reuse it without imposing a domain on the opening algebra.
- The Lean stack is now 4.33.1. Current probability and simulation helpers replace draft-local
  VCVio shims; those older helpers are not copied into the new implementation.
- #885/#887 supply proved execution and guarded completeness composition, with the updated
  `GuardedForm.ofEmpty` and factorization APIs. New guarded knowledge composition has its own
  proof, rather than inheriting the old admitted general knowledge theorem.
- Current Hachi weak-opening/CWSS packages, balanced digits and norm parameters are retained
  by the trace head. Its collision escape is not replaced with exact functionality.
- Main's interaction kernel and accumulated oracle-access work (#851–#853, #861) remain a
  separate API line. These protocols use the existing `OracleReduction` composition API;
  the audit does not claim a migration to the new interaction kernel.

Current validation includes the source-policy and zero-warning gates, acceptance and runtime
checks, and the axiom regression baseline. New modules are inventoried with the generated
umbrella; existing admissions are distinguished from new proof dependencies.

## Exact coordinate model

Let B be a commutative ring, E and P commutative B-algebras, and
`ε : Basis J B E`, `β : Basis I B P` finite bases. E is the opening algebra and P is the packing
algebra; no embedding between E and P is assumed. For `y : {0,1}^m`, `r : E^m`, and a
base-valued table `f_i(y)`, put

```text
packed(y) = Σ_i algebraMap_B_P(f_i(y)) * β_i
A(y,u) = ε.repr(eq_E(r,y))[u]
T(α)_u = Σ_i algebraMap_B_P(ε.repr(α_i)[u]) * β_i.
```

Both basis inverse laws make `T : (I → E) ≃ₗ[B] (J → P)` a linear equivalence. B-linearity gives

```text
(∀ i, α_i = Σ_y eq_E(r,y) * algebraMap_B_E(f_i(y)))
↔ (∀ u, T(α)_u = Σ_y algebraMap_B_P(A(y,u)) * packed(y)).
```

This identity needs no field, integral-domain, separability, or power-of-two-rank assumption.
An arbitrary public kernel `w(y):E` can replace `eq_E(r,y)` by the same argument. Identifying a
kernel with a particular polynomial evaluation is a separate interpolation/layout theorem.
Rank one and zero retained variables are legitimate cases. A Boolean scalar-head layout needs
an explicit `I ≃ {0,1}^κ`; the full-family algebra does not. `E ⊗[B] P` is an optional carrier
with two faithful coordinate presentations, not a required concrete representation.

### Defects in the reviewed main profile

At main commit `66f3d089a`,
[`Packing/Profile.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean) had a
single extension L, a carrier A, and row/column functions satisfying only reconstruction after
decomposition. Each decomposition was consequently injective **on A**. Those laws did not imply
linearity, preservation of zero, or decomposition after reconstruction of an arbitrary family.
The implementation now requires both coordinate inverse laws and coherent base embeddings; the
following counterexamples explain why that strengthening was necessary.

For example, let B=F₂, L=F₄ with basis `(1,w)`, A=L, and both embeddings the identity. Define
both decompositions by `D(z)=(z−w,1)`. They satisfy `(z−w)+1*w=z`, so both profile laws hold.
But `D(0)≠0`. At the zero original point/claim with zero witness, the honest carrier message
is zero and its scalar check fails. The verifier returns dummy target and batching point zero;
the honest prover returns batching point c and target `(-w)(1-c)+c`. For c≠0 the points differ;
for c=0 the targets differ. Thus the outputs disagree for every challenge: returning a dummy
does not rescue perfect completeness, whose profile-generic contract at the reviewed main commit was false. Stronger coordinate
laws belong to the coordinate construction; Hachi's trace pairing needs its own protocol laws.
Even adding linearity does not suffice: in the same collapsed carrier, `D(z)=(z,0)` is linear
and satisfies reconstruction, but `D(w)=(w,0)` is not the second basis vector. Thus decomposition
of an arbitrary encoded family still fails the inverse law. Faithful basis coordinates, not
merely an additive choice of preimages, are the relevant requirement.

### Coordinate direction in the legacy protocol

With the profile's actual reconstruction conventions, rows of `φ₀(x) * φ₁(y)` are
`x * basis.repr(y)`, and columns are `y * basis.repr(x)`. The embedded packed evaluation
has the form `Σ_b φ₀(eq(r,b)) * φ₁(t′(b))`. Therefore the original scalar-claim check must
use rows to recover the partial evaluations; batching and the public multiplier must use
columns to retain packed-ring values. The reviewed main commit used these directions in reverse; the implementation now repairs all three uses.

For a field basis `(1,ω)`, take the source polynomial `X_prefix`, packed constant `ω`,
and prefix point zero. The honest tensor message is `1 ⊗ ω`. Its row coordinates are
`(0,1)` and reconstruct the correct scalar zero; its column coordinates are `(ω,0)`
and cause the existing check to reject. Stronger profile laws alone do not fix this
operational error. Every use of the two coordinate maps must match its reconstruction
identity, including the batching target and final public multiplier.

## Protocol and relation matrix

| Construction | External claim | Transcript and output | Required evidence |
|---|---|---|---|
| Generalized note | Every base-valued `f_i` has claimed E-value `α_i` at one common r. | Verifier derives T(α), samples batching challenge, runs sumcheck, checks public multiplier, outputs one packed opening. | Transpose identity; batching root bound; degree-2 sumcheck; commitment anchoring. |
| Checked-slice variant | Same public full family. | Prover additionally sends slices; verifier checks them against α before batching. | Same identity plus the explicit slice check. This extra message is not in the note. |
| DP24/Binius | One scalar evaluation of the original multilinear. | Prover sends partial family as a tensor element; verifier checks equality-weighted reconstruction before the tail. | Boolean layout, correct head check, faithful coordinates, downstream PCS interpretation. |
| Flock ordinary/quirky | One multilinear or quirky evaluation. | Partial-family message and weighted scalar check, then coordinate batching and sumcheck. | Quirky weights `L_σ(ζ)*eq(ρ,b)` from Appendix B.3. |
| Hachi §3.1 | One subfield-coefficient evaluation at subfield points. | Prover sends Y; verifier checks scaled trace and outputs a ring evaluation at the retained point. | Monomial-coefficient packing, subfield-linearity, ψ bijection, trace pairing, scalar cancellation. |
| Quotient lift | Linear equality in a monic quotient presentation, with admissibility. | Commit to a lifted witness; receive α; output evaluated lift, commitment consistency, and admissibility. | Degree bound, coefficient embedding, interpolation, common-opening extraction or short collision. |

Concrete heads should be proved before extracting a common interface. A zero-round coercion
from a scalar claim to public partials loses their reconstruction equation. Singleton batching
does not construct a trace head.

### Multiplier and terminal opening

For challenge weights λ in a commutative B-algebra C, the public table is
`B_λ(y)=Σ_u λ_u*map_B_C(A(y,u))`. Sumcheck uses its C-multilinear extension times that of the
packed table when C also receives P with compatible B-action. Injectivity of `P → C` is needed
separately for the full-family security read-back. Coordinate extraction is justified on the Boolean table; a B-linear coordinate
map cannot be treated as an E- or C-algebra homomorphism.

RSG p.2 and Flock Appendix B.2.1 (pp.38–39) construct the multiplier as a multiplication-matrix
branching program; Flock Appendix B.4 (p.39) states the general multilinear evaluation identity. Replace each Boolean layer by
`(1-r′_i)M_i(0)+r′_i M_i(1)` to evaluate its multilinear extension. `Packing/Multiplier.lean` now proves this evaluator equals the actual multiplier polynomial
at every C-point. It transports only B-valued matrix entries and needs no E→C or P→C map. The
instrumented recursion counts exactly one matrix-vector action per retained variable; width is
the opening-basis cardinality, and preprocessing is excluded. Tests include a nonmultiplicative
observation, nonconstant direct evaluation, and opening/challenge fields admitting no homomorphism.
Independent review additionally checked layer order with noncommuting matrices.

The terminal statement is `packed^(r′)=v`, after checking `s_final=B_λ^(r′)*v`. It carries v
itself, even when the multiplier is zero. At the reviewed main commit,
[`finalSumcheckVerifier`](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean)
instead forwarded the product while its prover and `finalSumcheckKStateProp` used v. This was a
completeness/relation mismatch. Failed checks in that pipeline could also return ordinary
statements, including `(point=0,claim=0)`, which can have valid witnesses. This audit obligation
applies to the batching head, sumcheck loop, and final check. Rejection must be absorbing or
proved outside the output relation throughout composition.

The reviewed main also has two invalid auxiliary knowledge-state contracts. The loop's
post-challenge state demands equality of the entire received and honest round polynomials,
and retains the previous target's truth. A successful output opening gives their equality at
the sampled point; it does not eliminate an accidental root of their difference. The final
message state omits the residual-polynomial structural invariant while its message extractor
preserves that polynomial. Consequently, a witness with an unrelated residual polynomial
can satisfy the final message state without satisfying the preceding input state. These
contracts need repair alongside the operational verifier checks.

## Security currencies and assumptions

| Boundary | Correct scope |
|---|---|
| Exact packing and transpose | Algebraic equivalences over B; no probabilistic error. |
| Power batching | Note uses powers 1 through e and bound `e/|C|`; powers 0 through e−1 give a distinct sound variant `(e−1)/|C|` for e≥1. |
| Multilinear batching | For `J≃{0,1}^κ`, uniform C^κ challenges give `κ/|C|` over a field; singleton batching is deterministic. |
| Sumcheck | m retained variables and individual degree ≤2 give loss `2m/|C|` under the field sampling assumptions. |
| Final multiplier check | Deterministic read-back; no new random challenge. Legacy extra `1/|L|` is not a separate source-protocol error and cannot repair a false verifier contract. |
| Dense PCS | Exact functionality is one special case. DP24 Definition 2.9 extracts after commitment and before openings. |
| Flock list decoding | Appendix C's OOD selection has its own binding bad event; omitting the first OOD can multiply outer error by the candidate-list size (Remark 11). |
| Hachi trace head | Deterministic relative to a correct downstream ring opening; commitment and later reductions use CWSS with a norm-conditioned collision escape. |
| Field-target lift | Defect degree ≤2d−1; 2d distinct accepting challenges for special soundness; probability loss `(2d−1)/|F|` in Hachi Figure 4/Lemma 9. |

An identity commitment proves only that an interface can be instantiated. Real integrations
must interpret the committed table and use their actual extraction/binding theorem. Hachi's
short-collision event must remain restricted to short openings to give the intended Module-SIS
witness.

`PackedCommitment` carries the oracle relation and honest coverage without requiring uniqueness.
Its `Functional` proposition is supplied separately to randomized security proofs, and
`ExactPackedCommitment` is the specialization bundling that proof. Deterministic phases,
extractors, knowledge states and completeness use the base relation. A concrete two-candidate
oracle passes the actual scalar/family composition and is preserved at its output.

In the exact-binding specialization, the RBR bad event existentially chooses a witness after
the challenge. Compatibility must therefore remain in the relevant knowledge states, and a
proved functionality law must fix the packed polynomial from the commitment before applying
the root bound. Honest commitment coverage is a separate obligation. For Binius, functionality
must follow from the existing first-oracle unique-decoding relation, its actual code distance,
and injectivity of the corrected Boolean-table encoder; an arbitrary compatibility predicate
does not supply this argument.

Uniform sampling over an arbitrary finite ring does not justify a field-size denominator:
over `C=F_q×F_q`, the polynomial `(1,0)*X` has q roots, a fraction `1/q`, not `1/q²`.
HMZ's exceptional-set theorem requires unit differences between distinct challenges. Its
Galois-ring targets for prime-power moduli extend beyond ArkLib's field-target `Lift` security.
Supporting them needs a root-count/interpolation kernel, not just a weaker theorem signature.

## Hachi: exact trace and source defects

For `B=R_q^H`, n=d/k, Hachi Theorem 2 proves the B-linear packing bijection ψ and

```text
Tr_H(ψ(a) * σ₋₁(ψ(b))) = n * ⟨a,b⟩.
```

The trace sums automorphisms. The sentence on p.13 saying it fixes B omits n; its displayed
verifier equation retains n correctly. Main's
[`traceH_psi_mul_conj`](../../../ArkLib/Data/Lattices/CyclotomicRing/Subfield/TraceInnerProduct.lean)
also retains n. Read-back needs multiplication by n to be injective (a unit suffices); the
intended odd characteristic and power-of-two n supply this condition.

Hachi §3.1 packs monomial coefficients `f_(i,j)` and checks with monomial weights
`x_hi^i`, `x_lo^j`. A Boolean-table version needs explicit basis transport, including commitment
interpretation and norm growth; Lemma 6's ψ bound does not automatically cover that change.
The point must remain in the fixed subfield for trace-linearity to apply.

Section 3.2 p.14 and recursive §4.5 compress field-valued partials with `Σ_i y_i Z^i`.
The powers of Z are independent over F_q, not over the field containing y_i. For k=2,
errors `(Zδ,−δ)` cancel there and change scalar reconstruction at a by `δ(Z−a)`.
Flock Remark 5 warns against this same recombination. ArkLib's open `ZBatchBridge` pull-back
needs a proved repair. Fresh random batching and a fully specified §3.1 repacking route are
separate candidates; both need statement, commitment, layout, norm, and CWSS accounting.

The existing Hachi lift has progressed independently: quotient digits, reconstruction, and
shortness are implemented in `RingSwitch/RhoDigits.lean`; the lift has a concrete Ajtai
commitment and local collision-to-Module-SIS implication. Key-sampling and recursive end-to-end
security remain separate boundaries. See [NOZ26](../papers/NOZ26.md).

## Coverage and acceptance cases

The coordinate core should support unrelated extension degrees, distinct bases, rank one,
non-power-of-two rank, zero retained variables, and odd characteristic. Adapters should show:

- DP24/Flock ordinary and Flock quirky weighted heads with exact table layouts.
- Generalized-note E and P of coprime degrees with no embedding between them. A larger
  challenge field also requires the PCS to support extension-valued openings.
- Hachi's non-domain R_q with subfield points, explicit trace factor, and short-opening
  commitment semantics; points outside the fixed subfield must not inherit the shortcut.
- Zero public multiplier, failed check followed by a PCS-valid dummy, and false same-field
  recombination, as negative relation tests.
- List-valued committed candidates and a separately accounted OOD selection error.
- HMZ exceptional-set interpolation over a Galois ring as an unimplemented security adapter.

DP24 p.10 Eqs.(22)–(24) gives the Galois/product-carrier realization used to explain Hashcaster:
`L⊗_K L ≃ ∏_(σ∈Gal(L/K)) L`. This is a change of carrier under Galois hypotheses; those
hypotheses should not be imposed on the basic coordinate equivalence.

These are finite, evidence-backed targets, not support for every present or future use of
“ring switching.” FHE ring/modulus switching, cross-characteristic arithmetization, and code
switching need their own relations and proofs.

## Implementation and proof boundary

The findings above describe the pinned-main review. The integration now repairs the legacy
profile laws, all three coordinate directions, rejection behavior, final forwarded value, and
two auxiliary knowledge states. `Legacy.lean` and `Orientation.lean` under
`ArkLibTest/ProofSystem/RingSwitching/` exercise the actual production functions, including an
honest nonzero source and failure through actual verifier append. New execution and coordinate
lemmas passed independent named axiom checks. The final leaf now has ring-valid actual-run
completeness, both KSF boundaries and zero-error worst-case knowledge proofs; its product-ring
client covers packed value1 with multiplier0. Legacy batching/loop and general-composition
admissions remain open.

The actual FRI-Binius initial compatibility relation has separate proofs of functionality and
honest coverage. Its GF(16) acceptance client constructs the field, basis, size/rate parameters,
and honest oracle families for two nonconstant witnesses. The concrete `FRIBinius/RingSwitchingCommitment.lean` adapter now supplies the generic base
commitment, separate functionality proof, exact specialization and legacy functionality with
those same production semantics. Its GF(16) clients prove source coverage, same-oracle
output, rejection and actual knowledge/completeness through both the full-family phase and
the complete generic product-sumcheck pipeline. The latter rejects false original families
for every later tail transcript.
This does not certify the downstream interleaved FRI-Binius opening.

- The legacy modules in `Packing/` retain admitted leaves. The coordinate, terminal-value and
  rejection repairs above correct their contracts; they do not by themselves discharge those
  proof obligations or certify a generic end-to-end protocol.
- The separately based core is implemented in `Packing/Coordinates.lean`, `Polynomial.lean`,
  `Relations.lean`, and `Batching.lean`: two-sided polynomial transport, full-family read-back,
  and fixed-family separation have proofs over their stated algebraic assumptions. Independent
  review and named axiom checks cover this core. Its proofs do not inherit a certificate from
  the legacy profile.
- The checked-slice `FullFamily/` phase is implemented and independently reviewed. Its actual
  verifier retains the same commitment relation, aborts failed checks, and reduces the public
  family to a C-valued sumcheck claim. State-uniform completeness and exact-object worst-case
  knowledge proofs are standard-axiom-only. Concrete production clients cover non-domain rings,
  incompatible packing/opening fields, and a larger challenge field. Its polynomial-oracle test
  fixture is an explicit generic example; the base commitment admits finite candidate sets,
  while this randomized theorem explicitly requires functionality. Its precise downstream
  packed-opening contract remains a separate component obligation.
- `ScalarHead/` implements DP24's packed-prefix and Flock's packed-suffix layouts, with original
  source/component equivalences over commutative rings. Quirky Flock independently defines the
  original Lagrange extension, proves degree/node semantics and derives the exact `(σ,b)`
  reconstruction. The actual one-message checked head has state-uniform completeness and
  exact zero-error knowledge. Independent review covers off-grid quirky queries, failed full
  reduction and an extra zero-variable, non-domain scalar client.
- `ScalarFamily/` implements the actual scalar-head/family-head append. Both guards, the exact
  appended extractor and knowledge state, and suffix-state completeness survive composition.
  The composed scalar pipeline sends partial values and redundant checked slices in two
  consecutive messages, a documented variant of DP24/Flock's single-family message.
  False scalar execution still makes the suffix prover's real challenge query before producing
  no output. Independent review covers this equation and an actual cardinality-two oracle.
- `Tail/` implements the ring-valid residual-product relation and honest round polynomial,
  the actual clear degree-two message/scalar-challenge rounds, and the deterministic terminal
  check forwarding the same packed value. Before sampling, knowledge requires the honest round
  polynomial; afterward it requires only the local guard and sampled relation. Explicit
  functionality fixes the original witness before the `2/|C|` root bound. Terminal read-back
  needs neither uniqueness nor cancellation. The m=0 sequence is identity followed by that leaf.
- `Tail/FullFamilyOpening.lean` and `ScalarOpening.lean` are actual composed reductions from
  their original full-family/scalar relations to precisely `pc.evalRel`. They use the proved
  guarded finite-sequence/append constructors, with exact recursive extractors and knowledge
  states. Stateful completeness applies to the base commitment; fixed-prefix knowledge adds
  functionality and field-style challenge assumptions, with injective compatible P→C at the
  head. Public error lookups distinguish batching from each scalar challenge. Named independent
  axiom probes cover all production leaf and assembly contracts. These are RBR knowledge proofs
  to an opening relation, not a proof of an unspecified downstream PCS or ordinary soundness.
  `Tail/Accounting.lean` proves the exact sum over the actual challenge indices:
  batching error plus `m * (2/|C|)`, with no error from the adapter or terminal.
  Independent execution clients cover roots/nonroots of a forged quadratic, persistence of a
  failed middle guard, ordered two-round challenge prefixes, and a GF(9) opening point proved
  to lie outside the packing field's image. The zero-variable pipeline retains a genuine
  two-candidate product-ring oracle and forwards the nonzero value under a zero multiplier.
- `Packing/Opening.lean` fixes a downstream reduction's input to the same `pc.evalRel` and
  supplies actual append assembly with exact extractor/knowledge states and component
  worst-case premises. Arbitrary downstream verifier effects are allowed in that knowledge
  contract. Completeness separately requires guarded verification, every-seam-state completeness
  and a pure-output or first-message seam condition. Concrete production packing prefixes use
  the empty ambient oracle; generic assembly takes an explicit common ambient oracle.
  The checked polynomial-oracle client closes both actual public pipelines to a decision
  relation and proves probability-one acceptance of a nonconstant original source. A separate
  nonempty-ambient fixture verifies actual state-changing query execution and its prevention
  after a failed front. No downstream security premise can be replaced by a vacuous
  zero-challenge theorem: its knowledge-state endpoint still requires the actual opening check.
- `Lift/` has monic presentation algebra and field-target CWSS. Hachi's lift and digit
  encoding use that layer independently of the packing profile.
- `Append/Knowledge.lean` proves guarded-first composition from worst-case-per-prefix component
  knowledge bounds, including zero-round boundaries and arbitrary right effects. Independent
  review and named axiom checks cover this specialization. `KnowledgeNary.lean` now extends the
  proved construction to actual finite guarded sequences, including identity and empty-component
  boundaries, while exposing the exact recursive witness/extractor/state and canonical error
  indexing. General RBR knowledge composition
  remains admitted in the shared security layer. Perfect
  completeness and fixed-prefix soundness composition do not supply that theorem. Closing
  packing leaf proofs alone therefore does not establish an end-to-end RBR knowledge result;
  the composition and commitment-extraction dependencies need separate axiom checks.
- Hachi's `TraceHead/` is implemented and independently reviewed. It proves both monomial
  packing inverses, uses the actual ψ basis, and cancels the trace scale as a unit in R_q.
  Its one-message phase, ordinary/MsgShort completeness and CWSS preserve the actual weak
  opening. Honest source coverage commits every original polynomial's packed coefficients
  with the real balanced-gadget committer. A concrete rank-two/rank-one nonzero source rejects
  a false zero claim in the full reduction. All named new algebra/protocol/consumer probes are
  standard-axiom-only. The fixed-subring field conclusion remains conditional on
  `no_selfReciprocal_factor`; these proofs do not inherit that gap. Existing noncomputable
  infrastructure, scalar-Scheme packaging and §4.5 repair remain separate boundaries.

Independent review must examine relations, witnesses/extractors, challenge order and
distribution, failure propagation, commitment binding, and axiom reports at each integration.
A conditional theorem or a statement admitted with `sorry` is not a completed protocol proof.

## Completion sequence and follow-up obligations

The implementation follows the reviewed dependency order below. Each component has separate
source review and named axiom checks; permanent acceptance clients exercise its actual relations.

| Stage | Delivered result | Acceptance boundary |
|---|---|---|
| Model and legacy audit | Separate B/P/E/C roles; faithful legacy coordinates and absorbing failure | Nonconstant orientation, non-domain and terminal-value counterexamples |
| Generic algebra | Coordinate transpose, polynomial inverses, batching and matrix multiplier | Unequal ranks, incompatible fields and nonmultiplicative observations |
| Original-source heads | DP24/Flock layouts, quirky interpolation and Hachi monomial trace head | Actual source reconstruction, failed checks and norm-conditioned Hachi coverage |
| Commitment and composition | Base/functionality split; real Binius adapter; guarded append and finite sequence | Ambiguous finite candidates, shared-state seams and explicit recursive extraction |
| Complete generic packing | Actual scalar/family heads, product sumcheck, terminal and error accounting | Empty/two-round execution, extension-valued opening, real GF(16) total 7/16 |
| Downstream assembly | Actual opening contract and append wrapper | Checked-oracle closure of both public pipelines and effectful suffix behavior |

Further work has separate proof obligations: remove the redundant scalar slice message with a
proved protocol correspondence if exact DP24/Flock transcripts are needed; supply Flock list/OOD
probability accounting; discharge the legacy batching/loop and interleaved FRI-Binius opening
proofs; package Hachi's semantic trace head for the executable scalar scheme and repair its
§4.5 recombination; and add HMZ exceptional-set security and the Galois product-carrier adapter.
These extensions must preserve their source relations and stated binding models. They are not
premises silently supplied by the generic packing proofs above.
