# Ring-switching models and coverage

This page maps coordinate packing, trace relocation and quotient lifting to their source
relations, algebraic laws and ArkLib proof boundaries. The
[concept page](../concepts/ring-switching.md) is the shorter component guide.

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
February version.

## Finite-free coordinate reconstruction

Let B be a commutative ring, and let E and P be commutative B-algebras with finite bases
`ε : Basis J B E` and `β : Basis I B P`. E is the opening algebra and P is the packing
algebra. For a finite table `v : Y → P` and weights `a : Y → E`, define

```text
observe(a,v)_i = Σ_y [v(y)]β,i • a(y)
coordinateSlices(a,v)_u = Σ_y [a(y)]ε,u • v(y)
T(α)_u = Σ_i [α_i]ε,u • β_i.
```

Here `•` is the appropriate B-action. Basis reconstruction makes T a B-linear equivalence
`(I → E) ≃ₗ[B] (J → P)`, and finite-sum linearity gives

```text
T(observe(a,v)) = coordinateSlices(a,v).
```

[`FiniteObservation.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/FiniteObservation.lean)
proves this identity and its read-back form. It allows unequal ranks, empty Y and zero divisors.
Neither an embedding between E and P nor a power-of-two rank is required.

For a family of base-valued Boolean tables `f_i`, set
`v(y) = Σ_i f_i(y) • β_i` and `a(y) = eq_E(r,y)`. The identity becomes the full-family relation

```text
(∀ i, α_i = Σ_y eq_E(r,y) * map_B_E(f_i(y)))
↔ (∀ u, T(α)_u = Σ_y map_B_P([eq_E(r,y)]ε,u) * v(y)).
```

[`Polynomial.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Polynomial.lean) supplies the
polynomial packing inverses; [`Relations.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Relations.lean)
uses finite observation for this equivalence over commutative rings. Boolean and monomial
interpretations each require their own table/coefficient layout theorem.

The tensor carrier `E ⊗[B] P` is an optional representation. In DP24's `E=P=L` specialization,
`RingSwitchingProfile` requires two-sided coordinate inverses and agreement of the two embeddings
on B. Rows of `φ₀(x) * φ₁(y)` are `x * basis.repr(y)`; columns are `y * basis.repr(x)`.
Thus rows reconstruct partial evaluations and columns retain packed values for batching.
[`ProfileCoordinates.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProfileCoordinates.lean)
identifies the column family with T applied to the row family.

## Scalar reconstruction and trace observation

[`CheckedObservation.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/CheckedObservation.lean)
uses a source/output witness equivalence e and an unconditional identity

```text
scalarEval(q,w) = observe(q, honestMsg(q,e(w))).
```

Its honest-check and read-back lemmas transport an arbitrary retained witness predicate.
Concrete adapters prove that their input/output relations and guards agree with these expressions.
The inverse witness map recovers the original source witness.

| Head | Source representation and reconstruction | Retained commitment boundary |
|---|---|---|
| DP24 | Boolean table split into κ packed prefix bits and m retained suffix bits; equality-weighted partial values | Same packed-table oracle; Binius tensor uses its unique-distance compatibility relation |
| Flock ordinary | Boolean layout with packed suffix coordinates | Base commitment relation, which may admit multiple candidates |
| Flock quirky | Lagrange/Boolean weights `L_σ(ζ) * eq(ρ,b)` in the exact `(σ,b)` packing order | Same base relation; list/OOD binding is separate |
| Hachi §3.1 | Monomial coefficients and weights at fixed-subring points; one packed ring evaluation | Same norm-conditioned weak opening, with the existing message-shortness variant |

Hachi's packing map ψ is a B-linear bijection for `B=R_q^H` and n=d/k. The trace pairing is

```text
Tr_H(ψ(a) * σ₋₁(ψ(b))) = n * ⟨a,b⟩.
```

The trace is the sum of automorphisms, so it scales fixed-subring elements by n. Theorem 2
and the verifier equation retain this factor; the p.13 prose saying the trace fixes the subfield
omits it. The trace head proves n is a unit under its odd-characteristic and power-of-two
assumptions. Its guard equivalence applies to every sent ring value.

[`TraceHead/Coordinates.lean`](../../../ArkLib/Commitments/Functional/Hachi/TraceHead/Coordinates.lean)
identifies the actual ψ basis and numeric monomial indices with `PackingData`, then proves
`unpack_eval_eq_observation`. This feeds the trace equivalence and shared checked-observation
adapter. The proofs use the fixed subring as a ring and do not depend on its unfinished field
identification. A Boolean-value-table reformulation would require additional basis, commitment
and norm transport.

## Protocol correspondence

| Construction | Messages and endpoint | ArkLib correspondence |
|---|---|---|
| Generalized note, pp.1–2 | Public family; verifier derives slices, batches, runs sumcheck and requests a packed opening | `FullFamily/` checks a prover-supplied slice message instead of deriving it silently |
| DP24 Construction 3.1 | One tensor message for partial values, vector batching challenge, sumcheck/opening | Tensor `BatchingPhase` retains this head and its round-zero residual relation |
| Flock Appendix B | One partial-family message and weighted scalar check, then coordinate batching and sumcheck | `ScalarHead/` implements ordinary and quirky reconstruction; `ScalarFamily/` also sends checked slices |
| Generic scalar pipeline | Scalar partial-value message followed by a checked-slice message and sumcheck | `Tail/ScalarOpening` is a two-head-message composition variant of DP24/Flock |
| Hachi §3.1 | One ring-element message, deterministic scaled-trace check, ring-evaluation endpoint | `Hachi/TraceHead/` retains the original weak opening and proves completeness and CWSS |
| HMZ/Hachi quotient lift | Commitment to a lifted witness, scalar challenge, evaluated identity with commitment consistency/admissibility | `Lift/` proves the field-target CWSS specialization with collision escape |

Binius's interleaved suffix interleaves FRI and sumcheck. It is distinct from the generic standalone
product-sumcheck tail. The production FRI-Binius head uses the shared tensor batching proof;
the generic Binius commitment adapter also supports `FullFamilyOpening` on the same codeword oracle.

### Public multiplier and final value

For weights λ in a commutative B-algebra C, the public Boolean table is
`B_λ(y)=Σ_u λ_u * map_B_C([eq_E(r,y)]ε,u)`. Sumcheck uses its C-multilinear extension and the
extension of the packed table, with a compatible B-algebra map `P → C`.

[`Multiplier.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Multiplier.lean) evaluates
that public extension by multiplication matrices. A Boolean layer is interpolated as
`(1-z_i)M_i(0)+z_i M_i(1)`. This follows RSG p.2 and Flock Appendix B.2.1, pp.38–39, and B.4, p.39.
Only B-valued matrix entries move to C: no `E → C` map or multiplicativity of the final
coordinate observation is required. The instrumented evaluator counts one matrix-vector action
per retained variable, at width `|J|`, excluding preprocessing.

The terminal check is `s_final = B_λ^(r′) * v`, and its output is the opening claim
`packed^(r′) = v`. It forwards v even when the multiplier is zero. Failed checks abort through
verifier composition. These semantics hold for the generic tail, the profile-based terminal,
and the actual FRI-Binius final verifier; their proof coverage differs as listed below.

## Security assumptions and bounds

`PackedCommitment` records an oracle relation and honest coverage. Its separate `Functional`
proposition gives uniqueness; `ExactPackedCommitment` bundles this specialization. Deterministic
reconstruction and completeness use the base relation. Randomized knowledge bounds additionally
use functionality to fix the packed witness before the challenge, while compatibility remains
in the knowledge states. The tensor separation theorem needs compatibility and functionality,
without an honest-coverage premise.

| Component | Bound and assumptions |
|---|---|
| Finite and checked reconstruction | Exact algebraic read-back; arbitrary retained witness predicate |
| Power batching | RSG exponents 1 through e give `e/|C|`; zero-based exponents give the distinct bound `(e−1)/|C|` for e≥1 |
| Multilinear batching | Indexing `J≃{0,1}^κ` gives `κ/|C|` for uniform finite-domain challenges |
| Product sumcheck | Each retained-variable challenge contributes `2/|C|`; total `2m/|C|` |
| Final multiplier check | Deterministic; no additional challenge error |
| Full-family separation in C | Explicit functionality and injective `P → C`, compatible with the B-action |
| Flock binding | List/OOD selection has its own bad event; Appendix C Remark 11 accounts for the candidate-list factor without the first OOD selection |
| Hachi trace head | Deterministic CWSS read-back with the same weak opening; downstream norm-conditioned collisions remain in the Hachi security chain |
| Field-target lift | Defect degree ≤2d−1 and 2d distinct challenges for extraction; collision escape preserves the weak-binding boundary |

[`Tail/Accounting.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Tail/Accounting.lean)
sums the actual generic challenge indices to `batching error + m * (2/|C|)`. Domain assumptions
belong to these root bounds: over `F_q×F_q`, `(1,0)*X` vanishes at a fraction `1/q`, exceeding
`1/|F_q×F_q|`. HMZ's exceptional sets instead require invertible differences between distinct
challenges. Its Galois-ring targets are outside the implemented field-target security theorem.

## Shared implementation and proof coverage

| Shared component | Concrete consumers | Proof boundary |
|---|---|---|
| `PackingData.transpose_observe` and `readback_coordinateSlices` | Generic family read-back; tensor observations; Hachi monomial evaluation through its actual ψ basis | Commutative-ring algebra, arbitrary finite ranks/weights |
| `CheckedObservation.honest_check` and `readback_keep` | `ScalarHead`, tensor `packingObservation`, Hachi honest checking and source read-back | Exact witness transport and concrete guard/relation equivalences; preserves weak-opening predicates |
| `ClaimLayout` and polynomial transport | DP24 prefix split, Flock suffix and quirky layouts; `RingSwitching.packMLE_eq_packedMLE` identifies DP24 `splitFirst` components | Each layout proves its own original-source reconstruction |
| `FullFamily.compatibility_bad_event_le` | Generic family and tensor batching knowledge proofs | Functional compatibility fixes the witness before the challenge |
| Tensor batching specialization | `FullFRIBinius.batchingReduction_perfectCompleteness` and `batchingVerifier_rbrKnowledgeSoundnessWorstCaseWith` | Real `binaryBasefold_functional`; tensor extractor/state and error `κ/|L|` |

The generic `FullFamily/`, `ScalarHead/`, `ScalarFamily/` and `Tail/` reductions have completeness
from every initial oracle state. Their composed endpoints are precisely the same commitment's
C-valued `evalRel`. Worst-case-per-prefix knowledge uses the stated functionality, challenge
and transport hypotheses. `Append/Knowledge.lean` and `KnowledgeNary.lean` provide guarded binary
and finite-sequence composition with explicit extractors, knowledge states and component errors.
Averaged wrappers retain worst-case component premises.

[`Packing/Opening.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Opening.lean) appends a
supplied downstream reduction whose input is exactly `pc.evalRel`. Its knowledge contract permits
arbitrary downstream verifier effects. Completeness separately requires guarded verification,
every-seam-state completeness and the stated first-message or pure-output condition. Generic
assembly has an explicit common ambient oracle; concrete packing prefixes use the empty one.
The downstream opening must supply its own knowledge contract.

The tensor head and profile-based terminal have proved completeness and knowledge
contracts. The profile-based loop and unrestricted composition theorems retain admissions.
The actual FRI-Binius final verifier has accepted/rejected execution and suffix-absorption
lemmas; its downstream security and full completeness assembly still depend on admissions.
The real Binius adapter supplies both honest coverage and uniqueness from code distance and
injectivity of the Boolean-table encoder.

Hachi's trace head has monomial packing inverses, real-committer source coverage, ordinary and
message-shortness completeness, and same-opening CWSS. Its semantic ring/trace infrastructure
is noncomputable; scalar-Scheme packaging is separate. Hachi's quotient lift uses balanced
quotient digits and a local short-collision-to-Module-SIS theorem. Key sampling and recursive
end-to-end security have additional obligations; see [NOZ26](../papers/NOZ26.md).

## Coverage limits

Flock's coordinate layouts and deterministic heads share the packing proofs. A production Flock
PCS integration and list/OOD probability accounting are not implemented. Hachi §3.2/§4.5's
same-field recombination `Σ_i y_i Z^i` does not have the required injectivity: errors
`(Zδ,−δ)` cancel while changing scalar reconstruction at a by `δ(Z−a)`. The corresponding
recursive pull-back requires a sound construction with its commitment and norm semantics.
The fixed-subring field identification separately depends on `no_selfReciprocal_factor`.

DP24 p.10, Eqs.(22)–(24), describes the Galois product carrier
`L⊗_K L ≃ ∏_(σ∈Gal(L/K)) L` used for Hashcaster. This carrier adapter and HMZ exceptional-set
security are not implemented. Neither their Galois hypotheses nor field root bounds are
assumptions of the finite-free coordinate identity.

The construction map covers coordinate packing, deterministic trace relocation and quotient
lift. Other uses of “ring switching,” including FHE modulus switching or cross-characteristic
arithmetization, require their own relations and algebra.
