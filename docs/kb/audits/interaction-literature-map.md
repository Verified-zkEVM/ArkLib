# Interaction security beyond the textbook

The Chiesa-Yogev textbook is a required coverage target, but it is not the only source contract
for ArkLib. Later and parallel work develops relation-to-relation extraction, functional-query
compilers, duplex-sponge Fiat-Shamir, and compositional zero knowledge. These should inform
the native framework before its knowledge and compiler interfaces are fixed.

This page supplements the [textbook comparison](chiesa-yogev-interaction.md). It corrects the
impression that every difference from the book is an unsupported generalization. In particular,
ArkLib's witness-indexed round-by-round state has a close literature antecedent in WARP, and
the source explicitly compares its definition with ABF26 Appendix A.5. Conversely, an inherited
paper idea is not evidence that the implemented game or theorem is equivalent to that paper.

Checked on October 3, 2026 UTC, against ArkLib's code at
`ace55c3e29da1fc55a321378ada55ea4f7ed8790`, the research notes at `9afef7477`, and the
VCVio revisions recorded in the textbook comparison. This is source research, not a new proof
or transitive axiom audit. The [roadmap](../../design/05-roadmap.md#bounded-interaction-theory-investigation)
owns implementation sequencing.

## Source map and chronology

The ePrint identifier's year is not the date of the inspected revision. Several important
2025 papers have 2026 revisions later than the inspected March 25, 2026 textbook release.
Other foundational papers predate the original 2024 book. "Beyond the textbook" includes both.

| Source | Inspected version or evidence | Why it matters here |
|---|---|---|
| [Linear-Size Constant-Query IOPs for Delegating Computation][ior19], Ben-Sasson, Chiesa, Goldberg, Gur, Riabzev, Spooner | ePrint 2019/1230, October 24, 2019 revision, full PDF | Earlier IORs and virtual output oracles; this idea did not originate with ARC or ArkLib |
| [Linear-Time Arguments with Sublinear Verification from Tensor Codes][bcg20], Bootle, Chiesa, Groth | ePrint 2020/1426, December 28, 2020, full PDF | Special-query IOP lineage underlying functional IOPs |
| [On Soundness Notions for Interactive Oracle Proofs][bgtz23], Block, Garreta, Tiwari, Zajac | ePrint 2023/1256, March 5, 2024 revision, definitions/results inspected | A further RBR notion already explicitly referenced by pinned VCVio |
| [On the Security of Succinct Interactive Arguments from Vector Commitments][vector23], Chiesa, Dall'Agnol, Guan, Spooner | ePrint 2023/1737, September 14, 2024 revision; abstract-level screening only | IBCS, Finale, public-query IOPs and random continuation sampling; deeper audit remains open |
| [Accumulation without Homomorphism][awh24], Bünz, Mishra, Nguyen, Wang | ePrint 2024/474, September 26, 2024, full PDF | Hash-based accumulation and its earlier depth/decoding setting |
| [ARC: Accumulation for Reed-Solomon Codes][arc24], same authors | ePrint 2024/1731, cover October 25, 2024; ePrint revision June 5, 2025, full PDF | Relation-to-relation IOR knowledge security and proximity accumulation |
| [FICS and FACS][fics25], Baweja, Mishra, Mopuri, Shtepel | ePrint 2025/737, May 20, 2026, full PDF | Round-by-round tree extraction is a distinct live route |
| [Linear-Time Accumulation Schemes (WARP)][warp25], Bünz, Chiesa, Fenzi, Wang | ePrint 2025/753, cover June 17, 2026; ePrint revision June 18, 2026, full PDF | Witness-indexed local backward extraction and its SR theorem |
| [A Fiat-Shamir Transformation From Duplex Sponges][co25], Chiesa, Orrù | ePrint 2025/536, March 27, 2026, full PDF | Ideal-permutation compiler, codecs, trace translation and quantitative extraction |
| [On the Fiat-Shamir Security of Succinct Arguments from Functional Commitments][funky25], Chiesa, Guan, Knabenhans, Yu | ePrint 2025/902, June 2, 2026, full PDF | The Funky protocol; functional-query and commitment security under restoration |
| [How to Prove Post-Quantum Security for Succinct Non-Interactive Reductions][cdhz25], Chiesa, Di, Hu, Zheng | ePrint 2025/2166, March 2, 2026, full PDF | The WARP-style security route extends to post-quantum SR and compiled reductions |
| [Zero-Knowledge IOPPs for Constrained Interleaved Codes][cfw26], Chiesa, Fenzi, Weissenberg | ePrint 2026/391, February 25, 2026, full PDF | Relaxed relations, output-observing HVZK and compositional query accounting |

The existing [ABF26 comparison](open-problems-list-decoding-and-correlated-agreement.md) is
also essential, especially Appendix A.5 and the implemented toy-problem clients. The present
pass does not establish a complete bibliography or historical priority for every definition.
The inspected textbook already cites CGKY25; absence of a full Funky treatment is not absence
of awareness of that work.

## ARC, WARP and the library's actual knowledge notion

ARC Definition 5.5 uses a scalar state and an extractor on prover messages plus an output
witness. Remark 5.6 explains the restriction imposed by its demand for a witness at intermediate
success points. WARP Section 2.8 motivates relaxing this requirement: erasure-based recovery
can need the final witness. Definitions 4.1-4.2 instead index the state by a witness and bound
the probability of a failed backward transport step. Appendix B, Theorem B.4 and Construction
B.5, derive straightline SR extraction by running these steps backward from the output witness,
with error `(t + k) * max(error_i)` and summed extraction time. [ARC][arc24], [WARP][warp25].

The local bad event has this shape, for a fixed authored prefix `tr`:

```text
Pr[r fresh; exists w,
    not K(tr, E(tr ++ r, w)) and K(tr ++ r, w)] <= error_i.
```

The existential witness is inside the probability. Outside that bad event, transport succeeds
for every later witness, including one selected after the remainder of the protocol. This is
the precise reason offline backward composition can work. An online middle-witness supplier
is not a universal prerequisite.

The closest explicit code citation is **ABF26 A.5**, in
[`KnowledgeStateFunction`](../../../ArkLib/OracleReduction/Security/RoundByRound.lean).
The fixed-prefix API was added in commit `5cfd3e8a4` as the ABF26 split. The earlier generalized
extractor structure appears in `06a6e4d70`. The structural match to WARP is verified; these
facts alone do not prove which paper historically motivated that earlier commit.

| Clause | Literature-shaped contract | Current ArkLib difference or match |
|---|---|---|
| Initial state | Witness membership in the input relation, possibly relaxed | `toFun_empty` has this relation-based shape, unlike CY's scalar all-input zero law |
| Prover move | Preserve falsity for the same witness | ArkLib permits `extractMid` to change the witness even across a prover move |
| Witness carrier | Witness-bearing state with source-specific typing | ArkLib explicitly exposes a round-indexed `WitMid` and a final `extractOut` |
| Terminal state | Iff membership in the output relation | ArkLib requires only positive-probability related verifier output to imply final knowledge state |
| Local challenge | Every fixed prefix; existential later witness inside the sampled event | `rbrKnowledgeSoundnessWorstCase` has this quantifier shape |
| Execution average | Not a replacement for the local premise of the SR proof | Default `rbrKnowledgeSoundness` samples earlier prefixes; it is a separate consequence |
| Algorithm and resources | Deterministic extraction with explicit time bounds | The legacy API permits noncomputable functions and carries no such complexity proof |
| Effects | The inspected paper clauses have a definite terminal verifier interpretation | The legacy clause runs from fresh `init`; a persistent-world specialization needs additional evidence |

The right native target is therefore a **WARP/ABF-compatible witness-transport specialization**,
alongside CY-compatible scalar/whole-message notions. It is inaccurate to call ArkLib's notion
simply "stronger than CY": the allowed information, witness typing, terminal laws and efficiency
requirements differ. A generalization may weaken some assumptions while strengthening an event.

WARP Appendix C gives an older-to-new bridge with an explicit extractor-consistency premise.
Its Theorem C.1 is labeled informal. The text calls the new notion a strict relaxation, but this
audit did not locate a formal strict-separation construction there. Do not claim an unconditional
equivalence or silently delete the consistency premise. [WARP, Appendix C][warp25].

FICS/FACS makes the distinction sharper: its discussion says comparability between WARP's
notion and round-by-round tree extraction is unknown. Its Lemma 4.8 uses the earlier CY/ARC
notion, not an established WARP-to-tree implication. Preserve the tree-extraction lane without
making it a corollary of the wrong RBR contract. [FICS/FACS][fics25].

Pinned VCVio's [`KnowledgeExtractionFamily`](https://github.com/Verified-zkEVM/VCVio/blob/d7089e46d69e07640fa23b5ae6b1b966f1d4b949/VCVio/CryptoFoundations/RoundByRound.lean)
explicitly follows BGTZ Definition 3.12: efficient extraction in the paper is triggered when
escape probability exceeds the round error. The library deliberately formalizes extensional
content without polynomial-time claims. Reuse `GameFamily` as probability infrastructure;
do not identify these different knowledge interfaces merely because they share that container.

## FIOPs, IORs and Funky separate two independent axes

A functional IOP generalizes **what a verifier can ask** about a prover message. An IOR
generalizes **what the protocol returns**: a related statement, oracle data and witness rather
than just acceptance. ArkLib needs both axes, including their combination, without conflating
them with persistent oracle-world effects or dependent schedules.

Virtual output oracles and query-free reduction stages already appear in the 2019 IOR work.
Definitions 5.1-5.2 use nonadaptive source-location plans. Lemma 5.4 gives additive soundness
loss and multiplicative query locality for composition with an IOPP; the paper states that
lemma without proof. Native adaptive oracle programs need an explicit restricted-plan
correspondence before inheriting that particular cost formula.
Funky's FIOP definition builds on special-query IOPs: point queries, linear queries and
polynomial evaluations are different instances of a query class. These provide literature
precedents for significant parts of ArkLib's interfaces. Our additional dependent/effectful
semantics and proved bridges still require comparison; the labels "IOR" and "functional"
alone are not novelty claims. [IORs][ior19], [special queries][bcg20], [Funky][funky25].

Funky is an interactive **argument**, compiled from an FIOP and a functional commitment.
Its state-restoration theorem requires security of both ingredients against restoration.
Ordinary function binding is not interchangeable with state-restoration function binding.
The general result uses query-class solving and tail-error properties, not a universal demand
that the commitment backend expose the entire committed message. See Theorem 7.1, Section 5
and the commitment definitions in [CGKY25][funky25].

Consequences for ArkLib:

- The [functional commitment interface](../../../ArkLib/Commitments/Functional/Basic.lean)
  already cites CGKY25, and the [KZG reduction](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean)
  is a substantive client. These do not establish the whole Funky compiler theorem.
- Backend capabilities must be selected by the compiler proof. Merkle multi-extraction and
  functional-binding/solver arguments are different sufficient mechanisms; requiring the same
  extractor from every backend could unnecessarily exclude supported constructions.
- Funky ends in a verifier decision. A compiler for ArkLib's output-oracle reductions requires
  a separate relation/output-interface theorem; replacing an FIOP by an arbitrary F-IOR is
  not a free substitution in the published result.
- Keep ideal message guarantees distinct from allowed queries. A general query interface does
  not itself enforce a degree bound or prove a decoding promise.
- Native `Behavior` can be an answer function not represented by any single message. A
  FIOP/commitment bridge must identify realized behaviors and enforce joint consistency;
  it cannot treat every handler as a concrete committed string. See
  [Virtual](../../../ArkLib/Interaction/Oracle/Virtual.lean) and
  [Claim](../../../ArkLib/Interaction/Oracle/Claim.lean).

BCG2020 additionally permits queries jointly inspecting the instance and several messages;
query-dependent challenges and public-coin restrictions are separate choices. Funky's theorem
uses its own per-message query-class presentation. Supporting the former syntax is not yet a
compiler instance of the latter. Earlier [Marlin](https://eprint.iacr.org/2019/1047) also makes
bounded-degree messages an explicit admissibility condition: the ideal polynomial-message
model is established literature, while its concrete realization remains a compiler obligation.
The Marlin PDF inspected here is the October 4, 2021 revision; its AHP model and knowledge
definition, and Theorems 8.1/8.3, were checked as earlier context.

## Duplex-sponge Fiat-Shamir is a separate compiler branch

Chiesa-Orrù Definitions 4.1-4.2 and Construction 4.3 specify injective encodings, statistically
biased challenge decoding, random initialization, a random permutation and its inverse, and
sampled/absorbed salt. Lemma 5.1 translates the joint output and prover/verifier trace to **basic
full-prefix Fiat-Shamir**. This is not an identification with CY's hash-chain construction.
Theorems 6.1-6.2 give additive loss `25 t^2 / |Sigma|^c + t max(epsilon_i) + sum(epsilon_i)`
under their parameter hypotheses, plus failure/time substitution for knowledge extraction.
Section 2.6 explains the `DSFS[iBCS[IOP]]` branch. [Chiesa-Orrù][co25].

The exact paper comparison exposes statement repairs before security proof work:

| Current code | Measured issue against the inspected paper |
|---|---|
| [KeyLemma](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemma.lean), lines 116-122 | `duplexSpongeToFSGameStatDist` concludes `True` and is admitted; it is not yet a distance theorem |
| Same file, line 102; [sponge size](../../../ArkLib/Data/Hash/DuplexSponge.lean), lines 214-215 | Error denominator uses `2 * card(U)^(C+1)` despite `C = N-R`; paper Eq. (5) uses capacity exponent `c` |
| [TraceTransform](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean), lines 31-42 | Declared basic-to-duplex direction is opposite the paper's duplex-to-basic trace translation |
| [Defs](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean), lines 152-157 and 203-214 | Current transforms have initialization but no explicit sampled/absorbed salt from Construction 4.3 |
| [BadEvents](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean), lines 301-338 | Several events are placeholder empty-trace/zero-state predicates; there is also genuine proved collision analysis elsewhere in the file |
| [Backtrack](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Backtrack.lean), lines 92-93 | The maximality condition includes the self-pair; substituting the same sequence makes every disjunct false, forcing an empty family. This is a source-level deduction, not a new Lean counterexample |

These findings are recorded here without editing the Lean declarations. A later repair needs
explicit scope and fresh statement review, not an instruction to fill the existing holes.
Additional obligations include a coupled forward/inverse permutation semantics, preservation
of verifier/rejection traces, and normalization of the codec API's L1 bias against total variation.
Uniformly sampling a complete finite permutation exists in VCVio; that is distinct from a
proved efficient lazy permutation service. No such dedicated service surfaced in this search.

[CFRG draft-03][cfrg] is a related implementation specification with XOF suites and session
identifiers. It is a draft, dated August 17, 2026, and a separate conformance target; neither
the paper nor ArkLib currently gives an automatic equivalence to every deployed suite.

## Two further sources change future interface requirements

**Post-quantum reductions.** CDHZ Definitions 3.5-3.6 use the witness-indexed relaxed RBR
contract. Theorem 6.10 converts it to post-quantum SR, and Theorem 11.3 compiles IORs using
post-quantum multi-extractable vector commitments. Definition 10.3 separates simulation,
query consistency/idempotency, commutativity and extraction guarantees. This validates keeping
the WARP line in scope. It does not turn a classical persistent-state runner into a QROM model:
superposition access and disturbance require their own semantics. Also, SR queries can arrive
out of prefix order; a freshness argument must handle that explicitly. [CDHZ][cdhz25].
The compiler's monotone-output-relation premise must also be retained; erasure tolerance is
not an automatic property of arbitrary dependent output relations.

**Compositional zero knowledge.** CFW Definitions 3.6-3.7 extend the WARP contract to relaxed
relations. Definitions 4.1-4.2 give the verifier view an additional observer of the output oracle.
Theorem 4.5 composes HVZK using the distinguisher class induced by the suffix simulator,
with additive error and explicit input/proof query blowup. This is directly relevant to native
virtual outputs and access accounting. A transcript-only privacy condition could lose precisely
the information a later reduction can observe. HVZK is not silently malicious-verifier ZK.
[CFW][cfw26].

The remaining priority queue includes the full Finale/RCS proof, the relationship to algebraic
reductions of knowledge, and protocol-specific WHIR/STIR/FRI and code-switching clients.
Those are retained targets, not audited equivalences. The current pass is broad enough to
change the architecture questions, not to close the literature search.

## What this changes in the proposed overnight work

1. Preserve the ordinary arbitrary-prefix/Sumcheck work. It remains a useful execution test,
   but no longer serves as the only conceptual anchor for the next security layer.
2. Make a WARP/ABF-shaped relational RBR certificate and one backward-composition theorem the
   primary knowledge experiment. Require explicit source specialization and a non-`Unit`
   witness. Retain the same-prefix/existential-witness event and account for the paper's time
   claim separately.
3. Keep CY whole-message extraction, BGTZ escape-trigger extraction, and FICS/FACS tree
   extraction as named comparison targets. No universal implication diagram is adopted yet.
4. Keep the Funky and duplex paths in the compiler scope. Duplex statement repair is a distinct
   prerequisite package; it should not be smuggled into an already busy ordinary-security night.
5. Before accepting an interface, test whether it can express the CFW output-observing privacy
   experiment and the CDHZ reduction endpoint. This is a design test, not an overnight demand
   to formalize zero knowledge or quantum cryptography.

Open questions now have better evidence: how to generalize WARP's same-witness laws to native
dependent witness fibers; how to relate the distinct extraction capabilities; how to combine
functional-query and relation-output compilers; which backend guarantees each proof consumes;
and how to preserve actual-world effects, observation and cost. The literature solves parts
of these questions in particular models. ArkLib should recover those results before claiming
a new general theorem, and should not restrict its eventual generality to any one paper.

## Artifact provenance

No PDFs or extracted text are committed. The exact inspected PDF bytes are identified below;
URLs above are canonical ePrint identifiers and may serve newer revisions later. Page/definition
numbers refer to these artifacts. BGTZ was read through the primary PDF web view; vector23 was
screened only through its primary metadata/abstract and is not assigned a definition-level verdict.

| Source | Pages | PDF SHA-256 |
|---|---:|---|
| IOR19 | 54 | `baeb2f4b939c686eec80bbab4803f37175c295baa5068ebbe4d977e81001e131` |
| BCG20 | 70 | `cb00118c1c09bba04ebacaffe068d5409ca04354b177a4d2ed46e1d4af39cc49` |
| Marlin | 82 | `bb2f7af0cc59f12e900e25ab797ff69f01a5153a51ed4da1c0f07ca72c4ef375` |
| AWH24 | 51 | `fabfd59ff3bb40a548e2e9453ae1d510c2fb6e8dbd67b8962917b1901e0a9999` |
| ARC | 57 | `954f495a2521817a68a0be378dd6cdfd719ecc74cd10f52cb338b923f8cf21bf` |
| FICS/FACS | 92 | `6cc2da94ab707f0cfd17a1f8baf88d53bcc11420fd541e8316dddb2d6bd4781a` |
| WARP | 76 | `22944c8ef358bf973c4eaca7617fc534f024e3658142244668ae0030b4ae904c` |
| Chiesa-Orrù | 83 | `fca7ba09ebe59141c3c041ac660b4e3e161fdab8a709aee67e236db8d8da3a35` |
| Funky | 90 | `a3015f140ed9750b05e23a8b6fb3dcbb4d93be81cd388fb0ef39abb17dd06560` |
| CDHZ | 102 | `2cfb88c76732d9f39f4b1943b4aabc0390dd3d17830d91d910c38e16e4bb5a30` |
| CFW | 82 | `6a2092b7bc50e5ea68ec8e679c4b830f2fe260c961dc08ee7582b7e652a46f7c` |

[ior19]: https://eprint.iacr.org/2019/1230
[bcg20]: https://eprint.iacr.org/2020/1426
[bgtz23]: https://eprint.iacr.org/2023/1256
[vector23]: https://eprint.iacr.org/2023/1737
[awh24]: https://eprint.iacr.org/2024/474
[arc24]: https://eprint.iacr.org/2024/1731
[fics25]: https://eprint.iacr.org/2025/737
[warp25]: https://eprint.iacr.org/2025/753
[co25]: https://eprint.iacr.org/2025/536
[funky25]: https://eprint.iacr.org/2025/902
[cdhz25]: https://eprint.iacr.org/2025/2166
[cfw26]: https://eprint.iacr.org/2026/391
[cfrg]: https://www.ietf.org/archive/id/draft-irtf-cfrg-fiat-shamir-03.txt
