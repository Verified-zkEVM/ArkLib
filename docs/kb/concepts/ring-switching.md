# Ring Switching

This page is the KB landing page for the **ring-switching** technique. Ring switching is a
*family* of constructions, not one protocol — ArkLib formalizes two construction folders,
each with its own data layer: `Packing/` (`RingSwitchingProfile`, small→large packing)
and `Lift/` (`Lift.Presentation`, large quotient ring→field, the generic
HMZ25 switch); the taxonomy lives in the folder umbrella
`ArkLib/ProofSystem/RingSwitching/Basic.lean`. What the two constructions share sits at the folder
top level: the check-then-update round-shape verifiers (`RoundVerifiers.lean`) and the
embed-and-evaluate transport algebra (`Transport/Eval.lean` univariate, `Transport/Coeffs.lean`
degree-generic multivariate).

The folder names describe the algebraic operation, not merely the source and target types:

- **Packing** groups a basis-sized block of small-ring coefficients into the coordinates of
  one large-ring element. For rank `2^κ`, this turns `2^κ` coefficients—and therefore `κ`
  Boolean-variable positions—into one coefficient over the large ring.
- **Lift** replaces an equality in `S ≅ R[X]/(φ)`, which holds only modulo `φ`, by an exact
  equality in `R[X]` with an explicit quotient witness. Evaluating that lifted equality in a
  field is the subsequent verification step.

This distinction matters: both operations are called ring switching in the literature, but
they require different data layers and different security arguments.

## Scope

Use this page when a question is about:

- what ring switching is and why a polynomial commitment scheme uses it;
- the `RingSwitchingProfile` abstraction and how a protocol family instantiates it;
- where Binius plugs in, and why Hachi's §3 head needs its own interface;
- which security statements are generic vs. instance-specific.

## The idea

Ring switching reduces a multilinear evaluation claim `s = t(r)` over a **small** coefficient ring
`B` (a binary-tower field, `𝔽₂`, or a cyclotomic ring `R_q`) to an evaluation claim over a **large**
extension `L` and **without re-committing** over `L`. Field instances such as Binius pay only an
additive `O(ℓ/|L|)` soundness cost (`O(1/|L|)` per challenge); Hachi's cyclotomic-ring instance has a separate CWSS-style
soundness theorem because `R_q` is not a domain. This lets a PCS commit cheaply over a tiny ring
while running sum-check and the final opening over a carrier large enough for the intended
soundness argument.

With `ℓ = ℓ' + κ`, a small-field multilinear `t` in `ℓ` variables is *packed* into a large-field
multilinear `t'` in `ℓ'` variables (`packMLE`): each block of `2^κ` coefficients becomes one
`L`-element via a `B`-basis `β` of `L`. The interaction runs in a *pack/trace carrier* `A` where the
folded element `ŝ` lives; an eq̃/trace inner-product identity (DP24 §2.5) ties `ŝ`'s coordinates to
the original claim and the new sum-check target.

## ArkLib's abstraction

ArkLib formalizes the packing *data layer* once, generic over a `RingSwitchingProfile (B L) κ`:

- `basis`, carrier `A`, ring homomorphisms `φ₀`/`φ₁ : L →+* A`, coordinate maps `decomposeRows`/`Columns`,
- plus two **reconstruction laws** (`decomposeRows_spec`, `decomposeColumns_spec`) that tie the
  coordinate maps to `φ₀`/`φ₁`/`basis`,
- two **inverse laws** (`decomposeRows_recompose`, `decomposeColumns_recompose`) making each
  coordinate map a two-sided inverse of its recomposition, and `embeddings_agree` (`φ₀`, `φ₁`
  agree on `B`).

With the inverse laws the carrier is additively equivalent to each full coordinate family
(`RingSwitchingProfile.rowEquiv`/`columnEquiv`), so a finite carrier has `|L|^(2^κ)` elements
(`RingSwitchingProfile.card_A`). For a finite nontrivial `L` and `κ > 0`, a collapsed carrier
such as `A = L`, which reconstruction alone would allow, is therefore excluded.

The row law is `z = ∑ u, φ₀(basis u) * φ₁(decomposeRows z u)`; the column law is
`z = ∑ v, φ₀(decomposeColumns z v) * φ₁(basis v)`. In the tensor carrier these read
`z = ∑ u, basis u ⊗ rows z u` and `z = ∑ v, columns z v ⊗ basis v`. Rows use the
right-factor scalar action; columns use the left-factor scalar action.

Those laws are the algebraic profile boundary, not a complete soundness theorem by themselves.
The batching/sum-check proofs still have to connect the profile coordinates to `packMLE`,
`embedded_MLP_eval`, `compute_A_func`, and the instance's eq̃/trace identity.

The *protocol* on top of the profile is per-construction. The DP24 packing protocol
(the protocol files of `ProofSystem/RingSwitching/Packing/`) is three phases (batching → sum-check → large-field IOPCS
opening); see the blueprint section *Ring Switching*
(`blueprint/src/proof_systems/ring_switching.tex`) for the protocol and security statements.
Its RBR knowledge error is `κ/|L| + Σ 2/|L| + ε_IOPCS` (DP24 §3.1–3.2); the final consistency
step sends no challenge and adds no error. Soundness requires `[NoZeroDivisors L]`
(Schwartz–Zippel).

## Shared coordinate algebra

Below the profile, `Packing/` has a framework-independent coordinate layer that imports no
reduction framework. `PackingData` (`Packing/Coordinates.lean`) takes independent finite bases of a
packing algebra `P` and an opening algebra `E` over a common ring `B`, with no embedding between
them; `PackingData.transpose` is the coordinate transpose `(ιP → E) ≃ₗ[B] (ιE → P)`. On top of it:

- `FiniteObservation` and `CheckedObservation` — weighted observations, their coordinate slices,
  and read-back of a scalar claim from an accepted, honest message;
- `Polynomial` and `Relations` — packed multilinear polynomials with both round trips, and the
  opening, slice and batched-sumcheck relations;
- `Multiplier` — the public multiplier evaluated by a read-once matrix program
  (`Data/Matrix/ReadOnce.lean`);
- `Batching` — `BatchingStrategy`, a uniform challenge distribution with a proved collision bound
  (`gammaPowers`, `eqFold`, `singleton`, `reindex`);
- `ScalarHead/Layout` and `ScalarHead/Quirky` — prefix, suffix and quirky Lagrange layouts, each
  with a proved reconstruction identity.

Everything holds over commutative rings, including rings with zero divisors, except the two
Schwartz–Zippel batching strategies, which need a finite domain, and the quirky layout, whose
Lagrange interpolation needs the opening algebra to be a field.

## The three constructions

- **DP24 packing switch** (`ProofSystem/RingSwitching/Packing/`, tensor-product profile
  `tensorProductProfile`):
  small field → large field; `A = L ⊗_K L`, `φ₀ = ·⊗1`, `φ₁ = 1⊗·`, coordinates from the
  left/right `L`-module bases; all profile laws are **proven** in ArkLib. Because the
  evaluation point is an arbitrary big-field point, the claim is relocated *interactively*
  (batching challenge + dedicated packing sum-check).

  Binius instantiates it with `biniusProfile`. The conformance theorem `batching_conforms`
  (`ArkLibTest/ProofSystem/RingSwitching/Conformance/Binius.lean`) states the batching phase's
  accepting round through the coordinate layer, at `PackingData.ofBasis` of the profile basis
  and the prefix layout `packedPrefixLayout`. The column check passes and the accepted output is
  in the round-zero sumcheck relation exactly when:
  - the packed polynomial is compatible with the oracle statement;
  - the round polynomial is the shared `multiplier` times the packed polynomial;
  - the batched rows of the sent carrier are in the shared `sumcheckClaimRel`;
  - the claim is the layout-weighted sum of the carrier's columns.

  Companion statements put the input relation through the `packedMLE` of the prefix-layout
  components, and characterize the honest carrier by `sliceRel` on its rows or, equivalently,
  `openingClaimRel` on its columns. `biniusBatching_conforms` instantiates the theorem at
  `biniusProfile` and the first-codeword relation. `compute_final_eq_value_eq_multiplier`
  states the final sum-check check's equality value as the same shared `multiplier`, evaluated
  at the sum-check challenges. The intermediate sum-check rounds and the FRI phases are out of
  scope.

  These statements identify the relations only. Acceptance fixes only the batched target, not
  the carrier; that collision event is bounded by `compute_s0_collision_le`. The fixture
  `failedCheck_aborts` pins that a failed check aborts.

  Security of the DP24 phases is proved as follows.
  - The shared verifiers (`scalarRoundOracleVerifier`, `messageRoundOracleVerifier`,
    `Sumcheck.Structured.roundOracleVerifier`) abort on a failed check, so a rejected transcript
    produces no output.
  - Knowledge soundness assumes `AbstractOStmtIn.Functional`
    (`Packing/Compatibility.lean`): an oracle statement is compatible with at most one packed
    polynomial, so that polynomial is fixed before any challenge.
  - Each phase's knowledge soundness is proved in the worst-case form
    (`Verifier.rbrKnowledgeSoundnessWorstCaseWith`: every fixed transcript prefix, over the
    fresh challenge alone, with the extractor and knowledge-state function named). The
    existential worst-case and averaged forms are corollaries. These per-phase results are
    sorry-free and axiom-clean under their stated hypotheses (`AbstractOStmtIn.Functional` and
    `[NoZeroDivisors L]`).
  - Batching: `batchingReduction_perfectCompleteness` and
    `batchingOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor`, at error `κ/|L|`
    (`prob_exists_consistent_ne_le`).
  - Sum-check rounds: `iteratedSumcheckOracleReduction_perfectCompleteness` and
    `iteratedSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor`, at error
    `2/|L|` per round.
  - Final step: it outputs the claim `t'(r') = s'`, completeness is
    `finalSumcheckOracleReduction_perfectCompleteness`, and it has no challenge
    (`finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor` is vacuous).
  - Composed completeness: `coreInteraction_perfectCompleteness` and
    `FullRingSwitching.fullOracleReduction_perfectCompleteness` are proved through the
    guarded-verifier composition theorems. The full reduction's completeness is stated at the
    strict relations (`AbstractOStmtIn.strictView`, honest compatibility).
  - Composed knowledge soundness, sorry-free and axiom-clean under the stated hypotheses: the core
    interaction (`SumcheckPhase.coreInteraction_rbrKnowledgeSoundnessWorstCase`) and batching
    followed by it (`FullRingSwitching.batchingCore_rbrKnowledgeSoundnessWorstCase`) compose the
    phase theorems through the guarded worst-case composition theorems
    (`Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`,
    `Verifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded`, and their `OracleVerifier`
    wrappers). Each verifier is guarded by its own checks (`SumcheckPhase.sumcheckLoopGuardedForm`,
    `SumcheckPhase.coreInteractionGuardedForm`, `FullRingSwitching.batchingCoreGuardedForm`,
    transported to the converted oracle verifiers by `Verifier.GuardedForm.ofEq`). The averaged
    `coreInteraction_rbrKnowledgeSoundness` and `batchingCore_rbrKnowledgeSoundness` are
    corollaries.
  - The full composite, sorry-free and axiom-clean **given a worst-case opening**:
    `FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundnessWorstCase` additionally takes
    `hPCS : mlIOPCS.RbrKnowledgeSoundWorstCase`, which says the downstream opening's verifier is
    worst-case round-by-round knowledge sound (`OracleProof.rbrKnowledgeSoundnessWorstCase`) at the
    relation and error of its averaged field. Its averaged form is
    `FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness_of_worst_case`. The hypotheses
    hold together: `ArkLibTest/ProofSystem/RingSwitching/Conformance/BiniusComposition.lean`
    (`full_concrete`) closes the composite at the GF(4)/GF(2) fixture with the zero-round opening
    of `Conformance/DirectOpening.lean`, which reads the polynomial from its oracle.
    `MLIOPCS.RbrKnowledgeSoundWorstCase` is a hypothesis on an `MLIOPCS`, not a replacement of its
    averaged `rbrKnowledgeSoundness` field: worst-case implies averaged
    (`OracleProof.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness`, which also fills
    the averaged field of an instance that proves the worst-case form). The implication runs in
    one direction only (the note on the worst-case-per-prefix variants in
    `OracleReduction/Security/RoundByRound.lean`), so an opening whose knowledge soundness depends
    on averaging is still an `MLIOPCS`.
  - The full composite **under a plain `MLIOPCS`** stays conditional:
    `FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` uses only the averaged
    `MLIOPCS.rbrKnowledgeSoundness` contract, so it applies the admitted
    `OracleVerifier.append_rbrKnowledgeSoundness`. That contract's statement is flagged as not
    derivable from its hypotheses (`Composition/Sequential/Append/Security.lean`), so this is
    unverified statement debt.
  - Still conditional elsewhere, on other admitted lemmas: scalar (non-round-by-round) knowledge
    soundness of any composite would go through the admitted
    `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` (`Security/Implications.lean`).
    On this branch the FRI-Binius and Binary Basefold composites
    (`Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness`,
    the `Binius.BinaryBasefold.CoreInteraction.*OracleVerifier_rbrKnowledgeSoundness` composites,
    `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness`) apply
    the admitted averaged `OracleVerifier.append_rbrKnowledgeSoundness`. FRI-Binius `SumcheckFold`'s phase theorem is
    itself admitted, with `OracleVerifier.liftContext_rbr_knowledgeSoundness` (admitted) as its
    intended route. In the generic sum-check (`Sumcheck/Spec/`), the full protocol's
    `Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` applies the admitted
    `OracleVerifier.seqCompose_rbrKnowledgeSoundness`, and the single round's
    `Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness` applies the admitted
    `OracleVerifier.liftContext_rbr_knowledgeSoundness`.
- **Hachi §3 packing head** ([`../papers/NOZ26.md`](../papers/NOZ26.md), planned): `L = R_q`,
  `A = R_q`, `φ₀ = id`, `φ₁ = σ₋₁`, `β = ψ` (Theorem 2). The carrier is `L` itself, so for
  `κ > 0` this is **not** a `RingSwitchingProfile` instance; it needs its own trace interface
  over the shared finite-coordinate modules. The evaluation point is engineered to be
  subfield-valued, so the reduction is **deterministic**
  (one message + one trace check, no challenges, no sum-check). `R_q` is not a domain, so the
  Schwartz–Zippel soundness theorem does not apply — Hachi soundness is a separate (CWSS)
  argument.
- **HMZ25 `Lift` construction** ([`../papers/HMZ25.md`](../papers/HMZ25.md)): the
  *opposite* direction, `S ≅ R[X]/(φ)` → a field `F` — lift `M z = y` to `R[X]` and evaluate
  at a random `α`. **Formalized generically** in `ProofSystem/RingSwitching/Lift/`
  over any monic-modulus presentation (`Presentation`/`IsPresentation` — not
  cyclotomic-specific), with CWSS at `k = 2·deg φ` proven once from the presentation laws,
  on top of the committed-scalar shell
  (`OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`).
  Hachi's link 4 (`Commitments/Functional/Hachi/RingSwitch/Reduction.lean`) is the proven
  cyclotomic instance (`cyclotomicPresentation`). It does **not** instantiate
  `RingSwitchingProfile`; what it shares with DP24 is the `pSpecScalar` wire shape and the
  top-level layer of `ProofSystem/RingSwitching/` (round-shape verifiers, embed-and-evaluate
  transport).

## Core References

- [`../papers/DP24.md`](../papers/DP24.md) — origin of ring switching for binary towers.
- [`../papers/NOZ26.md`](../papers/NOZ26.md) — Hachi; the extension-field→cyclotomic-ring reduction.
- [`../papers/RSG.md`](../papers/RSG.md) — ring switching with independent packing and opening bases.
- [`../papers/BRW26.md`](../papers/BRW26.md) — Flock; scalar-claim heads and the quirky layout.

## Main ArkLib Touchpoints

- [`../../../ArkLib/ProofSystem/RingSwitching/Basic.lean`](../../../ArkLib/ProofSystem/RingSwitching/Basic.lean) — the family taxonomy umbrella.
- [`../../../ArkLib/ProofSystem/RingSwitching/RoundVerifiers.lean`](../../../ArkLib/ProofSystem/RingSwitching/RoundVerifiers.lean) — the shared check-then-update round verifiers.
- [`../../../ArkLib/ProofSystem/RingSwitching/Transport.lean`](../../../ArkLib/ProofSystem/RingSwitching/Transport.lean) — the shared claim-transport algebra (umbrella for `Transport/`).
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean) — the packing abstraction.
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/Coordinates.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Coordinates.lean) — independent packing and opening bases, coordinate transpose.
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/Relations.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Relations.lean) — opening, slice and batched-sumcheck relations.
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/Batching.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Batching.lean) — batching strategies with proved collision bounds.
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/Algebra.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Algebra.lean) — `packMLE`, the tensor-product constructor `tensorProductProfile`, the DP24 verifier subroutines.
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean) — DP24 protocol vocabulary and relations.
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/Compatibility.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Compatibility.lean) — the binding hypothesis `AbstractOStmtIn.Functional`.
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean) — the full DP24 reduction + security theorems.
- [`../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean`](../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean) — the quotient-presentation abstraction + lift algebra.
- [`../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean`](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean) — the generic `Lift` construction + CWSS.
- [`../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean) — the committed-scalar protocol seam.
- [`../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean`](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean) — `biniusProfile`, the concrete instantiation.

## Notes

- The DP24 protocol skeleton is profile-generic. The displayed completeness and soundness
  statements are unproved targets (`sorry`); instance-specific packing, folded-evaluation, and
  multiplier identities remain necessary proof obligations.
- Soundness reuse across instances is weaker than data-layer reuse: the intended
  Schwartz–Zippel bounds require `[IsDomain L]`, which fits field instances (Binius) but not
  non-domain rings (Hachi `R_q`). The latter need a separate soundness argument and error bound.
