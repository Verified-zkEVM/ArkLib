# FRI soundness and specification audit

Source: [GMW25](../papers/GMW25.md), March 27, 2026 revision. The earlier
`zksecurity/simple-rbr-fri` development informs the proof strategy; its foundational
definitions are not duplicated in ArkLib.

## Forward-port baseline and reusable upstream work

The original FRI contribution was validated on `14a4b351d` (Lean 4.32.2).
The forward-port targets `0b5b67c63` (Lean 4.34.0), incorporating 131 intervening
commits from `main`. The validation record below concerns this integrated tree,
not the former baseline.

| Upstream changes | Relevance to FRI and reuse decision |
| --- | --- |
| #897, #903, #913, #967: modules, Lean 4.34, native measure probabilities, VCVio repin | Migrate production modules and probability statements; import VCVio's native event, conditioning, uniform-sampling, and `OptionT` lemmas directly. Do not restore the removed `ToVCVio` tree or PMF compatibility surface. |
| #766, #865, #906: module-code MCA and same-set agreement extensions | Use the consolidated `ProximityGenerator/Basic` API. `not_isMCA_iff_forall_exists_codewords` supplies simultaneous extensions on the original witness set; FRI's remaining work is the protocol-specific polynomial reconstruction and block preimage. |
| #841, #918, #932: interleaved RS list decodability, interleaving MCA, and exact agreement transfer | Reusable for future interleaved/batched FRI; do not duplicate these bridges or claim that the present unbatched theorem proves batched FRI. |
| #902: unique-decoding MDS MCA bound | `mcaError_le_mdsMCAError_of_lt` is proved below `δ_C / (ℓ + 1)`, with the full-dimension and `ℓ ≥ 2` hypotheses. The all-radii `isMCAGenerator_of_isMDSGenerator` still has an admitted list-decoding branch; it is not a certified replacement for the current powers-MCA bound. |
| #825, #845: folding contexts and list-decoding preservation | Retain the existing folding operation and its arithmetic context. List-decoding preservation can support later parameter specializations. |
| #909, #910: Johnson counting and finite list-size bounds | Reuse for future numerical refinements rather than introducing a FRI-local list-decoding theory. |
| #937, #938, #945: tensor-fold probability and anchored agreement/reconstruction | Useful for related tensor and interleaved protocols; not a replacement for the actual retained-history FRI verifier execution bridge. |
| #907 polynomial/interpolation work: Hasse–Taylor and differential-polynomial APIs, hidden-derivative rank bounds, affine Hilbert/Bezout tools, and weighted-simplex counts/moments | Potential ingredients for later list-decoding and MCA improvements. They are not premises of the current GMW25 agreement-lifting proof and should remain shared mathematical infrastructure. |
| #885, #887: state-aware sequential composition | The pure-first-verifier composition APIs are relevant to modular security proofs. The general `rbrSoundness_implies_soundness` remains unfinished, so ordinary FRI soundness keeps the direct adaptive-execution accumulation proof. |
| Typed `Interaction` framework, beginning with #851; ordered execution/state and closed-outcome work in #880, #884, #886, #889, #891 | A future framework migration opportunity, including explicit acceptance/rejection/fault outcomes. The current theorem must continue to concern the existing computable `Fri.Spec.reduction`, not silently switch to a new specification. |

Before starting a large formalization, fetch upstream and compare both the toolchain
and dependency pins with the intended merge target. A clean local proof build alone
does not establish compatibility with current `main`.

In particular, #766 already provides
`Code.minRelHammingDistCode_moduleInterleavedCode`: nonempty interleaving preserves
relative minimum distance. Reuse it when specializing MCA bounds to interleaved
codes; no separate FRI-local distance-preservation lemma is needed.

## Proof map

| Source obligation | ArkLib declaration | Scope |
| --- | --- | --- |
| Agreement of coefficient words lifts before folding | `Fri.exists_codeword_agree_of_coefficients` | Entire preimage of the agreement set |
| Folding failure implies MCA failure | `Fri.foldingAgreementFailure_implies_isMCA` | One fixed input word, all witness sets |
| Folding-round probability | `Fri.foldingAgreementFailure_prob_le_powers` | Existing powers-MCA error value |
| Numerical folding bound | `Fri.foldingAgreementFailure_prob_le_generalizedJohnson` | Existing powers-MCA theorem with all hypotheses retained |
| Density cannot decrease under folding | `Fri.card_le_mul_card_sqFoldMapGen_image` | Reuses the existing index projection |
| Agreement propagates through a safe trace | `Fri.FoldTrace.exists_codeword_agree_on` | Any sufficiently large subset of accepting queries |
| Query-round probability | `Fri.FoldTrace.query_soundness_distance` | Fixed safe commitment trace; independent uniform queries |
| Binding | `Fri.FoldTrace.exists_unique_codeword_agree` | Accepting set meets both tradeoff and degree thresholds |
| Binding from probability | `Fri.FoldTrace.exists_unique_codeword_agree_of_query_probability` | Positive query count and explicit rate threshold |
| Interpolation extraction | `Fri.FoldTrace.interpolate_accepting_agrees` | Algebraic recovery; no runtime bound asserted |
| Erasure detection | `Fri.FoldTrace.not_accepts_of_disagreement` | A disagreement query forces rejection |
| Executable local-check bridge | `RoundConsistency.roundConsistencyCheck_eq_foldValue` | Arbitrary word; an injective enumeration of a complete block |
| Executable query acceptance | `Fri.Spec.QueryRound.eval_verifyQueries` | Exact oracle answers, all rounds, and all query positions |
| Exact composed verifier execution | `Fri.Spec.reduction_run` | Retained commitments, final polynomial degree guard, and query checks |
| Input-language bridge | `Fri.Spec.mem_inputLanguage_of_proximity` | Existing computational-polynomial witness relation |
| Adaptive transcript bound | `Fri.Spec.terminalEvent_prob_le` | Actual `Prover.run`, arbitrary private witness/state types |
| End-to-end rejection bound | `Fri.Spec.soundness_proximity` | Any acceptance for inputs at distance at least `δ` |
| End-to-end ordinary soundness | `Fri.Spec.soundness` | Existing `OracleVerifier.soundness` and original input/output relations |
| End-to-end round-by-round soundness | `Fri.Spec.rbrSoundness` | Existing `OracleVerifier.rbrSoundness` and original input/output relations |

The end-to-end theorems concern `Fri.Spec.reduction`, not an alternative protocol or merely
a fixed safe trace. For folding exponents `s i`, final degree bound `d`, and `l` queries,
`Fri.Spec.soundnessError` is the sum of the existing powers-MCA errors over all folds, plus
`Real.toNNReal (1 - min θ δ) ^ l`. The tradeoff parameter `θ` is independent of `δ`.
The main theorem uses the original closed-ball input relation. The stronger rejection theorem
uses the strict proximity language, hence applies even at distance exactly `δ`.

## Specification findings

- The non-final honest prover must retain `i + 1` old oracles at round `i`. Retaining only `i`
  overwrites the latest old word, and at round zero overwrites the input. `appendFoldOracle`
  now implements the correct boundary; its two projection lemmas cover old and new entries.
- The final folding verifier checks the transmitted polynomial's degree. The subsequent
  query verifier relies on this earlier guard; it is not an independently complete FRI verifier.
- Stage relations express proximity of the current word to its polynomial witness. Their
  definitions alone do not prove soundness of an individual folding reduction: the final
  query phase must check the retained history.
- The final oracle is a polynomial sent in the clear, whereas earlier words have point-query
  interfaces. A security bridge must preserve this distinction.
- The single query challenge is a whole `Fin t` vector of initial-domain positions. Uniform
  sampling therefore gives independent queries with replacement.
- A folding exponent `s i` means a folding factor `2 ^ (s i)`. Proofs and auxiliary simulators
  must not confuse the exponent with the factor. The older `BatchedFri.Security.oracleImpl`
  passed the exponent to `polyFold`; it now passes the factor, matching the honest prover.

## Execution and security architecture

1. `Spec/Execution`, `QueryExecution`, `FoldExecution`, and `VerifierExecution` evaluate the
   actual verifier. Protocol transcript components and the retained oracle history agree
   with the chronological folding and query challenges. The final polynomial is sent in
   the clear; it is not modeled as a point-query oracle.
2. `OracleReduction/Security/BadEvents` constructs a persistent state function over existing
   transcripts: the input is valid or a bad challenge occurred. Prover moves preserve a
   false state because they cannot alter earlier challenge prefixes.
3. `Spec/RoundSoundness` and `BadEvents` bound every fresh bad event, conditional on no earlier
   one. The query event includes the final degree guard. The existing, proved worst-case
   bridge then supplies actual round-by-round soundness.
4. `OracleReduction/Security/Accumulation` independently sums conditional errors along
   `Prover.runToRound`, retaining private prover state and shared oracle state. Its terminal
   event bound covers `Prover.run`, including the prover's output computation.
5. `OracleReduction/Security/Acceptance` turns that transcript bound into ordinary soundness
   when the verifier literally rejects outside the event. No oracle-state reset or independence
   between prover commitments is assumed.

This route deliberately does not invoke the unfinished general
`Verifier.rbrSoundness_implies_soundness`, round-by-round composition, or prover-append
execution theorems. The added generic lemmas belong to the existing security framework;
no parallel security definition, Reed–Solomon code, distance, or MCA interface is introduced.

The numerical specialization in `Fri/ErrorBounds.lean` retains the actual field-size,
minimum-distance, slack, and radius hypotheses. `mcaError` remains the common interface,
not an assumed zero error.

Probability statements use native `Pr{...}[...]` semantics. `SampleableType F` is
explicit in the MCA error and probability-facing theorems; pure agreement and
verifier-execution lemmas remain sampler-free. Challenge-type transport uses
VCVio's certified uniform-sampling equivalence, so the proof does not assume that
the executable challenge sampler and a separately chosen field sampler are the
same program.

## Scope

The result is information-theoretic ordinary and round-by-round soundness of the interactive
oracle reduction, for ArkLib's powers-of-two folding domains. It does not assert Fiat–Shamir
security, concrete commitment security, knowledge soundness, or efficient extraction. The
binding/interpolation consequences above are algebraic statements for a safe trace, not a
claim of end-to-end knowledge extraction. Zero query repetitions are permitted and give the
expected vacuous query bound one.

The older BCIKS20-based batched-FRI claims in `BatchedFri/Security.lean` remain separate
unfinished statements; the new theorems do not depend on them or certify batched FRI.

## Lean 4.34.0 forward-port validation

- `lake build ArkLibTest.ProofSystem.Fri.Soundness` passes (3,817 jobs).
  Its guarded kernel checks inspect the exact verifier execution, ordinary and
  round-by-round soundness, the generalized-Johnson specialization, and the generic
  adaptive accumulation/acceptance bridges. Each reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Documentation integrity and knowledge-base lint pass.
- The 63-page blueprint PDF and bibliography compile with XeLaTeX and BibTeX on the
  integrated source tree. A full API-documentation/site build is not certified here.
- `lake build ArkLibBlueprint` and `checkdecls` pass for both the existing blueprint
  declaration list and a separate list covering all new FRI references.
- The repository-wide `./scripts/validate.sh --axioms` passes: full library build
  (4,731 jobs), acceptance clients, warning budgets, source-policy and retirement
  fixtures, compiled toy-problem and Hachi runtime checks, imports, build-timing
  fixtures, documentation checks, and the axiom regression gate.
- The sweep checks 14,285 declarations across 638 modules: no nonstandard-axiom
  taint and no new admission debt. The remaining 283 admission-tainted declarations
  are pre-existing work elsewhere; the FRI kernel checks above are admission-free.
  Native probability retirement reports zero remaining uses.
