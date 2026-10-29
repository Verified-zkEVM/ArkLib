# FRI soundness and specification audit

Source: [GMW25](../papers/GMW25.md), March 27, 2026 revision. The earlier
`zksecurity/simple-rbr-fri` development informs the proof strategy. Source provenance and
author credit are recorded on the paper page.

## Proof map

| Source obligation | ArkLib declaration | Scope |
| --- | --- | --- |
| Agreement of coefficient words lifts before folding | `Fri.exists_codeword_agree_of_coefficients` | Entire preimage of the agreement set |
| Folding failure implies MCA failure | `Fri.isMCA_of_foldingAgreementFailure` | One fixed input word, all witness sets |
| Folding-round probability | `Fri.foldingAgreementFailure_prob_le_powers` | Existing powers-MCA error value |
| Numerical folding bound | `Fri.foldingAgreementFailure_prob_le_generalizedJohnson` | Existing powers-MCA theorem with all hypotheses retained |
| Density cannot decrease under folding | `Fri.card_le_mul_card_sqFoldMapGen_image` | Existing index projection |
| Agreement propagates through a safe trace | `Fri.FoldTrace.exists_codeword_agree_on` | Any sufficiently large subset of accepting queries |
| Query-round probability | `Fri.FoldTrace.query_soundness_distance` | Fixed safe commitment trace; independent uniform queries |
| Corollary 5.6, algebraic conclusions | `Fri.FoldTrace.exists_codeword_of_query_probability` | Separate distance and tradeoff parameters; proximity, binding, interpolation, and erasure detection |
| Binding from probability | `Fri.FoldTrace.exists_unique_codeword_agree_of_query_probability` | Positive query count; `δ ≤ θ` and `δ ≤ 1 - d / 2^n` |
| Interpolation | `Fri.FoldTrace.interpolate_accepting_agrees` | Every cardinality-`d` subset of accepting positions |
| Erasure detection | `Fri.FoldTrace.not_accepts_of_disagreement` | A disagreement query forces rejection |
| Executable local-check bridge | `RoundConsistency.roundConsistencyCheck_eq_foldValue` | Arbitrary word; an injective enumeration of a complete block |
| Executable query acceptance | `Fri.Spec.QueryRound.eval_verifyQueries` | Exact oracle answers, all rounds, and all query positions |
| Exact composed verifier execution | `Fri.Spec.reduction_run` | Retained commitments, final polynomial degree guard, and query checks |
| Input-language bridge | `Fri.Spec.mem_inputLanguage_of_proximity` | Existing computational-polynomial witness relation |
| Adaptive transcript bound | `Fri.Spec.terminalEvent_prob_le` | Actual `Prover.run`, arbitrary private witness/state types |
| End-to-end rejection bound | `Fri.Spec.soundness_proximity` | Any acceptance for inputs at distance at least `δ` |
| End-to-end ordinary soundness | `Fri.Spec.soundness` | Existing `OracleVerifier.soundness` and original input/output relations |
| Deterministic returned-witness recovery | `Fri.Spec.Extractor.extractHistory_eq_some_of_safeHistory` | Safe retained history, valid final polynomial, and enough accepting positions |
| Dense returned-witness recovery | `Fri.Spec.Extractor.extractHistory_eq_some_of_density` | Inclusive rate boundary; agreement within the stated distance |
| Literal measured extractor | `Fri.Spec.Extractor.extractHistory_eq_profile` | Public result is the first projection of the measured program |
| End-to-end knowledge soundness with named extractor | `Fri.Spec.knowledge_soundness_with` | Every input statement; actual logged knowledge game; extraction failure includes `none` |
| End-to-end existential knowledge soundness | `Fri.Spec.knowledge_soundness` | The same specific straightline extractor witnesses existence |
| End-to-end round-by-round soundness | `Fri.Spec.rbr_soundness` | Existing `OracleVerifier.rbrSoundnessAveraged` and original input/output relations |

## Parameters and conclusions

The end-to-end theorems concern the computable `Fri.Spec.reduction`. For folding exponents
`s i`, final degree bound `d`, and `l` queries, `Fri.Spec.soundnessError` is the sum of the
powers-MCA errors over all folds, plus `Real.toNNReal (1 - min θ δ) ^ l`. The tradeoff
parameter `θ` is independent of `δ`. Ordinary and round-by-round soundness use the original
closed-ball input relation. The stronger ordinary rejection theorem uses the strict proximity
language and applies even at distance exactly `δ`.

The total bound is parametric in the worst-case MCA error value; it does not assert that
this value is small for every parameter choice. Each value is finite because it is at most
one, so conversion to `NNReal` loses no mass. Useful numerical bounds require the explicit
field-size, distance, slack, and radius hypotheses in `Fri/ErrorBounds.lean`.

The algebraic consequences of Corollary 5.6 assume a safe trace, positive initial degree
bound `d`, positive query count `t`, `δ ≤ θ`, `δ ≤ 1 - d / 2^n`, and acceptance probability
at least `(1 - δ)^t`. These imply positive acceptance probability and hence a valid final
word. The accepting positions have density at least `1 - δ`; they determine a unique
codeword within relative distance `δ` of the input. Interpolation on any `d` accepting
positions recovers that codeword, and any query at a disagreement position is rejected.
The theorem permits real parameters outside the paper's unit intervals whenever its
hypotheses hold, and in particular covers the paper's full parameter range.

## Specification properties

- The non-final honest prover retains `i + 1` old words at round `i`, including the original
  input. `appendFoldOracle` and its projection lemmas specify old and new history entries.
- The final folding verifier checks the transmitted polynomial's degree before the query
  phase. The query verifier relies on this guard.
- Stage relations express proximity of the current word to its degree-bounded polynomial
  witness. Query verification checks the retained history, not only the final word.
- The final oracle is a polynomial sent in the clear; earlier words have point-query
  interfaces. The execution bridge preserves this distinction.
- A query challenge is a whole `Fin t` vector of initial-domain positions. Uniform sampling
  gives independent queries with replacement.
- A folding exponent `s i` denotes the folding factor `2 ^ (s i)`.

## Execution and security architecture

1. `Spec/Execution`, `QueryExecution`, `FoldExecution`, and `VerifierExecution` identify the
   actual verifier's acceptance event, including chronological challenges and oracle history.
2. `OracleReduction/Security/BadEvents` constructs a persistent state: the input is valid or
   a bad challenge has occurred. Prover messages preserve a false state because they cannot
   alter earlier challenge prefixes.
3. `Spec/RoundSoundness` and `BadEvents` bound each fresh bad event conditional on no earlier
   one. The query event includes the final degree guard. The worst-case-prefix interface
   supplies round-by-round soundness.
4. `OracleReduction/Security/Accumulation` sums conditional errors along `Prover.runToRound`,
   retaining private prover state and shared oracle state. Its terminal bound covers
   `Prover.run`, including the prover's output computation.
5. `OracleReduction/Security/Acceptance` turns that transcript bound into ordinary soundness
   when the verifier rejects outside the event. There is no oracle-state reset or assumed
   independence between prover commitments.

The proof uses ArkLib's Reed–Solomon codes, distances, folding, and consolidated MCA API.
`Fri/ErrorBounds.lean` retains the field-size, minimum-distance, slack, and radius hypotheses
of the powers-MCA bound. Probability statements use native `Pr{...}[...]` semantics, and
challenge-type transport uses the uniform-sampling equivalence. Pure agreement and verifier
execution lemmas do not require a field sampler.

## Certified extraction

`Fri.Spec.Extractor.extract` is a deterministic straightline extractor for the actual reduction.
It reconstructs only the retained prefix before query sampling, including every arbitrary
committed word and folding challenge. Query repetitions, output witnesses, and external logs do
not affect its result. It checks the final canonical polynomial's stored degree before reading
coefficients, domain points, challenges, or words. A failed guard returns `none`.

For a valid final degree, the program generates query points from at most two domain accesses
using explicit measured powers. It scans all `N = 2^n` positions in index order, applies the
actual local checks with short-circuiting between rounds, counts every accepting position, and
retains at most the first `D = 2^(Σ i, s i) * d` nodes and initial-word values. Fewer than `D`
acceptances yield `none`. Otherwise measured interpolation of these cached samples, followed by
a degree guard, produces the witness. No honest intermediate-word assumption is used.

The core deterministic recovery theorem assumes a safe history at `θ`, final degree below `d`,
accepting-set density at least `1 - θ`, and at least `D` accepting positions. It proves the exact
returned witness agrees at every accepting position. The density corollary replaces the latter
cardinality premise with `τ ≤ 1 - D/N` and density at least `1 - τ`, where `τ ≤ θ`.

The public knowledge theorem takes only the upper rate restriction
`min θ δ ≤ 1 - D/N`, including equality. It quantifies over every input statement and every
query count `l`, with the existing closed-ball input and output relations and unchanged
`soundnessError`. The informative dense-recovery regime is `0 ≤ min θ δ`. If `min θ δ < 0`,
the query term is at least one and the probability bound is vacuous. If `l = 0`, the query term
is one, also giving a vacuous bound. Neither case requires an extra public hypothesis.

The proof uses new extraction-failure bad events with the empty input language, unconditional
folding-error bounds, and a terminal query event combining actual acceptance with extraction
failure determined before query sampling. It does not apply the ordinary language-conditioned
soundness theorem to valid inputs. The generic bridge
`Verifier.knowledgeSoundnessWith_of_transcript_event` preserves prover and shared oracle state
and lifts the optional extraction result as a value, so `none` is counted as failure.

The public extractor is literally the result projection of its measured program. Primitive
responses carry erased equality certificates; their handlers perform the requested operation.
The profiles count repeated immutable word, domain, challenge, coefficient, and cache accesses,
field additions/subtractions/multiplications/equality tests, unit-cost inversions, and designated
metadata/control ticks. They exclude receipt or deserialization of retained functions, the cost
of evaluating those functions, allocation, machine index arithmetic, and field bit complexity.
In particular, metadata is an explicit source-instruction counter, not a count of all runtime
operations. The selected cache is bounded by `D`, but complete index enumeration exists and no
total `O(D)` workspace theorem is asserted.

For `r = k + 1` folds, write `N = 2^n`, `b_i = 2^(s_i)`, and `D = (∏ b_i) d`. Let
`I(m) = 100(m+1)^3`, `E(m) = (m+1)^2`, `Init = 1 + Σ_i (n-s_i)`, and

```text
G = 2(n+2) + Σ_i (4b_i+8)(n+1)
B = N [G + Σ_i (I(b_i) + E(b_i) + 1) + E(d)] + I(D) + Init.
```

The complete-program theorems require only the schedule bound `Σ_i s_i ≤ n`, not a safe
history, an honest word, a distance parameter, or the reduction's additional `D ≤ N` constraint.
They apply to early rejection as well as successful recovery, independently of the actual final
polynomial's coefficient count.

| Instruction count | Bound |
| --- | --- |
| Retained-word reads | `N (Σ_i b_i + k) + D` |
| Inversions | `1 + N Σ_i b_i(b_i-1) + D(D-1)` |
| Original-domain reads | `≤ 2` |
| Folding-challenge reads | `≤ r` |
| Final-polynomial retrievals | `= 1` |
| Each of combined additions/subtractions, multiplications, and field equality tests | `≤ B` |

`Fri.Spec.Extractor.profile_extractProgram_word_le`, the inversion and input-access theorems in
`Extraction/FullCost`, and the three field-operation theorems in `Extraction/ClosedCost` prove
these bounds for the same program whose result is the named extractor. Combined additions and
subtractions consume one `I` budget. The final polynomial consumes one `E(d)` per position,
only at the final round. `profile_extractProgram_apply_le` separately bounds every coefficient,
node-cache, value-cache, and metadata coordinate by the explicit `extractorProfileBound` vector.
Its transparent definition composes initialization, the complete scan, and final interpolation.

Under the reduction's `D ≤ N` constraint these envelopes are polynomial in `N`, rather than in
`log N`. They do not imply a cryptographic polynomial-time or bit-runtime bound. The compiled
fixtures include rejection of a canonical polynomial with 4097 coefficients before other input
accesses, and a total rejecting execution with `D > N`.

## Scope and trust boundary

The development establishes information-theoretic ordinary soundness, round-by-round soundness,
and straightline knowledge soundness for powers-of-two folding domains, together with
deterministic extraction correctness and instruction profiles for the same named program.
Fiat–Shamir and commitment security remain separate obligations. Numerical MCA estimates
retain their own hypotheses.

With zero query repetitions, the query-error term is one, so the total soundness bound is
vacuous. The earlier probability-to-binding and proximity consequences require a positive query
count; the new knowledge theorem covers zero queries explicitly.

`ArkLibTest/ProofSystem/Fri/Soundness.lean` and `Extraction.lean` contain guarded kernel-axiom
checks for the executable bridge and public security and extraction theorems.
`scripts/FriExtractorRuntime.lean` exercises small immutable histories and exact instruction
counts as compiled code. The proofs avoid the unfinished general round-by-round-to-ordinary
implication and the separate BCIKS20-based batched-FRI security claims.
