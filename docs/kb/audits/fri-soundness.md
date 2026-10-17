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
| End-to-end round-by-round soundness | `Fri.Spec.rbrSoundness` | Existing `OracleVerifier.rbrSoundness` and original input/output relations |

## Parameters and conclusions

The end-to-end theorems concern the computable `Fri.Spec.reduction`. For folding exponents
`s i`, final degree bound `d`, and `l` queries, `Fri.Spec.soundnessError` is the sum of the
powers-MCA errors over all folds, plus `Real.toNNReal (1 - min θ δ) ^ l`. The tradeoff
parameter `θ` is independent of `δ`. Ordinary soundness uses the original closed-ball input
relation. The stronger rejection theorem uses the strict proximity language and applies
even at distance exactly `δ`.

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

## Scope and trust boundary

The result establishes information-theoretic ordinary and round-by-round soundness for
powers-of-two folding domains. It does not assert Fiat–Shamir security, commitment security,
knowledge soundness, or an extraction runtime bound. Corollary 5.6's algebraic recovery is
formalized; its deterministic polynomial-time complexity claim is not. These consequences
are statements about safe traces, not end-to-end knowledge extraction.

Zero query repetitions give the vacuous soundness bound one. The probability-to-binding
and proximity consequences require a positive query count, as in the paper's proof.

`ArkLibTest/ProofSystem/Fri/Soundness.lean` contains guarded kernel-axiom checks for the
executable bridge, end-to-end soundness, numerical specialization, and algebraic consequences.
The proofs do not depend on the unfinished general round-by-round-to-ordinary implication
or the separate BCIKS20-based batched-FRI security claims.
