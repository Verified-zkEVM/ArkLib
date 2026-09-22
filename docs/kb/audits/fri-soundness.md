# FRI soundness and specification audit

Source: [GMW25](../papers/GMW25.md), March 27, 2026 revision. The earlier
`zksecurity/simple-rbr-fri` development informs the proof strategy; its foundational
definitions are not duplicated in ArkLib.

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

## Scope

The result is information-theoretic ordinary and round-by-round soundness of the interactive
oracle reduction, for ArkLib's powers-of-two folding domains. It does not assert Fiat–Shamir
security, concrete commitment security, knowledge soundness, or efficient extraction. The
binding/interpolation consequences above are algebraic statements for a safe trace, not a
claim of end-to-end knowledge extraction. Zero query repetitions are permitted and give the
expected vacuous query bound one.

The older BCIKS20-based batched-FRI claims in `BatchedFri/Security.lean` remain separate
unfinished statements; the new theorems do not depend on them or certify batched FRI.

## Validation notes

- Direct kernel axiom inspection of `Fri.Spec.soundness`, `soundness_proximity`,
  `rbrSoundness`, and `reduction_run` reports exactly `propext`, `Classical.choice`, and
  `Quot.sound`: no `sorryAx` or nonstandard axioms. The same holds for the reusable
  adaptive accumulation and acceptance-to-soundness theorems. There are no `sorry`
  declarations under `ArkLib/ProofSystem/Fri/`.
- The full Lean build, compiled toy-problem runtime checks, and the `ArkLib/Data`
  non-`sorry` warning gate pass. The new proof
  modules and the reviewed FRI specification files compile without warnings.
  The standalone Python style linter passes the new proof modules and `RoundConsistency`;
  it still reports legacy layout issues in `Spec/SingleRound` and `Spec/General`.
- The axiom-sweep fixture matrix and `lake exe axiomsweep --check` pass.
  The refreshed baseline removes eight FRI
  declarations made axiom-clean by replacing the four placeholder relation definitions;
  it adds no debt. The sweep covers 10,714 declarations across 422 modules and reports
  288 existing `sorryAx`-tainted declarations and no nonstandard-axiom dependencies.
- The import check and knowledge-base lint pass. Full `validate.sh --axioms --site` stops earlier
  at the pre-existing broken link in `docs/kb/ABF26_POLISH_PLAN.md` to
  `../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean`; the axiom checks are therefore
  also run separately. The unrelated document is left unchanged.
- The 63-page blueprint PDF and bibliography compile with XeLaTeX and BibTeX, and
  `checkdecls` validates every theorem reference in the FRI section. The full API-docs
  build was attempted but stopped during dependency-documentation generation; a full
  website build is not certified here.
- The user's unrelated, untracked `ArkLib/Data/CodingTheory/ProximityGenerator/` work is
  not imported or staged. Import validation uses a temporary, command-local Git exclusion
  for that directory, without changing repository ignore rules.
