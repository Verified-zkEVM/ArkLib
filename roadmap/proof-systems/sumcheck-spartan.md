# Sum-check and Spartan

**Page status:** active.
**Last checked:** 2026-10-04, against `main` at `ace55c3e29da1fc55a321378ada55ea4f7ed8790`.
**Contact:** [@quangvdao](https://github.com/quangvdao).
**Blueprint:** [sum-check](../../blueprint/src/proof_systems/sumcheck.tex) and
[Spartan](../../blueprint/src/proof_systems/spartan.tex).

The [folder README](../README.md) defines the terms used on this page.

## Where things stand

**Sum-check.** The version in the Interaction framework is in
[`ArkLib/ProofSystem/Sumcheck/Interaction`](../../ArkLib/ProofSystem/Sumcheck/Interaction), with
no `sorry`. For a polynomial in $$k$$ variables of individual degree at most $$d$$ over a field
$$F$$, the following are merged:

- Completeness: the honest prover always convinces the verifier of a true claim.
- Soundness: no prover convinces the verifier of a false claim with probability more than
  $$k \cdot d / \lvert F \rvert$$.
- A verifier and an honest prover that can be executed
  ([#1242](https://github.com/Verified-zkEVM/ArkLib/pull/1242),
  [#1243](https://github.com/Verified-zkEVM/ArkLib/pull/1243)). The prover computes each round
  message by summing over all remaining points. It is correct but not efficient.

The older version in
[`ArkLib/ProofSystem/Sumcheck/Spec`](../../ArkLib/ProofSystem/Sumcheck/Spec) uses the legacy
framework and has incomplete proofs.

**Spartan.** [`ArkLib/ProofSystem/Spartan`](../../ArkLib/ProofSystem/Spartan) defines the
protocol in the legacy framework. Its proofs are incomplete, and it has not been ported.

## Open PRs

Both are by [@quangvdao](https://github.com/quangvdao).

- [#1261](https://github.com/Verified-zkEVM/ArkLib/pull/1261) proves that round-by-round
  soundness implies soundness, and derives the $$k \cdot d / \lvert F \rvert$$ bound for
  sum-check from a per-round error of $$d / \lvert F \rvert$$.
- [#1269](https://github.com/Verified-zkEVM/ArkLib/pull/1269) proves that sum-check has
  state-restoration soundness error at most $$(Q + k) \cdot d / \lvert F \rvert$$ against a
  prover with query budget $$Q$$. It depends on the chain of PRs ending in
  [#1268](https://github.com/Verified-zkEVM/ArkLib/pull/1268), listed on the
  [Interaction framework page](../interaction-migration.md#open-prs).

## Open gaps

- **No witness is extracted.** The polynomial is an input oracle that the verifier queries, so
  the sum-check relation has a trivial witness, and the results above are soundness results. A
  protocol in which the polynomial is hidden or committed needs a knowledge soundness proof.
- **No efficient prover.** The standard linear-time prover for multilinear polynomials is not
  yet proved to produce the same messages as the merged prover.
- **Spartan is not ported.**
- **Legacy sum-check.** The incomplete proofs in `Sumcheck/Spec` remain until its users move to
  the Interaction version.

## Next step

Merge the open PRs. Then choose the next protocol to port, either Spartan or a protocol that
uses sum-check as a step, and write down its statement, witness, oracle interface, and target
security bound before porting it. [What a port must show](../interaction-migration.md#what-a-port-must-show)
lists the requirements.
