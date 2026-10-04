# Area roadmaps

This folder tracks ArkLib's development one area at a time, as proposed in
[issue #608](https://github.com/Verified-zkEVM/ArkLib/issues/608). The
[root roadmap](../ROADMAP.md) is the project-wide index. Each page here says what exists in the
source, which pull requests are open, what is missing, and what to do next.

## Current pages

| Area | Page |
|---|---|
| Interaction framework and porting protocols to it | [Moving protocols to the Interaction framework](interaction-migration.md) |
| Sum-check and Spartan | [Sum-check and Spartan](proof-systems/sumcheck-spartan.md) |
| Merkle commitments | [Merkle commitments](commitments/merkle-trees.md) |

These three pages are a start. They do not cover all of ArkLib. Other areas stay in the root
roadmap until a contributor writes their page.

## Status of a result

Every page uses the same three words for a result:

- **Merged:** on `main`.
- **Open PR:** proved on a branch whose pull request is not yet merged. The statement can still
  change in review.
- **Planned:** not yet proved.

## Terms

- **Interaction framework.** The current general theory of interactive protocols, in
  `ArkLib/Interaction/`.
- **Legacy framework.** The older theory in `ArkLib/OracleReduction/`. Most protocols still use
  it. Some of its general theorems have incomplete proofs.
- **Port.** To restate a protocol in the Interaction framework and prove that the new version
  matches the legacy one.
- **Soundness.** No prover makes the verifier accept a false claim, except with a stated small
  probability, called the soundness error.
- **Knowledge soundness.** Whenever a prover makes the verifier accept, an algorithm called the
  extractor recovers a valid witness, except with a stated small probability.
- **Round-by-round soundness.** A bound for each verifier challenge separately: if the claim is
  false before the challenge, it is still false after it, except with that round's error. The
  knowledge version bounds, for each challenge, the probability that extraction fails there.
- **Random oracle.** An idealized hash function: a uniformly random function that all parties
  can only query.
- **State-restoration soundness.** Soundness against a prover that may return the verifier to
  any earlier point of the protocol and try a different message, each time receiving a fresh
  challenge. The prover has a budget of $$Q$$ such attempts. This is the notion of security for
  an interactive protocol that carries over to its Fiat–Shamir transform in the random oracle
  model.
- **Real-to-ideal transfer.** A bound of the form
  Pr[the real verifier accepts] ≤ Pr[an ideal verifier accepts] + error. The real verifier
  checks opening proofs against a commitment. The ideal verifier reads the committed values
  directly.

## Adding a page

Add a page when you can check an area's status and next step against the source. Copy
[the template](TEMPLATE.md). Do not create empty pages for work that has not started.

## Keeping pages current

- When a PR changes what an area provides, update that area's page in the same PR. The author
  proposes the update, and reviewers check it with the code.
- Record the date and the commit you checked against. Link each open PR and name its author.
- Keep one plan per area. If a detailed plan already exists elsewhere, link it. The Interaction
  framework's plan is the [design roadmap](../docs/design/05-roadmap.md).
- Keep mathematical exposition in the blueprint and architecture in the
  [design documents](../docs/design/README.md). Link to them from here.
- When a PR is closed without merging, remove it from the page's list of open PRs.
- When everything a page tracks is merged, move the page to `roadmap/done/`, record the final
  commit, note what was left out of scope, and fix the links that pointed to it. Create `done/`
  when the first page moves there.
