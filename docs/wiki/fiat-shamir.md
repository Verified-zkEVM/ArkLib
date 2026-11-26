# Fiat–Shamir interfaces

`ArkLib/InteractiveProof/IP.lean` defines `InteractiveProver`, `InteractiveVerifier`, and
`InteractiveProtocol` for honest execution. `InteractiveProtocol.completeness` bounds the
acceptance probability for valid inputs from below. `InteractiveProtocol.toReduction_completeness_iff`
identifies that predicate with completeness of the legacy reduction.

`ArkLib/NonInteractiveArgument/NARG.lean` defines `NonInteractiveArgument`, its shared-oracle
execution and completeness, and the adaptive soundness and knowledge-soundness games and
statement-size restrictions. `Legacy.lean` connects these interfaces to legacy non-interactive
reductions. `ZeroKnowledge.lean` owns the adaptive simulation games.

The ordinary public-coin `IP` games and adapters live in
`InteractiveProof/StateRestorationSoundness.lean`, alongside the general state-restoration games.

## Canonical Fiat–Shamir

`ArkLib/NonInteractiveArgument/FiatShamir/Canonical.lean` exports the statement-keyed transform
and its completeness results. `Canonical/Construction.lean` replaces each verifier message with
a query keyed by the round, input statement, and preceding prover messages.

`Canonical/Completeness.lean` proves perfect completeness for a fixed verifier-message table and
preserves the completeness error bound under a shared lazy random oracle. The execution and
random-oracle lemmas used in these proofs live in `Canonical/Completeness/Shared.lean`.
