/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.Rewinding.Basic
import ArkLib.OracleReduction.Security.Rewinding.Coupling
import ArkLib.OracleReduction.Security.Rewinding.ReplayFork
import ArkLib.OracleReduction.Security.Rewinding.SeededReplay

/-!
  # Rewinding knowledge soundness (umbrella)

  Aggregates the rewinding-extraction infrastructure:

  * `Rewinding.Basic` — the abstract rewinding KS notions (`Extractor.Rewinding`,
    `QueryImpl.ReplayConsistent`, `Verifier.DeterminateAcceptance`,
    `knowledgeSoundnessRewinding(WithError)`).
  * `Rewinding.Coupling` — execution-semantics / run-coupling lemmas shared by every fork
    (`Prover.Realizes`, `runToRound_couple`, `oracleComp_replay`, `run_pin`, …) and the
    `QueryImpl.IsDeterministic` predicate.
  * `Rewinding.ReplayFork` — the protocol-generic round-indexed replay fork (`replayChallenge`,
    `replayForkImpl`, the structural guarantees, and `.replay` determinism).
  * `Rewinding.SeededReplay` — the `oSpec`-randomness-as-tape abstraction (`SeededReplay` /
    `LawfulSeededReplay`).

  See `docs/general-replay-fork-design.md`.
-/
