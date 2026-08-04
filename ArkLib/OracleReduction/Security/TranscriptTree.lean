/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.TranscriptTree.Basic
import ArkLib.OracleReduction.Security.TranscriptTree.Composition

/-!
  # Trees of transcripts

  Special soundness and its relatives extract a witness from a *bundle* of accepting transcripts:
  a knowledge extractor reruns the prover several times, replaying the same earlier messages but
  sending fresh verifier challenges, and recovers a witness from the transcripts it collects. These
  transcripts are not independent — they share everything that came before the challenge that was
  varied, and fan out only where the challenges differ. Grouped by their shared prefixes they form
  a *tree*. This module defines that tree once, generically, so every special-soundness-style notion
  can reuse it.

  ## The tree structure

  A `ChallengeTree` for a protocol `pSpec` branches **only at challenge rounds**:

  - a *message round* (prover → verifier) has a single child — the prover sends one message;
  - a *challenge round* (verifier → prover) has one child per branch, each labelled by the challenge
    the verifier sent on that branch.

  Reading the labels along a root-to-leaf path reconstructs one full protocol transcript, and any
  two paths automatically agree on everything before the round where their challenges first diverge.
  That shared prefix is exactly what rewinding the prover produces, which is why the tree is the
  natural object for the extractor to consume (`Extractor.TreeBased`) and for the rewinding
  reduction to produce.

  ## How special-soundness notions use it

  All tree-based soundness notions have the same shape: *given an accepting tree whose sibling
  challenges satisfy some combinatorial condition, a tree-based extractor outputs a valid witness.*
  They differ only in that condition:

  - plain `(k)`-special soundness (`Security.SpecialSoundness`) asks the `kᵢ` sibling challenges at
    each round to be pairwise distinct;
  - coordinate-wise special soundness (`Security.CoordinateWiseSpecialSoundness`) asks for a finer,
    coordinate-structured condition used by lattice-based arguments.

  Since only the sibling condition changes, the tree itself, the transcripts read off it, and how
  trees behave under composition are all shared. We therefore package "the condition" as a
  `ChallengeTreeShape` — a branching `arity` together with a `nodeOk` predicate on each round's
  siblings — and let `ChallengeTree.IsStructured` say that a tree meets it. A concrete notion is
  then just a choice of shape, which keeps its own definition and proofs short.

  ## Sequential composition

  The main payoff of separating the tree from its sibling condition is composition. Running two
  reductions in sequence appends their protocols (`pSpec₁ ++ₚ pSpec₂`); on trees this is
  `appendSplit`, which cuts a tree over the combined protocol into a first-stage tree over `pSpec₁`
  and, hanging below each of its leaves, a second-stage tree over `pSpec₂`. The generic theorems
  prove this split preserves structure (`appendSplit_fst_isStructured`,
  `appendSplit_sndAt_isStructured`) and recombines back to whole-protocol transcripts
  (`appendSplit_fullTranscripts_append_of_mem`). Because these hold for an *arbitrary* shape, each
  notion's "soundness is preserved under composition" theorem only has to check that its own shape
  composes the way the generic one does — a thin wrapper instead of a full re-proof.

  ## Folder layout

  - `TranscriptTree.Basic` — the core definitions: `ChallengeTree`, the shape abstraction
    (`ChallengeTreeShape`, `IsStructured`), root-to-leaf paths and the transcripts they read
    (`LeafPath`, `transcripts` / `fullTranscripts`), the accept condition (`IsAccepting`), and the
    shared `Extractor.TreeBased` extractor type.
  - `TranscriptTree.Composition` — the sequential-composition API (`appendArity`,
    `ChallengeTreeShape.append`, `appendSplit`) and the structure-preservation and recombination
    theorems above.

  ## Design notes and limitations

  - The branching arity is fixed by the round index, not by the path taken, so path-dependent
    branching is not supported.

-/
