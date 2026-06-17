/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.TranscriptTree

/-!
  # (Plain) Special Soundness

  This file defines the classic notion of `(k₁, …, k_μ)`-**special soundness** for multi-round
  public-coin (oracle) reductions, standalone (independent of the coordinate-wise generalization in
  `Security.CoordinateWiseSpecialSoundness`).

  A `(2μ+1)`-round protocol is `k`-special sound for a relation if there is a deterministic
  tree-based extractor that turns any *accepting* tree of transcripts in which, at each challenge
  round `i`, the `kᵢ` sibling challenges are **pairwise distinct**, into a valid input witness.

  The coordinate-wise generalization recovers this as the `ℓᵢ = 1` case; the bridge lemma
  `coordinateWiseSpecialSound (ofSpecialSound k) ↔ specialSound k` (the only place the two notions
  meet) is in the CWSS folder.

  Both notions share `ProtocolSpec.ChallengeTree` / `ChallengeTree.IsAccepting` and the
  `Extractor.TreeBased` extractor type from `Security.TranscriptTree`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace ProtocolSpec.ChallengeTree

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- A tree of transcripts with arity `k` is **`k`-distinct** if at every challenge round the `kᵢ`
  sibling challenges are pairwise distinct (`Function.Injective`). This is the structural condition
  a plain `k`-special-soundness extractor consumes — the `ℓ = 1` specialization of
  `ChallengeTree.IsStructured`. -/
def IsDistinct (k : pSpec.ChallengeIdx → ℕ) :
    {m : Fin (n + 1)} → ChallengeTree pSpec k m → Prop
  | _, .leaf => True
  | _, .msgNode _ _ _ child => child.IsDistinct k
  | _, .chalNode _ _ challenges children =>
      Function.Injective challenges ∧ ∀ j, (children j).IsDistinct k

end ProtocolSpec.ChallengeTree

/-! ## The special-soundness predicate -/

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A verifier is `(k₁, …, k_μ)`-**special sound** for an input relation `relIn` and output language
  `langOut` if there is a tree-based extractor `E` such that, for every input statement `stmtIn` and
  every tree of transcripts that is

  - `k`-distinct (the `kᵢ` sibling challenges at each round are pairwise distinct), and
  - accepting (the verifier accepts every root-to-leaf transcript, landing in `langOut`),

  the extracted witness `E stmtIn tree` satisfies `(stmtIn, E stmtIn tree) ∈ relIn`. -/
def specialSound (k : pSpec.ChallengeIdx → ℕ)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  ∃ E : Extractor.TreeBased StmtIn WitIn pSpec k,
  ∀ stmtIn : StmtIn,
  ∀ tree : ChallengeTree pSpec k 0,
    tree.IsDistinct k →
    tree.IsAccepting init impl verifier stmtIn langOut →
      (stmtIn, E stmtIn tree) ∈ relIn

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Special soundness of an oracle reduction, via its underlying non-oracle verifier on the combined
  (oracle + non-oracle) statements. -/
def specialSound (k : pSpec.ChallengeIdx → ℕ)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) : Prop :=
  verifier.toVerifier.specialSound init impl k relIn langOut

end OracleVerifier
