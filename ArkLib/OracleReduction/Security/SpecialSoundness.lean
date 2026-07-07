/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.TranscriptTree

/-!
  # (Plain) Special Soundness

  This file defines the classic notion of `(k₁, …, k_μ)`-**special soundness** for multi-round
  public-coin (oracle) reductions.

  A `(2μ+1)`-round protocol is `k`-special sound for a relation if there is a deterministic
  tree-based extractor that turns any *accepting* tree of transcripts in which, at each challenge
  round `i`, the `kᵢ` sibling challenges are **pairwise distinct**, into a valid input witness.

  Rather than re-deriving the tree machinery, special soundness is defined as the instance of the
  shape-generic `Verifier.treeSpecialSound` (`Security.TranscriptTree`) for the **distinct shape**
  `distinctShape k`: the `ChallengeTreeShape` with branching arity `kᵢ` whose node predicate
  requires the `kᵢ` sibling challenges at each round to be pairwise distinct (`Function.Injective`).

  This is standalone — independent of the coordinate-wise generalization in
  `Security.CoordinateWiseSpecialSoundness`. Both notions are *sibling* instances of
  `Verifier.treeSpecialSound` over the shared `Security.TranscriptTree` machinery; neither file
  imports the other. The bridge `coordinateWiseSpecialSound (ofSpecialSound k) ↔ specialSound k`
  (the `ℓᵢ = 1` case) is `Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff` in
  `Security.Implications`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- The **distinct shape** of plain `(k)`-special soundness: the `ChallengeTreeShape` with branching
  arity `kᵢ` whose node predicate requires the `kᵢ` sibling challenges at each challenge round to be
  pairwise distinct (`Function.Injective`). It is the `ℓ = 1` special case of
  `CWSSStructure.toShape` (`Security.CoordinateWiseSpecialSoundness`), and supplying it to
  `Verifier.treeSpecialSound` yields plain special soundness (`Verifier.specialSound`). -/
def distinctShape (k : pSpec.ChallengeIdx → ℕ) : ChallengeTreeShape pSpec where
  arity := k
  nodeOk := fun _ challenges => Function.Injective challenges

/-! ## The special-soundness predicate -/

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A verifier is `(k₁, …, k_μ)`-**special sound** for an input relation `relIn` and output relation
  `relOut` if it is `Verifier.treeSpecialSound` for the distinct shape `distinctShape k`: there is a
  tree-based extractor `E` such that, for every input statement `stmtIn` and every tree of
  transcripts that is

  - structured by `distinctShape k` (the `kᵢ` sibling challenges at each round are pairwise
    distinct), and
  - accepting (the verifier accepts every root-to-leaf transcript, landing in `relOut.language`),

  the extracted witness `E stmtIn tree` satisfies `(stmtIn, E stmtIn tree) ∈ relIn`. -/
def specialSound (k : pSpec.ChallengeIdx → ℕ)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  verifier.treeSpecialSound init impl (distinctShape k) relIn relOut

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Special soundness of an oracle reduction, via its underlying non-oracle verifier on the combined
  (oracle + non-oracle) statements. -/
def specialSound (k : pSpec.ChallengeIdx → ℕ)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) : Prop :=
  verifier.toVerifier.specialSound init impl k relIn relOut

end OracleVerifier
