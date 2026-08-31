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

  The extractor takes the tree together with a **leaf witnessing**, and may decline; the
  unconditioned textbook statement — a total extractor of `(stmtIn, tree)` correct on every
  structured accepting tree — follows as a theorem, `Verifier.specialSound.exists_total_extractor`.

  This is standalone — independent of the coordinate-wise generalization in
  `Security.CoordinateWiseSpecialSoundness`. Both notions are *sibling* instances of
  `Verifier.treeSpecialSound` over the shared `Security.TranscriptTree` machinery; neither file
  imports the other. The bridge `coordinateWiseSpecialSound (ofSpecialSound k) ↔ specialSound k`
  (the `ℓᵢ = 1` case) is `Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff` in
  `Security.Implications`.
-/

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
  tree-based extractor `E` such that, for every input statement `stmtIn`, every tree of transcripts
  that is

  - structured by `distinctShape k` (the `kᵢ` sibling challenges at each round are pairwise
    distinct), and
  - accepting (the verifier accepts every root-to-leaf transcript, landing in `relOut.language`),

  and every **valid leaf witnessing** of that tree, `E` succeeds with a `relIn`-witness.

  The leaf witnessing is the "output witnesses" input of a reduction-of-knowledge extractor
  (`Extractor.TreeBased`); the premise is never an obstruction, since acceptance alone supplies one
  (`ChallengeTree.canonWitnesses`), which is what makes the unconditioned textbook reading
  available — `Verifier.specialSound.exists_total_extractor` below. -/
def specialSound (k : pSpec.ChallengeIdx → ℕ)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  verifier.treeSpecialSound init impl (distinctShape k) relIn relOut

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **The textbook reading of `(k)`-special soundness.** A special-sound verifier admits a total
  extractor of `(stmtIn, tree)` alone that is correct on *every* structured accepting tree — no
  witnessing premise anywhere in the statement.

  The extractor is the notion's own, closed at the canonical witnessing acceptance already provides
  (`ChallengeTree.canonWitnesses`), and this costs only `[Inhabited WitIn]` — no purity, no
  finiteness. So the leaf-witnessing input costs nothing that was previously there.

  Be precise about what is recovered, though. `ChallengeTree.canonWitnesses` is
  `if h : ∃ w, … then some h.choose else none`, so closing at it plugs the choice function back in:
  what this theorem hands back is the *non-algorithmic* reading — the pre-witnessing statement,
  derived. That makes it the right migration receipt, not the preferred statement. For a reduction
  the `∀ o valid` form of `Verifier.specialSound` is strictly the better one: the output witnesses
  are a genuine input to a reduction-of-knowledge extractor, and carrying them is what lets a chain
  of certificates compose into a runnable end-to-end extractor. The premise is an argument for the
  interface, not an apology for it. -/
theorem specialSound.exists_total_extractor [Inhabited WitIn] (k : pSpec.ChallengeIdx → ℕ)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (h : verifier.specialSound (WitOut := WitOut) init impl k relIn relOut) :
    ∃ E : StmtIn → ProtocolSpec.ChallengeTree pSpec (distinctShape k).arity 0 → WitIn,
      ∀ stmtIn tree, ProtocolSpec.ChallengeTree.IsStructured (distinctShape k) tree →
        tree.IsAccepting init impl verifier stmtIn relOut.language →
          (stmtIn, E stmtIn tree) ∈ relIn := by
  obtain ⟨Ext, hExt⟩ := h
  refine ⟨fun stmtIn tree =>
    (Ext stmtIn tree
      (ProtocolSpec.ChallengeTree.canonWitnesses init impl verifier relOut stmtIn)).getD default,
    fun stmtIn tree hstr hacc => ?_⟩
  exact Verifier.treeSpecialSoundWith.mem_relIn_of_isAccepting init impl hExt stmtIn tree hstr hacc

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
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
