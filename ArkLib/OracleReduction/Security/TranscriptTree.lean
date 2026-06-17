/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Trees of transcripts

  This file defines the *tree of transcripts* abstraction that underlies tree-based knowledge
  extraction notions such as (coordinate-wise) special soundness.

  A tree of transcripts for a `pSpec : ProtocolSpec n` is a tree that branches **only at challenge
  rounds**. Concretely:

  - at a *message round* the prover sends a single message, so the corresponding node has exactly
    one child;
  - at a *challenge round* the node has `arity i` children, each labelled by the challenge value
    that the verifier sent on that branch.

  Reading the labels along any root-to-leaf path yields a `FullTranscript pSpec`. Two paths that
  agree on all challenges up to some round automatically share the same prover messages up to that
  round — this is exactly the "common prefix" guarantee that rewinding (forking) the prover
  provides, and the reason the tree shape is the natural object produced by a forking extractor.

  This abstraction is deliberately agnostic to *what* combinatorial relation the sibling challenges
  satisfy. Plain `k`-special soundness requires the siblings to be pairwise distinct;
  coordinate-wise special soundness requires them to form a coordinate-wise structured set. Both
  notions therefore reuse the `ChallengeTree` defined here, instantiating only the branching arity
  and the predicate on sibling challenges (see `CoordinateWiseSpecialSoundness.lean`).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec

variable {n : ℕ}

/-- A **tree of transcripts** for a protocol `pSpec`, branching only at challenge rounds.

The tree is indexed by the current round `m : Fin (n + 1)` (the rounds `m, m+1, …, n-1` are still to
come). Each challenge round `i` branches into `arity i` children. A `ChallengeTree pSpec arity 0`
(rooted at round `0`) describes a full tree of transcripts; reading the messages and challenges
along each root-to-leaf path recovers the corresponding `FullTranscript pSpec` (see
`ChallengeTree.transcripts`).

The challenge labels and subtrees of a challenge node are kept as two separate functions (rather
than a single function into a product) so that the recursive occurrence is not nested under `Prod`,
which the kernel forbids.

Note: The challenge arity is determined by the round index, not the path. So path-dependent
branching (e.g. "branch into 2 if the first challenge is `0`, branch into 3 if it's `1`") is not
currently supported. This may be generalized in the future, but keeps the current design simple
enough to follow the CWSS paper proofs.
-/
inductive ChallengeTree (pSpec : ProtocolSpec n) (arity : pSpec.ChallengeIdx → ℕ) :
    Fin (n + 1) → Type where
  /-- A leaf, reached once all `n` rounds have been processed. -/
  | leaf : ChallengeTree pSpec arity (Fin.last n)
  /-- A message round: the prover sends a single message `msg`, and the tree continues with a
    single child. -/
  | msgNode (m : Fin n) (h : pSpec.dir m = .P_to_V) (msg : pSpec.Message ⟨m, h⟩)
      (child : ChallengeTree pSpec arity m.succ) :
      ChallengeTree pSpec arity m.castSucc
  /-- A challenge round: the verifier branches into `arity ⟨m, h⟩` children, with `challenges j` the
    challenge value sent on branch `j` and `children j` the corresponding subtree. -/
  | chalNode (m : Fin n) (h : pSpec.dir m = .V_to_P)
      (challenges : Fin (arity ⟨m, h⟩) → pSpec.Challenge ⟨m, h⟩)
      (children : Fin (arity ⟨m, h⟩) → ChallengeTree pSpec arity m.succ) :
      ChallengeTree pSpec arity m.castSucc

namespace ChallengeTree

variable {pSpec : ProtocolSpec n} {arity : pSpec.ChallengeIdx → ℕ}

/-- Collect all root-to-leaf transcripts of a tree, given the partial transcript `pre` accumulated
  on the path from the root to the current node.

  At a message (resp. challenge) node we extend the prefix by the stored message (resp. by each
  child's challenge label) and recurse. At a leaf the accumulated prefix is a `FullTranscript`. -/
def transcripts :
    {m : Fin (n + 1)} → ChallengeTree pSpec arity m → Transcript m pSpec →
      List (FullTranscript pSpec)
  | _, .leaf, pre => [pre]
  | _, .msgNode _ _ msg child, pre => child.transcripts (pre.concat msg)
  | _, .chalNode m h challenges children, pre =>
      (List.finRange (arity ⟨m, h⟩)).flatMap fun j =>
        (children j).transcripts (pre.concat (challenges j))

/-- The transcripts of a full tree (rooted at round `0`), starting from the empty prefix. -/
def fullTranscripts (tree : ChallengeTree pSpec arity 0) : List (FullTranscript pSpec) :=
  tree.transcripts default

section IsAccepting

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {arity : pSpec.ChallengeIdx → ℕ}

/-- A tree of transcripts is **accepting** with respect to an input statement `stmtIn` and an output
  language `langOut` if the verifier accepts every root-to-leaf transcript, i.e. for each such
  transcript the verifier outputs a statement in `langOut` with probability `1`.

  This is the tree-level analogue of the verifier's "accept" condition, phrased exactly as in the
  round-by-round state-function machinery (cf. `Verifier.StateFunction.toFun_full`). -/
def IsAccepting (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (langOut : Set StmtOut)
    (tree : ChallengeTree pSpec arity 0) : Prop :=
  ∀ tr ∈ tree.fullTranscripts,
    Pr[(· ∈ langOut) |
      OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] = 1

end IsAccepting

end ChallengeTree

end ProtocolSpec

namespace Extractor

open ProtocolSpec

/-- A **tree-based extractor**: a deterministic algorithm that, given the input statement and a tree
  of transcripts (rooted at round `0`), outputs an input witness.

  This is the type of extractor used by tree-based knowledge-extraction notions — plain `k`-special
  soundness and coordinate-wise special soundness alike. The tree already contains all transcripts,
  so the extractor is a plain function; it is the rewinding/forking extractor of the
  knowledge-soundness reduction that actually *produces* the tree. Both notions share it, so it
  lives here on the shared `ChallengeTree` rather than in either notion's file. -/
def TreeBased (StmtIn WitIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  StmtIn → ProtocolSpec.ChallengeTree pSpec arity 0 → WitIn

end Extractor
