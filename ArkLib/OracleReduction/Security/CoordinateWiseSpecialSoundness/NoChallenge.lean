/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic

/-!
  # (Coordinate-wise) special soundness for protocols with no challenge rounds

  When a protocol has no challenge rounds (`IsEmpty pSpec.ChallengeIdx`) its challenge tree cannot
  contain a `chalNode`, so a tree rooted at round `0` is a single chain of message nodes with a
  unique full transcript, and `IsStructured S` holds vacuously. Hence tree special soundness
  collapses to a *transcript-level* extraction obligation: provide a function `e` from the input
  statement and the (unique) transcript to a witness, and show that whenever the verifier accepts
  the transcript into `relOut.language` the extracted witness lies in `relIn`.

  The bridges select that transcript through `ProtocolSpec.ChallengeTree.onlyPath`, the tree's
  unique root-to-leaf *path*, which is read off the tree by structural recursion. So the extractors
  they produce are computable, and they are stated at the path rather than at the transcript, which
  is the granularity a leaf-indexed extraction premise needs.

  This is the reusable bridge that makes the coordinate-wise special soundness of the zero-round /
  send / check components (`SendClaim`, `SendWitness`, `CheckClaim`, `ReduceClaim`) cheap: each is
  proved by supplying `e` and discharging the (degenerate, probability-free in the pure-verifier
  case) acceptance obligation.

  ## Main results

  * `ProtocolSpec.ChallengeTree.transcripts_eq_singleton` / `fullTranscripts_eq_singleton` —
    a no-challenge tree lists exactly one transcript.
  * `Verifier.treeSpecialSoundWith_of_isEmpty_challengeIdx` — the bridge.
  * `Verifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx` and its `OracleVerifier`
    analogue.

  The extractors these bridges produce **ignore their leaf witnessing** — they read the unique
  transcript instead — so the bridges carry no purity hypothesis and the notion's validity premise
  is unused. This is the *closing* shape: such a factor placed on the right of a chain is what lets
  the whole composed extractor run as a function of `(stmtIn, tree)` alone.

  **Which chains this actually closes.** A closing factor has to be *final*, and being zero-round is
  not the same as being final. Hachi's `iteration` ends in a witness-carrying evaluation claim
  (`relWEvalClaim`): one iteration is a *reduction*, so its composed extractor legitimately
  consumes a leaf witnessing and this bridge does not close it.
  Closure
  arrives only when the chain is capped by a factor whose output relation needs no witness — the
  final-evaluation piece appended after the iteration. So read the paragraph above as a statement
  about the *shape* a closing factor must have, not as a claim that every chain built from these
  components is already closed; a chain whose last link is a reduction is correctly left in the
  `∀ o valid` form.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace CWSSStructure

/-- The canonical coordinate-wise structure on a **challenge-free** protocol
  (`IsEmpty pSpec.ChallengeIdx`): every field is the empty eliminator, since there are no challenge
  rounds to describe. `coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx` proves CWSS for
  *any* `D` on such a protocol, but the binary-append composition theorem
  (`Verifier.append_coordinateWiseSpecialSoundWith`) needs a *concrete* structure for the zero-round
  left factor (a `ReduceClaim`/`CheckClaim` head); this is that structure. -/
def ofIsEmpty {n : ℕ} {pSpec : ProtocolSpec n} [IsEmpty pSpec.ChallengeIdx] :
    CWSSStructure pSpec where
  coordIndex := fun i => isEmptyElim i
  alphabet := fun i => isEmptyElim i
  decompose := fun i => isEmptyElim i
  soundnessParam := fun i => isEmptyElim i
  arity := fun i => isEmptyElim i
  arity_eq := funext fun i => isEmptyElim i

end CWSSStructure

namespace ProtocolSpec.ChallengeTree

variable {n : ℕ} {pSpec : ProtocolSpec n} {arity : pSpec.ChallengeIdx → ℕ}

/-- With no challenge rounds, every challenge (sub)tree lists exactly one transcript: there are no
  branch points, only a chain of message nodes ending in a leaf. -/
theorem transcripts_eq_singleton [IsEmpty pSpec.ChallengeIdx] :
    {m : Fin (n + 1)} → (tree : ChallengeTree pSpec arity m) → (pre : Transcript m pSpec) →
      ∃ tr, tree.transcripts pre = [tr]
  | _, .leaf, pre => ⟨pre, rfl⟩
  | _, .msgNode _ _ msg child, pre =>
      show ∃ tr, child.transcripts (pre.concat msg) = [tr] from
        transcripts_eq_singleton child (pre.concat msg)
  | _, .chalNode m h _ _, _ => isEmptyElim (⟨m, h⟩ : pSpec.ChallengeIdx)

/-- With no challenge rounds, a full tree (rooted at round `0`) has exactly one transcript. -/
theorem fullTranscripts_eq_singleton [IsEmpty pSpec.ChallengeIdx]
    (tree : ChallengeTree pSpec arity 0) : ∃ tr, tree.fullTranscripts = [tr] :=
  show ∃ tr, tree.transcripts default = [tr] from transcripts_eq_singleton tree default

end ProtocolSpec.ChallengeTree

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **Degenerate tree special soundness, named form.** For a protocol with no challenge rounds,
  the tree is a single message-chain, so tree special soundness reduces to a transcript-level
  extractor: any `e` such that "the verifier accepts the (unique) transcript into
  `relOut.language`" implies the extracted witness lies in `relIn`, witnesses tree special
  soundness at the tree extractor
  `fun stmtIn tree _ => some (e stmtIn tree.onlyPath.fullTranscript)`. The shape `S` is irrelevant
  (`IsStructured` is vacuous), and the extractor is computable, since `onlyPath` reads the path off
  the tree structurally.

  The extractor is **witnessing-agnostic**: it reads the transcript and never consults its leaf
  witnessing, so the notion's validity premise is simply unused and no purity hypothesis is needed.
  That is exactly the shape of a *closing* factor — the terminal link of a chain, whose witness the
  tree itself contains, and which therefore lets an otherwise open composed extractor run on
  `(stmtIn, tree)` alone. -/
theorem treeSpecialSoundWith_of_isEmpty_challengeIdx [IsEmpty pSpec.ChallengeIdx]
    (S : ChallengeTreeShape pSpec) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (e : StmtIn → FullTranscript pSpec → WitIn)
    (h : ∀ stmtIn tr,
      Pr[ (· ∈ relOut.language) |
        OptionT.mk do (simulateQ impl (V.run stmtIn tr)).run' (← init)] = 1 →
      (stmtIn, e stmtIn tr) ∈ relIn) :
    treeSpecialSoundWith init impl S relIn relOut V
      (fun stmtIn tree _ => some (e stmtIn tree.onlyPath.fullTranscript)) :=
  fun stmtIn tree _ hAcc _ _ =>
    ⟨_, rfl, h stmtIn _ (hAcc _ tree.onlyPath.mem_fullTranscripts)⟩

/-- CWSS of a challenge-free protocol, **named form**: the transcript-level extractor `e` on the
  tree's unique transcript witnesses CWSS. Any coordinate-wise structure `D` works, since
  `IsStructured` is vacuous with no challenge rounds. -/
theorem coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx [IsEmpty pSpec.ChallengeIdx]
    (D : CWSSStructure pSpec) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (e : StmtIn → FullTranscript pSpec → WitIn)
    (h : ∀ stmtIn tr,
      Pr[ (· ∈ relOut.language) |
        OptionT.mk do (simulateQ impl (V.run stmtIn tr)).run' (← init)] = 1 →
      (stmtIn, e stmtIn tr) ∈ relIn) :
    coordinateWiseSpecialSoundWith init impl D relIn relOut V
      (fun stmtIn tree _ => some (e stmtIn tree.onlyPath.fullTranscript)) :=
  treeSpecialSoundWith_of_isEmpty_challengeIdx init impl D.toShape V relIn relOut e h

end Verifier

namespace OracleVerifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Oracle-reduction analogue of `Verifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx`,
  on the combined `(StmtIn × ∀ i, OStmtIn i)` statement: the transcript-level extractor `e` on the
  tree's unique transcript witnesses CWSS, witnessing-agnostically. -/
theorem coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx [IsEmpty pSpec.ChallengeIdx]
    (D : CWSSStructure pSpec)
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (e : (StmtIn × ∀ i, OStmtIn i) → FullTranscript pSpec → WitIn)
    (h : ∀ stmtIn tr,
      Pr[ (· ∈ relOut.language) |
        OptionT.mk do (simulateQ impl (V.toVerifier.run stmtIn tr)).run' (← init)] = 1 →
      (stmtIn, e stmtIn tr) ∈ relIn) :
    V.coordinateWiseSpecialSoundWith init impl D relIn relOut
      (fun stmtIn tree _ => some (e stmtIn tree.onlyPath.fullTranscript)) :=
  Verifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx init impl D V.toVerifier
    relIn relOut e h

end OracleVerifier
