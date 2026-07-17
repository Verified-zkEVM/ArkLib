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

  This is the reusable bridge that makes the coordinate-wise special soundness of the zero-round /
  send / check components (`SendClaim`, `SendWitness`, `CheckClaim`, `ReduceClaim`) cheap: each is
  proved by supplying `e` and discharging the (degenerate, probability-free in the pure-verifier
  case) acceptance obligation.

  ## Main results

  * `ProtocolSpec.ChallengeTree.transcripts_eq_singleton` / `fullTranscripts_eq_singleton` —
    a no-challenge tree lists exactly one transcript.
  * `ProtocolSpec.ChallengeTree.onlyTranscript` (+ `onlyTranscript_mem`) — that unique transcript.
  * `Verifier.treeSpecialSound_of_isEmpty_challengeIdx` — the bridge.
  * `Verifier.coordinateWiseSpecialSound_of_isEmpty_challengeIdx` and its `OracleVerifier` analogue.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

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

/-- The unique full transcript of a no-challenge tree. -/
def onlyTranscript [IsEmpty pSpec.ChallengeIdx]
    (tree : ChallengeTree pSpec arity 0) : FullTranscript pSpec :=
  (fullTranscripts_eq_singleton tree).choose

theorem onlyTranscript_mem [IsEmpty pSpec.ChallengeIdx]
    (tree : ChallengeTree pSpec arity 0) :
    tree.onlyTranscript ∈ tree.fullTranscripts := by
  have h : tree.fullTranscripts = [tree.onlyTranscript] :=
    (fullTranscripts_eq_singleton tree).choose_spec
  rw [h]
  exact List.mem_singleton_self _

end ProtocolSpec.ChallengeTree

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **Degenerate tree special soundness.** For a protocol with no challenge rounds, the tree is a
  single message-chain, so tree special soundness reduces to a transcript-level extractor: any `e`
  such that "the verifier accepts the (unique) transcript into `relOut.language`" implies the
  extracted witness lies in `relIn`. The shape `S` is irrelevant (`IsStructured` is vacuous). -/
theorem treeSpecialSound_of_isEmpty_challengeIdx [IsEmpty pSpec.ChallengeIdx]
    (S : ChallengeTreeShape pSpec) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (e : StmtIn → FullTranscript pSpec → WitIn)
    (h : ∀ stmtIn tr,
      Pr[ (· ∈ relOut.language) |
        OptionT.mk do (simulateQ impl (V.run stmtIn tr)).run' (← init)] = 1 →
      (stmtIn, e stmtIn tr) ∈ relIn) :
    V.treeSpecialSound init impl S relIn relOut :=
  ⟨fun stmtIn tree => e stmtIn tree.onlyTranscript,
    fun stmtIn tree _ hAcc => h stmtIn _ (hAcc _ tree.onlyTranscript_mem)⟩

/-- CWSS corollary of `treeSpecialSound_of_isEmpty_challengeIdx`: any coordinate-wise structure `D`
  works, since `IsStructured` is vacuous with no challenge rounds. -/
theorem coordinateWiseSpecialSound_of_isEmpty_challengeIdx [IsEmpty pSpec.ChallengeIdx]
    (D : CWSSStructure pSpec) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (e : StmtIn → FullTranscript pSpec → WitIn)
    (h : ∀ stmtIn tr,
      Pr[ (· ∈ relOut.language) |
        OptionT.mk do (simulateQ impl (V.run stmtIn tr)).run' (← init)] = 1 →
      (stmtIn, e stmtIn tr) ∈ relIn) :
    V.coordinateWiseSpecialSound init impl D relIn relOut :=
  treeSpecialSound_of_isEmpty_challengeIdx init impl D.toShape V relIn relOut e h

end Verifier

namespace OracleVerifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Oracle-reduction analogue of `coordinateWiseSpecialSound_of_isEmpty_challengeIdx`, on the
  combined `(StmtIn × ∀ i, OStmtIn i)` statement. -/
theorem coordinateWiseSpecialSound_of_isEmpty_challengeIdx [IsEmpty pSpec.ChallengeIdx]
    (D : CWSSStructure pSpec)
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (e : (StmtIn × ∀ i, OStmtIn i) → FullTranscript pSpec → WitIn)
    (h : ∀ stmtIn tr,
      Pr[ (· ∈ relOut.language) |
        OptionT.mk do (simulateQ impl (V.toVerifier.run stmtIn tr)).run' (← init)] = 1 →
      (stmtIn, e stmtIn tr) ∈ relIn) :
    V.coordinateWiseSpecialSound init impl D relIn relOut :=
  V.toVerifier.coordinateWiseSpecialSound_of_isEmpty_challengeIdx init impl D relIn relOut e h

end OracleVerifier
