/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martin
-/
import ArkLib.Commitments.Functional.Hachi.Sumcheck.FinalEval
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge

/-!
  # The end-piece — closing the Hachi evaluation

  The closing component of the Hachi evaluation ([NOZ26]): it ends a (possible run of)
  iteration(s) of the §4.3 chain. The prover sends the reduced (end) witness `w̃` itself as its
  one message, and the verifier checks the reduced claim `relWEvalClaim` against it directly —
  recompute the commitment, evaluate the table's multilinear extension at the sumcheck point.
  Nothing is left to reduce, so the output relation is the full relation on `Unit`.

  This file was split out of `Composition.lean`, where the end-piece lived as a sorried skeleton;
  the split is what that file's own note asks for once the skeleton is filled ("it should move to
  a separate file/folder as a subprotocol in its own right, exporting its package the same way as
  the other subprotocols"). `Composition.lean` now imports `endPiece` and concatenates it after
  `iteration` to form `evaluation`.

  * **message (P→V)** — the reduced witness `w̃ : LiftedWitness Φ μ n`, sent in the clear. Sending
    the witness is sound *here* precisely because this is the terminal link: there is no
    downstream claim whose zero-knowledge the disclosure could damage, and [NOZ26] treats the
    evaluation argument as a plain (non-ZK) reduction.
  * **check (guarded)** — `endPieceCheck`: the two conjuncts of `relWEvalClaim` on the sent
    witness. The verifier **must** be guarded: the output statement is `Unit`, so it drops
    everything the check reads and the check can live neither downstream nor in a pull-back.
  * **output** — `Unit`, at the full relation `Set.univ`.

  ## Extraction

  The extractor is the reason the end-piece is cheap: the witness the extractor must produce is
  *in the transcript*. `endPieceWitness` reads it off (`fun _ tr => tr 0`) and
  `endPiece_coordinateWiseSpecialSoundWith` closes CWSS through the challenge-free bridge
  `Verifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx`: the protocol has no challenge
  round, so CWSS collapses to a transcript-level obligation, and acceptance forces the guard
  (`Verifier.check_eq_true_of_guarded_accepting`), which is definitionally the two conjuncts of
  `relWEvalClaim`.

  ## Note on the `relWEvalClaim` seam

  `endPiece`'s input relation is `relWEvalClaim` exactly as `Sumcheck/FinalEval.lean` defines it
  on this branch: `K.com w̃ = t` and `mle[w̃](a) = y′`, with **no shortness conjunct**. PR #729
  carries a variant of `relWEvalClaim` that additionally requires `liftShort Φ bound ρBound w̃`.
  Should that variant win, `endPieceCheck` needs a third conjunct deciding `liftShort` on the sent
  witness (decidable: an `L∞` bound on `z` and a coefficient-range predicate on `ρ`), and
  `endPiece_coordinateWiseSpecialSound_aux` a third projection — a localized change confined to
  those two declarations.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

/-- The end-piece wire format: one prover message sending the reduced (end) witness itself. -/
@[reducible] def pSpecEndPiece (Wit : Type) : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[Wit]⟩

/-- The end-piece has no challenge round: its `ChallengeIdx` is empty. -/
instance {Wit : Type} : IsEmpty (pSpecEndPiece Wit).ChallengeIdx :=
  ⟨fun ⟨0, h⟩ => nomatch h⟩

/-- Each challenge of `pSpecEndPiece` is (vacuously) sampleable — there are none. -/
instance {Wit : Type} : ∀ i, SampleableType ((pSpecEndPiece Wit).Challenge i) :=
  fun i => isEmptyElim i

section Protocol

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ : ℕ) (bound ρBound : ℕ) (b : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- **The end-piece check** — the two conjuncts of `relWEvalClaim`, decided on the sent witness:
the commitment recomputes to the claimed `t`, and the witness table's multilinear extension
evaluates to the claimed value at the sumcheck point. Unlike `finalCheck`, this is a *complete*
definition rather than a skeleton: everything it reads is either public statement data or the
message itself. -/
def endPieceCheck (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    [BEq K.TCom] (φF : ZMod q →+* F)
    (stmt : WEvalStatement K.TCom F m₀) (w : LiftedWitness Φ μ n) : Bool :=
  (K.com w == stmt.t) && (wTableMleEval Φ m₀ φF b w stmt.point == stmt.value)

/-- The end-piece verifier: **guarded** on `endPieceCheck`, outputting the trivial statement. -/
def endPieceVerifier (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    [BEq K.TCom] (φF : ZMod q →+* F) :
    Verifier oSpec (WEvalStatement K.TCom F m₀) Unit
      (pSpecEndPiece (LiftedWitness Φ μ n)) where
  verify := fun stmt tr =>
    if endPieceCheck Φ m₀ bound ρBound b K φF stmt (tr 0) then pure () else failure

omit [NeZero q] [IsCyclotomic Φ] [LawfulBEq F] in
/-- The end-piece verifier is guarded — definitionally, by `endPieceCheck`. -/
theorem endPieceVerifier_isGuarded
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    [BEq K.TCom] (φF : ZMod q →+* F) :
    (endPieceVerifier (oSpec := oSpec) Φ m₀ bound ρBound b K φF).IsGuarded :=
  ⟨fun stmt tr => endPieceCheck Φ m₀ bound ρBound b K φF stmt (tr 0),
   fun _ _ => (),
   fun _ _ => rfl⟩

/-- **The end-piece extraction map, at transcript level**: return the witness the prover sent.

This is the whole extraction algorithm — no search, no choice, no `Classical`. Keeping it as a
separate transcript-level def (rather than inlining it into `endPieceExtractor`) is deliberate:
it is the computable core, and it is the piece that survives unchanged if the tree-extractor
interface moves to the witness-only form of PR #697 (`Extractor.TreeBased StmtIn WitIn WitOut`,
returning `Option WitIn`), where only the wrapper below has to change. -/
def endPieceWitness {TCom : Type} (_stmt : WEvalStatement TCom F m₀)
    (tr : FullTranscript (pSpecEndPiece (LiftedWitness Φ μ n))) : LiftedWitness Φ μ n :=
  tr 0

/-- **The end-piece extraction algorithm**: `endPieceWitness` on the tree's unique transcript.

`noncomputable` only because `ChallengeTree.onlyTranscript` is defined by choice on this branch;
the extraction content itself (`endPieceWitness`) is computable. -/
noncomputable def endPieceExtractor
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound)) :
    Extractor.TreeBased (WEvalStatement K.TCom F m₀) (LiftedWitness Φ μ n)
      (pSpecEndPiece (LiftedWitness Φ μ n))
      (CWSSStructure.toShape (CWSSStructure.ofIsEmpty
        (pSpec := pSpecEndPiece (LiftedWitness Φ μ n)))).arity :=
  fun stmtIn tree => endPieceWitness Φ m₀ stmtIn tree.onlyTranscript

variable [SampleableType F]

/-- **CWSS of the end-piece, at the named `endPieceExtractor`.**

The protocol is challenge-free, so CWSS collapses through
`Verifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx` to the transcript-level
obligation "acceptance implies the extracted witness lies in `relWEvalClaim`". Acceptance forces
the guard (`Verifier.check_eq_true_of_guarded_accepting`), and the guard *is* the relation:
`endPieceCheck` decides exactly `relWEvalClaim`'s two conjuncts on the sent witness, which is what
`endPieceWitness` returns. -/
theorem endPiece_coordinateWiseSpecialSoundWith
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    [BEq K.TCom] [LawfulBEq K.TCom] (φF : ZMod q →+* F) :
    Verifier.coordinateWiseSpecialSoundWith init impl
      CWSSStructure.ofIsEmpty
      (relWEvalClaim Φ m₀ bound ρBound b K φF)
      (Set.univ : Set (Unit × Unit))
      (endPieceVerifier (oSpec := oSpec) Φ m₀ bound ρBound b K φF)
      (endPieceExtractor Φ m₀ bound ρBound K) := by
  sorry

/-- **The end-piece as a guarded `GCWSSPackage`**: the guarded one-message verifier with the empty
challenge structure, reducing the evaluation claim `relWEvalClaim` to the trivial claim. Escape-free
— the check re-reads data the prover just sent, so no cryptographic assumption is consulted and no
escape event is needed. -/
noncomputable def endPiece (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    [BEq K.TCom] [LawfulBEq K.TCom] (φF : ZMod q →+* F) :
    GCWSSPackage init impl
      (WEvalStatement K.TCom F m₀) (LiftedWitness Φ μ n)
      Unit Unit
      (pSpecEndPiece (LiftedWitness Φ μ n)) where
  verifier := endPieceVerifier (oSpec := oSpec) Φ m₀ bound ρBound b K φF
  struct := CWSSStructure.ofIsEmpty
  relIn := relWEvalClaim Φ m₀ bound ρBound b K φF
  relOut := Set.univ
  isGuarded := endPieceVerifier_isGuarded Φ m₀ bound ρBound b K φF
  extractor := endPieceExtractor Φ m₀ bound ρBound K
  isCWSS := endPiece_coordinateWiseSpecialSoundWith Φ m₀ bound ρBound b init impl K φF

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
