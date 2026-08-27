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

  The last step of Hachi's evaluation protocol ([NOZ26] §4.3). Every earlier step *reduces* one
  claim to a smaller one; this step settles the claim outright.

  The chain in `Composition.lean` ends at the evaluation claim `relWEvalClaim`: a table `w̃` opens
  the commitment `t`, and its multilinear extension takes the value `y′` at the sumcheck point `a`.
  The prover sends `w̃`, and the verifier checks that claim directly — recompute `K.com w̃` and
  compare with `t`, evaluate the extension at `a` and compare with `y′`. Nothing remains to reduce,
  so the output statement is `Unit` and the output relation is everything.

  Revealing `w̃` costs nothing here: no later claim depends on it staying hidden, and [NOZ26]
  treats the evaluation argument as a plain, non-zero-knowledge reduction.

  ## Why the verifier is guarded

  A *pure* verifier states its conditions in the output relation instead of rejecting. That is not
  available here — the output statement is `Unit` and retains none of the data the check reads — so
  the check runs at verification time and rejects on failure. That is a **guarded** verifier, in
  the sense of `CoordinateWiseSpecialSoundness/Guarded.lean`.

  ## How extraction works

  Special soundness asks for a witness recovered from accepting transcripts. Here the witness *is*
  the transcript's only message, so `endPieceWitness` returns it unchanged — read off the tree's
  unique root-to-leaf path (`ChallengeTree.onlyPath`), so the extractor is **computable**. The
  certificate `endPiece_coordinateWiseSpecialSoundWith` then follows in two moves:

  1. with no challenge round, coordinate-wise special soundness collapses to a statement about the
     single transcript (`coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx`);
  2. acceptance of a guarded verifier forces its check to have passed — a rejected check runs to
     `failure`, refuted by `Verifier.not_accepting_of_failure` — and that check is exactly
     membership in `relWEvalClaim`.

  Because the check only re-reads data the prover just sent, no hardness assumption is involved and
  the package carries no escape event. The package carries its guardedness **as data**
  (`endPieceVerifierGuardedForm : Verifier.GuardedForm`), so composition can run the verdict map
  at the seam without `Classical.choice` — every field of `endPiece` is executable.

  ## The shortness conjunct

  `relWEvalClaim` carries three conjuncts: the commitment opens, the opening is **short**
  (`liftShort Φ bound ρBound`), and the table's multilinear extension takes the claimed value.
  The shortness conjunct is what the *preceding* link's extractor has to produce out of an
  accepting `relWEvalClaim` (`nestedRoundRel` in `ZeroCheck/Constraints.lean` lists it among its
  components), and the end-piece is the one step that receives `w̃`, so its check decides all
  three. Deciding shortness is not purely mechanical: `vecLInftyNorm Φ w.z ≤ bound` is already
  decidable, but `RhoShort ρBound ρ = ∀ i k, ((ρ i).coeff k).valMinAbs.natAbs ≤ ρBound` ranges over
  every `k : ℕ` and is first cut down to `k < (ρ i).natDegree + 1` (`rhoShortCheck`), with the
  tail discharged by `CPolynomial.le_natDegree_of_ne_zero` (`rhoShortCheck_eq_true_iff`).

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

/-- Decides `RhoShort` by checking coefficients only up to the degree bound: beyond `natDegree`
every coefficient is `0` and satisfies the bound vacuously (`rhoShortCheck_eq_true_iff`). -/
def rhoShortCheck (ρ : Fin n → CPolynomial (ZMod q)) : Bool :=
  decide (∀ i, ∀ k < (ρ i).natDegree + 1, ((ρ i).coeff k).valMinAbs.natAbs ≤ ρBound)

omit [NeZero q] in
/-- The truncated check decides exactly `RhoShort`: coefficients past `natDegree` vanish
(`CPolynomial.le_natDegree_of_ne_zero`, contraposed), and `0` satisfies any bound. -/
theorem rhoShortCheck_eq_true_iff (ρ : Fin n → CPolynomial (ZMod q)) :
    rhoShortCheck ρBound ρ = true ↔ RhoShort ρBound ρ := by
  rw [rhoShortCheck, decide_eq_true_iff]
  constructor
  · intro h i k
    by_cases hk : k ≤ (ρ i).natDegree
    · exact h i k (Nat.lt_succ_of_le hk)
    · have hzero : (ρ i).coeff k = 0 := by
        by_contra hne
        exact hk (CPolynomial.le_natDegree_of_ne_zero hne)
      rw [hzero]
      simp
  · exact fun h i k _ => h i k

/-- Decides `liftShort`: the `ℓ∞` bound on `z` plus the truncated `RhoShort` check. -/
def liftShortCheck (w : LiftedWitness Φ μ n) : Bool :=
  decide (vecLInftyNorm Φ w.z ≤ bound) && rhoShortCheck ρBound w.ρ

omit [NeZero q] [IsCyclotomic Φ] in
/-- `liftShortCheck` decides exactly `liftShort`. -/
theorem liftShortCheck_eq_true_iff (w : LiftedWitness Φ μ n) :
    liftShortCheck Φ bound ρBound w = true ↔ liftShort Φ bound ρBound w := by
  rw [liftShortCheck, Bool.and_eq_true, decide_eq_true_iff, rhoShortCheck_eq_true_iff]
  rfl

/-- Decides `relWEvalClaim` on the witness the prover sent: the commitment recomputes to the
claimed `t`, the opening is short (`liftShortCheck`), and the table's multilinear extension takes
the claimed value at the sumcheck point. -/
def endPieceCheck (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    [BEq K.TCom] (φF : ZMod q →+* F)
    (stmt : WEvalStatement K.TCom F m₀) (w : LiftedWitness Φ μ n) : Bool :=
  (K.com w == stmt.t) && liftShortCheck Φ bound ρBound w &&
    (wTableMleEval Φ m₀ φF b w stmt.point == stmt.value)

/-- Accepts when `endPieceCheck` passes, rejects otherwise. The output statement is trivial. -/
def endPieceVerifier (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    [BEq K.TCom] (φF : ZMod q →+* F) :
    Verifier oSpec (WEvalStatement K.TCom F m₀) Unit
      (pSpecEndPiece (LiftedWitness Φ μ n)) where
  verify := fun stmt tr =>
    if endPieceCheck Φ m₀ bound ρBound b K φF stmt (tr 0) then pure () else failure

omit [NeZero q] [IsCyclotomic Φ] [LawfulBEq F] in
/-- The end-piece verifier's guardedness as computable data (`Verifier.GuardedForm`): the guard is
`endPieceCheck` and the verdict is trivial, so `verify_eq` is `rfl`. The package carries this
instead of a bare `Verifier.IsGuarded` instance, because a composed chain must *run* the left
verdict at the seam; reading it off the `IsGuarded` existential would cost `Classical.choice`. -/
def endPieceVerifierGuardedForm
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    [BEq K.TCom] (φF : ZMod q →+* F) :
    (endPieceVerifier (oSpec := oSpec) Φ m₀ bound ρBound b K φF).GuardedForm where
  check := fun stmt tr => endPieceCheck Φ m₀ bound ρBound b K φF stmt (tr 0)
  out := fun _ _ => ()
  verify_eq := fun _ _ => rfl

omit [NeZero q] [IsCyclotomic Φ] [LawfulBEq F] in
/-- The verifier is guarded, with `endPieceCheck` as its check. True by definition: the verifier
is literally `if endPieceCheck … then pure () else failure`. -/
theorem endPieceVerifier_isGuarded
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    [BEq K.TCom] (φF : ZMod q →+* F) :
    (endPieceVerifier (oSpec := oSpec) Φ m₀ bound ρBound b K φF).IsGuarded :=
  (endPieceVerifierGuardedForm Φ m₀ bound ρBound b K φF).isGuarded

/-- The witness read off a transcript: the prover's single message. Kept apart from
`endPieceExtractor` so that the extraction itself is a computable function of the transcript. -/
def endPieceWitness {TCom : Type} (_stmt : WEvalStatement TCom F m₀)
    (tr : FullTranscript (pSpecEndPiece (LiftedWitness Φ μ n))) : LiftedWitness Φ μ n :=
  tr 0

/-- `endPieceWitness` applied to the tree's unique root-to-leaf path
(`ChallengeTree.onlyPath`, structural recursion) — computable, and independent of the leaf
witnessing, since the extracted witness *is* the transcript's one message. -/
def endPieceExtractor
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound)) :
    Extractor.TreeBased (WEvalStatement K.TCom F m₀) (LiftedWitness Φ μ n) Unit
      (pSpecEndPiece (LiftedWitness Φ μ n))
      (CWSSStructure.toShape (CWSSStructure.ofIsEmpty
        (pSpec := pSpecEndPiece (LiftedWitness Φ μ n)))).arity :=
  fun stmtIn tree _ => some (endPieceWitness Φ m₀ stmtIn tree.onlyPath.fullTranscript)

omit [NeZero q] [IsCyclotomic Φ] in
/-- `endPieceExtractor` witnesses coordinate-wise special soundness, reducing `relWEvalClaim` to
the trivial claim.

With no challenge round the statement is about a single transcript, so it suffices to show that
acceptance puts the extracted witness in `relWEvalClaim`. Acceptance forces `endPieceCheck` to
have passed — a rejected check makes the verifier run `failure`, refuted by
`Verifier.not_accepting_of_failure` — and that check is `relWEvalClaim` evaluated at the message
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
  refine Verifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx init impl
    CWSSStructure.ofIsEmpty _ _ _ (endPieceWitness Φ m₀) ?_
  intro stmtIn tr hAcc
  have hcheck : endPieceCheck Φ m₀ bound ρBound b K φF stmtIn (tr 0) = true := by
    by_contra hc
    exact Verifier.not_accepting_of_failure
      (V := endPieceVerifier (oSpec := oSpec) Φ m₀ bound ρBound b K φF)
      (stmt := stmtIn) (tr := tr) (by simp [endPieceVerifier, hc]) hAcc
  simp only [endPieceCheck, Bool.and_eq_true, beq_iff_eq] at hcheck
  exact ⟨hcheck.1.1, (liftShortCheck_eq_true_iff Φ bound ρBound _).mp hcheck.1.2, hcheck.2⟩

/-- The end-piece packaged for composition: a guarded one-message verifier over the empty
challenge structure, taking `relWEvalClaim` to the trivial claim. No escape event — the check reads
only what the prover just sent, so no hardness assumption is involved. Every field is executable:
the guardedness rides along as data (`endPieceVerifierGuardedForm`) and the extractor reads the
tree's unique path. -/
def endPiece (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
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
  isGuarded := endPieceVerifierGuardedForm Φ m₀ bound ρBound b K φF
  extractor := endPieceExtractor Φ m₀ bound ρBound K
  isCWSS := endPiece_coordinateWiseSpecialSoundWith Φ m₀ bound ρBound b init impl K φF

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
