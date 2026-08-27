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

  ## The honest direction

  The link is certified in **both** directions about the same verifier: `endPieceReduction` pairs
  the honest reveal (`endPieceProver`) with `endPieceVerifier` — the package's verifier on the
  nose (`endPieceReduction_verifier`) — and `endPieceReduction_perfectCompleteness` (error `0`,
  axiom-clean) shows a witness in `relWEvalClaim` passes the guard, by the full reflection lemma
  `endPieceCheck_eq_true_iff`. That reflection lemma also serves the *nonrecursive scheme*
  (`Correctness.lean`): the `Commitment.Scheme` interface fixes the `Proof` shape to a `Bool`
  verdict, so the scheme's terminal verifier cannot be the guarded one — instead it **returns**
  `endPieceCheck` as its verdict, the very check guarded here
  (`terminalVerifier_verify_eq_endPieceCheck`), so the two shapes share one decision procedure.

  ## The shortness conjunct

  `relWEvalClaim` carries three conjuncts: the commitment opens, the opening is **short**
  (`liftShort Φ bound bDig`), and the table's multilinear extension takes the claimed value.
  The shortness conjunct is what the *preceding* link's extractor has to produce out of an
  accepting `relWEvalClaim` (`nestedRoundRel` in `ZeroCheck/Constraints.lean` lists it among its
  components), and the end-piece is the one step that receives `w̃`, so its check decides all
  three. Deciding shortness is not purely mechanical: `vecLInftyNorm Φ w.z ≤ bound` is already
  decidable, but `RhoDigitsShort` quantifies over every `k : ℕ`. It is cut down to `k < deg φ`
  (`rhoDigitsShortCheck`), the tail being discharged by the truncation built into `rhoDigits`
  (`rhoDigits_coeff`, used by `rhoDigitsShortCheck_eq_true_iff`).

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
variable (m₀ : ℕ) (bound bDig : ℕ) (b : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- Decides `RhoDigitsShort` by checking only the `δ` digit indices and the `d` coefficient
positions a digit actually occupies: `rhoDigits` truncates at `deg φ`, so every coefficient beyond
it is `0` and satisfies the bound vacuously (`rhoDigitsShortCheck_eq_true_iff`).

It range-checks the committed digits rather than the raw quotient rows, which is what lets it pass
at a small bound: a raw quotient is only `q/2`-bounded (`rhoShort_half`). -/
def rhoDigitsShortCheck (ρ : Fin n → CPolynomial (ZMod q)) : Bool :=
  decide (∀ i, ∀ u < rhoDigitCount q bDig, ∀ k < Φ.φ.natDegree,
    ((rhoDigits Φ bDig (ρ i) u).coeff k).valMinAbs.natAbs ≤ bound)

omit [NeZero q] [IsCyclotomic Φ] in
/-- The truncated check decides exactly `RhoDigitsShort`: `rhoDigits` is supported below `deg φ`
(`rhoDigits_coeff`), and `0` satisfies any bound. -/
theorem rhoDigitsShortCheck_eq_true_iff (ρ : Fin n → CPolynomial (ZMod q)) :
    rhoDigitsShortCheck Φ bound bDig ρ = true ↔ RhoDigitsShort Φ bound bDig ρ := by
  rw [rhoDigitsShortCheck, decide_eq_true_iff]
  constructor
  · intro h i u k
    by_cases hk : k < Φ.φ.natDegree
    · exact h i u u.isLt k hk
    · rw [rhoDigits_coeff, if_neg hk]
      simp
  · exact fun h i u hu k _ => h i ⟨u, hu⟩ k

omit [NeZero q] [IsCyclotomic Φ] in
/-- **The digit conjunct of `liftShortCheck` always passes** at an admissible digit base: the
committed digits are `⌊bDig/2⌋`-bounded for every quotient (`rhoDigitsShort_of_digitBaseOk`).

So at the chain's parameters `liftShortCheck` is effectively the `z`-norm check alone. It is kept
as a conjunct because the check must decide `liftShort` *as stated* — with no side condition on the
base — and because the soundness side reads `liftShort` at whatever regime the commitment is
indexed by. The corresponding conjunct on raw quotient rows would be `RhoShort`, which
`rhoShort_half` shows can only be met at `q/2`. -/
theorem rhoDigitsShortCheck_eq_true_of_digitBaseOk (h : DigitBaseOk q bound bDig)
    (ρ : Fin n → CPolynomial (ZMod q)) :
    rhoDigitsShortCheck Φ bound bDig ρ = true :=
  (rhoDigitsShortCheck_eq_true_iff Φ bound bDig ρ).mpr (rhoDigitsShort_of_digitBaseOk Φ h ρ)

/-- Decides `liftShort`: the `ℓ∞` bound on `z` plus the truncated digit check. -/
def liftShortCheck (w : LiftedWitness Φ μ n) : Bool :=
  decide (vecLInftyNorm Φ w.z ≤ bound) && rhoDigitsShortCheck Φ bound bDig w.ρ

omit [NeZero q] [IsCyclotomic Φ] in
/-- `liftShortCheck` decides exactly `liftShort`. -/
theorem liftShortCheck_eq_true_iff (w : LiftedWitness Φ μ n) :
    liftShortCheck Φ bound bDig w = true ↔ liftShort Φ bound bDig w := by
  rw [liftShortCheck, Bool.and_eq_true, decide_eq_true_iff, rhoDigitsShortCheck_eq_true_iff]
  rfl

/-- Decides `relWEvalClaim` on the witness the prover sent: the commitment recomputes to the
claimed `t`, the opening is short (`liftShortCheck`), and the table's multilinear extension takes
the claimed value at the sumcheck point. -/
def endPieceCheck (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] (φF : ZMod q →+* F)
    (stmt : WEvalStatement K.TCom F m₀) (w : LiftedWitness Φ μ n) : Bool :=
  (K.com w == stmt.t) && liftShortCheck Φ bound bDig w &&
    (wTableMleEval Φ m₀ φF b w stmt.point == stmt.value)

/-- Accepts when `endPieceCheck` passes, rejects otherwise. The output statement is trivial. -/
def endPieceVerifier (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] (φF : ZMod q →+* F) :
    Verifier oSpec (WEvalStatement K.TCom F m₀) Unit
      (pSpecEndPiece (LiftedWitness Φ μ n)) where
  verify := fun stmt tr =>
    if endPieceCheck Φ m₀ bound bDig b K φF stmt (tr 0) then pure () else failure

omit [NeZero q] [IsCyclotomic Φ] [LawfulBEq F] in
/-- The end-piece verifier's guardedness as computable data (`Verifier.GuardedForm`): the guard is
`endPieceCheck` and the verdict is trivial, so `verify_eq` is `rfl`. The package carries this
instead of a bare `Verifier.IsGuarded` instance, because a composed chain must *run* the left
verdict at the seam; reading it off the `IsGuarded` existential would cost `Classical.choice`. -/
def endPieceVerifierGuardedForm
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] (φF : ZMod q →+* F) :
    (endPieceVerifier (oSpec := oSpec) Φ m₀ bound bDig b K φF).GuardedForm where
  check := fun stmt tr => endPieceCheck Φ m₀ bound bDig b K φF stmt (tr 0)
  out := fun _ _ => ()
  verify_eq := fun _ _ => rfl

omit [NeZero q] [IsCyclotomic Φ] [LawfulBEq F] in
/-- The verifier is guarded, with `endPieceCheck` as its check. True by definition: the verifier
is literally `if endPieceCheck … then pure () else failure`. -/
theorem endPieceVerifier_isGuarded
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] (φF : ZMod q →+* F) :
    (endPieceVerifier (oSpec := oSpec) Φ m₀ bound bDig b K φF).IsGuarded :=
  (endPieceVerifierGuardedForm Φ m₀ bound bDig b K φF).isGuarded

/-- The witness read off a transcript: the prover's single message. Kept apart from
`endPieceExtractor` so that the extraction itself is a computable function of the transcript. -/
def endPieceWitness {TCom : Type} (_stmt : WEvalStatement TCom F m₀)
    (tr : FullTranscript (pSpecEndPiece (LiftedWitness Φ μ n))) : LiftedWitness Φ μ n :=
  tr 0

/-- `endPieceWitness` applied to the tree's unique root-to-leaf path
(`ChallengeTree.onlyPath`, structural recursion) — computable, and independent of the leaf
witnessing, since the extracted witness *is* the transcript's one message. -/
def endPieceExtractor
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig)) :
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
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] [LawfulBEq K.TCom] (φF : ZMod q →+* F) :
    Verifier.coordinateWiseSpecialSoundWith init impl
      CWSSStructure.ofIsEmpty
      (relWEvalClaim Φ m₀ bound bDig b K φF)
      (Set.univ : Set (Unit × Unit))
      (endPieceVerifier (oSpec := oSpec) Φ m₀ bound bDig b K φF)
      (endPieceExtractor Φ m₀ bound bDig K) := by
  refine Verifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx init impl
    CWSSStructure.ofIsEmpty _ _ _ (endPieceWitness Φ m₀) ?_
  intro stmtIn tr hAcc
  have hcheck : endPieceCheck Φ m₀ bound bDig b K φF stmtIn (tr 0) = true := by
    by_contra hc
    exact Verifier.not_accepting_of_failure
      (V := endPieceVerifier (oSpec := oSpec) Φ m₀ bound bDig b K φF)
      (stmt := stmtIn) (tr := tr) (by simp [endPieceVerifier, hc]) hAcc
  simp only [endPieceCheck, Bool.and_eq_true, beq_iff_eq] at hcheck
  exact ⟨hcheck.1.1, (liftShortCheck_eq_true_iff Φ bound bDig _).mp hcheck.1.2, hcheck.2⟩

/-! ## The honest direction -/

omit [NeZero q] [IsCyclotomic Φ] in
/-- **Full reflection**: `endPieceCheck` decides exactly `relWEvalClaim`. This is the *single*
decision procedure of the terminal claim: the guarded soundness verifier (`endPieceVerifier`)
guards on it, and the nonrecursive scheme's verdict-returning terminal verifier
(`Correctness.lean`) returns it — so the two security directions of the closing link cannot
drift onto different checks. -/
theorem endPieceCheck_eq_true_iff
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] [LawfulBEq K.TCom] (φF : ZMod q →+* F)
    (stmt : WEvalStatement K.TCom F m₀) (w : LiftedWitness Φ μ n) :
    endPieceCheck Φ m₀ bound bDig b K φF stmt w = true ↔
      (stmt, w) ∈ relWEvalClaim Φ m₀ bound bDig b K φF := by
  rw [endPieceCheck, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq,
    liftShortCheck_eq_true_iff]
  constructor
  · rintro ⟨⟨hcom, hshort⟩, hval⟩
    exact ⟨hcom, hshort, hval⟩
  · rintro ⟨hcom, hshort, hval⟩
    exact ⟨⟨hcom, hshort⟩, hval⟩

/-- The end-piece honest prover: sends the witness `w̃` in the clear. Nothing remains to compute —
the output statement and witness are trivial. -/
def endPieceProver {TCom : Type} :
    Prover oSpec (WEvalStatement TCom F m₀) (LiftedWitness Φ μ n) Unit Unit
      (pSpecEndPiece (LiftedWitness Φ μ n)) where
  PrvState
    | 0 => LiftedWitness Φ μ n
    | 1 => LiftedWitness Φ μ n
  input := fun st => st.2
  sendMessage
    | ⟨0, _⟩ => fun w => pure (w, w)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun _ => pure ((), ())

/-- **The end-piece as a protocol object**: the honest reveal paired with the guarded verifier.
The verifier field is `endPiece`'s on the nose (`endPieceReduction_verifier`), so the two security
directions of the closing link speak about the same object. Perfect completeness is
`endPieceReduction_perfectCompleteness`. -/
def endPieceReduction (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] (φF : ZMod q →+* F) :
    Reduction oSpec (WEvalStatement K.TCom F m₀) (LiftedWitness Φ μ n) Unit Unit
      (pSpecEndPiece (LiftedWitness Φ μ n)) where
  prover := endPieceProver Φ m₀
  verifier := endPieceVerifier Φ m₀ bound bDig b K φF

set_option linter.unusedSectionVars false in
omit [NeZero q] [IsCyclotomic Φ] in
/-- **The honest prover's run, characterized**: one message round and no challenge, so the run is
a single `pure` whose only transcript slot holds the witness, with trivial outputs. Proved by the
framework round-unfolding at the index that literally occurs, as in
`finalEvalProver_run_support`. -/
lemma endPieceProver_run_support {TCom : Type}
    (stmt : WEvalStatement TCom F m₀) (wit : LiftedWitness Φ μ n) :
    ∀ x ∈ support ((endPieceProver (oSpec := oSpec) (TCom := TCom) Φ m₀).run stmt wit),
      x.1 0 = wit ∧ x.2 = ((), ()) := by
  have step1 : (endPieceProver (oSpec := oSpec) (TCom := TCom) Φ m₀).runToRound
        (Fin.last 1) stmt wit
      = (endPieceProver (oSpec := oSpec) (TCom := TCom) Φ m₀).processRound (0 : Fin 1)
          ((endPieceProver (oSpec := oSpec) (TCom := TCom) Φ m₀).runToRound
            ((0 : Fin 1).castSucc) stmt wit) :=
    Prover.runToRound_succ (0 : Fin 1) stmt wit _
  have step0 : (endPieceProver (oSpec := oSpec) (TCom := TCom) Φ m₀).runToRound
        ((0 : Fin 1).castSucc) stmt wit
      = pure ((fun i => Fin.elim0 i), wit) := rfl
  intro x hx
  unfold Prover.run at hx
  rw [step1, step0, Prover.processRound_of_dir_eq_P_to_V (0 : Fin 1) rfl] at hx
  simp only [endPieceProver, Fin.isValue, Fin.vcons_of_one] at hx
  subst hx
  exact ⟨rfl, rfl⟩

omit [NeZero q] [IsCyclotomic Φ] in
/-- **Honest-run characterization.** Every outcome of an honest run is the single success with
the witness in the transcript and trivial outputs. Failure is excluded because a witness in
`relWEvalClaim` passes `endPieceCheck` (`endPieceCheck_eq_true_iff`), the guard of the verifier. -/
lemma endPieceReduction_run_support
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] [LawfulBEq K.TCom] (φF : ZMod q →+* F)
    (stmt : WEvalStatement K.TCom F m₀) (w : LiftedWitness Φ μ n)
    (h : (stmt, w) ∈ relWEvalClaim Φ m₀ bound bDig b K φF) :
    ∀ x ∈ support ((endPieceReduction (oSpec := oSpec) Φ m₀ bound bDig b
        K φF).run stmt w).run,
      ∃ tr, x = some ((tr, (), ()), ()) := by
  have hg : endPieceCheck Φ m₀ bound bDig b K φF stmt w = true :=
    (endPieceCheck_eq_true_iff Φ m₀ bound bDig b K φF stmt w).mpr h
  intro x hx
  unfold Reduction.run at hx
  simp only [OptionT.run_bind, Option.elimM] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨prOpt, hpr, hx⟩ := hx
  rw [show ((liftM (Prover.run stmt w
        (endPieceReduction (oSpec := oSpec) Φ m₀ bound bDig b K φF).prover) :
        OptionT (OracleComp _) _)).run
      = (Prover.run stmt w
          (endPieceReduction (oSpec := oSpec) Φ m₀ bound bDig b K φF).prover)
        >>= fun a => pure (some a) from rfl] at hpr
  rw [mem_support_bind_iff] at hpr
  obtain ⟨pr, hpr, hprOpt⟩ := hpr
  rw [mem_support_pure_iff] at hprOpt
  subst hprOpt
  rw [show (endPieceReduction (oSpec := oSpec) Φ m₀ bound bDig b K φF).prover
      = endPieceProver (TCom := K.TCom) Φ m₀ from rfl] at hpr
  obtain ⟨hmsg, hout⟩ :=
    endPieceProver_run_support (oSpec := oSpec) (TCom := K.TCom) Φ m₀ stmt w pr hpr
  refine ⟨pr.1, ?_⟩
  simp only [Option.elim_some, endPieceReduction, endPieceVerifier, Verifier.run, hmsg, hg,
    if_true] at hx
  simp only [OptionT.run_pure, liftM_pure, ProgrammingPolicy.empty_apply, pure_bind,
    Option.elim_some, Option.getM_some, support_pure, Set.mem_singleton_iff] at hx
  have hpr : pr = (pr.1, (), ()) := Prod.ext rfl hout
  rw [hx, hpr]

omit [NeZero q] [IsCyclotomic Φ] in
/-- **Perfect completeness of the end-piece**, error exactly `0`: a witness in `relWEvalClaim`
passes the guard by the reflection lemma, and the trivial output relation asks nothing more.
Together with `endPiece_coordinateWiseSpecialSoundWith` — stated about the same verifier
(`endPieceReduction_verifier`) — the closing link is certified in both directions. -/
theorem endPieceReduction_perfectCompleteness
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] [LawfulBEq K.TCom] (φF : ZMod q →+* F) :
    (endPieceReduction (oSpec := oSpec) Φ m₀ bound bDig b
        K φF).perfectCompleteness init impl
      (relWEvalClaim Φ m₀ bound bDig b K φF)
      (Set.univ : Set (Unit × Unit)) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt w h x hx
  obtain ⟨tr, hx'⟩ := endPieceReduction_run_support Φ m₀ bound bDig b K φF stmt w h x hx
  exact ⟨_, hx', Set.mem_univ _, rfl⟩

/-- The end-piece packaged for composition: a guarded one-message verifier over the empty
challenge structure, taking `relWEvalClaim` to the trivial claim. No escape event — the check reads
only what the prover just sent, so no hardness assumption is involved. Every field is executable:
the guardedness rides along as data (`endPieceVerifierGuardedForm`) and the extractor reads the
tree's unique path. -/
def endPiece (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] [LawfulBEq K.TCom] (φF : ZMod q →+* F) :
    GCWSSPackage init impl
      (WEvalStatement K.TCom F m₀) (LiftedWitness Φ μ n)
      Unit Unit
      (pSpecEndPiece (LiftedWitness Φ μ n)) where
  verifier := endPieceVerifier (oSpec := oSpec) Φ m₀ bound bDig b K φF
  struct := CWSSStructure.ofIsEmpty
  relIn := relWEvalClaim Φ m₀ bound bDig b K φF
  relOut := Set.univ
  isGuarded := endPieceVerifierGuardedForm Φ m₀ bound bDig b K φF
  extractor := endPieceExtractor Φ m₀ bound bDig K
  isCWSS := endPiece_coordinateWiseSpecialSoundWith Φ m₀ bound bDig b init impl K φF

omit [NeZero q] [IsCyclotomic Φ] in
/-- The end-piece's protocol object and its soundness package share a verifier. Holds by
`rfl`. -/
@[simp] theorem endPieceReduction_verifier (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] [LawfulBEq K.TCom] (φF : ZMod q →+* F) :
    (endPieceReduction (oSpec := oSpec) Φ m₀ bound bDig b K φF).verifier
      = (endPiece Φ m₀ bound bDig b init impl K φF).verifier :=
  rfl


end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
