/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas, Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Sumcheck.Rounds

/-!
  # Final evaluation

  The step closing the sumcheck loop:

  * **message (P→V)** — the claimed evaluation `y′ := w̃(a₁, …, a_{m₀}) ∈ F`, sent in the
    clear;
  * **check** — the verifier evaluates the two public factors `eq̃(τ₀, a)` and `Ã(a)` at the
    challenge point and checks both final sumcheck targets against the claimed `y′`:
    `eq̃(τ₀,a)·P_b(y′) = target₀` and `y′·Ã(a) = target_α`, plus the bound-sanity conjunct.
    The check reads the final targets, which the output statement drops, so the verifier is
    guarded (`failure` on a failed check), like the round verifiers of `Sumcheck/Rounds.lean`;
  * **output** — the evaluation claim `WEvalStatement`: the commitment `t`, the sumcheck
    point `a`, and the claimed value `y′`, consumed by the `Recursion/` adapters.

  The step has no challenge round. The computable extractor reads the opening from its unique
  valid leaf witness; acceptance forces the check, and that leaf gives a short opening `w̃` of
  `t` with `mle[w̃](a) = y′`. At `i = m₀` the two claims of `nestedRoundRel m₀` are plain
  evaluations (`hypercubeSum_of_le`) which factor through `mle[w̃](a)`
  (`eval_sumcheckPolyZero` / `eval_sumcheckPolyAlpha`), so substituting `y′` turns them into
  exactly the two check equations.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

/-- The final-evaluation wire format: one prover message carrying the claimed evaluation
`y′ ∈ F`. -/
@[reducible] def pSpecFinalEval (F : Type) : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[F]⟩

/-- The final-evaluation step has no challenge round: its `ChallengeIdx` is empty. -/
instance {F : Type} : IsEmpty (pSpecFinalEval F).ChallengeIdx :=
  ⟨fun ⟨0, h⟩ => nomatch h⟩

/-- Each challenge of `pSpecFinalEval` is (vacuously) sampleable — there are none. -/
instance {F : Type} [SampleableType F] :
    ∀ i, SampleableType ((pSpecFinalEval F).Challenge i) :=
  fun i => isEmptyElim i

/-- The evaluation-claim statement, output of the sumcheck and input of the recursion: the
`w̃`-commitment `t`, the sumcheck point `a ∈ F^{m₀}`, and the claimed multilinear evaluation
`y′`. Everything else (the `R^lin` data, `α`, the seeds, the targets) is dropped. -/
structure WEvalStatement (TCom F : Type) (m₀ : ℕ) where
  /-- The `w̃`-commitment from the lift stage. -/
  t : TCom
  /-- The sumcheck challenge point `a = (a₁, …, a_{m₀})`. -/
  point : Fin m₀ → F
  /-- The claimed evaluation `y′ = mle[w̃](a)`. -/
  value : F

section Protocol

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ) (b : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The final check: both final sumcheck targets against the public factors evaluated at the
challenge point, with the claimed `y′` in place of `w̃(a)`, plus the bound-sanity conjunct
`bound ≤ rlin.bound`:

* `eq̃(τ₀, a) · P_b(y′) = target₀` — the range claim;
* `y′ · Ã(a) = target_α` — the linear claim, where `Ã` is the multilinear extension of the
  public table `alphaPublicEvals`.

These are the two claims of `nestedRoundRel m₀` once the sumcheck has consumed every cube
coordinate (`hypercubeSum_of_le`), each factored into a public factor times a function of
`mle[w̃](a)` alone (`eval_sumcheckPolyZero` / `eval_sumcheckPolyAlpha`). -/
def finalCheck {TCom : Type} (m₁ bound b : ℕ) (φF : ZMod q →+* F)
    (stmt : NestedRoundStatement Φ TCom F n μ m₀ m₁ m₀) (y' : F) : Bool :=
  ((cEqualityPolynomial m₀ stmt.zc.τ₀).eval stmt.challenges * rangeProduct b y'
      == stmt.target₀) &&
    (y' * (cMultilinearExtension m₀
        (alphaPublicEvals Φ m₀ m₁ φF stmt.zc.rlin stmt.zc.α stmt.zc.τα)).eval stmt.challenges
      == stmt.targetα) &&
    decide (bound ≤ stmt.zc.rlin.bound)

/-- The final-evaluation verifier: on a passing `finalCheck`, output the evaluation claim
`⟨t, a, y′⟩`; otherwise `failure`. -/
def finalEvalVerifier {TCom : Type} (φF : ZMod q →+* F) :
    Verifier oSpec (NestedRoundStatement Φ TCom F n μ m₀ m₁ m₀)
      (WEvalStatement TCom F m₀)
      (pSpecFinalEval F) where
  verify := fun stmt tr =>
    if finalCheck Φ m₀ m₁ bound b φF stmt (tr 0) then
      pure ⟨stmt.zc.t, stmt.challenges, tr 0⟩
    else failure

omit [NeZero q] [IsCyclotomic Φ] in
/-- The final-evaluation verifier's guardedness as computable data (`Verifier.GuardedForm`): the
guard is `finalCheck` and the verdict is the evaluation claim `⟨t, a, y′⟩`, so `verify_eq` is
`rfl`.

The package carries this instead of a `Verifier.IsGuarded` instance, because a composed chain must
*run* the left verdict at the seam to know which statement to extract the right factor at (and the
composed escape event must name it too); reading either off the `IsGuarded` existential would cost
`Classical.choice`. -/
def finalEvalVerifierGuardedForm {TCom : Type} (φF : ZMod q →+* F) :
    (finalEvalVerifier (oSpec := oSpec) Φ m₀ m₁ bound b (n := n) (μ := μ) (TCom := TCom)
      φF).GuardedForm where
  check := fun stmt tr => finalCheck Φ m₀ m₁ bound b φF stmt (tr 0)
  out := fun stmt tr => ⟨stmt.zc.t, stmt.challenges, tr 0⟩
  verify_eq := fun _ _ => rfl

/-- The final-evaluation verifier is guarded — definitionally, by `finalCheck`. -/
theorem finalEvalVerifier_isGuarded {TCom : Type} (φF : ZMod q →+* F) :
    (finalEvalVerifier (oSpec := oSpec) Φ m₀ m₁ bound b (n := n) (μ := μ) (TCom := TCom)
      φF).IsGuarded :=
  ⟨fun stmt tr => finalCheck Φ m₀ m₁ bound b φF stmt (tr 0),
   fun stmt tr => ⟨stmt.zc.t, stmt.challenges, tr 0⟩,
   fun _ _ => rfl⟩

/-- The honest final-evaluation prover skeleton: sends `y′ := mle[w̃](a)` (the parameter
`computeY`, honestly `wTableMleEval`) and carries `w̃` forward as the output witness. -/
def finalEvalProver {TCom Wit : Type}
    (computeY : NestedRoundStatement Φ TCom F n μ m₀ m₁ m₀ →
      Wit → F) :
    Prover oSpec (NestedRoundStatement Φ TCom F n μ m₀ m₁ m₀) Wit
      (WEvalStatement TCom F m₀) Wit (pSpecFinalEval F) where
  PrvState
    | 0 => NestedRoundStatement Φ TCom F n μ m₀ m₁ m₀ × Wit
    | 1 => NestedRoundStatement Φ TCom F n μ m₀ m₁ m₀ × Wit
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (computeY st.1 st.2, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, wit⟩ =>
    pure (⟨stmt.zc.t, stmt.challenges, computeY stmt wit⟩, wit)

/-- The evaluation-claim relation, the sumcheck chain's output relation and the recursion's
input: `w̃` is a *short* opening of `t` and its table's multilinear extension evaluates to
the claimed value at the point. The shortness conjunct lives in the relation because the
verifier never sees `w̃`, so no check can supply it. -/
def relWEvalClaim (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Set (WEvalStatement K.TCom F m₀ × (LiftedWitness Φ μ n)) :=
  {p |
    K.com p.2 = p.1.t ∧
    liftShort Φ bound ρBound p.2 ∧
    wTableMleEval Φ m₀ φF b p.2 p.1.point = p.1.value}

variable [SampleableType F]

/-- The final-evaluation extraction algorithm reads the opening from the unique valid leaf
witness. -/
def finalEvalExtractor
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Extractor.TreeBased (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ m₀) (LiftedWitness Φ μ n)
      (LiftedWitness Φ μ n) (pSpecFinalEval F)
      (CWSSStructure.toShape (CWSSStructure.ofIsEmpty
        (pSpec := pSpecFinalEval F))).arity :=
  fun _ tree o => o tree.onlyPath

/-- Coordinate-wise special soundness of the final-evaluation step, with computable extractor
`finalEvalExtractor`.

The sole valid leaf supplies the opening that the extractor returns. Acceptance forces the
check; the leaf's reachable output is the emitted claim `⟨t, a, y′⟩` in `relWEvalClaim`, carrying
`K.com w̃ = t`, `liftShort w̃`, and `mle[w̃](a) = y′`. At `i = m₀` the two round claims are plain
evaluations (`hypercubeSum_of_le`) that factor through `mle[w̃](a)`
(`eval_sumcheckPolyZero` / `eval_sumcheckPolyAlpha`), so substituting `y′` turns them into
exactly the two check equations. -/
theorem finalEval_coordinateWiseSpecialSoundWith
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Verifier.coordinateWiseSpecialSoundWith init impl
      CWSSStructure.ofIsEmpty
      (nestedRoundRel Φ m₀ m₁ bound ρBound K φF b m₀)
      (relWEvalClaim Φ m₀ bound ρBound b K φF)
      (finalEvalVerifier (oSpec := oSpec) Φ m₀ m₁ bound b (TCom := K.TCom) φF)
      (finalEvalExtractor Φ m₀ m₁ bound ρBound K φF) := by
  intro stmt tree _ hAcc o hvalid
  obtain ⟨w, hw, out, hout, hrel⟩ := hvalid tree.onlyPath
  have hacc := hAcc _ tree.onlyPath.mem_fullTranscripts
  have hguard : finalCheck Φ m₀ m₁ bound b φF stmt (tree.onlyPath.fullTranscript 0) = true := by
    by_contra hc
    exact Verifier.not_accepting_of_failure
      (V := finalEvalVerifier (oSpec := oSpec) Φ m₀ m₁ bound b (TCom := K.TCom) φF)
      (stmt := stmt) (tr := tree.onlyPath.fullTranscript)
      (by simp [finalEvalVerifier, hc]) hacc
  have hout' : out = ⟨stmt.zc.t, stmt.challenges, tree.onlyPath.fullTranscript 0⟩ :=
    Verifier.outputs_guarded_subsingleton init impl
      (finalEvalVerifier (oSpec := oSpec) Φ m₀ m₁ bound b (TCom := K.TCom) φF)
      (fun s tr => finalCheck Φ m₀ m₁ bound b φF s (tr 0))
      (fun s tr => ⟨s.zc.t, s.challenges, tr 0⟩)
      (finalEvalVerifierGuardedForm Φ m₀ m₁ bound b φF).verify_eq
      stmt tree.onlyPath.fullTranscript hout
  rw [hout'] at hrel
  obtain ⟨hcom, hshort, hval⟩ := hrel
  rw [finalCheck, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq,
    decide_eq_true_iff] at hguard
  obtain ⟨⟨hg0, hgα⟩, hgb⟩ := hguard
  refine ⟨w, ?_, ?_⟩
  · change o tree.onlyPath = some w
    exact hw
  · refine ⟨hcom, hshort, ?_, ?_, hgb⟩
    · change hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b stmt.zc.τ₀ w) m₀
        stmt.challenges = _
      refine (hypercubeSum_of_le m₀ (sumcheckPolyZero Φ m₀ φF b stmt.zc.τ₀ w) le_rfl
        stmt.challenges).trans ?_
      simp only [Fin.eta]
      rw [eval_sumcheckPolyZero, hval]
      exact hg0
    · change hypercubeSum m₀
        (sumcheckPolyAlpha Φ m₀ m₁ φF b stmt.zc.rlin stmt.zc.α stmt.zc.τα w) m₀
        stmt.challenges = _
      refine (hypercubeSum_of_le m₀
        (sumcheckPolyAlpha Φ m₀ m₁ φF b stmt.zc.rlin stmt.zc.α stmt.zc.τα w) le_rfl
        stmt.challenges).trans ?_
      simp only [Fin.eta]
      rw [eval_sumcheckPolyAlpha, hval]
      exact hgα

/-- The final-evaluation step as a guarded `GCWSSPackage`: the guarded one-message verifier
with the empty challenge structure, reducing the round-`m₀` relation to the evaluation claim
`relWEvalClaim`; no challenge round, hence no escape event. -/
def finalEvalPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    GCWSSPackage init impl
      (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ m₀) (LiftedWitness Φ μ n)
      (WEvalStatement K.TCom F m₀) (LiftedWitness Φ μ n)
      (pSpecFinalEval F) where
  verifier := finalEvalVerifier (oSpec := oSpec) Φ m₀ m₁ bound b (TCom := K.TCom) φF
  struct := CWSSStructure.ofIsEmpty
  relIn := nestedRoundRel Φ m₀ m₁ bound ρBound K φF b m₀
  relOut := relWEvalClaim Φ m₀ bound ρBound b K φF
  isGuarded := finalEvalVerifierGuardedForm Φ m₀ m₁ bound b φF
  extractor := finalEvalExtractor Φ m₀ m₁ bound ρBound K φF
  isCWSS := finalEval_coordinateWiseSpecialSoundWith Φ m₀ m₁ bound ρBound b init impl K φF

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
