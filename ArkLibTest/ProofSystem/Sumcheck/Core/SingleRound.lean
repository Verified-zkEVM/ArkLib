/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Core.Soundness
import ArkLibTest.ProofSystem.Sumcheck.Core.Completeness

/-!
# One round of Sumcheck in the interaction layer

One round run against a prover that commits to a fixed message: closed forms of the run and of
the verdict, the output relation on accepted runs, rejection, and the distribution of the run with
a uniform challenge. The input polynomial, not the sent message, decides the output relation.
-/

namespace Sumcheck.Core.SingleRoundTest

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec MeasureTheory
open scoped ENNReal NNReal

/-! ## Support: a committed message -/

section Support

variable {R : Type} [CommSemiring R] {deg : ℕ} {ι : Type} (amb : OracleSpec ι)

/-- The one-round prover that commits to `q` and outputs `finish c` on the challenge `c`. -/
def oneRound {Out : Type} (q : R⦃≤ deg⦄[X]) (finish : R → Out) (c₀ : R) :
    Prover oracleSig amb (protocol R deg 1) (fun _ => Out) :=
  foldRounds (State := fun _ => R) (fun _ _ => q) (fun _ _ c => c) finish 1 c₀

/-- The one-round transcript of the message `q` and the challenge `c`. -/
def tr1 (q : R⦃≤ deg⦄[X]) (c : R) : PathAlong oracleSig (protocol R deg 1) :=
  foldTranscript (State := fun _ => R) (fun _ _ => q) (fun _ _ c => c) 1 c fun _ => c

/-- The transcript records the message and the challenge. -/
example (q : R⦃≤ deg⦄[X]) (c : R) : headMessage (tr1 q c) = q ∧ headChallenge (tr1 q c) = c :=
  ⟨rfl, rfl⟩

variable [DecidableEq R] [SampleableType R] {d : ℕ} (D : Fin d ↪ R)

/-- A message whose sum over the domain is the target passes, and the next target is the message
at the challenge. -/
theorem verdict_pass (stmt : Spec.StatementRound R 1 0) (q : R⦃≤ deg⦄[X]) (c : R)
    (h : ∑ x ∈ Finset.univ.map D, q.val.eval x = stmt.target) :
    legacyVerdict R deg 1 D amb stmt (decodeTranscript 1 (tr1 q c)) =
      some ⟨q.val.eval c, Fin.snoc stmt.challenges c⟩ := by
  refine (simulateQ_oracleVerifierProgram_succ 0 _ _ stmt (roundFullTranscript q c)
    (legacyTranscript 0 Fin.elim0 Fin.elim0)).trans ?_
  rw [roundCheck_eq_some 0 stmt _ h]
  rfl

/-- A message whose sum over the domain misses the target is rejected. -/
theorem verdict_fail (stmt : Spec.StatementRound R 1 0) (q : R⦃≤ deg⦄[X]) (c : R)
    (h : ∑ x ∈ Finset.univ.map D, q.val.eval x ≠ stmt.target) :
    legacyVerdict R deg 1 D amb stmt (decodeTranscript 1 (tr1 q c)) = none :=
  legacyVerdict_eq_none (k := 0) stmt (roundFullTranscript q c)
    (legacyTranscript 0 Fin.elim0 Fin.elim0) h

/-- The observation of a one-round run at the challenge `c`. -/
abbrev Obs1 (Out : Type) :=
  Observation oracleSig (protocol R deg 1) (fun _ => Out)
    (fun _ => Spec.StatementRound R 1 (Fin.last 1) × ∀ i, Spec.OracleStatement R 1 deg i)

/-- The observation of the committed run at the challenge `c`. -/
noncomputable def obs1 {Out : Type} (q : R⦃≤ deg⦄[X]) (finish : R → Out)
    (stmt : Spec.StatementRound R 1 0) (oStmt : ∀ i, Spec.OracleStatement R 1 deg i) (c : R) :
    Obs1 (R := R) (deg := deg) Out :=
  ⟨tr1 q c, finish c,
    (legacyVerdict R deg 1 D amb stmt (decodeTranscript 1 (tr1 q c))).map fun t => (t, oStmt)⟩

/-- Closed form of a committed run: draw the challenge, then record the message and the
challenge, the prover output and the verdict, with the input polynomial as output oracle. -/
theorem run_oneRound {Out : Type} (q : R⦃≤ deg⦄[X]) (finish : R → Out) (c₀ : R)
    (stmt : Spec.StatementRound R 1 0) (oStmt : ∀ i, Spec.OracleStatement R 1 deg i) :
    (verifier R deg 1 D amb).run stmt oStmt (oneRound amb q finish c₀) =
      (fun chals => obs1 amb D q finish stmt oStmt (chals 0)) <$>
        drawChallenges 1 (fun c =>
          liftM ((amb + challengeSpec oracleSig (protocol R deg 1)).query (.inr c))) := by
  rw [oneRound, run_verifier_foldRounds]
  refine congrArg (· <$> _) (funext fun chals => ?_)
  have hc : chals = fun _ => chals 0 := funext fun j => by rw [Subsingleton.elim j 0]
  conv_lhs => rw [hc]
  rfl

omit [DecidableEq R] [SampleableType R] in
/-- In an experiment, drawing one challenge runs the challenge implementation once. -/
theorem experiment_drawOne {σ α : Type} (init : ProbComp σ)
    (impl : QueryImpl amb (StateT σ ProbComp))
    (ch : QueryImpl (challengeSpec oracleSig (protocol R deg 1)) ProbComp)
    (f : (Fin 1 → R) → α) :
    experiment init impl ch
        (f <$> drawChallenges 1 (fun c =>
          liftM ((amb + challengeSpec oracleSig (protocol R deg 1)).query (.inr c)))) =
      init >>= fun _ => (fun c : R => f fun _ => c) <$> ch (headNode 0) := by
  have hprog : f <$> drawChallenges 1 (fun c =>
      liftM ((amb + challengeSpec oracleSig (protocol R deg 1)).query (.inr c))) =
      (fun c : (amb + challengeSpec oracleSig (protocol R deg 1)).Range (.inr (headNode 0)) =>
        f fun _ => c) <$>
        (liftM ((amb + challengeSpec oracleSig (protocol R deg 1)).query (.inr (headNode 0))) :
          OracleComp (amb + challengeSpec oracleSig (protocol R deg 1)) _) := by
    simp only [drawChallenges, LawfulMonad.pure_bind, map_eq_bind_pure_comp]
    erw [LawfulMonad.bind_assoc]
    congr 1
    funext c
    simp only [Function.comp_apply, LawfulMonad.pure_bind]
    congr 2
    funext j
    rw [Subsingleton.elim (α := Fin 1) j 0]
    rfl
  rw [hprog, experiment]
  refine bind_congr fun s => ?_
  rw [simulateQ_map, simulateQ_spec_query, StateT.run'_eq, StateT.run_map, Functor.map_map]
  simp only [QueryImpl.addLift, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply_run,
    Functor.map_map]
  rfl

/-- The outcome of a committed run on any event is the mass of the challenges whose observation
lies in it. -/
theorem outcome_oneRound {Out σ : Type} (init : ProbComp σ)
    (impl : QueryImpl amb (StateT σ ProbComp))
    (ch : QueryImpl (challengeSpec oracleSig (protocol R deg 1)) ProbComp)
    (q : R⦃≤ deg⦄[X]) (finish : R → Out) (c₀ : R)
    (stmt : Spec.StatementRound R 1 0) (oStmt : ∀ i, Spec.OracleStatement R 1 deg i)
    (E : Set (Obs1 (R := R) (deg := deg) Out)) :
    letI : MeasurableSpace (Obs1 (R := R) (deg := deg) Out) := ⊤
    letI : MeasurableSpace R := ⊤
    𝒟[experiment init impl ch
        ((verifier R deg 1 D amb).run stmt oStmt (oneRound amb q finish c₀))] E =
      𝒟[(init >>= fun _ => ch (headNode 0) : ProbComp R)]
        ((obs1 amb D q finish stmt oStmt) ⁻¹' E) := by
  let : MeasurableSpace (Obs1 (R := R) (deg := deg) Out) := ⊤
  let : MeasurableSpace R := ⊤
  rw [run_oneRound, experiment_drawOne]
  rw [show (init >>= fun _ => (fun c : R => obs1 amb D q finish stmt oStmt c) <$>
      ch (headNode 0)) = obs1 amb D q finish stmt oStmt <$>
        (init >>= fun _ => ch (headNode 0) : ProbComp R) by
    exact (_root_.map_bind _ _ _).symm]
  rw [evalDist_map _ measurable_from_top,
    Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]

omit [DecidableEq R] [SampleableType R] in
/-- In one variable, the final relation says that the input polynomial at the challenge is the
target. -/
theorem relationLast_iff (p : Spec.OracleStatement R 1 deg ()) (t c : R) :
    (((⟨t, fun _ => c⟩, fun _ => p), ()) ∈ Spec.relationRound R 1 deg D (Fin.last 1)) ↔
      MvPolynomial.eval (fun _ => c) p.val = t := by
  have h : Fin.append (fun _ : Fin 1 => c) (default : Fin 0 → R) = fun _ => c :=
    funext fun i => by fin_cases i; rfl
  simp [Spec.relationRound, h]

end Support

/-! ## Fixtures -/

noncomputable section

open Sumcheck.Core.CompletenessTest

/-- An oracle-capable ambient context, unused by these provers. -/
abbrev ambient : OracleSpec Unit := Unit →ₒ Unit

/-- The univariate message `X`. -/
def msgX : F⦃≤ 1⦄[X] := ⟨X, Polynomial.mem_degreeLE.mpr Polynomial.degree_X_le⟩

/-- The constant message one, of degree zero. -/
def msgOne (deg : ℕ) : F⦃≤ deg⦄[X] := ⟨1, Polynomial.mem_degreeLE.mpr (by
  rw [← C_1]; exact degree_C_le.trans (by exact_mod_cast Nat.zero_le _))⟩

/-- The zero polynomial in one variable. -/
def poly0 (deg : ℕ) : Spec.OracleStatement F 1 deg () := 0

/-- The domain `{0}`. -/
def D₁ : Fin 1 ↪ F := ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

/-- The empty domain. -/
def D₀ : Fin 0 ↪ F := ⟨Fin.elim0, fun i => i.elim0⟩

/-- A claim with target `t` and no challenges yet. -/
def claim (t : F) : Spec.StatementRound F 1 0 := ⟨t, Fin.elim0⟩

/-- The coordinate polynomial evaluates to the unique coordinate. -/
theorem eval_X₀ (c : F) : MvPolynomial.eval (fun _ => c) polyX.val = c := by
  simp [polyX]

/-- The zero polynomial evaluates to zero. -/
theorem eval_poly0 {deg : ℕ} (c : F) : MvPolynomial.eval (fun _ => c) (poly0 deg).val = 0 := by
  simp [poly0]

/-- The honest-shaped prover output: target the message at the challenge, history the
challenge. -/
def finishWith (q : F⦃≤ 1⦄[X]) (c : F) : F × F := (q.val.eval c, c)

/-! ## Honest and dishonest runs at a fixed challenge -/

-- Migration rows: Sumcheck Interaction/SingleRound #2–#6, Closing #2, #3, #5.

-- Migration row: Sumcheck Interaction/SingleRound #1.

/-- The message `X` sums to one over `{0, 1}`. -/
theorem msgX_sum : ∑ x ∈ Finset.univ.map D₂, msgX.val.eval x = 1 := by
  simp [msgX, D₂, Fin.sum_univ_two]

/-- Committing to `X` on the true claim that `X₀` sums to one over `{0, 1}`: the run with
challenge three records `(X, 3)`, the prover outputs `(3, 3)`, and the verifier accepts the
target three with history three and the input polynomial `X₀`. -/
example : obs1 ambient D₂ msgX (finishWith msgX) stmtX (fun _ => polyX) 3 =
    ⟨tr1 msgX 3, (3, 3), some (⟨3, Fin.snoc Fin.elim0 3⟩, fun _ => polyX)⟩ := by
  have h := verdict_pass ambient D₂ stmtX msgX 3 (by
    simp [msgX, D₂, stmtX, Fin.sum_univ_two])
  rw [obs1, h]
  simp [finishWith, msgX, stmtX]

/-- The accepted claim lies in the final relation: `X₀` at the challenge is the target. -/
example : (((⟨3, fun _ => 3⟩, fun _ => polyX), ()) ∈
    Spec.relationRound F 1 1 D₂ (Fin.last 1)) :=
  (relationLast_iff D₂ polyX 3 3).2 (eval_X₀ 3)

/-- With the wrong target two, the run still records the message, the challenge and the prover
output, and the verifier rejects. -/
example : obs1 ambient D₂ msgX (finishWith msgX) (claim 2) (fun _ => polyX) 3 =
    ⟨tr1 msgX 3, (3, 3), none⟩ := by
  have h := verdict_fail ambient D₂ (claim 2) msgX 3 (by
    simpa [msgX, D₂, claim, Fin.sum_univ_two] using (by decide : (1 : F) ≠ 2))
  rw [obs1, h]
  simp [finishWith, msgX]

/-- A dishonest constant message one passes the false claim that the zero polynomial sums to one
over `{0}`; the next target comes from the message, while the output oracle is the input
polynomial, so the final relation fails. -/
example (r : F) : obs1 ambient D₁ (msgOne 0) (fun c => c) (claim 1) (fun _ => poly0 0) r =
    ⟨tr1 (msgOne 0) r, r, some (⟨1, Fin.snoc Fin.elim0 r⟩, fun _ => poly0 0)⟩ ∧
    (((⟨1, fun _ => r⟩, fun _ => poly0 0), ()) ∉
      Spec.relationRound F 1 0 D₁ (Fin.last 1)) := by
  refine ⟨?_, ?_⟩
  · have h := verdict_pass ambient D₁ (claim 1) (msgOne 0) r (by simp [msgOne, claim])
    rw [obs1, h]
    simp [msgOne, claim]
  · rw [relationLast_iff, eval_poly0]
    decide

/-! ## The input polynomial decides the output relation -/

-- Migration rows: Sumcheck Interaction/Soundness #1, #2, #4.

/-- The cheating constant message one passes the false claim that `X₀` sums to one over `{0}`.
At challenge zero the final relation fails: `X₀(0) = 0 ≠ 1`. -/
example : obs1 ambient D₁ (msgOne 1) (fun c => c) (claim 1) (fun _ => polyX) 0 =
    ⟨tr1 (msgOne 1) 0, 0, some (⟨1, Fin.snoc Fin.elim0 0⟩, fun _ => polyX)⟩ ∧
    (((⟨1, fun _ => 0⟩, fun _ => polyX), ()) ∉ Spec.relationRound F 1 1 D₁ (Fin.last 1)) := by
  refine ⟨?_, ?_⟩
  · have h := verdict_pass ambient D₁ (claim 1) (msgOne 1) 0 (by simp [msgOne, claim])
    rw [obs1, h]
    simp [msgOne, claim]
  · rw [relationLast_iff, eval_X₀]
    decide

/-- At the collision challenge one the cheating message fools the round: the final relation
holds. -/
example : obs1 ambient D₁ (msgOne 1) (fun c => c) (claim 1) (fun _ => polyX) 1 =
    ⟨tr1 (msgOne 1) 1, 1, some (⟨1, Fin.snoc Fin.elim0 1⟩, fun _ => polyX)⟩ ∧
    (((⟨1, fun _ => 1⟩, fun _ => polyX), ()) ∈ Spec.relationRound F 1 1 D₁ (Fin.last 1)) := by
  refine ⟨?_, ?_⟩
  · have h := verdict_pass ambient D₁ (claim 1) (msgOne 1) 1 (by simp [msgOne, claim])
    rw [obs1, h]
    simp [msgOne, claim]
  · rw [relationLast_iff, eval_X₀]

/-- Against target two the cheating message is rejected, even at the collision challenge. -/
example : obs1 ambient D₁ (msgOne 1) (fun c => c) (claim 2) (fun _ => polyX) 1 =
    ⟨tr1 (msgOne 1) 1, 1, none⟩ := by
  have h := verdict_fail ambient D₁ (claim 2) (msgOne 1) 1 (by
    simpa [msgOne, claim] using (by decide : (1 : F) ≠ 2))
  rw [obs1, h]
  rfl

/-! ## Degree bound -/

-- Migration row: Sumcheck Interaction/Closing #1.

/-- Every message carries its degree bound. -/
example (q : F⦃≤ 1⦄[X]) : q.val.degree ≤ 1 := mem_degreeLE.mp q.property

end

end Sumcheck.Core.SingleRoundTest

-- Migration rows: Sumcheck Interaction/SingleRound #5, #6, Closing #6–#8, Soundness #24.
run_cmd do
  for decl in [``Sumcheck.Core.SingleRoundTest.verdict_pass,
      ``Sumcheck.Core.SingleRoundTest.verdict_fail, ``Sumcheck.Core.SingleRoundTest.run_oneRound,
      ``Sumcheck.Core.SingleRoundTest.experiment_drawOne,
      ``Sumcheck.Core.SingleRoundTest.outcome_oneRound,
      ``Sumcheck.Core.SingleRoundTest.relationLast_iff,
      ``Sumcheck.Core.SingleRoundTest.msgX_sum] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
