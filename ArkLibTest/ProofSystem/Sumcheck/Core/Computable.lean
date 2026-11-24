/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Core.Computable
import Mathlib.Algebra.Field.ZMod
import SumcheckRuntime

/-!
# The computable interaction-layer Sumcheck

The computable protocol, verifier, verdict reader and honest prover are executable; the
interpreted computable honest prover is the interaction-layer honest prover; completeness and
soundness hold at a concrete field, with uniform challenges for soundness. The compiled runs are
in `scripts/SumcheckRuntime.lean`.
-/

namespace Sumcheck.Core.ComputableTest

open scoped ENNReal NNReal
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec Sumcheck.Core.Computable Sumcheck.Impl.Representation

/-- The test field `ZMod 5`. -/
abbrev F := ZMod 5

/-- `5` is prime, which gives `ZMod 5` its field structure. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The evaluation domain `{0, 1}`. -/
def D₂ : Fin 2 ↪ F := ⟨fun i => (i.val : F), by decide⟩

variable {ι : Type} (ambient : OracleSpec ι) {σ : Type} (init : ProbComp σ)
  (impl : QueryImpl ambient (StateT σ ProbComp))

/-- Each honest round message is the CompPoly projection of the input. -/
example {k : ℕ} (x : Computable.Input F 2 3) (st : Computable.RoundState F 3 (k + 1)) :
    Computable.honestMessage D₂ x k st =
      Sumcheck.Impl.Computable.projectedMessage D₂ st.index st.statement.challenges x.val
        x.property :=
  rfl

/-- The interpreted computable honest prover is the interaction-layer honest prover. -/
example (stmt : Sumcheck.Spec.StatementRound F 3 0) (data : ∀ _ : Unit, Computable.Input F 2 3) :
    Computable.interpretProver (fun _ => Computable.honestOutputMap)
        (Computable.honestProver (m := OracleComp ambient) D₂ stmt data) =
      Sumcheck.Core.honestProver D₂ stmt (Computable.interpretInput F 2 3 data) :=
  interpretProver_honestProver D₂ stmt data

/-- A computable run, renamed and mapped, is the interaction-layer run of the interpreted
prover against `Sumcheck.Core.verifier`. -/
example (stmt : Sumcheck.Spec.StatementRound F 3 0) (data : ∀ _ : Unit, Computable.Input F 2 3)
    {Out : Transcript oracleSig (Computable.protocol F 2 3) → Type}
    (P : Prover oracleSig ambient (Computable.protocol F 2 3) Out) :
    simulateQ (Sumcheck.Core.renameQueries (M' := F⦃≤ 2⦄[X])
        (eval' := fun p x => p.val.eval x) ambient 3)
        (Sumcheck.Core.mapOutcome (toMessage F 2) 3 (Out' := fun _ => Σ tr, Out tr)
          (fun tr o => ⟨tr, o⟩) (Computable.interpretInput F 2 3) <$>
            (Computable.verifier F 2 3 D₂ ambient).run stmt data P) =
      (Sumcheck.Core.verifier F 2 3 D₂ ambient).run stmt (Computable.interpretInput F 2 3 data)
        (Computable.interpretProver (Out' := fun _ => Σ tr, Out tr) (fun tr o => ⟨tr, o⟩) P) :=
  Sumcheck.Core.run_eq_interpret D₂ (Computable.inputFamily F 2 3) (evaluate_eq F 2)
    (Sumcheck.Spec.polynomialFamily F 3 2) (Computable.interpretInput F 2 3) stmt data _ P

/-- Transporting challenges to the polynomial carrier and back returns them. -/
example (challenges : QueryImpl (challengeSpec oracleSig (Computable.protocol F 2 3)) ProbComp) :
    Sumcheck.Core.Interpreted.transportDraw (N := F⦃≤ 2⦄[X])
        (evaluateN := fun p x => p.val.eval x) 3
        (Sumcheck.Core.Interpreted.transportDraw 3 challenges) = challenges :=
  Sumcheck.Core.Interpreted.transportDraw_transportDraw 3 challenges

/-- Uniform challenges at the polynomial carrier transport to uniform computable challenges. -/
example : Sumcheck.Core.Interpreted.transportDraw (N := F⦃≤ 2⦄[X])
      (evaluateN := fun p x => p.val.eval x) 3
      (@challengeQueryImpl _ oracleSig (Sumcheck.Core.protocol F 2 3)
        (Sumcheck.Core.challengeSampleable F 2 3)) =
    @challengeQueryImpl _ oracleSig (Computable.protocol F 2 3)
          (Sumcheck.Core.Interpreted.challengeSampleable F _ _ 3) :=
  funext (Sumcheck.Core.transportDraw_challengeQueryImpl F 2 _ _ 3)

/-- Perfect completeness of the computable Sumcheck with uniform challenges. -/
example :
    letI : MeasurableSpace (Computable.HonestOutcome F 2 3) := ⊤
    completeness ((Computable.verifier F 2 3 D₂ ambient).classicalModel init impl
        (@challengeQueryImpl _ oracleSig (Computable.protocol F 2 3)
          (Sumcheck.Core.Interpreted.challengeSampleable F _ _ 3)))
      (Computable.relationProblem F 2 3 D₂ 0) (Computable.relationProblem F 2 3 D₂ (Fin.last 3))
      (Computable.judgement F 2 3 D₂) (fun x _ => Computable.honestProver D₂ x.1 x.2) 0 :=
  Computable.perfectCompleteness D₂ ambient init impl _

/-- A supported run accepts a true output even before choosing any oracle distribution. -/
example (stmt : Sumcheck.Spec.StatementRound F 3 0) (data : ∀ _ : Unit, Computable.Input F 2 3)
    (htrue : (Computable.relationProblem F 2 3 D₂ 0).rel () (stmt, data) ())
    (obs : Computable.HonestOutcome F 2 3)
    (hs : obs ∈ support ((Computable.verifier F 2 3 D₂ ambient).run stmt data
      (Computable.honestProver D₂ stmt data))) :
    ∃ t, obs.2.2 = some t ∧ (Computable.relationProblem F 2 3 D₂ (Fin.last 3)).rel () t () := by
  obtain ⟨t, ht, -, hrel⟩ := Computable.support_completeness D₂ ambient stmt data htrue obs hs
  exact ⟨t, ht, hrel⟩

/-- Soundness of the computable Sumcheck with uniform challenges, for every prover output. -/
example (Out : Transcript oracleSig (Computable.protocol F 2 3) → Type) :
    letI : MeasurableSpace (Computable.RunOutcome F 2 3 Out) := ⊤
    Interaction.Core.soundness
      ((Computable.verifier F 2 3 D₂ ambient).classicalModel (Out := Out) init impl
        (@challengeQueryImpl _ oracleSig (Computable.protocol F 2 3)
          (Sumcheck.Core.Interpreted.challengeSampleable F _ _ 3)))
      (Legacy.langProblem (Computable.language F 2 3 D₂ 0))
      (Legacy.langProblem (Computable.language F 2 3 D₂ (Fin.last 3)))
      (fun obs => Transcript.path obs.1) (fun obs => obs.2.2)
      ((∑ _ : (Sumcheck.Spec.pSpec F 2 3).ChallengeIdx, (2 : ℝ≥0) / Fintype.card F : ℝ≥0) : ℝ≥0∞) :=
  Computable.soundness F 2 3 D₂ ambient init impl Out

/-- Direct evaluation of the quadratic at the final challenge prefix. -/
theorem quadratic_final_value : SumcheckRuntime.quadratic.eval ![4, 4] = 16 := by
  rw [CPoly.eval_equiv]
  change (CPoly.polyRingEquiv (n := 2) (R := SumcheckRuntime.F)
    SumcheckRuntime.quadratic).eval ![4, 4] = 16
  norm_num [SumcheckRuntime.quadratic, map_add, map_mul, map_pow, CPoly.coe_polyRingEquiv,
    CPoly.CMvPolynomial.fromCMvPolynomial_X, CPoly.CMvPolynomial.fromCMvPolynomial_C]
  decide

/-- The final-state empty interval returns the verifier's accepted value without queries. -/
theorem zero_interval_verdict :
    SumcheckRuntime.quadraticZeroObserve = (some (16, 4, 4, 16), []) := by
  unfold SumcheckRuntime.quadraticZeroObserve
  rw [OracleVerifier.run_eq]
  change (some (16, 4, 4, SumcheckRuntime.quadratic.eval ![4, 4]), []) = _
  rw [quadratic_final_value]

/-- The separate empty prover outcome retains the same polynomial evaluation. -/
theorem zero_prover_output :
    SumcheckRuntime.quadraticZeroProverObserve = ((16, 4, 4, 16), []) := by
  change ((16, 4, 4, SumcheckRuntime.quadratic.eval ![4, 4]), []) = _
  rw [quadratic_final_value]

end Sumcheck.Core.ComputableTest

namespace Sumcheck.Core.ComputableTest.Universes

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec Sumcheck.Core

universe wI

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {deg n d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)
  {I : Type 1} {A : I → Type} (inputs : OracleFamily.{1, 0, wI} I A)
  {M : Type} {eval : M → R → R}

/-- Construction over a bundle index in `Type 1` leaves the query universe independent. -/
def verifierAtHigherIndex :
    OracleVerifier ambient (protocolOn R M eval n) (Sumcheck.Spec.StatementRound R n 0)
      (fun _ => Sumcheck.Spec.StatementRound R n (Fin.last n)) inputs (fun _ => inputs) :=
  verifierOn R deg n D ambient M eval inputs

omit [SampleableType R] in
/-- The final decision law accepts higher bundle indices through an ordinary import. -/
theorem simulate_decision {f : M → R⦃≤ deg⦄[X]}
    (hf : ∀ x r, eval x r = (f x).val.eval r) {κ : Type} {target : OracleSpec κ}
    (amb : QueryImpl ambient (OracleComp target)) (stmt : Sumcheck.Spec.StatementRound R n 0)
    (data : ∀ i, A i) (tr : Transcript oracleSig (protocolOn R M eval n)) :
    simulateQ (QueryImpl.addLift amb ((pathBundle inputs (protocolOn R M eval n)
      tr.path).answer (data, oracleMessages _ tr)))
      ((verifierAtHigherIndex (deg := deg) D ambient inputs).decide stmt _ (toView _ tr)).run =
      (pure (legacyVerdict R deg n D ambient stmt (decodeTranscript n (polyTranscript f n tr))) :
        OracleComp target _) :=
  simulateQ_decideOn D inputs hf amb stmt data tr

/-- The review's constant-evaluation constructor also accepts a high bundle-query universe. -/
example (domain : Fin 1 ↪ R) {J : Type 1} {B : J → Type}
    (family : OracleFamily.{1, 0, 1} J B) :
    OracleVerifier emptySpec (protocolOn R R (fun x _ => x) 1)
      (Sumcheck.Spec.StatementRound R 1 0)
      (fun _ => Sumcheck.Spec.StatementRound R 1 (Fin.last 1)) family (fun _ => family) :=
  verifierOn R 1 1 domain emptySpec R (fun x _ => x) family

end Sumcheck.Core.ComputableTest.Universes

/-! The executable definitions are computable, and the theorems use only the standard axioms. -/

run_cmd do
  let env ← Lean.getEnv
  for decl in [``Sumcheck.Core.Computable.verifier, ``Sumcheck.Core.Computable.observe,
      ``Sumcheck.Core.Computable.honestProver, ``Sumcheck.Core.Computable.honestFrom,
      ``Sumcheck.Core.Computable.honestMessage, ``Sumcheck.Core.Computable.nextState,
      ``Sumcheck.Core.verifierOn, ``Interaction.Core.sampler] do
    if Lean.isNoncomputable env decl then
      throwError "{decl} is noncomputable"
  for decl in [``Sumcheck.Core.run_eq_interpret, ``Sumcheck.Core.experiment_renameQueries,
      ``Sumcheck.Core.transportDraw_challengeQueryImpl,
      ``Sumcheck.Core.Computable.interpretProver_honestProver,
      ``Sumcheck.Core.Computable.support_completeness,
      ``Sumcheck.Core.Computable.perfectCompleteness, ``Sumcheck.Core.Computable.soundness,
      ``Sumcheck.Core.Computable.interval_run_eq_interpret,
      ``Sumcheck.Core.Computable.interval_support_completeness,
      ``Sumcheck.Core.Computable.interval_perfectCompleteness,
      ``Sumcheck.Core.Computable.interval_measureCompleteness,
      ``Sumcheck.Core.Computable.interval_soundness,
      ``Sumcheck.Core.verifier_run_full_interval, ``Sumcheck.Core.Computable.full_run_interval,
      ``Sumcheck.Core.ComputableTest.zero_interval_verdict] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
