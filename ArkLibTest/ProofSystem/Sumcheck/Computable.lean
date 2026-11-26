/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Computable
import Mathlib.Algebra.Field.ZMod
import SumcheckRuntime

/-!
# The computable interaction-layer Sumcheck

The computable protocol, verifier, verdict reader and honest prover are executable; the
interpreted computable honest prover is the interaction-layer honest prover; completeness and
soundness hold at a concrete field, with uniform challenges for soundness. A suffix soundness
bound of `1/17` over `ZMod 17` comes with a proved false starting claim. The compiled runs are in
`scripts/SumcheckRuntime.lean`.
-/

namespace Sumcheck.ComputableTest

open scoped ENNReal NNReal
open Polynomial PFunctor FreeM Interaction Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec Sumcheck.Computable Sumcheck.Impl.Representation

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
      Sumcheck.honestProver D₂ stmt (Computable.interpretInput F 2 3 data) :=
  interpretProver_honestProver D₂ stmt data

/-- A computable run, renamed and mapped, is the interaction-layer run of the interpreted
prover against `Sumcheck.verifier`. -/
example (stmt : Sumcheck.Spec.StatementRound F 3 0) (data : ∀ _ : Unit, Computable.Input F 2 3)
    {Out : Transcript oracleSig (Computable.protocol F 2 3) → Type}
    (P : Prover oracleSig ambient (Computable.protocol F 2 3) Out) :
    simulateQ (Sumcheck.renameQueries (M' := F⦃≤ 2⦄[X])
        (eval' := fun p x => p.val.eval x) ambient 3)
        (Sumcheck.mapOutcome (toMessage F 2) 3 (Out' := fun _ => Σ tr, Out tr)
          (fun tr o => ⟨tr, o⟩) (Computable.interpretInput F 2 3) <$>
            (Computable.verifier F 2 3 D₂ ambient).run stmt data P) =
      (Sumcheck.verifier F 2 3 D₂ ambient).run stmt (Computable.interpretInput F 2 3 data)
        (Computable.interpretProver (Out' := fun _ => Σ tr, Out tr) (fun tr o => ⟨tr, o⟩) P) :=
  Sumcheck.run_eq_interpret D₂ (Computable.inputFamily F 2 3) (evaluate_eq F 2)
    (Sumcheck.Spec.polynomialFamily F 3 2) (Computable.interpretInput F 2 3) stmt data _ P

/-- Transporting challenges to the polynomial carrier and back returns them. -/
example (challenges : QueryImpl (challengeSpec oracleSig (Computable.protocol F 2 3)) ProbComp) :
    Sumcheck.Interpreted.transportDraw (N := F⦃≤ 2⦄[X])
        (evaluateN := fun p x => p.val.eval x) 3
        (Sumcheck.Interpreted.transportDraw 3 challenges) = challenges :=
  Sumcheck.Interpreted.transportDraw_transportDraw 3 challenges

/-- Uniform challenges at the polynomial carrier transport to uniform computable challenges. -/
example : Sumcheck.Interpreted.transportDraw (N := F⦃≤ 2⦄[X])
      (evaluateN := fun p x => p.val.eval x) 3
      (@challengeQueryImpl _ oracleSig (Sumcheck.protocol F 2 3)
        (Sumcheck.challengeSampleable F 2 3)) =
    @challengeQueryImpl _ oracleSig (Computable.protocol F 2 3)
          (Sumcheck.Interpreted.challengeSampleable F _ _ 3) :=
  funext (Sumcheck.transportDraw_challengeQueryImpl F 2 _ _ 3)

/-- Perfect completeness of the computable Sumcheck with uniform challenges. -/
example :
    letI : MeasurableSpace (Computable.HonestOutcome F 2 3) := ⊤
    completeness ((Computable.verifier F 2 3 D₂ ambient).classicalModel init impl
        (@challengeQueryImpl _ oracleSig (Computable.protocol F 2 3)
          (Sumcheck.Interpreted.challengeSampleable F _ _ 3)))
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
    Interaction.soundness
      ((Computable.verifier F 2 3 D₂ ambient).classicalModel (Out := Out) init impl
        (@challengeQueryImpl _ oracleSig (Computable.protocol F 2 3)
          (Sumcheck.Interpreted.challengeSampleable F _ _ 3)))
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

/-- The compatibility verifier's input family `Spec.polynomialFamily` and the family
`Sumcheck.polynomialFamily` of the indexed and interval verifiers are equal by `rfl`. -/
theorem spec_polynomialFamily_eq (R : Type) [CommSemiring R] (n deg : ℕ) :
    Sumcheck.Spec.polynomialFamily R n deg = Sumcheck.polynomialFamily R n deg := rfl

/-! ## A suffix soundness bound below one over `ZMod 17`

The actual computable suffix run has two variables, start one, one round, degree one and the
repeated domain `[0, 0]`. The original polynomial is zero and the incoming target is two, so the
starting claim is false. The prover sends `X + 1` and outputs the challenge it receives, so its
private output type depends on the transcript. The message sums to two over `[0, 0]`, so the sum
check passes at every challenge `r` and the run returns the endpoint claim `r + 1`. That claim is
true only at `r = -1`, and `interval_soundness` bounds the probability by `1/17`. -/

section SuffixSoundness

open SumcheckRuntime (zeroZero affine original)

/-- The false starting claim: after the prefix `[0]`, the zero polynomial has remaining sum two
over `[0, 0]`. -/
def shiftStart : RoundStatement SumcheckRuntime.F 2 ⟨1, by decide⟩ := ⟨2, ![0]⟩

/-- The private output records the actual challenge, so its type depends on the transcript. -/
abbrev ChallengeOut (tr : Transcript oracleSig (Computable.protocol SumcheckRuntime.F 1 1)) :
    Type := {r : SumcheckRuntime.F // Interpreted.challenge tr = r}

/-- The prover sends `X + 1` and outputs the challenge it receives. -/
def shiftProver {ι : Type} (ambient : OracleSpec ι) :
    Prover oracleSig ambient (Computable.protocol SumcheckRuntime.F 1 1) ChallengeOut :=
  consProver (affine 1 1) fun chal => (pure ⟨chal, rfl⟩ : OracleComp ambient _)

/-- The starting claim is false: the zero polynomial sums to zero, not two. -/
theorem shiftStart_false :
    ¬ indexedRelation zeroZero _ shiftStart
      (Computable.toPolynomial (original ()).val (original ()).property) := by
  simp only [indexedRelation, roundSum, Nat.reduceAdd, Fin.mk_one, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.add_one_sub_one, shiftStart, Fin.cast_refl,
    CompTriple.comp_eq, Computable.toPolynomial, Impl.Computable.toRestrictDegree, original,
    CPoly.map_zero, map_zero, Finset.sum_const_zero]
  decide

/-- The message `X + 1` sums to the target two over `[0, 0]`, so the sum check passes. -/
theorem shift_sum :
    (∑ a : Fin 2, evaluate SumcheckRuntime.F 1 (affine 1 1) (zeroZero a)) = 2 := by
  decide +kernel

/-- Horner evaluation of the message `X + 1` at every challenge `r` gives `r + 1`. -/
theorem shift_eval :
    ∀ r : SumcheckRuntime.F, evaluate SumcheckRuntime.F 1 (affine 1 1) r = r + 1 := by
  decide +kernel

/-- The endpoint claim after challenge `r` is true for the zero polynomial exactly when
`r = -1`. -/
theorem shift_endpoint_iff (r : SumcheckRuntime.F) :
    indexedRelation zeroZero (Fin.last 2)
      ⟨evaluate SumcheckRuntime.F 1 (affine 1 1) r, Fin.snoc shiftStart.challenges r⟩
      (Computable.toPolynomial (original ()).val (original ()).property) ↔ r = -1 := by
  rw [indexedRelation_last, shift_eval]
  simp only [Nat.reduceAdd, Fin.reduceLast, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.mk_one,
    Fin.isValue, Computable.toPolynomial, Impl.Computable.toRestrictDegree, original,
    CPoly.map_zero, map_zero]
  constructor
  · intro h; linear_combination -h
  · intro h; rw [h]; ring

/-- From the false claim, the actual computable suffix run with uniform challenges returns a
true endpoint claim with probability at most `1/17`, for a prover whose private output type
depends on the challenge. -/
theorem suffix_soundness_one_seventeenth {ι : Type} (ambient : OracleSpec ι) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp)) :
    Pr{let obs ← (experiment init impl
      (@challengeQueryImpl _ oracleSig (Computable.protocol SumcheckRuntime.F 1 1)
        (Interpreted.challengeSampleable SumcheckRuntime.F _ _ 1))
      ((Computable.intervalVerifier zeroZero ambient 1 1 (by decide)).run shiftStart original
        (shiftProver ambient)))}[
        ∃ t, obs.2.2 = some t ∧
          indexedRelation zeroZero _ t.1
            (Computable.toPolynomial (t.2 ()).val (t.2 ()).property)] ≤ 1 / 17 := by
  have h := Computable.interval_soundness zeroZero ambient init impl 1 1 rfl shiftStart original
    (shiftProver ambient) shiftStart_false
  refine h.trans (le_of_eq ?_)
  rw [ZMod.card, Nat.cast_one, one_mul, Nat.cast_one, ENNReal.coe_div (by norm_num)]
  norm_num

end SuffixSoundness

end Sumcheck.ComputableTest

namespace Sumcheck.ComputableTest.Universes

open Polynomial PFunctor FreeM Interaction Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec Sumcheck


variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {deg n d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)
  {I : Type} {A : I → Type} (inputs : OracleFamily I A)
  {M : Type} {eval : M → R → R}

/-- Construction over an input family with queries in `Type`. -/
def verifierAtQueryUniverse :
    OracleVerifier ambient (protocolOn R M eval n) (Sumcheck.Spec.StatementRound R n 0)
      (fun _ => Sumcheck.Spec.StatementRound R n (Fin.last n)) inputs (fun _ => inputs) :=
  verifierOn R deg n D ambient M eval inputs

omit [SampleableType R] in
/-- The final decision law accepts queries in `Type` through an ordinary import. -/
theorem simulate_decision {f : M → R⦃≤ deg⦄[X]}
    (hf : ∀ x r, eval x r = (f x).val.eval r) {κ : Type} {target : OracleSpec κ}
    (amb : QueryImpl ambient (OracleComp target)) (stmt : Sumcheck.Spec.StatementRound R n 0)
    (data : ∀ i, A i) (tr : Transcript oracleSig (protocolOn R M eval n)) :
    simulateQ (QueryImpl.addLift amb ((pathBundle inputs (protocolOn R M eval n)
      tr.path).answer (data, oracleMessages _ tr)))
      ((verifierAtQueryUniverse (deg := deg) D ambient inputs).decide stmt _ (toView _ tr)).run =
      (pure (legacyVerdict R deg n D ambient stmt (decodeTranscript n (polyTranscript f n tr))) :
        OracleComp target _) :=
  simulateQ_decideOn D inputs hf amb stmt data tr

/-- The review's constant-evaluation constructor also accepts bundle queries in `Type`. -/
example (domain : Fin 1 ↪ R) {J : Type} {B : J → Type}
    (family : OracleFamily J B) :
    OracleVerifier emptySpec (protocolOn R R (fun x _ => x) 1)
      (Sumcheck.Spec.StatementRound R 1 0)
      (fun _ => Sumcheck.Spec.StatementRound R 1 (Fin.last 1)) family (fun _ => family) :=
  verifierOn R 1 1 domain emptySpec R (fun x _ => x) family

end Sumcheck.ComputableTest.Universes

/-! The executable definitions are computable, and the theorems use only the standard axioms. -/

run_cmd do
  let env ← Lean.getEnv
  for decl in [``Sumcheck.Computable.verifier, ``Sumcheck.Computable.observe,
      ``Sumcheck.Computable.honestProver, ``Sumcheck.Computable.honestFrom,
      ``Sumcheck.Computable.honestMessage, ``Sumcheck.Computable.nextState,
      ``Sumcheck.verifierOn, ``Interaction.sampler] do
    if Lean.isNoncomputable env decl then
      throwError "{decl} is noncomputable"
  for decl in [``Sumcheck.run_eq_interpret, ``Sumcheck.experiment_renameQueries,
      ``Sumcheck.transportDraw_challengeQueryImpl,
      ``Sumcheck.Computable.interpretProver_honestProver,
      ``Sumcheck.Computable.support_completeness,
      ``Sumcheck.Computable.perfectCompleteness, ``Sumcheck.Computable.soundness,
      ``Sumcheck.Computable.interval_run_eq_interpret,
      ``Sumcheck.Computable.interval_support_completeness,
      ``Sumcheck.Computable.interval_perfectCompleteness,
      ``Sumcheck.Computable.interval_measureCompleteness,
      ``Sumcheck.Computable.interval_soundness,
      ``Sumcheck.verifier_run_full_interval, ``Sumcheck.Computable.full_run_interval,
      ``Sumcheck.ComputableTest.zero_interval_verdict,
      ``Sumcheck.ComputableTest.spec_polynomialFamily_eq,
      ``Sumcheck.ComputableTest.shiftStart_false, ``Sumcheck.ComputableTest.shift_sum,
      ``Sumcheck.ComputableTest.shift_eval, ``Sumcheck.ComputableTest.shift_endpoint_iff,
      ``Sumcheck.ComputableTest.suffix_soundness_one_seventeenth] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
