/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.BehaviorComposition
import ArkLib.ProofSystem.Sumcheck.ComputableSoundness
import ArkLib.ProofSystem.Sumcheck.IntervalRoundSoundness
import ArkLib.ProofSystem.Sumcheck.IntervalExecution
import ArkLib.ProofSystem.Sumcheck.IntervalCompleteness
import ArkLib.ProofSystem.Sumcheck.IntervalSoundness
import ArkLib.ProofSystem.Sumcheck.FoldComposition
import ArkLib.ProofSystem.Sumcheck.Projection
import ArkLib.ProofSystem.Sumcheck.IntervalAdaptive
import ArkLib.ProofSystem.Sumcheck.Behavior
import ArkLib.ProofSystem.Sumcheck.InterpretedExecution
import ArkLibTest.ProofSystem.Sumcheck.Effects

/-! # Interaction-layer interval boundary and security regressions -/

/-! ## Public interval append on the effect fixture -/

namespace Sumcheck.EffectsTest
open Polynomial PFunctor FreeM Interaction Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec

noncomputable section


/-- The Effects fixture's true starting claim `1`, as an interval round statement. -/
def intervalStart : RoundStatement K 2 ⟨0, by decide⟩ := ⟨1, Fin.elim0⟩

/-- The two-round interval verdict on the adaptive prover's transcript. -/
theorem interval_verdict_adaptive (a b r s : K) :
    intervalVerdict (⇑D₀) 2 (intervalInitial 0 2 (by decide) intervalStart)
      (consTranscript (affine a 1) r (consTranscript (affine (b + a) (a * r + 1)) s ⟨⟩)) =
      some ⟨(b + a) * s + (a * r + 1), ![r, s]⟩ := by
  unfold intervalVerdict
  rw [foldVerdict_succ, roundVerdict_intervalCheck, ite_eq_left (by
    simp [affine, Interpreted.message, consTranscript, intervalInitial, intervalStart])]
  dsimp only [Option.bind_some]
  rw [foldVerdict_succ, roundVerdict_intervalCheck, ite_eq_left (by
    simp [affine, Interpreted.message, Interpreted.challenge, Interpreted.tail, consTranscript,
      IntervalClaim.next, intervalInitial, intervalStart])]
  simp only [Nat.reduceAdd, Nat.add_zero, Fin.reduceFinMk, IntervalClaim.next, intervalStart,
    Fin.zero_eta, Fin.isValue, intervalInitial, affine, consTranscript, liftBind_eq, bind_eq_bind,
    Interpreted.challenge, Interpreted.message, IntervalClaim.index, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, Fin.succ_zero_eq_one, Nat.reduceMod, Fin.mk_one, Fin.succ_one_eq_two,
    Interpreted.tail, map_add, map_mul, map_one, eval_add, eval_mul, eval_C, eval_X, eval_one,
    foldVerdict, Interpreted.verdict, IntervalClaim.finish, Option.bind_some, Fin.cast_refl,
    CompTriple.comp_eq, Option.some.injEq, RoundStatement.mk.injEq, true_and]
  exact funext fun i => by fin_cases i <;> rfl

/-- The interval run maps the verdict over the protocol run, for every prover. -/
theorem interval_run_eq (P : Prover oracleSig events (protocol K 1 2) (fun _ => Unit)) :
    (intervalVerifier K 1 2 (⇑D₀) events 0 2 (by decide)).run intervalStart
      (fun _ => original) P =
      (fun x => (⟨x.1, x.2.1, (intervalVerdict (⇑D₀) 2
          (intervalInitial 0 2 (by decide) intervalStart) x.1).map
            fun t => (t, fun _ => original)⟩ :
          Outcome oracleSig (protocol K 1 2) (fun _ => Unit)
            (fun _ => RoundStatement K 2 ⟨2 + 0, by decide⟩ × ∀ i, PolynomialData K 2 1 i)))
              <$> Interaction.TwoParty.Lens.run (protocol K 1 2) (P.simulate liftEvents)
                (sampler oracleSig (protocol K 1 2) drawE) := by
  rw [intervalVerifier_run, Interpreted.verifier_run, map_eq_bind_pure_comp]
  refine bind_congr fun x => ?_
  rfl

/-- The full two-round interval run on the adaptive prover, in protocol order. -/
theorem interval_two_rounds :
    (intervalVerifier K 1 2 (⇑D₀) events 0 2 (by decide)).run intervalStart
      (fun _ => original) adaptive = (do
    let a ← eventE 0
    let r : K ← drawE (headNode 1)
    let b ← eventE 2
    let s : K ← tailDraw drawE (headNode 0)
    let _ ← eventE 3
    pure (⟨consTranscript (affine a 1) r (consTranscript (affine (b + a) (a * r + 1)) s ⟨⟩), (),
      some (⟨(b + a) * s + (a * r + 1), ![r, s]⟩, fun _ => original)⟩ :
      Outcome oracleSig (protocol K 1 2) (fun _ => Unit)
        (fun _ => RoundStatement K 2 ⟨2 + 0, by decide⟩ × ∀ i, PolynomialData K 2 1 i))) := by
  rw [interval_run_eq]
  erw [run_adaptive]
  refine (_root_.map_bind _ _ _).trans (bind_congr fun a => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun r => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun b => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun s => ?_)
  refine (_root_.map_bind _ _ _).trans (bind_congr fun _ => ?_)
  refine (map_pure _ _).trans ?_
  dsimp only
  erw [interval_verdict_adaptive]
  rfl

/-- The public interval append of two one-round interval verifiers returns target `7` and records
the order `[0, 1, 2, 1, 3]`, as frozen `Protocol.lean` #7 does for the composed run. -/
theorem public_append_record :
    (simulateQ record ((fun obs => obs.2.2.map fun t => t.1.target) <$>
      ((intervalVerifier K 1 2 (⇑D₀) events 0 1 (by decide)).append
        (fun _ => intervalVerifier K 1 2 (⇑D₀) events (1 + 0) 1 (by decide))
        (publicIntervalCompatibility events (⇑D₀) 0 1 (by decide))).run intervalStart
          (fun _ => original) adaptive)).run [] =
      (some 7, [0, 1, 2, 1, 3]) := by
  rw [run_append_public_intervalVerifier, Functor.map_map]
  erw [interval_two_rounds]
  rfl

end

end Sumcheck.EffectsTest

namespace Sumcheck.IntervalTest
open Polynomial MvPolynomial PFunctor FreeM Interaction Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec

noncomputable section

/-- An unused ambient oracle for deterministic interaction-layer executions. -/
abbrev ambient : OracleSpec Unit := Unit →ₒ Unit

/-- A repeated indexed domain, with both occurrences retained. -/
def repeated : Fin 2 → ℕ := fun _ => 0

/-- A constant honest message over the natural numbers. -/
def zeroMessage : ℕ⦃≤ 0⦄[X] := ⟨0, by simp⟩

/-- The zero input polynomial in three variables. -/
def zeroInput : ℕ⦃≤ 0⦄[X Fin 3] := ⟨0, by simp⟩

/-- A nonzero starting round with its earlier challenge preserved. -/
def initial : RoundStatement ℕ 3 1 := ⟨0, ![7]⟩

/-- A deterministic one-round handler answers with `3` and never samples uniformly. -/
def oneHandler : QueryImpl (ambient + challengeSpec oracleSig (protocol ℕ 0 1)) Id :=
  QueryImpl.addLift ⟨fun _ => (pure () : Id Unit)⟩ (indexedRoundDraw (deg := 0) (pure 3 : Id ℕ))

/-- The nonzero-start transcript accepts and appends its challenge to the earlier prefix. -/
theorem nonzero_verdict :
    intervalVerdict repeated 1 (intervalInitial 1 1 (by decide : 1 + 1 ≤ 3) initial)
      (roundTranscript zeroMessage 3) = some ⟨0, ![7, 3]⟩ := by
  unfold intervalVerdict
  rw [foldVerdict_succ, roundVerdict_intervalCheck]
  simp [repeated, zeroMessage, Interpreted.message, Interpreted.challenge, roundTranscript,
    foldVerdict, Interpreted.verdict, IntervalClaim.finish, IntervalClaim.next, IntervalClaim.index,
    intervalInitial, initial]

/-- The actual interval run preserves its private output and the earlier challenge. -/
theorem nonzero_run :
    simulateQ oneHandler ((intervalVerifier ℕ 0 3 repeated ambient 1 1 (by decide)).run
      initial (fun _ => zeroInput) (committedProver ambient zeroMessage (fun _ => 37))) =
      ⟨roundTranscript zeroMessage 3, 37, some (⟨0, ![7, 3]⟩, fun _ => zeroInput)⟩ := by
  rw [intervalVerifier_run_one, simulateQ_map]
  change (⟨roundTranscript zeroMessage 3, 37,
    (intervalVerdict repeated 1 (intervalInitial 1 1 (by decide) initial)
      (roundTranscript zeroMessage 3)).map (fun t => (t, fun _ => zeroInput))⟩ :
      Outcome oracleSig (protocol ℕ 0 1) (fun _ => ℕ)
        (fun _ => RoundStatement ℕ 3 2 × (∀ i, PolynomialData ℕ 3 0 i))) = _
  rw [nonzero_verdict]
  rfl

/-- A bad claim at a nonzero start rejects even with a correct degree-bounded message. -/
theorem nonzero_rejects :
    intervalVerdict repeated 1 (intervalInitial 1 1 (by decide : 1 + 1 ≤ 3)
      (⟨1, ![7]⟩ : RoundStatement ℕ 3 1)) (roundTranscript zeroMessage 3) = none := by
  unfold intervalVerdict
  rw [foldVerdict_succ, roundVerdict_intervalCheck]
  simp [repeated, zeroMessage, Interpreted.message, roundTranscript, intervalInitial]

/-- Zero rounds accept the unchanged endpoint claim without issuing a challenge. -/
theorem zero_count :
    (intervalVerdict repeated (deg := 0) 0
      (intervalInitial 1 0 (by decide : 1 + 0 ≤ 3) initial) PUnit.unit).map
        (fun t => (t.target, t.challenges 0)) = some (0, 7) := rfl

/-- The actual empty interval executes the prover's leaf action and accepts the same claim. -/
theorem zero_run :
    ((fun obs => (obs.2.1, obs.2.2.map (fun t => (t.1.target, t.1.challenges 0)))) <$>
      (intervalVerifier ℕ 0 3 repeated ambient 1 0 (by decide)).run (Out := fun _ => ℕ)
        initial (fun _ => zeroInput)
        (pure 43 : OracleComp ambient ℕ)) = pure (43, some (0, 7)) := by
  rw [intervalVerifier_run_zero]
  simp only [simulateQ_pure, LawfulApplicative.map_pure]
  rfl

/-- The constant-one input in two variables with individual degree zero. -/
def oneInput : ℕ⦃≤ 0⦄[X Fin 2] := ⟨1, by
  refine (MvPolynomial.mem_restrictDegree _ _ _).mpr fun s hs i => ?_
  rw [MvPolynomial.support_one] at hs
  simp_all⟩

/-- A `projectedMap` query over the repeated domain `[0, 0]` with one variable left to sum over
reads the constant-one input twice and returns `2`. -/
theorem repeated_projectedMap (r : ℕ) :
    simulateQ ((polynomialFamily ℕ 2 0).behaviorOfRealizations fun _ => oneInput)
      ((projectedMap (deg := 0) repeated (0 : Fin 2) Fin.elim0).impl ⟨(), r⟩) = (2 : ℕ) := by
  refine (simulateQ_projectedQuery (deg := 0) repeated (0 : Fin 2) Fin.elim0
    (fun _ => oneInput) r).trans ?_
  simp [projectedRoundPolynomial, oneInput, MvPolynomial.evalExcept]

/-- Generic interaction-layer suffix soundness retains arbitrary nonzero starts and zero counts. -/
example {R : Type} [CommSemiring R] [DecidableEq R] [IsDomain R] [Fintype R]
    [SampleableType R] {n deg d : ℕ} (D : Fin d → R) {ι σ : Type} (a : OracleSpec ι)
    (init : ProbComp σ) (impl : QueryImpl a (StateT σ ProbComp))
    (start count : ℕ) (finish : start + count = n) :
    (intervalVerifier R deg n D a start count finish.le).soundness init impl
      (indexedDraw (R := R) (deg := deg) count)
      (intervalInputProblem D ⟨start, by omega⟩)
      (intervalOutputProblem D ⟨count + start, by omega⟩ count)
      ((count : ENNReal) * (((deg : NNReal) / Fintype.card R : NNReal) : ENNReal)) :=
  intervalVerifier_soundness D a init impl start count finish

end

run_cmd
  for decl in [``Sumcheck.intervalVerifier, ``Sumcheck.intervalVerifier_rbrSoundness,
      ``Sumcheck.intervalVerifier_soundness, ``Sumcheck.intervalVerifier_soundness_list,
      ``Sumcheck.intervalVerifier_soundness_injective,
      ``Sumcheck.intervalVerifier_supportCompleteness,
      ``Sumcheck.intervalVerifier_perfectCompleteness,
      ``Sumcheck.Computable.interpret_intervalHonestProver,
      ``Sumcheck.Computable.execute_perfectCompleteness,
      ``Sumcheck.Computable.execute_soundness,
      ``Sumcheck.intervalRoundExecute_soundness,
      ``Sumcheck.intervalRoundExecute_measureSoundness,
      ``Sumcheck.run_append_behaviorIntervalVerifier,
      ``Sumcheck.intervalVerifier_full_run, ``Sumcheck.run_append_intervalVerifier,
      ``Sumcheck.run_append_public_intervalVerifier,
      ``Sumcheck.intervalVerifier_measureCompleteness,
      ``Sumcheck.intervalVerifier_adaptive_perfectCompleteness,
      ``Sumcheck.intervalVerifier_evaluation,
      ``Sumcheck.behaviorRoundRelation_last,
      ``Sumcheck.behaviorIntervalVerifier_run_zero,
      ``Sumcheck.Interpreted.run_transport,
      ``Sumcheck.projectedMap, ``Sumcheck.simulateQ_projectedQuery,
      ``Sumcheck.projectedQuery_isChargeBound, ``OracleVerifier.run_eq_decideWith,
      ``Sumcheck.Impl.Computable.indexedRoundPolynomial_toPoly,
      ``Sumcheck.Computable.indexedRoundPolynomial_toPoly,
      ``Sumcheck.Computable.projectedMessage_evaluate,
      ``Sumcheck.projectedExecute_honest_eq, ``Sumcheck.projectedExecute_closed,
      ``Sumcheck.projectedExecute_related, ``Sumcheck.simulateQ_projectedInput,
      ``Sumcheck.IntervalTest.nonzero_run,
      ``Sumcheck.IntervalTest.nonzero_rejects, ``Sumcheck.IntervalTest.zero_run,
      ``Sumcheck.IntervalTest.repeated_projectedMap,
      ``Sumcheck.EffectsTest.public_append_record] do
    for ax in ← Lean.collectAxioms decl do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.IntervalTest
