/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Interval

/-! # Native suffix Sumcheck soundness

The round-by-round state records the truth of the remaining indexed sum. The generic oracle
verifier implication bounds the actual run by the number of remaining challenges times the
single-round polynomial agreement bound.
-/

@[expose] public section

namespace Sumcheck.Core
open scoped ENNReal NNReal
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec

variable {R : Type} [CommSemiring R] [DecidableEq R] {deg n d : ℕ} (D : Fin d → R)

/-- The indexed relation at any starting round, with the original polynomial as oracle data. -/
def intervalInputProblem (i : Fin (n + 1)) : StatementProblem
    (RoundStatement R n i × (∀ j, PolynomialData R n deg j)) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ stmt _ := indexedRelation D i stmt.1 (stmt.2 ())
  rel_admissible _ _ _ _ := trivial

/-- The endpoint relation, with the same polynomial retained as output oracle data. -/
def intervalOutputProblem (stop : Fin (n + 1)) (count : ℕ) :
    PathProblem (protocol R deg count)
      (fun _ => RoundStatement R n stop × (∀ j, PolynomialData R n deg j)) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ stmt _ := indexedRelation D stop stmt.1 (stmt.2 ())
  rel_admissible _ _ _ _ := trivial

/-- A valid accepting decision returns a true endpoint claim of the actual transcript. -/
theorem interval_validAcceptance {ι σ : Type} {ambient : OracleSpec ι}
    (impl : QueryImpl ambient (StateT σ ProbComp)) (start count : ℕ)
    (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩ × (∀ i, PolynomialData R n deg i))
    (tr : PathAlong oracleSig (protocol R deg count)) :
    (intervalVerifier R deg n D ambient start count bound).validAcceptance impl stmt tr
        ((intervalOutputProblem D ⟨count + start, by omega⟩ count).language
          (projectPathAlong oracleSig _ tr)) →
      ∃ t, intervalVerdict D count (intervalInitial start count bound stmt.1) tr = some t ∧
        indexedRelation D _ t (stmt.2 ()) := by
  unfold OracleVerifier.validAcceptance
  dsimp only
  rw [simulateQ_intervalVerifier_decide]
  intro h
  obtain ⟨state, hs⟩ := h
  classical
  by_contra hf
  simp [intervalVerifier, intervalOutputProblem, Problem.language, OracleMap.fst, hf] at hs

/-- The suffix state follows the parent's native indexed remaining-sum invariant. -/
noncomputable def intervalStateFunction {ι σ : Type} {ambient : OracleSpec ι}
    (start count : ℕ) (impl : QueryImpl ambient (StateT σ ProbComp)) :
    StateFunction oracleSig (protocol R deg count)
      (RoundStatement R (count + start) ⟨start, by omega⟩ ×
        (∀ i, PolynomialData R (count + start) deg i))
      ((intervalInputProblem D ⟨start, by omega⟩).admissible ())
      ((intervalInputProblem D ⟨start, by omega⟩).language ())
      (fun stmt tr =>
        (intervalVerifier R deg (count + start) D ambient start count (by omega)).validAcceptance
          impl stmt tr
        ((intervalOutputProblem D (Fin.last (count + start)) count).language
          (projectPathAlong oracleSig _ tr))) where
  toFun sp history stmt := foldPrefix (indexedGood D (stmt.2 ())) (fun _ => indexedNext D)
    count (some (intervalInitial start count (by omega) stmt.1).toIndexed) sp history
  root stmt _ h := by
    refine ⟨(), ?_⟩
    change indexedRelation D _ stmt.1 (stmt.2 ())
    cases count with
    | zero => simpa [foldPrefix, indexedGood, intervalInitial, IntervalClaim.toIndexed] using h
    | succ count =>
      simpa [foldPrefix, indexedGood, intervalInitial, IntervalClaim.toIndexed] using h
  send sp history stmt howner hfalse x := by
    rwa [foldPrefix_send _ _ _ _ _ _ howner x]
  leaf sp history stmt hfalse hacc := by
    obtain ⟨t, ht, hrel⟩ := interval_validAcceptance D impl start count (by omega) stmt _ hacc
    rw [intervalVerdict_eq_indexed] at ht
    exact hfalse ((foldPrefix_indexed_leaf D (stmt.2 ()) count _ sp history).mpr
      ⟨t, ht, (indexedRelation_last D t (stmt.2 ())).mp hrel⟩)

/-- Every suffix has native round-by-round soundness, with one polynomial error per challenge. -/
theorem intervalVerifier_rbrSoundness [IsDomain R] [Fintype R] [SampleableType R]
    {ι σ : Type} (ambient : OracleSpec ι) (impl : QueryImpl ambient (StateT σ ProbComp))
    (start count : ℕ) (finish : start + count = n) :
    (intervalVerifier R deg n D ambient start count finish.le).rbrSoundness impl
      (intervalInputProblem D ⟨start, by omega⟩)
      (intervalOutputProblem D ⟨count + start, by omega⟩ count)
      (indexedDraw (R := R) (deg := deg) count)
      (fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  have hn : n = count + start := by omega
  subst hn
  refine ⟨intervalStateFunction D start count impl, fun stmt _ _ a rest sp h history => ?_⟩
  exact foldPrefix_indexed_flip_le D (stmt.2 ()) count _ sp h history

/-- The actual suffix run is sound with error `count * (deg / |R|)`, at every start. -/
theorem intervalVerifier_soundness [IsDomain R] [Fintype R] [SampleableType R]
    {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (start count : ℕ) (finish : start + count = n) :
    (intervalVerifier R deg n D ambient start count finish.le).soundness init impl
      (indexedDraw (R := R) (deg := deg) count)
      (intervalInputProblem D ⟨start, by omega⟩)
      (intervalOutputProblem D ⟨count + start, by omega⟩ count)
      ((count : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  simpa only [nsmul_eq_mul] using
    (OracleVerifier.soundness_of_rbrSoundness_uniform (init := init)
      (intervalVerifier_rbrSoundness D ambient impl start count finish) (fun _ => le_rfl)
      (fun path => (card_challengeNodesOn_protocol count path).le))

/-- A list domain keeps repetitions in the native suffix verifier. -/
theorem intervalVerifier_soundness_list [IsDomain R] [Fintype R] [SampleableType R]
    (domain : List R) {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (start count : ℕ) (finish : start + count = n) :
    (intervalVerifier R deg n domain.get ambient start count finish.le).soundness init impl
      (indexedDraw (R := R) (deg := deg) count)
      (intervalInputProblem domain.get ⟨start, by omega⟩)
      (intervalOutputProblem domain.get ⟨count + start, by omega⟩ count)
      ((count : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) :=
  intervalVerifier_soundness domain.get ambient init impl start count finish

/-- The injective-domain form is a specialization of native indexed suffix soundness. -/
theorem intervalVerifier_soundness_injective [IsDomain R] [Fintype R] [SampleableType R]
    (embedding : Fin d ↪ R) {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (start count : ℕ) (finish : start + count = n) :
    (intervalVerifier R deg n (⇑embedding) ambient start count finish.le).soundness init impl
      (indexedDraw (R := R) (deg := deg) count)
      (intervalInputProblem (⇑embedding) ⟨start, by omega⟩)
      (intervalOutputProblem (⇑embedding) ⟨count + start, by omega⟩ count)
      ((count : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) :=
  intervalVerifier_soundness (⇑embedding) ambient init impl start count finish


/-- The full native run is the interval from zero through all variables, after identifying
its endpoint with `n`. -/
theorem intervalVerifier_full_run {ι : Type} (ambient : OracleSpec ι)
    (stmt : RoundStatement R n 0) (data : ∀ i, PolynomialData R n deg i)
    {Out : PathAlong oracleSig (protocol R deg n) → Type}
    (prover : Prover oracleSig ambient (protocol R deg n) Out) :
    (intervalVerifier R deg n D ambient 0 n (by omega)).run stmt data prover =
      (indexedVerifier R deg n D ambient).run stmt data prover := by
  erw [intervalVerifier_run, foldVerifier_run, indexedVerifier_run]
  refine bind_congr fun result => ?_
  rcases result with ⟨tr, out, u⟩
  exact congrArg (fun v : Option (RoundStatement R n (Fin.last n)) =>
    (pure ⟨tr, out, v.map (fun t => (t, data))⟩ :
      OracleComp (ambient + challengeSpec oracleSig (protocol R deg n))
        (Observation oracleSig (protocol R deg n) Out
          (fun _ => RoundStatement R n (Fin.last n) × (∀ i, PolynomialData R n deg i)))))
    (intervalVerdict_eq_indexed D n (intervalInitial 0 n (by omega) stmt) tr)

end Sumcheck.Core
