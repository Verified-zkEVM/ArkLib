/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Core.Completeness
import Mathlib.Algebra.Field.ZMod

/-!
# Perfect completeness of Sumcheck in the interaction layer

The completeness theorem applies with uniform challenges over a concrete field, the honest
event has mass one, and on a satisfied claim the honest verdict accepts the prover's output on
every challenge.
-/

namespace Sumcheck.Core.CompletenessTest

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens OracleComp OracleSpec
open scoped ENNReal

abbrev F := ZMod 5

/-- The evaluation domain `{0, 1}`. -/
def D₂ : Fin 2 ↪ F := ⟨fun i => (i.val : F), by decide⟩

variable {ι : Type} (ambient : OracleSpec ι) {σ : Type} (init : ProbComp σ)
  (impl : QueryImpl ambient (StateT σ ProbComp))

/-- Three rounds of degree two over `ZMod 5` with uniform challenges. -/
example :
    letI : MeasurableSpace (HonestObservation F 2 3) := ⊤
    completeness ((verifier F 2 3 D₂ ambient).classicalModel init impl
        (challengeQueryImpl oracleSig (protocol F 2 3)))
      (relationProblem F 2 3 D₂ 0) (relationProblem F 2 3 D₂ (Fin.last 3))
      (judgement F 2 3 D₂) (fun x _ => honestProver D₂ x.1 x.2) 0 :=
  perfectCompleteness_uniform D₂ ambient init impl

/-- On a satisfied claim the honest event has mass one in the uniform-challenge experiment. -/
example (stmt : Spec.StatementRound F 2 0) (oStmt : ∀ i, Spec.OracleStatement F 2 1 i)
    (h : ((stmt, oStmt), ()) ∈ Spec.relationRound F 2 1 D₂ 0) :
    letI : MeasurableSpace (HonestObservation F 1 2) := ⊤
    1 ≤ 𝒟[experiment init impl (challengeQueryImpl oracleSig (protocol F 1 2))
      ((verifier F 1 2 D₂ ambient).run stmt oStmt (honestProver D₂ stmt oStmt))]
        {obs | (judgement F 1 2 D₂).honest obs} := by
  let : MeasurableSpace (HonestObservation F 1 2) := ⊤
  exact le_of_eq_of_le (tsub_zero 1).symm
    ((perfectCompleteness_uniform D₂ ambient init impl).2 (stmt, oStmt) () h)

/-- On a satisfied claim the legacy verdict accepts the honest output statement and the output
oracle is the input polynomial, for every choice of challenges. -/
example (stmt : Spec.StatementRound F 2 0) (oStmt : ∀ i, Spec.OracleStatement F 2 1 i)
    (h : ((stmt, oStmt), ()) ∈ Spec.relationRound F 2 1 D₂ 0) (chals : Fin 2 → F) :
    legacyVerdict F 1 2 D₂ ambient stmt (decodeTranscript 2 (honestTranscript D₂ stmt oStmt chals))
        = some (honestOutput D₂ stmt oStmt chals).1.1 ∧
      (honestOutput D₂ stmt oStmt chals).1.2 = oStmt :=
  ⟨(legacyVerdict_honestTranscript D₂ ambient stmt oStmt h chals).1,
    (legacyVerdict_honestTranscript D₂ ambient stmt oStmt h chals).2.1⟩

/-- The zero-polynomial claim with target zero satisfies the round-`0` relation, so the theorem
is not vacuous on it. -/
example (stmt : Spec.StatementRound F 2 0) (htarget : stmt.target = 0) :
    (relationProblem F 1 2 D₂ 0).rel () (stmt, fun _ => 0) () := by
  obtain ⟨target, chs⟩ := stmt
  change target = 0 at htarget
  subst htarget
  simp [relationProblem, Spec.relationRound]

end Sumcheck.Core.CompletenessTest

run_cmd do
  for decl in [``Sumcheck.Core.verdict_foldTranscript, ``Sumcheck.Core.honestRel_step,
      ``Sumcheck.Core.legacyVerdict_honestTranscript, ``Sumcheck.Core.perfectCompleteness,
      ``Sumcheck.Core.perfectCompleteness_uniform] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
