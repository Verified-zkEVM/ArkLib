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
every challenge. On the explicit polynomial `X₀` with target `1`, the run accepts with the
expected final target, challenge history and output oracle.
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
        (@challengeQueryImpl _ oracleSig (protocol F 2 3) (challengeSampleable F 2 3)))
      (relationProblem F 2 3 D₂ 0) (relationProblem F 2 3 D₂ (Fin.last 3))
      (judgement F 2 3 D₂) (fun x _ => honestProver D₂ x.1 x.2) 0 :=
  perfectCompleteness_uniform D₂ ambient init impl

/-- On a satisfied claim the honest event has mass one in the uniform-challenge experiment. -/
example (stmt : Spec.StatementRound F 2 0) (oStmt : ∀ i, Spec.OracleStatement F 2 1 i)
    (h : ((stmt, oStmt), ()) ∈ Spec.relationRound F 2 1 D₂ 0) :
    letI : MeasurableSpace (HonestObservation F 1 2) := ⊤
    1 ≤ 𝒟[experiment init impl (@challengeQueryImpl _ oracleSig (protocol F 1 2)
      (challengeSampleable F 1 2))
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

/-! ## A concrete accepting run

The polynomial `X₀` in one variable over `ZMod 5`, summed over the domain `{0, 1}`, has target
`0 + 1 = 1`. Its honest round polynomial is `X`, so on the challenge `c` the run accepts with
final target `c`, challenge history `c` and the output oracle `X₀`.
-/

/-- The polynomial `X₀` in one variable, of individual degree at most one. -/
noncomputable def polyX : Spec.OracleStatement F 1 1 () :=
  ⟨MvPolynomial.X 0, by
    have : Nontrivial F := ⟨⟨0, 1, by decide⟩⟩
    rw [MvPolynomial.mem_restrictDegree]
    intro s hs i
    rw [MvPolynomial.support_X, Finset.mem_singleton] at hs
    subst hs
    rw [Finsupp.single_apply]
    split_ifs <;> omega⟩

/-- The claim that `X₀` sums to `0 + 1 = 1` over `{0, 1}`. -/
def stmtX : Spec.StatementRound F 1 0 := ⟨1, Fin.elim0⟩

/-- The honest round polynomial of `X₀` is the identity: it evaluates every challenge to
itself. -/
theorem honestMessage_X_eval (c : F) :
    (honestMessage D₂ 0 (initState stmtX fun _ => polyX)).val.eval c = c := by
  change (∑ x ∈ Fintype.piFinset (fun _ : Fin 0 => Finset.univ.map D₂),
    (MvPolynomial.X 0 : MvPolynomial (Fin 1) F).evalExcept 0
      (Spec.SingleRound.roundSuffix F 1 0 Fin.elim0 x)).eval c = c
  simp only [Fintype.piFinset_of_isEmpty, Fintype.sum_unique]
  rw [MvPolynomial.eval_evalExcept, MvPolynomial.eval_X, Fin.insertNth_apply_same]

/-- The claim `(stmtX, X₀)` lies in the round-`0` Sumcheck relation. -/
theorem relation_X : (relationProblem F 1 1 D₂ 0).rel () (stmtX, fun _ => polyX) () := by
  refine (Spec.SingleRound.projected_sum_iff_relationRound F 1 1 D₂ 0 stmtX polyX).1 ?_
  rw [Finset.sum_map_toList]
  change ∑ x ∈ Finset.univ.map D₂,
    (honestMessage D₂ 0 (initState stmtX fun _ => polyX)).val.eval x = 1
  simp only [honestMessage_X_eval, Finset.sum_map, Fin.sum_univ_two]
  rfl

/-- The honest prover's output on `X₀` with challenge `c`: target `c`, challenge history `c`,
and the input polynomial. -/
theorem honestOutput_X (c : F) :
    honestOutput D₂ stmtX (fun _ => polyX) (fun _ => c) =
      ((⟨c, fun _ => c⟩, fun _ => polyX), ()) := by
  change (((⟨(honestMessage D₂ 0 (initState stmtX fun _ => polyX)).val.eval c, _⟩ :
    Spec.StatementRound F 1 (Fin.last 1)), fun _ => polyX), ()) = _
  rw [honestMessage_X_eval]
  rfl

/-- On `X₀` with challenge `c`, the completeness lemma gives acceptance of the statement with
target `c` and challenge history `c`, which lies in the final relation. -/
theorem legacyVerdict_honest_X (c : F) :
    legacyVerdict F 1 1 D₂ ambient stmtX
        (decodeTranscript 1 (honestTranscript D₂ stmtX (fun _ => polyX) fun _ => c)) =
      some ⟨c, fun _ => c⟩ ∧
      (((⟨c, fun _ => c⟩, fun _ => polyX), ()) ∈ Spec.relationRound F 1 1 D₂ (Fin.last 1)) := by
  obtain ⟨hv, -, hr⟩ := legacyVerdict_honestTranscript D₂ ambient stmtX _ relation_X fun _ => c
  rw [honestOutput_X] at hv hr
  exact ⟨hv, hr⟩

/-- The honest execution on `X₀`: after the challenge `c` is drawn, the prover outputs target
`c`, challenge history `c` and the oracle `X₀`, and the verifier accepts exactly that statement
with the oracle `X₀`. -/
theorem run_honest_X :
    (verifier F 1 1 D₂ ambient).run stmtX (fun _ => polyX)
        (honestProver D₂ stmtX fun _ => polyX) =
      (fun chals => (⟨honestTranscript D₂ stmtX (fun _ => polyX) chals,
        ((⟨chals 0, fun _ => chals 0⟩, fun _ => polyX), ()),
        some (⟨chals 0, fun _ => chals 0⟩, fun _ => polyX)⟩ : HonestObservation F 1 1)) <$>
        drawChallenges 1 (fun c =>
          liftM ((ambient + challengeSpec oracleSig (protocol F 1 1)).query (.inr c))) := by
  rw [run_verifier_honestProver]
  refine congrArg (· <$> _) (funext fun chals => ?_)
  have hc : chals = fun _ => chals 0 := funext fun j => by rw [Subsingleton.elim j 0]
  have hv := (legacyVerdict_honest_X ambient (chals 0)).1
  have ho := honestOutput_X (chals 0)
  rw [← hc] at hv ho
  simp only [hv, ho, Option.map_some]

/-- Perfect completeness applies to the claim `(stmtX, X₀)`: the honest event has mass one in
the uniform-challenge experiment. -/
example :
    letI : MeasurableSpace (HonestObservation F 1 1) := ⊤
    1 ≤ 𝒟[experiment init impl (@challengeQueryImpl _ oracleSig (protocol F 1 1)
      (challengeSampleable F 1 1))
      ((verifier F 1 1 D₂ ambient).run stmtX (fun _ => polyX)
        (honestProver D₂ stmtX fun _ => polyX))]
        {obs | (judgement F 1 1 D₂).honest obs} := by
  let : MeasurableSpace (HonestObservation F 1 1) := ⊤
  exact le_of_eq_of_le (tsub_zero 1).symm
    ((perfectCompleteness_uniform D₂ ambient init impl).2 (stmtX, fun _ => polyX) () relation_X)

end Sumcheck.Core.CompletenessTest

run_cmd do
  for decl in [``Sumcheck.Core.verdict_foldTranscript, ``Sumcheck.Core.honestRel_step,
      ``Sumcheck.Core.legacyVerdict_honestTranscript, ``Sumcheck.Core.perfectCompleteness,
      ``Sumcheck.Core.perfectCompleteness_uniform,
      ``Sumcheck.Core.CompletenessTest.relation_X, ``Sumcheck.Core.CompletenessTest.honestOutput_X,
      ``Sumcheck.Core.CompletenessTest.legacyVerdict_honest_X,
      ``Sumcheck.Core.CompletenessTest.run_honest_X] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
