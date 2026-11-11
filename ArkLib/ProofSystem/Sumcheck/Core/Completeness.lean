/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Execution
public import ArkLib.Interaction.Core.Security.Completeness

/-!
# Perfect completeness of Sumcheck in the interaction layer

The honest prover of the replicated Sumcheck protocol is accepted with probability one by the
interaction-layer verifier, on every input in the round-`0` Sumcheck relation. The accepted
output statement equals the prover's output statement and lies in the final Sumcheck relation,
and the output oracle is the input polynomial.

The proof runs the legacy decision fold along the honest transcript. `verdict_foldTranscript`
is the induction: it relates the prover's state with `k` remaining rounds to the fold's statement
at each round index under `Fin.succ` reindexing, through a relation that each round preserves. For
the honest prover the relation says that the two statements agree and satisfy the round's
relation; the round step uses the legacy facts `projected_sum_of_relationRound` and
`relationRound_projected_output`.

The main result is `perfectCompleteness`. It holds for every ambient state, ambient oracle
implementation and challenge implementation, since the honest run accepts on every challenge;
`perfectCompleteness_uniform` specializes it to uniform challenges, as in the legacy statement.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec MeasureTheory
open scoped ENNReal

/-! ## The legacy fold along a fold of pure rounds -/

section Fold

variable {R : Type} [CommSemiring R] {deg : ℕ} {State : ℕ → Type}


/-- The decoded transcript of one more round is the first round followed by the rest. -/
theorem decodeTranscript_foldTranscript_succ (msg : (k : ℕ) → State (k + 1) → R⦃≤ deg⦄[X])
    (next : (k : ℕ) → State (k + 1) → R → State k) (k : ℕ) (st : State (k + 1))
    (chals : Fin (k + 1) → R) :
    decodeTranscript (k + 1) (foldTranscript msg next (k + 1) st chals) =
      roundFullTranscript (msg k st) (chals 0) ++ₜ
        decodeTranscript k (foldTranscript msg next k (next k st (chals 0)) (Fin.tail chals)) :=
  rfl

/-- The legacy decision fold along a fold of pure rounds.

`Rel i r st s` relates the prover state with `r` remaining rounds to the fold's statement at round
index `i`. If each round check, run on the prover's message, accepts and preserves the relation,
then the whole fold accepts, and its result is related to the prover's final state. -/
theorem verdict_foldTranscript (msg : (k : ℕ) → State (k + 1) → R⦃≤ deg⦄[X])
    (next : (k : ℕ) → State (k + 1) → R → State k) :
    (k : ℕ) → (S : Fin (k + 1) → Type) →
    (V : (i : Fin k) → S i.castSucc → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) (S i.succ)) →
    (Rel : (i : Fin (k + 1)) → (r : ℕ) → State r → S i → Prop) →
    (∀ i r st s chal, Rel i.castSucc (r + 1) st s → ∃ s',
      simulateQ (OracleInterface.simOracle0 _ (roundFullTranscript (msg r st) chal).messages)
        (V i s (roundFullTranscript (msg r st) chal).challenges).run = some s' ∧
      Rel i.succ r (next r st chal) s') →
    (st : State k) → (s : S 0) → (chals : Fin k → R) → Rel 0 k st s → ∃ s',
      simulateQ (OracleInterface.simOracle0 (Spec.pSpec R deg k).Message
          (decodeTranscript k (foldTranscript msg next k st chals)).messages)
        (Spec.oracleVerifierProgram R deg S V s
          (decodeTranscript k (foldTranscript msg next k st chals)).challenges) = some s' ∧
      Rel (Fin.last k) 0 (foldState next k st chals) s'
  | 0, _, _, _, _, _, s, _, h => ⟨s, rfl, h⟩
  | k + 1, S, V, Rel, hstep, st, s, chals, h => by
    obtain ⟨s₁, hs₁, h₁⟩ := hstep 0 k st s (chals 0) h
    obtain ⟨s', hs', h'⟩ := verdict_foldTranscript msg next k (S ∘ Fin.succ) (fun i => V i.succ)
      (fun i r => Rel i.succ r) (fun i r => hstep i.succ r) _ s₁ (Fin.tail chals) h₁
    refine ⟨s', (simulateQ_oracleVerifierProgram_succ k S V s
      (roundFullTranscript (msg k st) (chals 0))
      (decodeTranscript k (foldTranscript msg next k (next k st (chals 0)) (Fin.tail chals)))).trans
        ?_, h'⟩
    rw [hs₁]
    exact hs'

end Fold

/-! ## The honest prover passes every round -/

section Honest

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {deg n : ℕ}
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)

/-- The honest prover's state agrees with the fold's statement, keeps the input polynomial, and
satisfies the Sumcheck relation of its round. -/
def HonestRel (p : Spec.OracleStatement R n deg ()) (i : Fin (n + 1)) (r : ℕ)
    (st : RoundState R deg n r) (s : Spec.StatementRound R n i) : Prop :=
  st.round = i ∧ HEq st.statement s ∧ st.poly = p ∧
    ((s, fun _ => st.poly), ()) ∈ Spec.relationRound R n deg D i

/-- An honest round passes its check and preserves `HonestRel`. -/
theorem honestRel_step (p : Spec.OracleStatement R n deg ()) (i : Fin n) (r : ℕ)
    (st : RoundState R deg n (r + 1)) (s : Spec.StatementRound R n i.castSucc) (chal : R)
    (h : HonestRel D p i.castSucc (r + 1) st s) : ∃ s',
      simulateQ (OracleInterface.simOracle0 _
          (roundFullTranscript (honestMessage D r st) chal).messages)
        (roundCheck R deg n D ambient i s
          (roundFullTranscript (honestMessage D r st) chal).challenges).run = some s' ∧
      HonestRel D p i.succ r (nextState (honestMessage D) r st chal) s' := by
  obtain ⟨round, hadd, stmt, poly⟩ := st
  obtain ⟨hround, hstmt, hpoly, hrel⟩ := h
  dsimp only at hround hstmt hpoly hrel
  subst hround
  cases eq_of_heq hstmt
  have hsum := Spec.SingleRound.projected_sum_of_relationRound R n deg D i _ poly hrel
  rw [Finset.sum_map_toList] at hsum
  refine ⟨_, roundCheck_eq_some i _ _ hsum, rfl, HEq.rfl, hpoly, ?_⟩
  exact Spec.SingleRound.relationRound_projected_output R n deg D i _ poly chal

/-- On an input in the round-`0` relation, the legacy verdict of the honest transcript accepts
the honest output statement, on every choice of challenges. -/
theorem legacyVerdict_honestTranscript (stmt : Spec.StatementRound R n 0)
    (oStmt : ∀ i, Spec.OracleStatement R n deg i)
    (h : ((stmt, oStmt), ()) ∈ Spec.relationRound R n deg D 0) (chals : Fin n → R) :
    legacyVerdict R deg n D ambient stmt (decodeTranscript n (honestTranscript D stmt oStmt chals))
        = some (honestOutput D stmt oStmt chals).1.1 ∧
      (honestOutput D stmt oStmt chals).1.2 = oStmt ∧
      ((honestOutput D stmt oStmt chals).1, ()) ∈ Spec.relationRound R n deg D (Fin.last n) := by
  obtain ⟨s', hs', hrel⟩ := verdict_foldTranscript (honestMessage D) (nextState (honestMessage D))
    n (Spec.StatementRound R n) (roundCheck R deg n D ambient) (HonestRel D (oStmt ()))
    (fun i r st s chal h => honestRel_step D ambient (oStmt ()) i r st s chal h)
    (initState stmt oStmt) stmt chals ⟨rfl, HEq.rfl, rfl, h⟩
  unfold honestOutput
  generalize foldState (nextState (honestMessage D)) n (initState stmt oStmt) chals = st at hrel
  obtain ⟨round, hadd, stmtF, poly⟩ := st
  obtain ⟨hround, hstmt, hpoly, hrelF⟩ := hrel
  dsimp only at hround hstmt hpoly hrelF
  subst hround
  cases eq_of_heq hstmt
  exact ⟨hs', funext fun _ => hpoly, hrelF⟩

end Honest

/-! ## Uniform challenges -/


/-! ## Completeness -/

section Completeness

variable (R : Type) [CommSemiring R] (deg n : ℕ) {d : ℕ} (D : Fin d ↪ R)

/-- The Sumcheck relation at round `i` as a problem with unit witness and no promise, with the
same statement type in every public context. -/
def relationProblem {Ctx : Type} (i : Fin (n + 1)) :
    Problem (⟨fun _ : Ctx => Spec.StatementRound R n i × ∀ j, Spec.OracleStatement R n deg j⟩ :
      ClaimFamily Ctx) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ x _ := (x, ()) ∈ Spec.relationRound R n deg D i
  rel_admissible _ _ _ _ := trivial

/-- The observation of a Sumcheck run with the honest prover's output type. -/
abbrev HonestObservation :=
  Observation oracleSig (protocol R deg n) (fun _ => HonestOutput R deg n)
    (fun _ => Spec.StatementRound R n (Fin.last n) × ∀ i, Spec.OracleStatement R n deg i)

/-- Judge a Sumcheck run by the verifier verdict and the statement in the prover output. -/
def judgement :
    OutputJudgement (HonestObservation R deg n)
      (relationProblem (Ctx := Path (protocol R deg n)) R deg n D (Fin.last n)) :=
  OutputJudgement.ofObservation _ (fun _ out => out.1) fun _ _ _ => ()

variable {R deg n} [DecidableEq R] [SampleableType R] {ι : Type} (ambient : OracleSpec ι)

/-- Perfect completeness of the interaction-layer Sumcheck.

For every ambient state, ambient oracle implementation and challenge implementation, the honest
prover on an input in the round-`0` relation is accepted with probability one; the accepted
statement is the prover's output statement and lies in the final relation. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig (protocol R deg n)) ProbComp) :
    letI : MeasurableSpace (HonestObservation R deg n) := ⊤
    completeness ((verifier R deg n D ambient).classicalModel init impl challenges)
      (relationProblem R deg n D 0) (relationProblem R deg n D (Fin.last n))
      (judgement R deg n D) (fun x _ => honestProver D x.1 x.2) 0 := by
  let : MeasurableSpace (HonestObservation R deg n) := ⊤
  let : MeasurableSpace (Fin n → R) := ⊤
  refine ⟨MeasurableSpace.measurableSet_top, fun x _ hx => ?_⟩
  rcases x with ⟨stmt, oStmt⟩
  change 1 - 0 ≤ 𝒟[experiment init impl challenges
    ((verifier R deg n D ambient).run stmt oStmt (honestProver D stmt oStmt))] _
  rw [run_verifier_honestProver, experiment_map, evalDist_map _ measurable_from_top,
    Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top, tsub_zero]
  refine le_of_eq_of_le (OracleComp.evalDist_apply_univ_eq_one _).symm
    (measure_mono fun chals _ => ?_)
  obtain ⟨hverdict, hout, hrel⟩ := legacyVerdict_honestTranscript D ambient stmt oStmt hx chals
  refine ⟨(honestOutput D stmt oStmt chals).1, ?_, rfl, hrel⟩
  change Option.map _ (legacyVerdict R deg n D ambient stmt _) = _
  rw [hverdict, Option.map_some]
  exact congrArg some (Prod.ext rfl hout.symm)

/-- Perfect completeness of the interaction-layer Sumcheck with uniformly sampled challenges. -/
theorem perfectCompleteness_uniform {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) :
    letI : MeasurableSpace (HonestObservation R deg n) := ⊤
    completeness ((verifier R deg n D ambient).classicalModel init impl
        (challengeQueryImpl oracleSig (protocol R deg n)))
      (relationProblem R deg n D 0) (relationProblem R deg n D (Fin.last n))
      (judgement R deg n D) (fun x _ => honestProver D x.1 x.2) 0 :=
  perfectCompleteness D ambient init impl _

end Completeness

end Sumcheck.Core
