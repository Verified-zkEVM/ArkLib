/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Domain
public import ArkLib.ProofSystem.Sumcheck.Core.Execution
public import ArkLib.ProofSystem.Sumcheck.Core.IntervalSoundness
public import ArkLib.ProofSystem.Sumcheck.Core.IntervalCompleteness
public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-! # Indexed-domain compatibility with the injective Sumcheck specification

For an injective domain `D : Fin d ↪ R`, this file relates the indexed definitions of `Domain` to
the finite-set definitions of `Spec.SingleRound`: the honest projected polynomials
(`projectedRoundPolynomial_embedding`) and the remaining-sum relations
(`indexedRelation_embedding`). It also compares the verifiers after converting statements
fieldwise with `RoundStatement.ofSpec`. `legacyVerdict_map_ofSpec` equates the closed full-run
verdicts, `verifier_run_eq_indexedVerifier` and `verifier_run_full_interval` show that every
compatibility run is the indexed run and the zero-start interval run, and `honest_full_interval`
derives full compatibility honesty from interval completeness. A security transfer would also
need the matching relations, output maps and challenge draws. The interaction-layer soundness
proof in `Soundness` does not import this file.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial Finset PFunctor FreeM Interaction.Core
  Interaction.TwoParty.Lens Interaction.Oracle OracleComp OracleSpec ProtocolSpec
/-- The interaction layer's suffix assignment `roundSuffix` is the frozen legacy
`Spec.SingleRound.roundSuffix`, by definition. -/
theorem roundSuffix_eq_spec {R : Type} [CommSemiring R] {n : ℕ} (i : Fin n)
    (c : Fin i.castSucc → R) (x : Fin (n - 1 - i) → R) :
    roundSuffix i c x = Spec.SingleRound.roundSuffix R n i c x :=
  rfl

variable {R : Type} [CommSemiring R] {d n deg : ℕ}

/-- For an injective domain the indexed honest polynomial is Spec's projected polynomial. -/
theorem projectedRoundPolynomial_embedding (D : Fin d ↪ R) (i : Fin n)
    (c : Fin i.castSucc → R) (p : R⦃≤ deg⦄[X Fin n]) :
    projectedRoundPolynomial (⇑D) i c p =
      Spec.SingleRound.projectedRoundPolynomial R n deg D i c p := by
  apply Subtype.ext
  exact sum_domain_embedding D _ (fun x =>
    p.val.evalExcept i (roundSuffix i c x))

/-- The indexed relation agrees with the finite-set relation for an injective domain. -/
theorem indexedRelation_embedding (D : Fin d ↪ R) (i : Fin (n + 1))
    (stmt : Spec.StatementRound R n i) (p : R⦃≤ deg⦄[X Fin n]) :
    indexedRelation (⇑D) i ⟨stmt.target, stmt.challenges⟩ p ↔
      ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D i := by
  unfold indexedRelation roundSum
  rw [sum_domain_embedding D _ (fun x =>
    p.val.eval (Fin.append stmt.challenges x ∘ Fin.cast (by have := i.isLt; omega)))]
  rfl


/-- Convert a compatibility statement without changing its target or challenge prefix. -/
def RoundStatement.ofSpec {i : Fin (n + 1)} (stmt : Spec.StatementRound R n i) :
    RoundStatement R n i := ⟨stmt.target, stmt.challenges⟩

omit [CommSemiring R] in
/-- The fieldwise conversion of compatibility statements is injective. -/
theorem RoundStatement.ofSpec_injective {i : Fin (n + 1)} :
    Function.Injective (RoundStatement.ofSpec (R := R) (n := n) (i := i)) := by
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  cases h
  rfl

private def claimStep [DecidableEq R] (D : Fin d → R) (msg : R⦃≤ deg⦄[X]) (r : R)
    (st : (i : Fin (n + 1)) × RoundStatement R n i) :
    Option ((i : Fin (n + 1)) × RoundStatement R n i) :=
  if (∑ a : Fin d, msg.val.eval (D a)) = st.2.target then
    if h : st.1.val < n then
      some ⟨⟨st.1.val + 1, by omega⟩, ⟨msg.val.eval r, Fin.snoc st.2.challenges r⟩⟩
    else none
  else none

private def claimFold {S : Type} (step : R⦃≤ deg⦄[X] → R → S → Option S) :
    (k : ℕ) → Option S → Transcript oracleSig (protocol R deg k) → Option S
  | 0, st, _ => st
  | k + 1, st, tr => claimFold step k
      (st.bind (step (Interpreted.message tr) (Interpreted.challenge tr))) (Interpreted.tail tr)

private theorem claimFold_none {S : Type} (step : R⦃≤ deg⦄[X] → R → S → Option S) :
    (k : ℕ) → (tr : Transcript oracleSig (protocol R deg k)) →
    claimFold step k none tr = none
  | 0, _ => rfl
  | k + 1, tr => claimFold_none step k (Interpreted.tail tr)

private theorem legacyProgram_claimFold {X : Type}
    (step : R⦃≤ deg⦄[X] → R → X → Option X) :
    (k : ℕ) → (S : Fin (k + 1) → Type) →
    (V : (i : Fin k) → S i.castSucc → (Spec.SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(Spec.SingleRound.pSpec R deg).Message]ₒ) (S i.succ)) →
    (read : ∀ i, S i → X) →
    (∀ i stmt msg r,
      (simulateQ (OracleInterface.simOracle0 (Spec.SingleRound.pSpec R deg).Message
        (roundFullTranscript msg r).messages)
        (V i stmt (roundFullTranscript msg r).challenges).run).map (read i.succ) =
          step msg r (read i.castSucc stmt)) →
    (stmt : S 0) → (tr : Transcript oracleSig (protocol R deg k)) →
    (simulateQ (OracleInterface.simOracle0 (Spec.pSpec R deg k).Message
      (decodeTranscript k tr).messages)
      (Spec.oracleVerifierProgram R deg S V stmt (decodeTranscript k tr).challenges)).map
        (read (Fin.last k)) = claimFold step k (some (read 0 stmt)) tr := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro S V read hstep stmt tr
    rcases tr with ⟨msg, r, tail⟩
    change Option.map (read (Fin.last (k + 1)))
      (simulateQ (OracleInterface.simOracle0 (Spec.pSpec R deg (k + 1)).Message
        (roundFullTranscript msg r ++ₜ decodeTranscript k tail).messages)
        (Spec.oracleVerifierProgram R deg S V stmt
          (roundFullTranscript msg r ++ₜ decodeTranscript k tail).challenges)) = _
    rw [simulateQ_oracleVerifierProgram_succ]
    change _ = claimFold step k (step msg r (read 0 stmt)) tail
    have hhead := hstep 0 stmt msg r
    change Option.map _ _ = step msg r (read 0 stmt) at hhead
    rw [← hhead]
    cases h : simulateQ (OracleInterface.simOracle0 (Spec.SingleRound.pSpec R deg).Message
        (roundFullTranscript msg r).messages)
        (V 0 stmt (roundFullTranscript msg r).challenges).run with
    | none => simp only [Option.bind_none, Option.map_none, claimFold_none]
    | some mid =>
      simp only [Option.bind_some, Option.map_some]
      exact ih (S ∘ Fin.succ) (fun i => V i.succ) (fun i => read i.succ)
        (fun i => hstep i.succ) mid tail

private theorem indexedVerdict_claimFold [DecidableEq R] (D : Fin d → R) :
    (k : ℕ) → (st : Option (IndexedClaim R n k)) →
    (tr : Transcript oracleSig (protocol R deg k)) →
    (indexedVerdict D k st tr).map (fun t => (⟨Fin.last n, t⟩ :
      (i : Fin (n + 1)) × RoundStatement R n i)) =
      claimFold (claimStep D) k (st.map (fun st => ⟨st.round, st.statement⟩)) tr := by
  intro k
  induction k with
  | zero =>
    intro st tr
    cases st with
    | none => rfl
    | some st =>
      obtain ⟨i, hi, stmt⟩ := st
      have he : i = Fin.last n := Fin.ext (by simpa using hi)
      subst i
      rfl
  | succ k ih =>
    intro st tr
    rw [indexedVerdict_succ, ih]
    cases st with
    | none => rfl
    | some st =>
      have hlt : st.round.val < n := by have := st.round_add; omega
      simp only [claimFold, Option.map_some, Option.bind_some, claimStep, hlt, dite_true,
        indexedNext]
      split <;> rfl

/-- The compatibility and interaction-layer full-run verdicts agree after fieldwise statement
conversion. -/
theorem legacyVerdict_map_ofSpec [DecidableEq R] [SampleableType R]
    (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)
    (stmt : Spec.StatementRound R n 0) (tr : Transcript oracleSig (protocol R deg n)) :
    (legacyVerdict R deg n D ambient stmt (decodeTranscript n tr)).map RoundStatement.ofSpec =
      indexedVerdict (⇑D) n (some (IndexedClaim.initial (RoundStatement.ofSpec stmt))) tr := by
  have h := legacyProgram_claimFold (claimStep (⇑D)) n (Spec.StatementRound R n)
    (roundCheck R deg n D ambient) (fun i stmt => ⟨i, RoundStatement.ofSpec stmt⟩)
    (fun i s msg r => ?_) stmt tr
  · have hn := indexedVerdict_claimFold (⇑D) n
      (some (IndexedClaim.initial (RoundStatement.ofSpec stmt))) tr
    simp only [Option.map_some, IndexedClaim.initial] at hn
    rw [← hn] at h
    apply (Option.map_injective (f := fun t => (⟨Fin.last n, t⟩ :
      (i : Fin (n + 1)) × RoundStatement R n i)) (fun a b e => eq_of_heq (Sigma.mk.inj_iff.mp e).2))
    simpa only [legacyVerdict, legacyProgram, Option.map_map, Function.comp_def,
      IndexedClaim.initial] using h
  · by_cases hs : (∑ a : Fin d, msg.val.eval (D a)) = s.target
    · rw [roundCheck_eq_some i s (roundFullTranscript msg r) (by
        simpa [Finset.sum_map, roundFullTranscript] using hs)]
      simp [claimStep, RoundStatement.ofSpec, hs, roundFullTranscript]
      rfl
    · rw [roundCheck_eq_none i s (roundFullTranscript msg r) (by
        simpa [Finset.sum_map, roundFullTranscript] using hs)]
      simp [claimStep, RoundStatement.ofSpec, hs]

/-- Map a compatibility outcome to its interaction-layer statement representation, retaining the
transcript, private output and the original oracle data. -/
def outcomeOfSpec {s : OracleProtocol} {Out : Transcript oracleSig s → Type}
    {Data : Type}
    (obs : Outcome oracleSig s Out
      (fun _ => Spec.StatementRound R n (Fin.last n) × Data)) :
    Outcome oracleSig s Out
      (fun _ => RoundStatement R n (Fin.last n) × Data) :=
  ⟨obs.1, obs.2.1, obs.2.2.map (fun t => (RoundStatement.ofSpec t.1, t.2))⟩

/-- Every compatibility run is the interaction-layer indexed run after converting the verdict
statement. -/
theorem verifier_run_eq_indexedVerifier [DecidableEq R] [SampleableType R]
    (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)
    (stmt : Spec.StatementRound R n 0) (data : ∀ i, PolynomialData R n deg i)
    {Out : Transcript oracleSig (protocol R deg n) → Type}
    (P : Prover oracleSig ambient (protocol R deg n) Out) :
    outcomeOfSpec <$> (verifier R deg n D ambient).run stmt data P =
      (indexedVerifier R deg n (⇑D) ambient).run (RoundStatement.ofSpec stmt) data P := by
  rw [indexedVerifier_run]
  rw [OracleVerifier.run_eq]
  rw [_root_.map_bind]
  refine bind_congr fun x => ?_
  rcases x with ⟨tr, out, u⟩
  dsimp only
  rw [simulateQ_decide]
  simp only [LawfulMonad.pure_bind, LawfulApplicative.map_pure, outcomeOfSpec,
    Option.map_map]
  rw [← legacyVerdict_map_ofSpec D ambient stmt tr]
  simp only [verifier_outputMap, OracleMap.fst, Option.map_map]
  rfl

/-- The compatibility run is precisely the zero-start interaction-layer interval, including
arbitrary private continuations and output families. -/
theorem verifier_run_full_interval [DecidableEq R] [SampleableType R]
    (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)
    (stmt : Spec.StatementRound R n 0) (data : ∀ i, PolynomialData R n deg i)
    {Out : Transcript oracleSig (protocol R deg n) → Type}
    (P : Prover oracleSig ambient (protocol R deg n) Out) :
    outcomeOfSpec <$> (verifier R deg n D ambient).run stmt data P =
      (intervalVerifier R deg n (⇑D) ambient 0 n (by omega)).run
        (RoundStatement.ofSpec stmt) data P := by
  exact (verifier_run_eq_indexedVerifier D ambient stmt data P).trans
    (intervalVerifier_full_run (⇑D) ambient (RoundStatement.ofSpec stmt) data P).symm

/-- Interpret the public state of the compatibility honest prover as a full-suffix claim. -/
def IntervalClaim.ofRoundState {k : ℕ} (st : RoundState R deg n k) :
    IntervalClaim R n (Fin.last n) k :=
  ⟨st.round, st.round_add, RoundStatement.ofSpec st.statement⟩

private theorem IntervalClaim.ofRoundState_nextState (D : Fin d ↪ R)
    {k : ℕ} (st : RoundState R deg n (k + 1)) (r : R) :
    IntervalClaim.ofRoundState (nextState (honestMessage D) k st r) =
      intervalNext (⇑D) st.poly k (IntervalClaim.ofRoundState st) r := by
  change (IntervalClaim.ofRoundState st).next ((honestMessage D k st).val.eval r) r =
    (IntervalClaim.ofRoundState st).next
      ((projectedRoundPolynomial (⇑D) st.index st.statement.challenges st.poly).val.eval r) r
  exact congrArg
    (fun (msg : R⦃≤ deg⦄[X]) => (IntervalClaim.ofRoundState st).next (msg.val.eval r) r)
    (projectedRoundPolynomial_embedding D st.index st.statement.challenges st.poly).symm

/-- Compatibility honest transcripts and leaf states are the interaction-layer honest interval
fold. -/
theorem honestFold_eq_intervalFold (D : Fin d ↪ R) :
    (k : ℕ) → (st : RoundState R deg n k) → (chals : Fin k → R) →
    foldTranscript (eval := fun (p : R⦃≤ deg⦄[X]) x => p.val.eval x) (honestMessage D)
        (nextState (honestMessage D)) k st chals =
      foldTranscript (intervalMessage (⇑D) st.poly) (intervalNext (⇑D) st.poly) k
        (IntervalClaim.ofRoundState st) chals ∧
    IntervalClaim.ofRoundState (foldState (nextState (honestMessage D)) k st chals) =
      foldState (intervalNext (⇑D) st.poly) k (IntervalClaim.ofRoundState st) chals := by
  intro k
  induction k with
  | zero => intros; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro st chals
    have ht := ih (nextState (honestMessage D) k st (chals 0)) (Fin.tail chals)
    change _ ∧ IntervalClaim.ofRoundState (foldState (nextState (honestMessage D)) k
      (nextState (honestMessage D) k st (chals 0)) (Fin.tail chals)) = _
    constructor
    · simp only [foldTranscript]
      have hm : intervalMessage (⇑D) st.poly k (IntervalClaim.ofRoundState st) =
          honestMessage D k st := projectedRoundPolynomial_embedding D _ _ _
      rw [hm, ← IntervalClaim.ofRoundState_nextState]
      exact congrArg (consTranscript (honestMessage D k st) (chals 0)) ht.1
    · change _ = foldState (intervalNext (⇑D) st.poly) k
        (intervalNext (⇑D) st.poly k (IntervalClaim.ofRoundState st) (chals 0)) (Fin.tail chals)
      rw [← IntervalClaim.ofRoundState_nextState]
      exact ht.2

/-- The compatibility honest prover's public statement at the leaf is its interaction-layer interval
output. -/
theorem RoundStatement.ofSpec_finishState (st : RoundState R deg n 0) :
    RoundStatement.ofSpec (finishState st).1.1 = (IntervalClaim.ofRoundState st).finish := rfl

private theorem honestFold_poly (D : Fin d ↪ R) :
    (k : ℕ) → (st : RoundState R deg n k) → (chals : Fin k → R) →
    (foldState (nextState (honestMessage D)) k st chals).poly = st.poly
  | 0, _, _ => rfl
  | k + 1, st, chals => honestFold_poly D k
      (nextState (honestMessage D) k st (chals 0)) (Fin.tail chals)

/-- Full compatibility honesty follows from interaction-layer interval completeness at
endpoints `0, n`. The accepted statement equals the honest prover output, and the original
polynomial is retained. -/
theorem honest_full_interval [DecidableEq R] [SampleableType R]
    (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)
    (stmt : Spec.StatementRound R n 0) (data : ∀ i, Spec.OracleStatement R n deg i)
    (htrue : ((stmt, data), ()) ∈ Spec.relationRound R n deg D 0) (chals : Fin n → R) :
    legacyVerdict R deg n D ambient stmt
        (decodeTranscript n (honestTranscript D stmt data chals)) =
      some (honestOutput D stmt data chals).1.1 ∧
    (honestOutput D stmt data chals).1.2 = data ∧
    ((honestOutput D stmt data chals).1, ()) ∈ Spec.relationRound R n deg D (Fin.last n) := by
  have hi : indexedRelation (⇑D) 0 (RoundStatement.ofSpec stmt) (data ()) :=
    (indexedRelation_embedding D 0 stmt (data ())).mpr htrue
  have h := intervalVerdict_honest (⇑D) (initState stmt data).poly n
    (IntervalClaim.ofRoundState (initState stmt data)) hi chals
  have hf := honestFold_eq_intervalFold (n := n) D n (initState stmt data) chals
  change honestTranscript D stmt data chals = _ ∧ _ at hf
  rw [← hf.1, ← hf.2] at h
  have he := legacyVerdict_map_ofSpec D ambient stmt (honestTranscript D stmt data chals)
  have hv : legacyVerdict R deg n D ambient stmt
      (decodeTranscript n (honestTranscript D stmt data chals)) =
      some (honestOutput D stmt data chals).1.1 := by
    apply Option.map_injective RoundStatement.ofSpec_injective
    exact he.trans h.1
  have hd : (honestOutput D stmt data chals).1.2 = data := by
    funext u
    cases u
    exact honestFold_poly D n (initState stmt data) chals
  refine ⟨hv, hd, ?_⟩
  have hr := (indexedRelation_embedding D (Fin.last n)
    (honestOutput D stmt data chals).1.1 (data ())).mp h.2
  change (((honestOutput D stmt data chals).1.1,
    (honestOutput D stmt data chals).1.2), ()) ∈ _
  rw [hd]
  exact hr

end Sumcheck.Core
