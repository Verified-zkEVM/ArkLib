/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Fold

/-! # Sumcheck verifiers between arbitrary endpoints

The endpoint bounds the number of rounds, independently of the polynomial's number of variables.
Every domain index contributes to each sum check, including repeated points.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle
  OracleComp OracleSpec

variable {R : Type} [CommSemiring R] {deg n d : ℕ}

/-- A claim at a current round with a fixed endpoint and a remaining round count. -/
structure IntervalClaim (R : Type) (n : ℕ) (stop : Fin (n + 1)) (k : ℕ) where
  /-- The round at the start of the remaining interval. -/
  round : Fin (n + 1)
  /-- The remaining interval ends at `stop`. -/
  round_add : round.val + k = stop.val
  /-- The target and previously received challenges. -/
  statement : RoundStatement R n round

omit [CommSemiring R] in
/-- Equality of the current round and public statement determines an interval claim. -/
theorem IntervalClaim.ext {stop : Fin (n + 1)} {k : ℕ}
    {a b : IntervalClaim R n stop k} (hr : a.round = b.round)
    (hs : HEq a.statement b.statement) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

/-- The next variable exists whenever the interval contains another round. -/
def IntervalClaim.index {stop : Fin (n + 1)} {k : ℕ}
    (st : IntervalClaim R n stop (k + 1)) : Fin n :=
  ⟨st.round, by have := st.round_add; have := stop.isLt; omega⟩

/-- Extend the public prefix and replace its target by the message evaluation. -/
def IntervalClaim.next {stop : Fin (n + 1)} {k : ℕ}
    (st : IntervalClaim R n stop (k + 1)) (value r : R) : IntervalClaim R n stop k where
  round := st.index.succ
  round_add := by have := st.round_add; change st.round.val + 1 + k = stop.val; omega
  statement := ⟨value, Fin.snoc st.statement.challenges r⟩

/-- Read the public claim at the interval's endpoint. -/
def IntervalClaim.finish {stop : Fin (n + 1)} (st : IntervalClaim R n stop 0) :
    RoundStatement R n stop :=
  ⟨st.statement.target, st.statement.challenges ∘ Fin.cast (by
    have := st.round_add; omega)⟩

/-- Transport a public claim along equality of its round indices. -/
def RoundStatement.transport {i j : Fin (n + 1)} (h : i = j)
    (stmt : RoundStatement R n i) : RoundStatement R n j :=
  ⟨stmt.target, stmt.challenges ∘ Fin.cast (congrArg Fin.val h).symm⟩

omit [CommSemiring R] in
/-- Round transport preserves the target and challenge vector up to their index equality. -/
theorem RoundStatement.heq_transport {i j : Fin (n + 1)} (h : i = j)
    (stmt : RoundStatement R n i) : HEq stmt (stmt.transport h) := by
  subst j
  cases stmt
  rfl

/-- Transporting an endpoint preserves its indexed remaining-sum relation. -/
theorem indexedRelation_transport (D : Fin d → R) {i j : Fin (n + 1)} (h : i = j)
    (stmt : RoundStatement R n i) (p : R⦃≤ deg⦄[X Fin n]) :
    indexedRelation D j (stmt.transport h) p ↔ indexedRelation D i stmt p := by
  subst j
  cases stmt
  rfl

/-- Transport an internal interval claim along equality of its endpoints. -/
def IntervalClaim.transport {stop stop' : Fin (n + 1)} {k : ℕ} (h : stop = stop')
    (st : IntervalClaim R n stop k) : IntervalClaim R n stop' k :=
  ⟨st.round, st.round_add.trans (congrArg Fin.val h), st.statement⟩

/-- The initial state of an interval. -/
def intervalInitial (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) :
    IntervalClaim R n ⟨count + start, by omega⟩ count :=
  ⟨⟨start, by omega⟩, by change start + count = count + start; omega, stmt⟩

variable [DecidableEq R] (D : Fin d → R)

/-- Check the indexed sum, then query the polynomial at the public challenge. -/
def intervalCheck {stop : Fin (n + 1)} (k : ℕ) (st : IntervalClaim R n stop (k + 1))
    (r : R) : OptionT (OracleComp (R →ₒ R)) (IntervalClaim R n stop k) := OptionT.mk do
  let values ← (List.finRange d).mapM fun a => liftM ((R →ₒ R).query (D a))
  if values.sum = st.statement.target then
    let value ← liftM ((R →ₒ R).query r)
    return some (st.next value r)
  else return none

/-- A round's oracle check is exactly the indexed polynomial sum check. -/
theorem roundVerdict_intervalCheck {stop : Fin (n + 1)} (k : ℕ)
    (st : IntervalClaim R n stop (k + 1)) (msg : R⦃≤ deg⦄[X]) (r : R) :
    roundVerdict (intervalCheck D k) st msg r =
      if (∑ a : Fin d, msg.val.eval (D a)) = st.statement.target then
        some (st.next (msg.val.eval r) r) else none := by
  unfold roundVerdict Interpreted.roundVerdict
  change simulateQ _ ((List.finRange d).mapM (fun a => liftM ((R →ₒ R).query (D a))) >>= _) = _
  simp only [simulateQ_bind, simulateQ_list_mapM]
  change ((List.finRange d).mapM (fun a => (pure (msg.val.eval (D a)) : Id R)) >>= _) = _
  simp only [List.mapM_pure, LawfulMonad.pure_bind]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  split <;> rfl

/-- The transcript verdict for an interval claim. -/
noncomputable def intervalVerdict {stop : Fin (n + 1)} (k : ℕ)
    (st : IntervalClaim R n stop k) (tr : PathAlong oracleSig (protocol R deg k)) :
    Option (RoundStatement R n stop) := foldVerdict (intervalCheck D)
      IntervalClaim.finish k st tr

/-- Endpoint transport commutes with every transcript verdict. -/
theorem intervalVerdict_transport {stop stop' : Fin (n + 1)} (h : stop = stop') (k : ℕ)
    (st : IntervalClaim R n stop k) (tr : PathAlong oracleSig (protocol R deg k)) :
    (intervalVerdict D k st tr).map (RoundStatement.transport h) =
      intervalVerdict D k (st.transport h) tr := by
  subst stop'
  have hs : st.transport rfl = st := by cases st; rfl
  rw [hs]
  cases intervalVerdict D k st tr <;> rfl

/-- An interval is its first public one-round verdict followed by its public suffix verdict,
with the endpoint identified by associativity. -/
theorem intervalVerdict_succ_public (start count : ℕ) (bound : start + (count + 1) ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (msg : R⦃≤ deg⦄[X]) (r : R)
    (tail : PathAlong oracleSig (protocol R deg count)) :
    (intervalVerdict D (count + 1) (intervalInitial start (count + 1) bound stmt)
      (consTranscript msg r tail)).map
        (RoundStatement.transport (show (⟨count + 1 + start, by omega⟩ : Fin (n + 1)) =
          ⟨count + (1 + start), by omega⟩ from Fin.ext (by
            change count + 1 + start = count + (1 + start); omega))) =
      (intervalVerdict D 1 (intervalInitial start 1 (by omega) stmt)
        (roundTranscript msg r)).bind fun mid =>
          intervalVerdict D count (intervalInitial (1 + start) count (by omega) mid) tail := by
  rw [intervalVerdict_transport]
  unfold intervalVerdict
  rw [foldVerdict_succ, foldVerdict_succ, roundVerdict_intervalCheck, roundVerdict_intervalCheck]
  dsimp only [headMessage, headChallenge, tailTranscript, IntervalClaim.transport,
    intervalInitial, consTranscript, roundTranscript]
  by_cases h : (∑ a : Fin d, msg.val.eval (D a)) = stmt.target
  · simp only [h, ite_true, Option.bind_some]
    congr 1
    apply IntervalClaim.ext (Fin.ext (by
      change start + 1 = 1 + start
      omega))
    exact RoundStatement.heq_transport
      (i := ⟨start + 1, by omega⟩) (j := ⟨1 + start, by omega⟩)
      (Fin.ext (by change start + 1 = 1 + start; omega))
      ⟨msg.val.eval r, Fin.snoc stmt.challenges r⟩
  · simp only [h, ite_false, Option.bind_none]

/-- The verifier for `count` rounds beginning at `start`, retaining the input polynomial. -/
noncomputable def intervalVerifier (R : Type) [CommSemiring R] [DecidableEq R] (deg n : ℕ)
    {d : ℕ} (D : Fin d → R) {ι : Type} (ambient : OracleSpec ι)
    (start count : ℕ) (bound : start + count ≤ n) :
    OracleVerifier ambient (protocol R deg count) (RoundStatement R n ⟨start, by omega⟩)
      (fun _ => RoundStatement R n ⟨count + start, by omega⟩) (polynomialFamily R n deg)
      (fun _ => polynomialFamily R n deg) where
  decide stmt := (foldVerifier R deg ambient (polynomialFamily R n deg) (intervalCheck D)
    IntervalClaim.finish count).decide (intervalInitial start count bound stmt)
  outputMap _ _ _ := OracleMap.fst _ _

/-- Answering the interval verifier's final queries computes its transcript verdict. -/
theorem simulateQ_intervalVerifier_decide {ι : Type} {ambient : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl ambient m)
    (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ i, PolynomialData R n deg i)
    (tr : PathAlong oracleSig (protocol R deg count)) :
    simulateQ (QueryImpl.addLift impl ((pathResources (polynomialFamily R n deg)
      (protocol R deg count) (projectPathAlong oracleSig _ tr)).answer (data, payloads _ tr)))
      ((intervalVerifier R deg n D ambient start count bound).decide stmt _ (toView _ tr)).run =
      (pure (intervalVerdict D count (intervalInitial start count bound stmt) tr) : m _) :=
  Interpreted.simulate_verifier impl _ _ _ _ _ _

/-- The interval run is an actual interaction followed by the transcript's final decision. -/
theorem intervalVerifier_run {ι : Type} (ambient : OracleSpec ι)
    (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ i, PolynomialData R n deg i)
    {Out : PathAlong oracleSig (protocol R deg count) → Type}
    (prover : Prover oracleSig ambient (protocol R deg count) Out) :
    (intervalVerifier R deg n D ambient start count bound).run stmt data prover =
      (foldVerifier R deg ambient (polynomialFamily R n deg) (intervalCheck D)
        IntervalClaim.finish count).run (intervalInitial start count bound stmt) data prover := rfl

/-- A suffix claim has the same state as the native full-run verifier at that round. -/
def IntervalClaim.toIndexed {k : ℕ} (st : IntervalClaim R n (Fin.last n) k) :
    IndexedClaim R n k := ⟨st.round, st.round_add, st.statement⟩

/-- The interval and indexed verdicts agree for every suffix state and transcript. -/
theorem intervalVerdict_eq_indexed : ∀ (k : ℕ) (st : IntervalClaim R n (Fin.last n) k)
    (tr : PathAlong oracleSig (protocol R deg k)),
    intervalVerdict D k st tr = indexedVerdict D k (some st.toIndexed) tr := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro st tr
    unfold intervalVerdict
    rw [foldVerdict_succ, roundVerdict_intervalCheck]
    unfold indexedVerdict indexedNext
    dsimp only [IntervalClaim.toIndexed]
    simp only [Option.bind_some]
    split
    · simp only [Option.bind_some]
      exact ih _ (tailTranscript tr)
    · simp only [Option.bind_none]
      exact (indexedVerdict_none D k _).symm

end Sumcheck.Core
