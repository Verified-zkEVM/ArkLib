/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.StateRestoration
public import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Per-round errors in the state-restoration experiment

Each round of the protocol has its own local error. A challenge node's error is the error of its
round (`roundEps`, through `nodeRound`), and a key is charged the error of its round (`keyError`),
which is the error of its challenge node (`keyError_eq_roundEps`). An adaptive adversary with at
most `Q` queries pays at most `Q` times the largest round error on every branch, and completion pays
the sum of the round errors, so the restored execution has worst-case charge at most
`Q * max + sum` (`restoredExecution_round_cost`).
-/

@[expose] public section

namespace Interaction.Core.StateRestoration
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec

/-- Local errors indexed by round, in protocol order. -/
abbrev RoundErrors (rounds : List Round) := Fin rounds.length → ENNReal

/-- The round of a challenge node. -/
def nodeRound : (rounds : List Round) → ChallengeNode oracleSig (protocol rounds) →
    Fin rounds.length
  | [], ⟨n, _⟩ => n.elim
  | _ :: _, ⟨.inl _, h⟩ => nomatch h
  | _ :: _, ⟨.inr ⟨_, .inl _⟩, _⟩ => 0
  | _ :: rounds, ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, h⟩ => (nodeRound rounds ⟨n, h⟩).succ

/-- The error of a challenge node is the error of its round. -/
def roundEps {rounds : List Round} (errors : RoundErrors rounds) :
    ChallengeNode oracleSig (protocol rounds) → ENNReal :=
  errors ∘ nodeRound rounds

/-- A key is charged the error of its round. -/
def keyError {Input Salt : Type} : {rounds : List Round} → RoundErrors rounds →
    Key Input Salt rounds → ENNReal
  | [], _, key => nomatch key
  | _ :: _, errors, .inl _ => errors 0
  | _ :: _, errors, .inr (_, _, key) => keyError (fun j => errors j.succ) key

/-- A key's charge is the error of its challenge node. -/
theorem keyError_eq_roundEps {Input Salt : Type} : {rounds : List Round} →
    (errors : RoundErrors rounds) → (key : Key Input Salt rounds) →
    keyError errors key = roundEps errors (keyNode key)
  | [], _, key => key.elim
  | _ :: _, _, .inl _ => rfl
  | _ :: _, errors, .inr (_, _, key) => keyError_eq_roundEps (fun j => errors j.succ) key

/-- Every key's charge is at most the largest round error. -/
theorem keyError_le_max {Input Salt : Type} {rounds : List Round}
    (errors : RoundErrors rounds) (key : Key Input Salt rounds) :
    keyError errors key ≤ Finset.univ.sup errors := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
      cases key with
      | inl _ => exact Finset.le_sup (Finset.mem_univ (0 : Fin (rounds.length + 1)))
      | inr data =>
          apply (ih (fun j => errors j.succ) data.2.2).trans
          apply Finset.sup_le
          intro j _
          exact Finset.le_sup (Finset.mem_univ j.succ)

/-- Routing a key of the remaining rounds keeps its round's charge on every execution. -/
theorem costDist_prependQuery {Input Salt A : Type} {round : Round} {rounds : List Round}
    (errors : RoundErrors (round :: rounds)) (message : round.Message) (salt : Salt)
    (program : OracleComp (oracleSpec Input Salt rounds) A) :
    costDist (simulateQ (prependQuery message salt) program)
        (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt (round :: rounds)) ENNReal) =
      simulateQ (prependQuery message salt)
        (costDist program (⟨keyError (fun j => errors j.succ)⟩ :
          CostModel (oracleSpec Input Salt rounds) ENNReal)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [costDist, instrumentedRun]
  | query_bind key next ih =>
      simp only [costDist, instrumentedRun, QueryImpl.withAddCost, QueryImpl.ofLift_eq_id'] at ih
      simp [costDist, instrumentedRun, QueryImpl.withAddCost, prependQuery, OracleSpec.query,
        WriterT.run_bind, simulateQ_bind, simulateQ_query, bind_assoc, keyError, ih]

/-- A `Q`-query program pays at most `Q` times the largest round error on every branch. -/
theorem queryBound_round_cost {Input Salt A : Type} {rounds : List Round}
    (errors : RoundErrors rounds) (program : OracleComp (oracleSpec Input Salt rounds) A)
    (Q : Nat) (bounded : IsTotalQueryBound program Q) :
    WorstCaseCostBound program (⟨keyError errors⟩ :
      CostModel (oracleSpec Input Salt rounds) ENNReal) (Q * Finset.univ.sup errors) := by
  induction program using OracleComp.inductionOn generalizing Q with
  | pure value => simp
  | query_bind key next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      apply (worstCaseCostBound_query_bind_iff _ _ _ _).mpr
      intro response result supported
      have tail := ih response (Q - 1) (bounded.2 response) result supported
      calc
        keyError errors key + Multiplicative.toAdd result.2 ≤
            Finset.univ.sup errors + (Q - 1 : Nat) * Finset.univ.sup errors :=
          add_le_add (keyError_le_max errors key) tail
        _ = Q * Finset.univ.sup errors := by
          have hQ : Q = (Q - 1) + 1 := by omega
          conv_rhs => rw [hQ]
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

/-- Routing keys of the remaining rounds preserves a worst-case charge bound. -/
theorem roundCost_prependQuery {Input Salt A : Type} {round : Round} {rounds : List Round}
    (errors : RoundErrors (round :: rounds)) (message : round.Message) (salt : Salt)
    (program : OracleComp (oracleSpec Input Salt rounds) A) (budget : ENNReal)
    (bounded : WorstCaseCostBound program (⟨keyError (fun j => errors j.succ)⟩ :
      CostModel (oracleSpec Input Salt rounds) ENNReal) budget) :
    WorstCaseCostBound (simulateQ (prependQuery message salt) program)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt (round :: rounds)) ENNReal) budget := by
  intro result supported
  change result ∈ support (costDist _ _) at supported
  rw [costDist_prependQuery] at supported
  exact bounded result (support_simulateQ_subset _ _ supported)

/-- Completion pays one round error per round, hence the sum of the round errors. -/
theorem complete_round_cost {Input Salt : Type} (rounds : List Round) (errors : RoundErrors rounds)
    (z : Input) (messages : Messages Salt rounds) :
    WorstCaseCostBound (complete rounds z messages)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt rounds) ENNReal) (∑ j, errors j) := by
  induction rounds with
  | nil => exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [complete, List.length_cons]
      rw [Fin.sum_univ_succ]
      apply (worstCaseCostBound_query_bind_iff _ _ _ _).mpr
      intro challenge result supported
      have tail := roundCost_prependQuery errors message salt (complete rounds z messages) _
        (ih (fun j => errors j.succ) messages)
      have combined := tail.bind (fun tr => show WorstCaseCostBound
        (pure (⟨message, ⟨challenge, tr⟩⟩ : PathAlong oracleSig (protocol (round :: rounds))))
          (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt (round :: rounds)) ENNReal) 0 from
            by simp)
      have hcost := combined result supported
      simpa only [keyError, add_zero, zero_add, add_comm] using add_le_add_left hcost (errors 0)

/-- The adversary's and completion's charges add in the restored execution. -/
theorem restoredExecution_round_cost {Input Salt W : Type} (rounds : List Round)
    (errors : RoundErrors rounds)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : Nat) (bounded : IsTotalQueryBound adversary Q) :
    WorstCaseCostBound (restoredExecution rounds adversary)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt rounds) ENNReal)
      (Q * Finset.univ.sup errors + ∑ j, errors j) := by
  apply (queryBound_round_cost errors adversary Q bounded).bind
  rintro ⟨z, messages, witness⟩
  have completed := (complete_round_cost rounds errors z messages).bind
    (fun tr => show WorstCaseCostBound (pure (z, tr, witness))
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt rounds) ENNReal) 0 from by simp)
  simpa only [add_zero] using completed

end Interaction.Core.StateRestoration
