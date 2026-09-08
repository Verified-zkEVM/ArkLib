/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.LoggedRun
import ArkLibTest.Interaction.Oracle.ExecutionExample
import ArkLibTest.Interaction.Oracle.CoreRunExample

/-!
# Logged execution acceptance clients

Reuse the existing branch-distinguishing strategies to test the new producer. These checks catch
lost source queries, reversed logs, wrong extension routing, reordered ambient effects, and
executing a terminal virtual oracle eagerly. No result is assembled from separate runs.
-/

namespace Interaction.Oracle.LoggedExecutionExample

open OracleComp OracleSpec
open ExecutionExample

/-- Observe the generic logged producer with the noncommutative ambient handler. -/
def observed (hidden : Nat) :=
  (simulateQ logImpl (executeStrategiesLogged ambient protocol.tree protocol.roles protocol.oracles
    inputSpec.toPFunctor inputImpl (prover hidden) verifier)).run []

/-- Public, receive, challenge, and terminal effects retain the existing schedule. -/
example (hidden : Nat) : (observed hidden).2 = [0, 1, 5, 2, 4, 3] := rfl

/-- Two receives isolate prior-slot routing and repeated terminal observations. -/
abbrev logProtocol : Oracle.Protocol :=
  .oracleWith (Nat × Nat) firstInterface <|
    .oracleWith (Nat × Nat) firstInterface .done

/-- Query the first message before the second is sent, then repeat a terminal source query. -/
def logVerifier : Verifier.Strategy ambient logProtocol.tree logProtocol.roles logProtocol.oracles
    inputSpec.toPFunctor (fun _ => Nat) := by
  change OracleComp (ambient + OracleSpec.ofPFunctor firstAccess)
    (OracleComp (ambient + OracleSpec.ofPFunctor finalAccess)
      (OracleComp (ambient + OracleSpec.ofPFunctor finalAccess) Nat))
  exact do
    let _ : Nat ← liftM
      ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inr (.inr ())))
    return pure (do
      let old : Nat ← liftM
        ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inr (.inl (.inl ()))))
      let latest : Nat ← liftM
        ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inr (.inr ())))
      let _ : Nat ← liftM
        ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inr (.inr ())))
      return old + latest)

/-- Concrete message answers differ, so exchanging source slots changes the evidence. -/
def logProver : Prover.Strategy ambient logProtocol.tree logProtocol.roles (fun _ => Unit) :=
  pure ⟨(11, 99), pure ⟨(19, 88), ()⟩⟩

/-- Query/answer observations produced by the executor, without replay. -/
def sourceObserved :=
  (simulateQ logImpl (executeStrategiesLogged ambient logProtocol.tree logProtocol.roles
    logProtocol.oracles inputSpec.toPFunctor inputImpl logProver logVerifier)).run []

/-- Routing keeps old slots and answers; repeated queries survive in order. -/
example : sourceObserved.1.deltaTrace =
    ([⟨Sum.inl (Sum.inr ()), (11 : Nat)⟩, ⟨Sum.inl (Sum.inl ()), (7 : Nat)⟩,
      ⟨Sum.inr (), (19 : Nat)⟩, ⟨Sum.inr (), (19 : Nat)⟩] :
      QueryLog (OracleSpec.ofPFunctor finalAccess)) := rfl

/-- Observe the supported claim-bearing executor. -/
def claimObserved (accept : Bool) (message hidden : Nat) :=
  (simulateQ CoreRunExample.logger
    (executeLogged (CoreRunExample.reduction accept) (fun _ => 7) () (message, hidden))).run []

/-- The terminal query is logged, while the deferred virtual output plan is not replayed. -/
example (hidden : Nat) :
    (claimObserved true 11 hidden).1.deltaTrace = [⟨Sum.inr (), (11 : Nat)⟩] := rfl

/-- Closing later uses the same paired message and input behavior. -/
example (hidden : Nat) :
    (claimObserved true 11 hidden).1.closed.map (fun claim => claim.oracles ⟨(), ()⟩) =
      some (18 : Nat) := rfl

/-- Explicit rejection retains the source observations already made. -/
example (hidden : Nat) :
    ((claimObserved false 19 hidden).1.closed,
      (claimObserved false 19 hidden).1.verifierLocalView.2.1) =
      (none, [⟨Sum.inr (), (19 : Nat)⟩]) := rfl

#print axioms executeStrategiesLogged_erase
#print axioms executeLogged_erase

end Interaction.Oracle.LoggedExecutionExample
