/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.PublicExecutionCorrespondence

/-! # Transport of native stopped completion through full-prefix key embeddings -/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- Interpret a suffix restoration key in an enclosing full-prefix oracle. -/
def embeddedQuery {Input : Type} {rounds allRounds : List Round}
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    QueryImpl (oracleSpec Input PUnit rounds)
      (OracleComp (oracleSpec Input PUnit allRounds)) :=
  fun key => (cast (preserve key)) <$>
    liftM ((oracleSpec Input PUnit allRounds).query (embed key))

private theorem embeddedQuery_comp_prepend {Input : Type} {round : Round}
    {rounds allRounds : List Round} (message : round.Message)
    (embed : Key Input PUnit (round :: rounds) → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    (embeddedQuery embed preserve) ∘ₛ (prependQuery message PUnit.unit) =
      embeddedQuery (fun key => embed (Key.later message PUnit.unit key))
        (fun key => preserve (Key.later message PUnit.unit key)) := by
  funext key
  simp only [QueryImpl.apply_compose, prependQuery, simulateQ_query,
    OracleQuery.cont_query, OracleQuery.input_query, id_map, embeddedQuery]

set_option backward.isDefEq.respectTransparency false in
theorem mappedStoppedComplete_eq_simulate {Input : Type} {allRounds : List Round}
    (rounds : List Round) (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : PublicMessages rounds)
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    mappedStoppedComplete rounds guards z messages embed preserve =
      simulateQ (embeddedQuery embed preserve)
        (stoppedComplete rounds guards z (withUnitSalts rounds messages)) := by
  induction rounds with
  | nil =>
      simp [mappedStoppedComplete, stoppedComplete, simulateQ_pure]
  | cons round rounds ih =>
      rcases guards with ⟨guard, next⟩
      rcases messages with ⟨message, messages⟩
      simp only [mappedStoppedComplete, stoppedComplete, withUnitSalts]
      cases hguard : guard z message PUnit.unit with
      | false => simp [simulateQ_pure]
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false,
            simulateQ_bind, simulateQ_pure, simulateQ_query,
            OracleQuery.cont_query, OracleQuery.input_query, id_map]
          simp only [embeddedQuery, bind_map_left, bind_pure_comp]
          apply bind_congr
          intro response
          rw [← QueryImpl.simulateQ_compose,
            embeddedQuery_comp_prepend message embed preserve]
          rw [← ih (next message PUnit.unit
            (cast (preserve (Key.here z message PUnit.unit)) response)) messages
            (fun key => embed (Key.later message PUnit.unit key))
            (fun key => preserve (Key.later message PUnit.unit key))]

private theorem embeddedQuery_id {Input : Type} (rounds : List Round) :
    embeddedQuery (Input := Input) (rounds := rounds) id (fun _ => rfl) =
      QueryImpl.id' (oracleSpec Input PUnit rounds) := by
  funext key
  change (cast (rfl : key.Challenge = key.Challenge)) <$>
    liftM ((oracleSpec Input PUnit rounds).query key) =
      liftM ((oracleSpec Input PUnit rounds).query key)
  have hcast : (cast (rfl : key.Challenge = key.Challenge)) =
      (id : key.Challenge → key.Challenge) := by
    funext x
    exact cast_eq _ x
  rw [hcast, id_map]

/-- Actual public strategy verification executes the native stopped completion, with the
same query order and stopping point, for the single-unit salt schedule. -/
theorem publicStoppedVerify_eq_stoppedComplete {Input : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : PublicMessages rounds) :
    publicStoppedVerify rounds guards z messages =
      stoppedComplete rounds guards z (withUnitSalts rounds messages) := by
  rw [publicStoppedVerify_eq_with, publicStoppedVerifyWith_eq_mapped,
    mappedStoppedComplete_eq_simulate, embeddedQuery_id, simulateQ_id']

end Interaction.Oracle.FiatShamir
