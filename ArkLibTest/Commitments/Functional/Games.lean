/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Commitments.Functional.Basic

/-!
# Stateful commitment security games

A deterministic counter oracle distinguishes setup, commitment, and opening queries. These
clients check that setup state reaches the adversary, that opening state continues from the
commitment phase, and that extraction sees only the commitment-phase log.
-/

open OracleSpec OracleComp Commitment

namespace CommitmentGamesTest

private abbrev spec : OracleSpec Unit := fun _ => Fin 4
private abbrev protocol : ProtocolSpec 1 := ⟨fun _ => .P_to_V, fun _ => Unit⟩
private instance : ∀ i, VCVCompatible (protocol.Challenge i) := by
  rintro ⟨i, h⟩
  cases h

private abbrev Data := Unit → Fin 4
private def ask : OracleComp spec (Fin 4) := liftM (spec.query ())

private def counter : QueryImpl spec (StateT ℕ ProbComp) := fun _ => do
  let s ← get
  set (s + 1)
  pure ⟨s % 4, Nat.mod_lt _ (by decide)⟩

private def prover : Prover spec (Unit × (_q : Unit) × Fin 4) Unit Bool Unit protocol where
  PrvState _ := Unit
  input _ := ()
  sendMessage _ _ := pure ((), ())
  receiveChallenge i := by cases i with | mk i h => cases h
  output _ := pure (true, ())

private def scheme : Scheme spec Data Unit Unit (Fin 4) Unit protocol where
  keygen := do return (← ask, ())
  commit _ _ := pure ((), ())
  opening _ := {
    prover := {
      PrvState _ := Unit
      input _ := ()
      sendMessage _ _ := pure ((), ())
      receiveChallenge i := by cases i with | mk i h => cases h
      output _ := pure (true, ())
    }
    verifier := ⟨fun _ _ => do return (← ask) == (2 : Fin 4)⟩
  }

private def bindingAdversary : BindingAdversary spec Data Unit Unit protocol (Fin 4) where
  claim ck := do return ((), ⟨(), ck, ← ask, (), ()⟩)
  prover _ := prover

private def functionBindingAdversary :
    FunctionBindingAdversary spec Data Unit Unit 2 protocol (Fin 4) where
  claim ck := do
    let response ← ask
    pure ((), ⟨fun _ => (), (fun i => if i = 0 then ck else response), fun _ => ()⟩)
  prover _ := prover

private def extractabilityAdversary : ExtractabilityAdversary spec Data Unit Unit (Fin 4) :=
  fun ck => do
    let _ ← ask
    pure ((), ⟨(), ck, ()⟩)

private def extractor : StraightlineExtractor spec Data Unit :=
  fun _ log _ => match log with
    | [⟨_, response⟩] => response
    | _ => 3

private theorem mapM_pair {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (f : α → m β) (a b : α) :
    (#v[a, b]).mapM f = (do
      let x ← f a
      let y ← f b
      pure #v[x, y]) := by
  apply Vector.map_toArray_inj.mp
  simp [Array.mapM_eq_mapM_toList]

/-- Setup returns zero; commitment sees one; the two openings see two and three. -/
example : (bindingGame (pure 0) counter scheme Unit bindingAdversary).run =
    pure (some ⟨(), (0 : Fin 4), (1 : Fin 4), true, false⟩) := by
  rfl

/-- Function-binding openings also continue through the setup and commitment queries. -/
example : (do
    let result ← (functionBindingGame (pSpec := protocol) (pure 0) counter rfl Unit scheme
      functionBindingAdversary).run
    pure (result.map fun result => (result.2.2 0, result.2.2 1))) =
      (pure (some (true, false)) : ProbComp _) := by
  have hindices : Vector.ofFn (id : Fin 2 → Fin 2) = #v[0, 1] := by
    ext i hi
    interval_cases i <;> simp
  simp only [functionBindingGame, Reduction.allVerdicts, hindices, mapM_pair,
    bind_assoc, pure_bind]
  rfl

/-- The extractor reads the commitment query's response, excluding setup and opening queries. -/
private theorem extractabilityGame_run : (extractabilityGame (pure 0) counter scheme extractor Unit
    extractabilityAdversary prover).run =
      pure (some (true, (fun _ => (1 : Fin 4)), ⟨(), (0 : Fin 4)⟩)) := by
  rfl

/-- An accepted opening inconsistent with the extracted response has probability one. -/
example : extractabilityExperiment (pure 0) counter scheme extractor Unit
    extractabilityAdversary prover = 1 := by
  unfold extractabilityExperiment
  rw [OptionT.prEvent_eq_run, extractabilityGame_run]
  simp only [map_pure]
  change prEvent (pure ((true : Bool) = true ∧ (1 : Fin 4) ≠ 0) : ProbComp Prop) = 1
  simp

/-- The universal definition admits the trivial probability upper bound. -/
example : extractability (pure 0) counter scheme 1 := by
  refine ⟨extractor, fun _ _ _ => ?_⟩
  exact prEvent_le_one _

end CommitmentGamesTest
